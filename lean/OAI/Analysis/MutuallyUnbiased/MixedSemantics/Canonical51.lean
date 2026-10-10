import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw6528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6528Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6528step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw6528step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6528step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6528step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6528step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6528step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6528 raw6528Labels = mixedMoment B node3461 node3461Labels := by
  calc
    mixedMoment B raw6528 raw6528Labels = mixedMoment B raw6528step0 raw6528step0Labels := by
      have ha : raw6528step0 = (fun i j => raw6528 (permutation155 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6528step0 raw6528; decide +kernel
      have hl : raw6528step0Labels = raw6528Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6528 raw6528Labels permutation155 permutation7
    mixedMoment B raw6528step0 raw6528step0Labels = mixedMoment B raw6528step1 raw6528step1Labels := by
      have ha : raw6528step1 = -raw6528step0 := by apply Matrix.ext; change ∀ i j, raw6528step1 i j = -(raw6528step0 i j); unfold raw6528step1 raw6528step0; decide +kernel
      have hl : raw6528step1Labels = raw6528step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6528step1 raw6528step1Labels = mixedMoment B raw6528step2 raw6528step2Labels := by
      have ha : raw6528step2 = raw6528step1 := by apply Matrix.ext; unfold raw6528step2 raw6528step1; decide +kernel
      have hl : raw6528step1Labels = labelEmbedding1 ∘ raw6528step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6528step1 raw6528step1Labels raw6528step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3461 node3461Labels := by rfl

def raw6529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6529Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6529step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw6529step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6529step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw6529step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6529step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw6529step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6529 raw6529Labels = mixedMoment B node2836 node2836Labels := by
  calc
    mixedMoment B raw6529 raw6529Labels = mixedMoment B raw6529step0 raw6529step0Labels := by
      have ha : raw6529step0 = (fun i j => raw6529 (permutation434 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6529step0 raw6529; decide +kernel
      have hl : raw6529step0Labels = raw6529Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6529 raw6529Labels permutation434 permutation5
    mixedMoment B raw6529step0 raw6529step0Labels = mixedMoment B raw6529step1 raw6529step1Labels := by
      have ha : raw6529step1 = -raw6529step0 := by apply Matrix.ext; change ∀ i j, raw6529step1 i j = -(raw6529step0 i j); unfold raw6529step1 raw6529step0; decide +kernel
      have hl : raw6529step1Labels = raw6529step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6529step1 raw6529step1Labels = mixedMoment B raw6529step2 raw6529step2Labels := by
      have ha : raw6529step2 = raw6529step1 := by apply Matrix.ext; unfold raw6529step2 raw6529step1; decide +kernel
      have hl : raw6529step1Labels = labelEmbedding1 ∘ raw6529step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6529step1 raw6529step1Labels raw6529step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2836 node2836Labels := by rfl

def raw6530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1]]
def raw6530Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw6530step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6530step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw6530step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6530step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6530step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6530step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6530step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6530 raw6530Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw6530 raw6530Labels = mixedMoment B raw6530step0 raw6530step0Labels := by
      have hz : ∀ j, raw6530 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw6530step0 = (fun i j => raw6530 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw6530step0 raw6530; decide +kernel
      have hl : raw6530step0Labels = raw6530Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6530 raw6530Labels permutation520 hz
    mixedMoment B raw6530step0 raw6530step0Labels = mixedMoment B raw6530step1 raw6530step1Labels := by
      have ha : raw6530step1 = (fun i j => raw6530step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6530step1 raw6530step0; decide +kernel
      have hl : raw6530step1Labels = raw6530step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6530step0 raw6530step0Labels permutation33 permutation7
    mixedMoment B raw6530step1 raw6530step1Labels = mixedMoment B raw6530step2 raw6530step2Labels := by
      have ha : raw6530step2 = -raw6530step1 := by apply Matrix.ext; change ∀ i j, raw6530step2 i j = -(raw6530step1 i j); unfold raw6530step2 raw6530step1; decide +kernel
      have hl : raw6530step2Labels = raw6530step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6530step2 raw6530step2Labels = mixedMoment B raw6530step3 raw6530step3Labels := by
      have ha : raw6530step3 = raw6530step2 := by apply Matrix.ext; unfold raw6530step3 raw6530step2; decide +kernel
      have hl : raw6530step2Labels = labelEmbedding1 ∘ raw6530step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6530step2 raw6530step2Labels raw6530step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3535 node3535Labels := by rfl

def raw6531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6531Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6531step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw6531step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6531step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6531step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6531step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6531step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6531 raw6531Labels = mixedMoment B node3526 node3526Labels := by
  calc
    mixedMoment B raw6531 raw6531Labels = mixedMoment B raw6531step0 raw6531step0Labels := by
      have ha : raw6531step0 = (fun i j => raw6531 (permutation155 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6531step0 raw6531; decide +kernel
      have hl : raw6531step0Labels = raw6531Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6531 raw6531Labels permutation155 permutation7
    mixedMoment B raw6531step0 raw6531step0Labels = mixedMoment B raw6531step1 raw6531step1Labels := by
      have ha : raw6531step1 = -raw6531step0 := by apply Matrix.ext; change ∀ i j, raw6531step1 i j = -(raw6531step0 i j); unfold raw6531step1 raw6531step0; decide +kernel
      have hl : raw6531step1Labels = raw6531step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6531step1 raw6531step1Labels = mixedMoment B raw6531step2 raw6531step2Labels := by
      have ha : raw6531step2 = raw6531step1 := by apply Matrix.ext; unfold raw6531step2 raw6531step1; decide +kernel
      have hl : raw6531step1Labels = labelEmbedding1 ∘ raw6531step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6531step1 raw6531step1Labels raw6531step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3526 node3526Labels := by rfl

def raw6532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6532Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6532step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6532step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw6532step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6532step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw6532step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6532step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw6532step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6532 raw6532Labels = mixedMoment B node3294 node3294Labels := by
  calc
    mixedMoment B raw6532 raw6532Labels = mixedMoment B raw6532step0 raw6532step0Labels := by
      have hz : ∀ j, raw6532 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6532step0 = (fun i j => raw6532 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6532step0 raw6532; decide +kernel
      have hl : raw6532step0Labels = raw6532Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6532 raw6532Labels permutation346 hz
    mixedMoment B raw6532step0 raw6532step0Labels = mixedMoment B raw6532step1 raw6532step1Labels := by
      have ha : raw6532step1 = (fun i j => raw6532step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6532step1 raw6532step0; decide +kernel
      have hl : raw6532step1Labels = raw6532step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6532step0 raw6532step0Labels permutation35 permutation7
    mixedMoment B raw6532step1 raw6532step1Labels = mixedMoment B raw6532step2 raw6532step2Labels := by
      have ha : raw6532step2 = -raw6532step1 := by apply Matrix.ext; change ∀ i j, raw6532step2 i j = -(raw6532step1 i j); unfold raw6532step2 raw6532step1; decide +kernel
      have hl : raw6532step2Labels = raw6532step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6532step2 raw6532step2Labels = mixedMoment B raw6532step3 raw6532step3Labels := by
      have ha : raw6532step3 = raw6532step2 := by apply Matrix.ext; unfold raw6532step3 raw6532step2; decide +kernel
      have hl : raw6532step2Labels = labelEmbedding1 ∘ raw6532step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6532step2 raw6532step2Labels raw6532step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3294 node3294Labels := by rfl

def raw6533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6533Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6533step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6533step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw6533step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6533step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw6533step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6533step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw6533step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6533 raw6533Labels = mixedMoment B node3471 node3471Labels := by
  calc
    mixedMoment B raw6533 raw6533Labels = mixedMoment B raw6533step0 raw6533step0Labels := by
      have hz : ∀ j, raw6533 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6533step0 = (fun i j => raw6533 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6533step0 raw6533; decide +kernel
      have hl : raw6533step0Labels = raw6533Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6533 raw6533Labels permutation346 hz
    mixedMoment B raw6533step0 raw6533step0Labels = mixedMoment B raw6533step1 raw6533step1Labels := by
      have ha : raw6533step1 = (fun i j => raw6533step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6533step1 raw6533step0; decide +kernel
      have hl : raw6533step1Labels = raw6533step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6533step0 raw6533step0Labels permutation35 permutation7
    mixedMoment B raw6533step1 raw6533step1Labels = mixedMoment B raw6533step2 raw6533step2Labels := by
      have ha : raw6533step2 = -raw6533step1 := by apply Matrix.ext; change ∀ i j, raw6533step2 i j = -(raw6533step1 i j); unfold raw6533step2 raw6533step1; decide +kernel
      have hl : raw6533step2Labels = raw6533step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6533step2 raw6533step2Labels = mixedMoment B raw6533step3 raw6533step3Labels := by
      have ha : raw6533step3 = raw6533step2 := by apply Matrix.ext; unfold raw6533step3 raw6533step2; decide +kernel
      have hl : raw6533step2Labels = labelEmbedding1 ∘ raw6533step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6533step2 raw6533step2Labels raw6533step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3471 node3471Labels := by rfl

def raw6534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6534Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6534step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw6534step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6534step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw6534step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6534step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw6534step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6534 raw6534Labels = mixedMoment B node3515 node3515Labels := by
  calc
    mixedMoment B raw6534 raw6534Labels = mixedMoment B raw6534step0 raw6534step0Labels := by
      have ha : raw6534step0 = (fun i j => raw6534 (permutation155 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6534step0 raw6534; decide +kernel
      have hl : raw6534step0Labels = raw6534Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6534 raw6534Labels permutation155 permutation7
    mixedMoment B raw6534step0 raw6534step0Labels = mixedMoment B raw6534step1 raw6534step1Labels := by
      have ha : raw6534step1 = -raw6534step0 := by apply Matrix.ext; change ∀ i j, raw6534step1 i j = -(raw6534step0 i j); unfold raw6534step1 raw6534step0; decide +kernel
      have hl : raw6534step1Labels = raw6534step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6534step1 raw6534step1Labels = mixedMoment B raw6534step2 raw6534step2Labels := by
      have ha : raw6534step2 = raw6534step1 := by apply Matrix.ext; unfold raw6534step2 raw6534step1; decide +kernel
      have hl : raw6534step1Labels = labelEmbedding1 ∘ raw6534step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6534step1 raw6534step1Labels raw6534step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3515 node3515Labels := by rfl

def raw6535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw6535Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw6535step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6535step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw6535step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6535step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw6535step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6535step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw6535step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6535step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw6535step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6535 raw6535Labels = mixedMoment B node3548 node3548Labels := by
  calc
    mixedMoment B raw6535 raw6535Labels = mixedMoment B raw6535step0 raw6535step0Labels := by
      have hz : ∀ j, raw6535 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw6535step0 = (fun i j => raw6535 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw6535step0 raw6535; decide +kernel
      have hl : raw6535step0Labels = raw6535Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6535 raw6535Labels permutation520 hz
    mixedMoment B raw6535step0 raw6535step0Labels = mixedMoment B raw6535step1 raw6535step1Labels := by
      have hz : ∀ j, raw6535step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6535step1 = (fun i j => raw6535step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6535step1 raw6535step0; decide +kernel
      have hl : raw6535step1Labels = raw6535step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6535step0 raw6535step0Labels permutation80 hz
    mixedMoment B raw6535step1 raw6535step1Labels = mixedMoment B raw6535step2 raw6535step2Labels := by
      have ha : raw6535step2 = (fun i j => raw6535step1 (permutation9 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6535step2 raw6535step1; decide +kernel
      have hl : raw6535step2Labels = raw6535step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6535step1 raw6535step1Labels permutation9 permutation7
    mixedMoment B raw6535step2 raw6535step2Labels = mixedMoment B raw6535step3 raw6535step3Labels := by
      have ha : raw6535step3 = -raw6535step2 := by apply Matrix.ext; change ∀ i j, raw6535step3 i j = -(raw6535step2 i j); unfold raw6535step3 raw6535step2; decide +kernel
      have hl : raw6535step3Labels = raw6535step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6535step3 raw6535step3Labels = mixedMoment B raw6535step4 raw6535step4Labels := by
      have ha : raw6535step4 = raw6535step3 := by apply Matrix.ext; unfold raw6535step4 raw6535step3; decide +kernel
      have hl : raw6535step3Labels = labelEmbedding1 ∘ raw6535step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6535step3 raw6535step3Labels raw6535step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3548 node3548Labels := by rfl

def raw6536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6536Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6536step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6536step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6536step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw6536step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6536step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6536step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6536step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6536step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6536 raw6536Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw6536 raw6536Labels = mixedMoment B raw6536step0 raw6536step0Labels := by
      have hz : ∀ j, raw6536 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6536step0 = (fun i j => raw6536 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6536step0 raw6536; decide +kernel
      have hl : raw6536step0Labels = raw6536Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6536 raw6536Labels permutation346 hz
    mixedMoment B raw6536step0 raw6536step0Labels = mixedMoment B raw6536step1 raw6536step1Labels := by
      have ha : raw6536step1 = (fun i j => raw6536step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6536step1 raw6536step0; decide +kernel
      have hl : raw6536step1Labels = raw6536step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6536step0 raw6536step0Labels permutation35 permutation7
    mixedMoment B raw6536step1 raw6536step1Labels = mixedMoment B raw6536step2 raw6536step2Labels := by
      have ha : raw6536step2 = -raw6536step1 := by apply Matrix.ext; change ∀ i j, raw6536step2 i j = -(raw6536step1 i j); unfold raw6536step2 raw6536step1; decide +kernel
      have hl : raw6536step2Labels = raw6536step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6536step2 raw6536step2Labels = mixedMoment B raw6536step3 raw6536step3Labels := by
      have ha : raw6536step3 = raw6536step2 := by apply Matrix.ext; unfold raw6536step3 raw6536step2; decide +kernel
      have hl : raw6536step2Labels = labelEmbedding1 ∘ raw6536step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6536step2 raw6536step2Labels raw6536step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3534 node3534Labels := by rfl

def raw6537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6537Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6537step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6537step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6537step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw6537step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6537step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw6537step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6537step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw6537step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6537 raw6537Labels = mixedMoment B node3243 node3243Labels := by
  calc
    mixedMoment B raw6537 raw6537Labels = mixedMoment B raw6537step0 raw6537step0Labels := by
      have hz : ∀ j, raw6537 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6537step0 = (fun i j => raw6537 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6537step0 raw6537; decide +kernel
      have hl : raw6537step0Labels = raw6537Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6537 raw6537Labels permutation346 hz
    mixedMoment B raw6537step0 raw6537step0Labels = mixedMoment B raw6537step1 raw6537step1Labels := by
      have ha : raw6537step1 = (fun i j => raw6537step0 (permutation39 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6537step1 raw6537step0; decide +kernel
      have hl : raw6537step1Labels = raw6537step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6537step0 raw6537step0Labels permutation39 permutation5
    mixedMoment B raw6537step1 raw6537step1Labels = mixedMoment B raw6537step2 raw6537step2Labels := by
      have ha : raw6537step2 = -raw6537step1 := by apply Matrix.ext; change ∀ i j, raw6537step2 i j = -(raw6537step1 i j); unfold raw6537step2 raw6537step1; decide +kernel
      have hl : raw6537step2Labels = raw6537step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6537step2 raw6537step2Labels = mixedMoment B raw6537step3 raw6537step3Labels := by
      have ha : raw6537step3 = raw6537step2 := by apply Matrix.ext; unfold raw6537step3 raw6537step2; decide +kernel
      have hl : raw6537step2Labels = labelEmbedding1 ∘ raw6537step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6537step2 raw6537step2Labels raw6537step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3243 node3243Labels := by rfl

def raw6538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6538Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6538step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6538step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6538step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw6538step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6538step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw6538step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6538step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw6538step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6538 raw6538Labels = mixedMoment B node3480 node3480Labels := by
  calc
    mixedMoment B raw6538 raw6538Labels = mixedMoment B raw6538step0 raw6538step0Labels := by
      have hz : ∀ j, raw6538 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6538step0 = (fun i j => raw6538 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6538step0 raw6538; decide +kernel
      have hl : raw6538step0Labels = raw6538Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6538 raw6538Labels permutation346 hz
    mixedMoment B raw6538step0 raw6538step0Labels = mixedMoment B raw6538step1 raw6538step1Labels := by
      have ha : raw6538step1 = (fun i j => raw6538step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6538step1 raw6538step0; decide +kernel
      have hl : raw6538step1Labels = raw6538step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6538step0 raw6538step0Labels permutation35 permutation7
    mixedMoment B raw6538step1 raw6538step1Labels = mixedMoment B raw6538step2 raw6538step2Labels := by
      have ha : raw6538step2 = -raw6538step1 := by apply Matrix.ext; change ∀ i j, raw6538step2 i j = -(raw6538step1 i j); unfold raw6538step2 raw6538step1; decide +kernel
      have hl : raw6538step2Labels = raw6538step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6538step2 raw6538step2Labels = mixedMoment B raw6538step3 raw6538step3Labels := by
      have ha : raw6538step3 = raw6538step2 := by apply Matrix.ext; unfold raw6538step3 raw6538step2; decide +kernel
      have hl : raw6538step2Labels = labelEmbedding1 ∘ raw6538step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6538step2 raw6538step2Labels raw6538step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3480 node3480Labels := by rfl

def raw6539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6539Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6539step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 2, 0]]
def raw6539step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6539step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw6539step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6539step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -2, 0]]
def raw6539step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6539 raw6539Labels = mixedMoment B node3518 node3518Labels := by
  calc
    mixedMoment B raw6539 raw6539Labels = mixedMoment B raw6539step0 raw6539step0Labels := by
      have ha : raw6539step0 = (fun i j => raw6539 (permutation155 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6539step0 raw6539; decide +kernel
      have hl : raw6539step0Labels = raw6539Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6539 raw6539Labels permutation155 permutation7
    mixedMoment B raw6539step0 raw6539step0Labels = mixedMoment B raw6539step1 raw6539step1Labels := by
      have ha : raw6539step1 = -raw6539step0 := by apply Matrix.ext; change ∀ i j, raw6539step1 i j = -(raw6539step0 i j); unfold raw6539step1 raw6539step0; decide +kernel
      have hl : raw6539step1Labels = raw6539step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6539step1 raw6539step1Labels = mixedMoment B raw6539step2 raw6539step2Labels := by
      have ha : raw6539step2 = raw6539step1 := by apply Matrix.ext; unfold raw6539step2 raw6539step1; decide +kernel
      have hl : raw6539step1Labels = labelEmbedding1 ∘ raw6539step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6539step1 raw6539step1Labels raw6539step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3518 node3518Labels := by rfl

def raw6540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6540Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6540step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6540step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6540step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw6540step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6540step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw6540step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6540step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw6540step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6540 raw6540Labels = mixedMoment B node2838 node2838Labels := by
  calc
    mixedMoment B raw6540 raw6540Labels = mixedMoment B raw6540step0 raw6540step0Labels := by
      have hz : ∀ j, raw6540 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6540step0 = (fun i j => raw6540 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6540step0 raw6540; decide +kernel
      have hl : raw6540step0Labels = raw6540Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6540 raw6540Labels permutation346 hz
    mixedMoment B raw6540step0 raw6540step0Labels = mixedMoment B raw6540step1 raw6540step1Labels := by
      have ha : raw6540step1 = (fun i j => raw6540step0 (permutation81 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6540step1 raw6540step0; decide +kernel
      have hl : raw6540step1Labels = raw6540step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6540step0 raw6540step0Labels permutation81 permutation5
    mixedMoment B raw6540step1 raw6540step1Labels = mixedMoment B raw6540step2 raw6540step2Labels := by
      have ha : raw6540step2 = -raw6540step1 := by apply Matrix.ext; change ∀ i j, raw6540step2 i j = -(raw6540step1 i j); unfold raw6540step2 raw6540step1; decide +kernel
      have hl : raw6540step2Labels = raw6540step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6540step2 raw6540step2Labels = mixedMoment B raw6540step3 raw6540step3Labels := by
      have ha : raw6540step3 = raw6540step2 := by apply Matrix.ext; unfold raw6540step3 raw6540step2; decide +kernel
      have hl : raw6540step2Labels = labelEmbedding1 ∘ raw6540step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6540step2 raw6540step2Labels raw6540step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2838 node2838Labels := by rfl

def raw6541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![1, 0, -1]]
def raw6541Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![1, 0, -1]]
def raw6541step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6541step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw6541step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6541step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6541step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6541step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6541step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6541 raw6541Labels = mixedMoment B node3541 node3541Labels := by
  calc
    mixedMoment B raw6541 raw6541Labels = mixedMoment B raw6541step0 raw6541step0Labels := by
      have hz : ∀ j, raw6541 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6541step0 = (fun i j => raw6541 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6541step0 raw6541; decide +kernel
      have hl : raw6541step0Labels = raw6541Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6541 raw6541Labels permutation346 hz
    mixedMoment B raw6541step0 raw6541step0Labels = mixedMoment B raw6541step1 raw6541step1Labels := by
      have ha : raw6541step1 = (fun i j => raw6541step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6541step1 raw6541step0; decide +kernel
      have hl : raw6541step1Labels = raw6541step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6541step0 raw6541step0Labels permutation35 permutation7
    mixedMoment B raw6541step1 raw6541step1Labels = mixedMoment B raw6541step2 raw6541step2Labels := by
      have ha : raw6541step2 = -raw6541step1 := by apply Matrix.ext; change ∀ i j, raw6541step2 i j = -(raw6541step1 i j); unfold raw6541step2 raw6541step1; decide +kernel
      have hl : raw6541step2Labels = raw6541step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6541step2 raw6541step2Labels = mixedMoment B raw6541step3 raw6541step3Labels := by
      have ha : raw6541step3 = raw6541step2 := by apply Matrix.ext; unfold raw6541step3 raw6541step2; decide +kernel
      have hl : raw6541step2Labels = labelEmbedding1 ∘ raw6541step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6541step2 raw6541step2Labels raw6541step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3541 node3541Labels := by rfl

def raw6542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6542Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6542step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6542step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw6542step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6542step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw6542step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6542step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw6542step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6542 raw6542Labels = mixedMoment B node3242 node3242Labels := by
  calc
    mixedMoment B raw6542 raw6542Labels = mixedMoment B raw6542step0 raw6542step0Labels := by
      have hz : ∀ j, raw6542 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6542step0 = (fun i j => raw6542 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6542step0 raw6542; decide +kernel
      have hl : raw6542step0Labels = raw6542Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6542 raw6542Labels permutation346 hz
    mixedMoment B raw6542step0 raw6542step0Labels = mixedMoment B raw6542step1 raw6542step1Labels := by
      have ha : raw6542step1 = (fun i j => raw6542step0 (permutation38 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6542step1 raw6542step0; decide +kernel
      have hl : raw6542step1Labels = raw6542step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6542step0 raw6542step0Labels permutation38 permutation5
    mixedMoment B raw6542step1 raw6542step1Labels = mixedMoment B raw6542step2 raw6542step2Labels := by
      have ha : raw6542step2 = -raw6542step1 := by apply Matrix.ext; change ∀ i j, raw6542step2 i j = -(raw6542step1 i j); unfold raw6542step2 raw6542step1; decide +kernel
      have hl : raw6542step2Labels = raw6542step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6542step2 raw6542step2Labels = mixedMoment B raw6542step3 raw6542step3Labels := by
      have ha : raw6542step3 = raw6542step2 := by apply Matrix.ext; unfold raw6542step3 raw6542step2; decide +kernel
      have hl : raw6542step2Labels = labelEmbedding1 ∘ raw6542step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6542step2 raw6542step2Labels raw6542step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3242 node3242Labels := by rfl

def raw6543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6543Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6543step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6543step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6543step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw6543step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6543step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -2, 0]]
def raw6543step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6543 raw6543Labels = mixedMoment B node3472 node3472Labels := by
  calc
    mixedMoment B raw6543 raw6543Labels = mixedMoment B raw6543step0 raw6543step0Labels := by
      have hz : ∀ j, raw6543 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6543step0 = (fun i j => raw6543 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6543step0 raw6543; decide +kernel
      have hl : raw6543step0Labels = raw6543Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6543 raw6543Labels permutation346 hz
    mixedMoment B raw6543step0 raw6543step0Labels = mixedMoment B raw6543step1 raw6543step1Labels := by
      have ha : raw6543step1 = (fun i j => raw6543step0 (permutation148 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6543step1 raw6543step0; decide +kernel
      have hl : raw6543step1Labels = raw6543step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6543step0 raw6543step0Labels permutation148 permutation5
    mixedMoment B raw6543step1 raw6543step1Labels = mixedMoment B raw6543step2 raw6543step2Labels := by
      have ha : raw6543step2 = raw6543step1 := by apply Matrix.ext; unfold raw6543step2 raw6543step1; decide +kernel
      have hl : raw6543step1Labels = labelEmbedding1 ∘ raw6543step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6543step1 raw6543step1Labels raw6543step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3472 node3472Labels := by rfl

def raw6544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6544Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6544step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw6544step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6544step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw6544step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6544 raw6544Labels = mixedMoment B node3437 node3437Labels := by
  calc
    mixedMoment B raw6544 raw6544Labels = mixedMoment B raw6544step0 raw6544step0Labels := by
      have ha : raw6544step0 = (fun i j => raw6544 (permutation673 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6544step0 raw6544; decide +kernel
      have hl : raw6544step0Labels = raw6544Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6544 raw6544Labels permutation673 permutation5
    mixedMoment B raw6544step0 raw6544step0Labels = mixedMoment B raw6544step1 raw6544step1Labels := by
      have ha : raw6544step1 = raw6544step0 := by apply Matrix.ext; unfold raw6544step1 raw6544step0; decide +kernel
      have hl : raw6544step0Labels = labelEmbedding1 ∘ raw6544step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6544step0 raw6544step0Labels raw6544step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3437 node3437Labels := by rfl

def raw6545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6545Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6545step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6545step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6545step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 2, -3], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw6545step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6545step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw6545step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6545step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw6545step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6545 raw6545Labels = mixedMoment B node2837 node2837Labels := by
  calc
    mixedMoment B raw6545 raw6545Labels = mixedMoment B raw6545step0 raw6545step0Labels := by
      have hz : ∀ j, raw6545 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6545step0 = (fun i j => raw6545 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6545step0 raw6545; decide +kernel
      have hl : raw6545step0Labels = raw6545Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6545 raw6545Labels permutation346 hz
    mixedMoment B raw6545step0 raw6545step0Labels = mixedMoment B raw6545step1 raw6545step1Labels := by
      have ha : raw6545step1 = (fun i j => raw6545step0 (permutation80 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6545step1 raw6545step0; decide +kernel
      have hl : raw6545step1Labels = raw6545step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6545step0 raw6545step0Labels permutation80 permutation5
    mixedMoment B raw6545step1 raw6545step1Labels = mixedMoment B raw6545step2 raw6545step2Labels := by
      have ha : raw6545step2 = -raw6545step1 := by apply Matrix.ext; change ∀ i j, raw6545step2 i j = -(raw6545step1 i j); unfold raw6545step2 raw6545step1; decide +kernel
      have hl : raw6545step2Labels = raw6545step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6545step2 raw6545step2Labels = mixedMoment B raw6545step3 raw6545step3Labels := by
      have ha : raw6545step3 = raw6545step2 := by apply Matrix.ext; unfold raw6545step3 raw6545step2; decide +kernel
      have hl : raw6545step2Labels = labelEmbedding1 ∘ raw6545step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6545step2 raw6545step2Labels raw6545step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2837 node2837Labels := by rfl

def raw6546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![0, 0, 0], ![3, -2, -1]]
def raw6546Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![3, -2, -1]]
def raw6546step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6546step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw6546step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6546step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw6546step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6546step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw6546step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6546 raw6546Labels = mixedMoment B node3549 node3549Labels := by
  calc
    mixedMoment B raw6546 raw6546Labels = mixedMoment B raw6546step0 raw6546step0Labels := by
      have hz : ∀ j, raw6546 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw6546step0 = (fun i j => raw6546 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw6546step0 raw6546; decide +kernel
      have hl : raw6546step0Labels = raw6546Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6546 raw6546Labels permutation520 hz
    mixedMoment B raw6546step0 raw6546step0Labels = mixedMoment B raw6546step1 raw6546step1Labels := by
      have hz : ∀ j, raw6546step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6546step1 = (fun i j => raw6546step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6546step1 raw6546step0; decide +kernel
      have hl : raw6546step1Labels = raw6546step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6546step0 raw6546step0Labels permutation80 hz
    mixedMoment B raw6546step1 raw6546step1Labels = mixedMoment B raw6546step2 raw6546step2Labels := by
      have ha : raw6546step2 = (fun i j => raw6546step1 (permutation28 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6546step2 raw6546step1; decide +kernel
      have hl : raw6546step2Labels = raw6546step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6546step1 raw6546step1Labels permutation28 permutation5
    mixedMoment B raw6546step2 raw6546step2Labels = mixedMoment B raw6546step3 raw6546step3Labels := by
      have ha : raw6546step3 = raw6546step2 := by apply Matrix.ext; unfold raw6546step3 raw6546step2; decide +kernel
      have hl : raw6546step2Labels = labelEmbedding1 ∘ raw6546step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6546step2 raw6546step2Labels raw6546step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3549 node3549Labels := by rfl

def raw6547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6547Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6547step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6547step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6547 raw6547Labels = mixedMoment B node2731 node2731Labels := by
  calc
    mixedMoment B raw6547 raw6547Labels = mixedMoment B raw6547step0 raw6547step0Labels := by
      have hz : ∀ j, raw6547 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6547step0 = (fun i j => raw6547 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6547step0 raw6547; decide +kernel
      have hl : raw6547step0Labels = raw6547Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6547 raw6547Labels permutation346 hz
    _ = mixedMoment B node2731 node2731Labels := by rfl

def raw6548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6548Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6548step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6548step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6548 raw6548Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw6548 raw6548Labels = mixedMoment B raw6548step0 raw6548step0Labels := by
      have hz : ∀ j, raw6548 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6548step0 = (fun i j => raw6548 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6548step0 raw6548; decide +kernel
      have hl : raw6548step0Labels = raw6548Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6548 raw6548Labels permutation346 hz
    _ = mixedMoment B node3813 node3813Labels := by rfl

def raw6549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6549Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6549step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6549step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6549 raw6549Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw6549 raw6549Labels = mixedMoment B raw6549step0 raw6549step0Labels := by
      have ha : raw6549step0 = (fun i j => raw6549 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6549step0 raw6549; decide +kernel
      have hl : raw6549step0Labels = raw6549Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6549 raw6549Labels permutation176 permutation2
    _ = mixedMoment B node3840 node3840Labels := by rfl

def raw6550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6550Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6550step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6550step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw6550step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6550step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw6550step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6550 raw6550Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw6550 raw6550Labels = mixedMoment B raw6550step0 raw6550step0Labels := by
      have hz : ∀ j, raw6550 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6550step0 = (fun i j => raw6550 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6550step0 raw6550; decide +kernel
      have hl : raw6550step0Labels = raw6550Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6550 raw6550Labels permutation346 hz
    mixedMoment B raw6550step0 raw6550step0Labels = mixedMoment B raw6550step1 raw6550step1Labels := by
      have ha : raw6550step1 = (fun i j => raw6550step0 (permutation85 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6550step1 raw6550step0; decide +kernel
      have hl : raw6550step1Labels = raw6550step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6550step0 raw6550step0Labels permutation85 permutation4
    mixedMoment B raw6550step1 raw6550step1Labels = mixedMoment B raw6550step2 raw6550step2Labels := by
      have ha : raw6550step2 = -raw6550step1 := by apply Matrix.ext; change ∀ i j, raw6550step2 i j = -(raw6550step1 i j); unfold raw6550step2 raw6550step1; decide +kernel
      have hl : raw6550step2Labels = raw6550step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2773 node2773Labels := by rfl

def raw6551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1]]
def raw6551Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6551step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw6551step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6551step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw6551step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6551 raw6551Labels = mixedMoment B node3907 node3907Labels := by
  calc
    mixedMoment B raw6551 raw6551Labels = mixedMoment B raw6551step0 raw6551step0Labels := by
      have hz : ∀ j, raw6551 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw6551step0 = (fun i j => raw6551 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw6551step0 raw6551; decide +kernel
      have hl : raw6551step0Labels = raw6551Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6551 raw6551Labels permutation520 hz
    mixedMoment B raw6551step0 raw6551step0Labels = mixedMoment B raw6551step1 raw6551step1Labels := by
      have hz : ∀ j, raw6551step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6551step1 = (fun i j => raw6551step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6551step1 raw6551step0; decide +kernel
      have hl : raw6551step1Labels = raw6551step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6551step0 raw6551step0Labels permutation80 hz
    _ = mixedMoment B node3907 node3907Labels := by rfl

def raw6552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6552Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6552step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6552step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6552 raw6552Labels = mixedMoment B node3906 node3906Labels := by
  calc
    mixedMoment B raw6552 raw6552Labels = mixedMoment B raw6552step0 raw6552step0Labels := by
      have hz : ∀ j, raw6552 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6552step0 = (fun i j => raw6552 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6552step0 raw6552; decide +kernel
      have hl : raw6552step0Labels = raw6552Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6552 raw6552Labels permutation346 hz
    _ = mixedMoment B node3906 node3906Labels := by rfl

def raw6553 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![2, -2], ![0, 0], ![1, -1]]
def raw6553Labels : Fin 2 → Fin 2 := ![0, 1]

def raw6553step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![2, -2], ![1, -1]]
def raw6553step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw6553step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]
def raw6553step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw6553step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw6553step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical6553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6553 raw6553Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw6553 raw6553Labels = mixedMoment B raw6553step0 raw6553step0Labels := by
      have hz : ∀ j, raw6553 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw6553step0 = (fun i j => raw6553 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw6553step0 raw6553; decide +kernel
      have hl : raw6553step0Labels = raw6553Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6553 raw6553Labels permutation520 hz
    mixedMoment B raw6553step0 raw6553step0Labels = mixedMoment B raw6553step1 raw6553step1Labels := by
      have hz : ∀ j, raw6553step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6553step1 = (fun i j => raw6553step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6553step1 raw6553step0; decide +kernel
      have hl : raw6553step1Labels = raw6553step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6553step0 raw6553step0Labels permutation80 hz
    mixedMoment B raw6553step1 raw6553step1Labels = mixedMoment B raw6553step2 raw6553step2Labels := by
      have ha : raw6553step2 = (fun i j => raw6553step1 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw6553step2 raw6553step1; decide +kernel
      have hl : raw6553step2Labels = raw6553step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6553step1 raw6553step1Labels permutation9 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw6554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6554Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6554step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6554step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw6554step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6554 raw6554Labels = mixedMoment B node1277 node1277Labels := by
  calc
    mixedMoment B raw6554 raw6554Labels = mixedMoment B raw6554step0 raw6554step0Labels := by
      have hz : ∀ j, raw6554 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6554step0 = (fun i j => raw6554 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6554step0 raw6554; decide +kernel
      have hl : raw6554step0Labels = raw6554Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6554 raw6554Labels permutation346 hz
    mixedMoment B raw6554step0 raw6554step0Labels = mixedMoment B raw6554step1 raw6554step1Labels := by
      have ha : raw6554step1 = (fun i j => raw6554step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6554step1 raw6554step0; decide +kernel
      have hl : raw6554step1Labels = raw6554step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6554step0 raw6554step0Labels permutation38 permutation2
    _ = mixedMoment B node1277 node1277Labels := by rfl

def raw6555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6555Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6555step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw6555step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6555 raw6555Labels = mixedMoment B node1222 node1222Labels := by
  calc
    mixedMoment B raw6555 raw6555Labels = mixedMoment B raw6555step0 raw6555step0Labels := by
      have ha : raw6555step0 = (fun i j => raw6555 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6555step0 raw6555; decide +kernel
      have hl : raw6555step0Labels = raw6555Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6555 raw6555Labels permutation158 permutation2
    _ = mixedMoment B node1222 node1222Labels := by rfl

def raw6556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6556Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6556step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6556step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6556step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw6556step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6556 raw6556Labels = mixedMoment B node1237 node1237Labels := by
  calc
    mixedMoment B raw6556 raw6556Labels = mixedMoment B raw6556step0 raw6556step0Labels := by
      have hz : ∀ j, raw6556 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6556step0 = (fun i j => raw6556 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6556step0 raw6556; decide +kernel
      have hl : raw6556step0Labels = raw6556Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6556 raw6556Labels permutation346 hz
    mixedMoment B raw6556step0 raw6556step0Labels = mixedMoment B raw6556step1 raw6556step1Labels := by
      have ha : raw6556step1 = (fun i j => raw6556step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6556step1 raw6556step0; decide +kernel
      have hl : raw6556step1Labels = raw6556step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6556step0 raw6556step0Labels permutation34 permutation2
    _ = mixedMoment B node1237 node1237Labels := by rfl

def raw6557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6557Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6557step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6557step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6557 raw6557Labels = mixedMoment B node1226 node1226Labels := by
  calc
    mixedMoment B raw6557 raw6557Labels = mixedMoment B raw6557step0 raw6557step0Labels := by
      have hz : ∀ j, raw6557 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6557step0 = (fun i j => raw6557 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6557step0 raw6557; decide +kernel
      have hl : raw6557step0Labels = raw6557Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6557 raw6557Labels permutation346 hz
    _ = mixedMoment B node1226 node1226Labels := by rfl

def raw6558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6558Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6558step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6558 raw6558Labels = mixedMoment B node1224 node1224Labels := by
  calc
    mixedMoment B raw6558 raw6558Labels = mixedMoment B raw6558step0 raw6558step0Labels := by
      have hz : ∀ j, raw6558 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6558step0 = (fun i j => raw6558 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6558step0 raw6558; decide +kernel
      have hl : raw6558step0Labels = raw6558Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6558 raw6558Labels permutation346 hz
    _ = mixedMoment B node1224 node1224Labels := by rfl

def raw6559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6559Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6559step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw6559step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6559 raw6559Labels = mixedMoment B node2577 node2577Labels := by
  calc
    mixedMoment B raw6559 raw6559Labels = mixedMoment B raw6559step0 raw6559step0Labels := by
      have ha : raw6559step0 = (fun i j => raw6559 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6559step0 raw6559; decide +kernel
      have hl : raw6559step0Labels = raw6559Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6559 raw6559Labels permutation182 permutation2
    _ = mixedMoment B node2577 node2577Labels := by rfl

def raw6560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6560Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6560step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6560step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6560step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw6560step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6560 raw6560Labels = mixedMoment B node2650 node2650Labels := by
  calc
    mixedMoment B raw6560 raw6560Labels = mixedMoment B raw6560step0 raw6560step0Labels := by
      have hz : ∀ j, raw6560 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6560step0 = (fun i j => raw6560 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6560step0 raw6560; decide +kernel
      have hl : raw6560step0Labels = raw6560Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6560 raw6560Labels permutation346 hz
    mixedMoment B raw6560step0 raw6560step0Labels = mixedMoment B raw6560step1 raw6560step1Labels := by
      have ha : raw6560step1 = (fun i j => raw6560step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6560step1 raw6560step0; decide +kernel
      have hl : raw6560step1Labels = raw6560step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6560step0 raw6560step0Labels permutation38 permutation2
    _ = mixedMoment B node2650 node2650Labels := by rfl

def raw6561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1]]
def raw6561Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6561step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1]]
def raw6561step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6561step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![2, -1, -1]]
def raw6561step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6561step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw6561step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6561 raw6561Labels = mixedMoment B node2774 node2774Labels := by
  calc
    mixedMoment B raw6561 raw6561Labels = mixedMoment B raw6561step0 raw6561step0Labels := by
      have hz : ∀ j, raw6561 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw6561step0 = (fun i j => raw6561 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw6561step0 raw6561; decide +kernel
      have hl : raw6561step0Labels = raw6561Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6561 raw6561Labels permutation520 hz
    mixedMoment B raw6561step0 raw6561step0Labels = mixedMoment B raw6561step1 raw6561step1Labels := by
      have hz : ∀ j, raw6561step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6561step1 = (fun i j => raw6561step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6561step1 raw6561step0; decide +kernel
      have hl : raw6561step1Labels = raw6561step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6561step0 raw6561step0Labels permutation80 hz
    mixedMoment B raw6561step1 raw6561step1Labels = mixedMoment B raw6561step2 raw6561step2Labels := by
      have ha : raw6561step2 = (fun i j => raw6561step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6561step2 raw6561step1; decide +kernel
      have hl : raw6561step2Labels = raw6561step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6561step1 raw6561step1Labels permutation10 permutation2
    _ = mixedMoment B node2774 node2774Labels := by rfl

def raw6562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6562Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6562step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6562step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6562step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw6562step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6562 raw6562Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw6562 raw6562Labels = mixedMoment B raw6562step0 raw6562step0Labels := by
      have hz : ∀ j, raw6562 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6562step0 = (fun i j => raw6562 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6562step0 raw6562; decide +kernel
      have hl : raw6562step0Labels = raw6562Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6562 raw6562Labels permutation346 hz
    mixedMoment B raw6562step0 raw6562step0Labels = mixedMoment B raw6562step1 raw6562step1Labels := by
      have ha : raw6562step1 = (fun i j => raw6562step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6562step1 raw6562step0; decide +kernel
      have hl : raw6562step1Labels = raw6562step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6562step0 raw6562step0Labels permutation38 permutation2
    _ = mixedMoment B node2773 node2773Labels := by rfl

def raw6563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6563Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6563step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw6563step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6563 raw6563Labels = mixedMoment B node2493 node2493Labels := by
  calc
    mixedMoment B raw6563 raw6563Labels = mixedMoment B raw6563step0 raw6563step0Labels := by
      have ha : raw6563step0 = (fun i j => raw6563 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6563step0 raw6563; decide +kernel
      have hl : raw6563step0Labels = raw6563Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6563 raw6563Labels permutation158 permutation2
    _ = mixedMoment B node2493 node2493Labels := by rfl

def raw6564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6564Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6564step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6564step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6564step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw6564step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6564 raw6564Labels = mixedMoment B node2512 node2512Labels := by
  calc
    mixedMoment B raw6564 raw6564Labels = mixedMoment B raw6564step0 raw6564step0Labels := by
      have hz : ∀ j, raw6564 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6564step0 = (fun i j => raw6564 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6564step0 raw6564; decide +kernel
      have hl : raw6564step0Labels = raw6564Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6564 raw6564Labels permutation346 hz
    mixedMoment B raw6564step0 raw6564step0Labels = mixedMoment B raw6564step1 raw6564step1Labels := by
      have ha : raw6564step1 = (fun i j => raw6564step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6564step1 raw6564step0; decide +kernel
      have hl : raw6564step1Labels = raw6564step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6564step0 raw6564step0Labels permutation34 permutation2
    _ = mixedMoment B node2512 node2512Labels := by rfl

def raw6565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6565Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6565step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6565step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6565 raw6565Labels = mixedMoment B node2499 node2499Labels := by
  calc
    mixedMoment B raw6565 raw6565Labels = mixedMoment B raw6565step0 raw6565step0Labels := by
      have hz : ∀ j, raw6565 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6565step0 = (fun i j => raw6565 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6565step0 raw6565; decide +kernel
      have hl : raw6565step0Labels = raw6565Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6565 raw6565Labels permutation346 hz
    _ = mixedMoment B node2499 node2499Labels := by rfl

def raw6566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6566Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6566step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6566step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6566 raw6566Labels = mixedMoment B node2495 node2495Labels := by
  calc
    mixedMoment B raw6566 raw6566Labels = mixedMoment B raw6566step0 raw6566step0Labels := by
      have hz : ∀ j, raw6566 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6566step0 = (fun i j => raw6566 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6566step0 raw6566; decide +kernel
      have hl : raw6566step0Labels = raw6566Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6566 raw6566Labels permutation346 hz
    _ = mixedMoment B node2495 node2495Labels := by rfl

def raw6567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![-1, 3, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6567Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6567step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw6567step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6567 raw6567Labels = mixedMoment B node2645 node2645Labels := by
  calc
    mixedMoment B raw6567 raw6567Labels = mixedMoment B raw6567step0 raw6567step0Labels := by
      have ha : raw6567step0 = (fun i j => raw6567 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6567step0 raw6567; decide +kernel
      have hl : raw6567step0Labels = raw6567Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6567 raw6567Labels permutation200 permutation2
    _ = mixedMoment B node2645 node2645Labels := by rfl

def raw6568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![0, 0, 0], ![2, -1, -1]]
def raw6568Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6568step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![2, -1, -1]]
def raw6568step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6568step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6568step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6568 raw6568Labels = mixedMoment B node2731 node2731Labels := by
  calc
    mixedMoment B raw6568 raw6568Labels = mixedMoment B raw6568step0 raw6568step0Labels := by
      have hz : ∀ j, raw6568 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw6568step0 = (fun i j => raw6568 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw6568step0 raw6568; decide +kernel
      have hl : raw6568step0Labels = raw6568Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6568 raw6568Labels permutation520 hz
    mixedMoment B raw6568step0 raw6568step0Labels = mixedMoment B raw6568step1 raw6568step1Labels := by
      have ha : raw6568step1 = (fun i j => raw6568step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6568step1 raw6568step0; decide +kernel
      have hl : raw6568step1Labels = raw6568step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6568step0 raw6568step0Labels permutation34 permutation2
    _ = mixedMoment B node2731 node2731Labels := by rfl

def raw6569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6569Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6569step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw6569step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6569 raw6569Labels = mixedMoment B node2730 node2730Labels := by
  calc
    mixedMoment B raw6569 raw6569Labels = mixedMoment B raw6569step0 raw6569step0Labels := by
      have ha : raw6569step0 = (fun i j => raw6569 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6569step0 raw6569; decide +kernel
      have hl : raw6569step0Labels = raw6569Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6569 raw6569Labels permutation158 permutation2
    _ = mixedMoment B node2730 node2730Labels := by rfl

def raw6570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6570Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6570step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw6570step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6570 raw6570Labels = mixedMoment B node2554 node2554Labels := by
  calc
    mixedMoment B raw6570 raw6570Labels = mixedMoment B raw6570step0 raw6570step0Labels := by
      have ha : raw6570step0 = (fun i j => raw6570 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6570step0 raw6570; decide +kernel
      have hl : raw6570step0Labels = raw6570Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6570 raw6570Labels permutation178 permutation2
    _ = mixedMoment B node2554 node2554Labels := by rfl

def raw6571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6571Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6571step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6571step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6571 raw6571Labels = mixedMoment B node2549 node2549Labels := by
  calc
    mixedMoment B raw6571 raw6571Labels = mixedMoment B raw6571step0 raw6571step0Labels := by
      have ha : raw6571step0 = (fun i j => raw6571 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6571step0 raw6571; decide +kernel
      have hl : raw6571step0Labels = raw6571Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6571 raw6571Labels permutation176 permutation2
    _ = mixedMoment B node2549 node2549Labels := by rfl

def raw6572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6572Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6572step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6572step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6572 raw6572Labels = mixedMoment B node2547 node2547Labels := by
  calc
    mixedMoment B raw6572 raw6572Labels = mixedMoment B raw6572step0 raw6572step0Labels := by
      have ha : raw6572step0 = (fun i j => raw6572 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6572step0 raw6572; decide +kernel
      have hl : raw6572step0Labels = raw6572Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6572 raw6572Labels permutation176 permutation2
    _ = mixedMoment B node2547 node2547Labels := by rfl

def raw6573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![0, 0, 0], ![2, -1, -1]]
def raw6573Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6573step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1]]
def raw6573step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6573step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw6573step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6573 raw6573Labels = mixedMoment B node2743 node2743Labels := by
  calc
    mixedMoment B raw6573 raw6573Labels = mixedMoment B raw6573step0 raw6573step0Labels := by
      have hz : ∀ j, raw6573 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw6573step0 = (fun i j => raw6573 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw6573step0 raw6573; decide +kernel
      have hl : raw6573step0Labels = raw6573Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6573 raw6573Labels permutation520 hz
    mixedMoment B raw6573step0 raw6573step0Labels = mixedMoment B raw6573step1 raw6573step1Labels := by
      have hz : ∀ j, raw6573step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6573step1 = (fun i j => raw6573step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6573step1 raw6573step0; decide +kernel
      have hl : raw6573step1Labels = raw6573step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6573step0 raw6573step0Labels permutation80 hz
    _ = mixedMoment B node2743 node2743Labels := by rfl

def raw6574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6574Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6574step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0], ![1, 0, -1]]
def raw6574step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6574step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw6574step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6574 raw6574Labels = mixedMoment B node2739 node2739Labels := by
  calc
    mixedMoment B raw6574 raw6574Labels = mixedMoment B raw6574step0 raw6574step0Labels := by
      have hz : ∀ j, raw6574 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6574step0 = (fun i j => raw6574 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6574step0 raw6574; decide +kernel
      have hl : raw6574step0Labels = raw6574Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6574 raw6574Labels permutation346 hz
    mixedMoment B raw6574step0 raw6574step0Labels = mixedMoment B raw6574step1 raw6574step1Labels := by
      have ha : raw6574step1 = (fun i j => raw6574step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6574step1 raw6574step0; decide +kernel
      have hl : raw6574step1Labels = raw6574step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6574step0 raw6574step0Labels permutation35 permutation2
    _ = mixedMoment B node2739 node2739Labels := by rfl

def raw6575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6575Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6575step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw6575step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6575step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![0, -1, 1], ![2, -2, 0], ![2, -1, -1]]
def raw6575step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6575 raw6575Labels = mixedMoment B node2649 node2649Labels := by
  calc
    mixedMoment B raw6575 raw6575Labels = mixedMoment B raw6575step0 raw6575step0Labels := by
      have hz : ∀ j, raw6575 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6575step0 = (fun i j => raw6575 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6575step0 raw6575; decide +kernel
      have hl : raw6575step0Labels = raw6575Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6575 raw6575Labels permutation346 hz
    mixedMoment B raw6575step0 raw6575step0Labels = mixedMoment B raw6575step1 raw6575step1Labels := by
      have ha : raw6575step1 = (fun i j => raw6575step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6575step1 raw6575step0; decide +kernel
      have hl : raw6575step1Labels = raw6575step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6575step0 raw6575step0Labels permutation38 permutation2
    _ = mixedMoment B node2649 node2649Labels := by rfl

def raw6576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6576Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6576step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 3, -2], ![1, -1, 0], ![3, -2, -1]]
def raw6576step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6576step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![3, -2, -1]]
def raw6576step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6576 raw6576Labels = mixedMoment B node2647 node2647Labels := by
  calc
    mixedMoment B raw6576 raw6576Labels = mixedMoment B raw6576step0 raw6576step0Labels := by
      have hz : ∀ j, raw6576 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6576step0 = (fun i j => raw6576 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6576step0 raw6576; decide +kernel
      have hl : raw6576step0Labels = raw6576Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6576 raw6576Labels permutation346 hz
    mixedMoment B raw6576step0 raw6576step0Labels = mixedMoment B raw6576step1 raw6576step1Labels := by
      have ha : raw6576step1 = (fun i j => raw6576step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6576step1 raw6576step0; decide +kernel
      have hl : raw6576step1Labels = raw6576step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6576step0 raw6576step0Labels permutation38 permutation2
    _ = mixedMoment B node2647 node2647Labels := by rfl

def raw6577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![1, 0, -1]]
def raw6577Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6577step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![1, 0, -1]]
def raw6577step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6577step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw6577step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6577 raw6577Labels = mixedMoment B node2732 node2732Labels := by
  calc
    mixedMoment B raw6577 raw6577Labels = mixedMoment B raw6577step0 raw6577step0Labels := by
      have hz : ∀ j, raw6577 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6577step0 = (fun i j => raw6577 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6577step0 raw6577; decide +kernel
      have hl : raw6577step0Labels = raw6577Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6577 raw6577Labels permutation346 hz
    mixedMoment B raw6577step0 raw6577step0Labels = mixedMoment B raw6577step1 raw6577step1Labels := by
      have ha : raw6577step1 = (fun i j => raw6577step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6577step1 raw6577step0; decide +kernel
      have hl : raw6577step1Labels = raw6577step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6577step0 raw6577step0Labels permutation33 permutation2
    _ = mixedMoment B node2732 node2732Labels := by rfl

def raw6578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6578Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6578step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6578step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6578step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw6578step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6578step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw6578step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6578 raw6578Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw6578 raw6578Labels = mixedMoment B raw6578step0 raw6578step0Labels := by
      have hz : ∀ j, raw6578 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6578step0 = (fun i j => raw6578 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6578step0 raw6578; decide +kernel
      have hl : raw6578step0Labels = raw6578Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6578 raw6578Labels permutation346 hz
    mixedMoment B raw6578step0 raw6578step0Labels = mixedMoment B raw6578step1 raw6578step1Labels := by
      have ha : raw6578step1 = (fun i j => raw6578step0 (permutation102 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6578step1 raw6578step0; decide +kernel
      have hl : raw6578step1Labels = raw6578step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6578step0 raw6578step0Labels permutation102 permutation4
    mixedMoment B raw6578step1 raw6578step1Labels = mixedMoment B raw6578step2 raw6578step2Labels := by
      have ha : raw6578step2 = raw6578step1 := by apply Matrix.ext; unfold raw6578step2 raw6578step1; decide +kernel
      have hl : raw6578step1Labels = labelEmbedding7 ∘ raw6578step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6578step1 raw6578step1Labels raw6578step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

def raw6579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6579Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6579step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw6579step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6579step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw6579step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6579 raw6579Labels = mixedMoment B node5445 node5445Labels := by
  calc
    mixedMoment B raw6579 raw6579Labels = mixedMoment B raw6579step0 raw6579step0Labels := by
      have ha : raw6579step0 = (fun i j => raw6579 (permutation515 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6579step0 raw6579; decide +kernel
      have hl : raw6579step0Labels = raw6579Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6579 raw6579Labels permutation515 permutation4
    mixedMoment B raw6579step0 raw6579step0Labels = mixedMoment B raw6579step1 raw6579step1Labels := by
      have ha : raw6579step1 = raw6579step0 := by apply Matrix.ext; unfold raw6579step1 raw6579step0; decide +kernel
      have hl : raw6579step0Labels = labelEmbedding7 ∘ raw6579step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6579step0 raw6579step0Labels raw6579step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5445 node5445Labels := by rfl

def raw6580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6580Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6580step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6580step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6580step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw6580step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6580 raw6580Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw6580 raw6580Labels = mixedMoment B raw6580step0 raw6580step0Labels := by
      have hz : ∀ j, raw6580 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6580step0 = (fun i j => raw6580 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6580step0 raw6580; decide +kernel
      have hl : raw6580step0Labels = raw6580Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6580 raw6580Labels permutation346 hz
    mixedMoment B raw6580step0 raw6580step0Labels = mixedMoment B raw6580step1 raw6580step1Labels := by
      have ha : raw6580step1 = (fun i j => raw6580step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6580step1 raw6580step0; decide +kernel
      have hl : raw6580step1Labels = raw6580step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6580step0 raw6580step0Labels permutation38 permutation2
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw6581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1]]
def raw6581Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6581step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1]]
def raw6581step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6581step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw6581step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6581step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw6581step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6581 raw6581Labels = mixedMoment B node5448 node5448Labels := by
  calc
    mixedMoment B raw6581 raw6581Labels = mixedMoment B raw6581step0 raw6581step0Labels := by
      have hz : ∀ j, raw6581 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6581step0 = (fun i j => raw6581 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6581step0 raw6581; decide +kernel
      have hl : raw6581step0Labels = raw6581Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6581 raw6581Labels permutation346 hz
    mixedMoment B raw6581step0 raw6581step0Labels = mixedMoment B raw6581step1 raw6581step1Labels := by
      have ha : raw6581step1 = (fun i j => raw6581step0 (permutation98 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6581step1 raw6581step0; decide +kernel
      have hl : raw6581step1Labels = raw6581step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6581step0 raw6581step0Labels permutation98 permutation4
    mixedMoment B raw6581step1 raw6581step1Labels = mixedMoment B raw6581step2 raw6581step2Labels := by
      have ha : raw6581step2 = raw6581step1 := by apply Matrix.ext; unfold raw6581step2 raw6581step1; decide +kernel
      have hl : raw6581step1Labels = labelEmbedding7 ∘ raw6581step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6581step1 raw6581step1Labels raw6581step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5448 node5448Labels := by rfl

def raw6582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw6582Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6582step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw6582step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6582step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw6582step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6582step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw6582step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw6582step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw6582step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6582 raw6582Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw6582 raw6582Labels = mixedMoment B raw6582step0 raw6582step0Labels := by
      have hz : ∀ j, raw6582 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6582step0 = (fun i j => raw6582 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6582step0 raw6582; decide +kernel
      have hl : raw6582step0Labels = raw6582Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6582 raw6582Labels permutation346 hz
    mixedMoment B raw6582step0 raw6582step0Labels = mixedMoment B raw6582step1 raw6582step1Labels := by
      have ha : raw6582step1 = (fun i j => raw6582step0 (permutation83 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6582step1 raw6582step0; decide +kernel
      have hl : raw6582step1Labels = raw6582step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6582step0 raw6582step0Labels permutation83 permutation6
    mixedMoment B raw6582step1 raw6582step1Labels = mixedMoment B raw6582step2 raw6582step2Labels := by
      have ha : raw6582step2 = -raw6582step1 := by apply Matrix.ext; change ∀ i j, raw6582step2 i j = -(raw6582step1 i j); unfold raw6582step2 raw6582step1; decide +kernel
      have hl : raw6582step2Labels = raw6582step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6582step2 raw6582step2Labels = mixedMoment B raw6582step3 raw6582step3Labels := by
      have ha : raw6582step3 = raw6582step2 := by apply Matrix.ext; unfold raw6582step3 raw6582step2; decide +kernel
      have hl : raw6582step2Labels = labelEmbedding9 ∘ raw6582step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6582step2 raw6582step2Labels raw6582step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw6583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6583Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6583step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6583step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6583step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw6583step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6583step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw6583step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6583 raw6583Labels = mixedMoment B node4474 node4474Labels := by
  calc
    mixedMoment B raw6583 raw6583Labels = mixedMoment B raw6583step0 raw6583step0Labels := by
      have hz : ∀ j, raw6583 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6583step0 = (fun i j => raw6583 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6583step0 raw6583; decide +kernel
      have hl : raw6583step0Labels = raw6583Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6583 raw6583Labels permutation346 hz
    mixedMoment B raw6583step0 raw6583step0Labels = mixedMoment B raw6583step1 raw6583step1Labels := by
      have ha : raw6583step1 = (fun i j => raw6583step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6583step1 raw6583step0; decide +kernel
      have hl : raw6583step1Labels = raw6583step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6583step0 raw6583step0Labels permutation38 permutation3
    mixedMoment B raw6583step1 raw6583step1Labels = mixedMoment B raw6583step2 raw6583step2Labels := by
      have ha : raw6583step2 = raw6583step1 := by apply Matrix.ext; unfold raw6583step2 raw6583step1; decide +kernel
      have hl : raw6583step1Labels = labelEmbedding6 ∘ raw6583step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6583step1 raw6583step1Labels raw6583step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4474 node4474Labels := by rfl

def raw6584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6584Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6584step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw6584step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6584step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw6584step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6584 raw6584Labels = mixedMoment B node5085 node5085Labels := by
  calc
    mixedMoment B raw6584 raw6584Labels = mixedMoment B raw6584step0 raw6584step0Labels := by
      have ha : raw6584step0 = (fun i j => raw6584 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6584step0 raw6584; decide +kernel
      have hl : raw6584step0Labels = raw6584Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6584 raw6584Labels permutation182 permutation3
    mixedMoment B raw6584step0 raw6584step0Labels = mixedMoment B raw6584step1 raw6584step1Labels := by
      have ha : raw6584step1 = raw6584step0 := by apply Matrix.ext; unfold raw6584step1 raw6584step0; decide +kernel
      have hl : raw6584step0Labels = labelEmbedding6 ∘ raw6584step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6584step0 raw6584step0Labels raw6584step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5085 node5085Labels := by rfl

def raw6585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6585Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6585step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6585step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6585step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw6585step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6585step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw6585step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6585 raw6585Labels = mixedMoment B node5203 node5203Labels := by
  calc
    mixedMoment B raw6585 raw6585Labels = mixedMoment B raw6585step0 raw6585step0Labels := by
      have hz : ∀ j, raw6585 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6585step0 = (fun i j => raw6585 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6585step0 raw6585; decide +kernel
      have hl : raw6585step0Labels = raw6585Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6585 raw6585Labels permutation346 hz
    mixedMoment B raw6585step0 raw6585step0Labels = mixedMoment B raw6585step1 raw6585step1Labels := by
      have ha : raw6585step1 = (fun i j => raw6585step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6585step1 raw6585step0; decide +kernel
      have hl : raw6585step1Labels = raw6585step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6585step0 raw6585step0Labels permutation38 permutation3
    mixedMoment B raw6585step1 raw6585step1Labels = mixedMoment B raw6585step2 raw6585step2Labels := by
      have ha : raw6585step2 = raw6585step1 := by apply Matrix.ext; unfold raw6585step2 raw6585step1; decide +kernel
      have hl : raw6585step1Labels = labelEmbedding6 ∘ raw6585step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6585step1 raw6585step1Labels raw6585step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5203 node5203Labels := by rfl

def raw6586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1]]
def raw6586Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6586step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1]]
def raw6586step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6586step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6586step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6586step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6586step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6586 raw6586Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw6586 raw6586Labels = mixedMoment B raw6586step0 raw6586step0Labels := by
      have hz : ∀ j, raw6586 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6586step0 = (fun i j => raw6586 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6586step0 raw6586; decide +kernel
      have hl : raw6586step0Labels = raw6586Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6586 raw6586Labels permutation346 hz
    mixedMoment B raw6586step0 raw6586step0Labels = mixedMoment B raw6586step1 raw6586step1Labels := by
      have ha : raw6586step1 = (fun i j => raw6586step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6586step1 raw6586step0; decide +kernel
      have hl : raw6586step1Labels = raw6586step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6586step0 raw6586step0Labels permutation46 permutation3
    mixedMoment B raw6586step1 raw6586step1Labels = mixedMoment B raw6586step2 raw6586step2Labels := by
      have ha : raw6586step2 = raw6586step1 := by apply Matrix.ext; unfold raw6586step2 raw6586step1; decide +kernel
      have hl : raw6586step1Labels = labelEmbedding6 ∘ raw6586step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6586step1 raw6586step1Labels raw6586step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

def raw6587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw6587Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw6587step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6587step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw6587step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6587step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw6587step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6587 raw6587Labels = mixedMoment B node5301 node5301Labels := by
  calc
    mixedMoment B raw6587 raw6587Labels = mixedMoment B raw6587step0 raw6587step0Labels := by
      have hz : ∀ j, raw6587 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6587step0 = (fun i j => raw6587 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6587step0 raw6587; decide +kernel
      have hl : raw6587step0Labels = raw6587Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6587 raw6587Labels permutation346 hz
    mixedMoment B raw6587step0 raw6587step0Labels = mixedMoment B raw6587step1 raw6587step1Labels := by
      have ha : raw6587step1 = (fun i j => raw6587step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6587step1 raw6587step0; decide +kernel
      have hl : raw6587step1Labels = raw6587step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6587step0 raw6587step0Labels permutation38 permutation3
    mixedMoment B raw6587step1 raw6587step1Labels = mixedMoment B raw6587step2 raw6587step2Labels := by
      have ha : raw6587step2 = raw6587step1 := by apply Matrix.ext; unfold raw6587step2 raw6587step1; decide +kernel
      have hl : raw6587step1Labels = labelEmbedding6 ∘ raw6587step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6587step1 raw6587step1Labels raw6587step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5301 node5301Labels := by rfl

def raw6588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6588Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6588step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw6588step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6588step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw6588step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6588 raw6588Labels = mixedMoment B node4407 node4407Labels := by
  calc
    mixedMoment B raw6588 raw6588Labels = mixedMoment B raw6588step0 raw6588step0Labels := by
      have ha : raw6588step0 = (fun i j => raw6588 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6588step0 raw6588; decide +kernel
      have hl : raw6588step0Labels = raw6588Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6588 raw6588Labels permutation160 permutation3
    mixedMoment B raw6588step0 raw6588step0Labels = mixedMoment B raw6588step1 raw6588step1Labels := by
      have ha : raw6588step1 = raw6588step0 := by apply Matrix.ext; unfold raw6588step1 raw6588step0; decide +kernel
      have hl : raw6588step0Labels = labelEmbedding6 ∘ raw6588step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6588step0 raw6588step0Labels raw6588step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4407 node4407Labels := by rfl

def raw6589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6589Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6589step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw6589step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6589step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw6589step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6589 raw6589Labels = mixedMoment B node5005 node5005Labels := by
  calc
    mixedMoment B raw6589 raw6589Labels = mixedMoment B raw6589step0 raw6589step0Labels := by
      have ha : raw6589step0 = (fun i j => raw6589 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6589step0 raw6589; decide +kernel
      have hl : raw6589step0Labels = raw6589Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6589 raw6589Labels permutation160 permutation3
    mixedMoment B raw6589step0 raw6589step0Labels = mixedMoment B raw6589step1 raw6589step1Labels := by
      have ha : raw6589step1 = raw6589step0 := by apply Matrix.ext; unfold raw6589step1 raw6589step0; decide +kernel
      have hl : raw6589step0Labels = labelEmbedding6 ∘ raw6589step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6589step0 raw6589step0Labels raw6589step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5005 node5005Labels := by rfl

def raw6590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6590Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6590step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw6590step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6590step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw6590step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6590 raw6590Labels = mixedMoment B node5185 node5185Labels := by
  calc
    mixedMoment B raw6590 raw6590Labels = mixedMoment B raw6590step0 raw6590step0Labels := by
      have ha : raw6590step0 = (fun i j => raw6590 (permutation202 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6590step0 raw6590; decide +kernel
      have hl : raw6590step0Labels = raw6590Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6590 raw6590Labels permutation202 permutation3
    mixedMoment B raw6590step0 raw6590step0Labels = mixedMoment B raw6590step1 raw6590step1Labels := by
      have ha : raw6590step1 = raw6590step0 := by apply Matrix.ext; unfold raw6590step1 raw6590step0; decide +kernel
      have hl : raw6590step0Labels = labelEmbedding6 ∘ raw6590step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6590step0 raw6590step0Labels raw6590step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5185 node5185Labels := by rfl

def raw6591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1]]
def raw6591Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6591step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6591step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6591step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6591step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6591 raw6591Labels = mixedMoment B node5244 node5244Labels := by
  calc
    mixedMoment B raw6591 raw6591Labels = mixedMoment B raw6591step0 raw6591step0Labels := by
      have ha : raw6591step0 = (fun i j => raw6591 (permutation166 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6591step0 raw6591; decide +kernel
      have hl : raw6591step0Labels = raw6591Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6591 raw6591Labels permutation166 permutation3
    mixedMoment B raw6591step0 raw6591step0Labels = mixedMoment B raw6591step1 raw6591step1Labels := by
      have ha : raw6591step1 = raw6591step0 := by apply Matrix.ext; unfold raw6591step1 raw6591step0; decide +kernel
      have hl : raw6591step0Labels = labelEmbedding6 ∘ raw6591step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6591step0 raw6591step0Labels raw6591step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5244 node5244Labels := by rfl

def raw6592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw6592Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6592step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw6592step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6592step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw6592step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6592 raw6592Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw6592 raw6592Labels = mixedMoment B raw6592step0 raw6592step0Labels := by
      have ha : raw6592step0 = (fun i j => raw6592 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6592step0 raw6592; decide +kernel
      have hl : raw6592step0Labels = raw6592Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6592 raw6592Labels permutation161 permutation3
    mixedMoment B raw6592step0 raw6592step0Labels = mixedMoment B raw6592step1 raw6592step1Labels := by
      have ha : raw6592step1 = raw6592step0 := by apply Matrix.ext; unfold raw6592step1 raw6592step0; decide +kernel
      have hl : raw6592step0Labels = labelEmbedding6 ∘ raw6592step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6592step0 raw6592step0Labels raw6592step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

def raw6593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6593Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6593step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6593step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6593step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw6593step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6593step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw6593step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6593 raw6593Labels = mixedMoment B node4420 node4420Labels := by
  calc
    mixedMoment B raw6593 raw6593Labels = mixedMoment B raw6593step0 raw6593step0Labels := by
      have hz : ∀ j, raw6593 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6593step0 = (fun i j => raw6593 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6593step0 raw6593; decide +kernel
      have hl : raw6593step0Labels = raw6593Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6593 raw6593Labels permutation346 hz
    mixedMoment B raw6593step0 raw6593step0Labels = mixedMoment B raw6593step1 raw6593step1Labels := by
      have ha : raw6593step1 = (fun i j => raw6593step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6593step1 raw6593step0; decide +kernel
      have hl : raw6593step1Labels = raw6593step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6593step0 raw6593step0Labels permutation34 permutation3
    mixedMoment B raw6593step1 raw6593step1Labels = mixedMoment B raw6593step2 raw6593step2Labels := by
      have ha : raw6593step2 = raw6593step1 := by apply Matrix.ext; unfold raw6593step2 raw6593step1; decide +kernel
      have hl : raw6593step1Labels = labelEmbedding6 ∘ raw6593step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6593step1 raw6593step1Labels raw6593step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4420 node4420Labels := by rfl

def raw6594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6594Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6594step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -3, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6594step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6594step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw6594step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6594step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw6594step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6594 raw6594Labels = mixedMoment B node5016 node5016Labels := by
  calc
    mixedMoment B raw6594 raw6594Labels = mixedMoment B raw6594step0 raw6594step0Labels := by
      have hz : ∀ j, raw6594 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6594step0 = (fun i j => raw6594 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6594step0 raw6594; decide +kernel
      have hl : raw6594step0Labels = raw6594Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6594 raw6594Labels permutation346 hz
    mixedMoment B raw6594step0 raw6594step0Labels = mixedMoment B raw6594step1 raw6594step1Labels := by
      have ha : raw6594step1 = (fun i j => raw6594step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6594step1 raw6594step0; decide +kernel
      have hl : raw6594step1Labels = raw6594step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6594step0 raw6594step0Labels permutation34 permutation3
    mixedMoment B raw6594step1 raw6594step1Labels = mixedMoment B raw6594step2 raw6594step2Labels := by
      have ha : raw6594step2 = raw6594step1 := by apply Matrix.ext; unfold raw6594step2 raw6594step1; decide +kernel
      have hl : raw6594step1Labels = labelEmbedding6 ∘ raw6594step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6594step1 raw6594step1Labels raw6594step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5016 node5016Labels := by rfl

def raw6595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6595Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6595step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw6595step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6595step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw6595step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6595 raw6595Labels = mixedMoment B node5057 node5057Labels := by
  calc
    mixedMoment B raw6595 raw6595Labels = mixedMoment B raw6595step0 raw6595step0Labels := by
      have ha : raw6595step0 = (fun i j => raw6595 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6595step0 raw6595; decide +kernel
      have hl : raw6595step0Labels = raw6595Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6595 raw6595Labels permutation178 permutation3
    mixedMoment B raw6595step0 raw6595step0Labels = mixedMoment B raw6595step1 raw6595step1Labels := by
      have ha : raw6595step1 = raw6595step0 := by apply Matrix.ext; unfold raw6595step1 raw6595step0; decide +kernel
      have hl : raw6595step0Labels = labelEmbedding6 ∘ raw6595step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6595step0 raw6595step0Labels raw6595step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5057 node5057Labels := by rfl

def raw6596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![0, 1, -1], ![2, -1, -1]]
def raw6596Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![0, 1, -1], ![2, -1, -1]]
def raw6596step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6596step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw6596step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6596step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw6596step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6596 raw6596Labels = mixedMoment B node5205 node5205Labels := by
  calc
    mixedMoment B raw6596 raw6596Labels = mixedMoment B raw6596step0 raw6596step0Labels := by
      have hz : ∀ j, raw6596 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6596step0 = (fun i j => raw6596 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6596step0 raw6596; decide +kernel
      have hl : raw6596step0Labels = raw6596Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6596 raw6596Labels permutation346 hz
    mixedMoment B raw6596step0 raw6596step0Labels = mixedMoment B raw6596step1 raw6596step1Labels := by
      have ha : raw6596step1 = (fun i j => raw6596step0 (permutation101 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6596step1 raw6596step0; decide +kernel
      have hl : raw6596step1Labels = raw6596step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6596step0 raw6596step0Labels permutation101 permutation4
    mixedMoment B raw6596step1 raw6596step1Labels = mixedMoment B raw6596step2 raw6596step2Labels := by
      have ha : raw6596step2 = raw6596step1 := by apply Matrix.ext; unfold raw6596step2 raw6596step1; decide +kernel
      have hl : raw6596step1Labels = labelEmbedding7 ∘ raw6596step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6596step1 raw6596step1Labels raw6596step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5205 node5205Labels := by rfl

def raw6597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw6597Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6597step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw6597step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6597step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw6597step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6597step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw6597step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6597 raw6597Labels = mixedMoment B node5270 node5270Labels := by
  calc
    mixedMoment B raw6597 raw6597Labels = mixedMoment B raw6597step0 raw6597step0Labels := by
      have hz : ∀ j, raw6597 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6597step0 = (fun i j => raw6597 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6597step0 raw6597; decide +kernel
      have hl : raw6597step0Labels = raw6597Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6597 raw6597Labels permutation346 hz
    mixedMoment B raw6597step0 raw6597step0Labels = mixedMoment B raw6597step1 raw6597step1Labels := by
      have ha : raw6597step1 = (fun i j => raw6597step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6597step1 raw6597step0; decide +kernel
      have hl : raw6597step1Labels = raw6597step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6597step0 raw6597step0Labels permutation35 permutation3
    mixedMoment B raw6597step1 raw6597step1Labels = mixedMoment B raw6597step2 raw6597step2Labels := by
      have ha : raw6597step2 = raw6597step1 := by apply Matrix.ext; unfold raw6597step2 raw6597step1; decide +kernel
      have hl : raw6597step1Labels = labelEmbedding6 ∘ raw6597step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6597step1 raw6597step1Labels raw6597step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5270 node5270Labels := by rfl

def raw6598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw6598Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6598step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw6598step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6598step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw6598step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6598step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw6598step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6598 raw6598Labels = mixedMoment B node4412 node4412Labels := by
  calc
    mixedMoment B raw6598 raw6598Labels = mixedMoment B raw6598step0 raw6598step0Labels := by
      have hz : ∀ j, raw6598 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6598step0 = (fun i j => raw6598 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6598step0 raw6598; decide +kernel
      have hl : raw6598step0Labels = raw6598Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6598 raw6598Labels permutation346 hz
    mixedMoment B raw6598step0 raw6598step0Labels = mixedMoment B raw6598step1 raw6598step1Labels := by
      have ha : raw6598step1 = (fun i j => raw6598step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6598step1 raw6598step0; decide +kernel
      have hl : raw6598step1Labels = raw6598step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6598step0 raw6598step0Labels permutation32 permutation3
    mixedMoment B raw6598step1 raw6598step1Labels = mixedMoment B raw6598step2 raw6598step2Labels := by
      have ha : raw6598step2 = raw6598step1 := by apply Matrix.ext; unfold raw6598step2 raw6598step1; decide +kernel
      have hl : raw6598step1Labels = labelEmbedding6 ∘ raw6598step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6598step1 raw6598step1Labels raw6598step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4412 node4412Labels := by rfl

def raw6599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw6599Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6599step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw6599step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6599step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw6599step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6599step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw6599step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6599 raw6599Labels = mixedMoment B node5010 node5010Labels := by
  calc
    mixedMoment B raw6599 raw6599Labels = mixedMoment B raw6599step0 raw6599step0Labels := by
      have hz : ∀ j, raw6599 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6599step0 = (fun i j => raw6599 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6599step0 raw6599; decide +kernel
      have hl : raw6599step0Labels = raw6599Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6599 raw6599Labels permutation346 hz
    mixedMoment B raw6599step0 raw6599step0Labels = mixedMoment B raw6599step1 raw6599step1Labels := by
      have ha : raw6599step1 = (fun i j => raw6599step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6599step1 raw6599step0; decide +kernel
      have hl : raw6599step1Labels = raw6599step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6599step0 raw6599step0Labels permutation32 permutation3
    mixedMoment B raw6599step1 raw6599step1Labels = mixedMoment B raw6599step2 raw6599step2Labels := by
      have ha : raw6599step2 = raw6599step1 := by apply Matrix.ext; unfold raw6599step2 raw6599step1; decide +kernel
      have hl : raw6599step1Labels = labelEmbedding6 ∘ raw6599step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6599step1 raw6599step1Labels raw6599step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5010 node5010Labels := by rfl

def raw6600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw6600Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6600step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw6600step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6600step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw6600step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6600 raw6600Labels = mixedMoment B node5054 node5054Labels := by
  calc
    mixedMoment B raw6600 raw6600Labels = mixedMoment B raw6600step0 raw6600step0Labels := by
      have ha : raw6600step0 = (fun i j => raw6600 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6600step0 raw6600; decide +kernel
      have hl : raw6600step0Labels = raw6600Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6600 raw6600Labels permutation176 permutation3
    mixedMoment B raw6600step0 raw6600step0Labels = mixedMoment B raw6600step1 raw6600step1Labels := by
      have ha : raw6600step1 = raw6600step0 := by apply Matrix.ext; unfold raw6600step1 raw6600step0; decide +kernel
      have hl : raw6600step0Labels = labelEmbedding6 ∘ raw6600step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6600step0 raw6600step0Labels raw6600step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5054 node5054Labels := by rfl

def raw6601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![2, -1, -1], ![2, -1, -1]]
def raw6601Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, -1, 2], ![2, -1, -1], ![2, -1, -1]]
def raw6601step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6601step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw6601step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6601step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw6601step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6601 raw6601Labels = mixedMoment B node5189 node5189Labels := by
  calc
    mixedMoment B raw6601 raw6601Labels = mixedMoment B raw6601step0 raw6601step0Labels := by
      have hz : ∀ j, raw6601 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6601step0 = (fun i j => raw6601 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6601step0 raw6601; decide +kernel
      have hl : raw6601step0Labels = raw6601Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6601 raw6601Labels permutation346 hz
    mixedMoment B raw6601step0 raw6601step0Labels = mixedMoment B raw6601step1 raw6601step1Labels := by
      have ha : raw6601step1 = (fun i j => raw6601step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6601step1 raw6601step0; decide +kernel
      have hl : raw6601step1Labels = raw6601step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6601step0 raw6601step0Labels permutation38 permutation3
    mixedMoment B raw6601step1 raw6601step1Labels = mixedMoment B raw6601step2 raw6601step2Labels := by
      have ha : raw6601step2 = raw6601step1 := by apply Matrix.ext; unfold raw6601step2 raw6601step1; decide +kernel
      have hl : raw6601step1Labels = labelEmbedding6 ∘ raw6601step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6601step1 raw6601step1Labels raw6601step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5189 node5189Labels := by rfl

def raw6602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1]]
def raw6602Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1]]
def raw6602step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6602step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6602step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6602step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6602step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6602 raw6602Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw6602 raw6602Labels = mixedMoment B raw6602step0 raw6602step0Labels := by
      have hz : ∀ j, raw6602 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6602step0 = (fun i j => raw6602 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6602step0 raw6602; decide +kernel
      have hl : raw6602step0Labels = raw6602Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6602 raw6602Labels permutation346 hz
    mixedMoment B raw6602step0 raw6602step0Labels = mixedMoment B raw6602step1 raw6602step1Labels := by
      have ha : raw6602step1 = (fun i j => raw6602step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6602step1 raw6602step0; decide +kernel
      have hl : raw6602step1Labels = raw6602step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6602step0 raw6602step0Labels permutation33 permutation3
    mixedMoment B raw6602step1 raw6602step1Labels = mixedMoment B raw6602step2 raw6602step2Labels := by
      have ha : raw6602step2 = raw6602step1 := by apply Matrix.ext; unfold raw6602step2 raw6602step1; decide +kernel
      have hl : raw6602step1Labels = labelEmbedding6 ∘ raw6602step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6602step1 raw6602step1Labels raw6602step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

def raw6603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw6603Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6603step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw6603step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6603step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw6603step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6603step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw6603step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6603 raw6603Labels = mixedMoment B node4408 node4408Labels := by
  calc
    mixedMoment B raw6603 raw6603Labels = mixedMoment B raw6603step0 raw6603step0Labels := by
      have hz : ∀ j, raw6603 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6603step0 = (fun i j => raw6603 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6603step0 raw6603; decide +kernel
      have hl : raw6603step0Labels = raw6603Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6603 raw6603Labels permutation346 hz
    mixedMoment B raw6603step0 raw6603step0Labels = mixedMoment B raw6603step1 raw6603step1Labels := by
      have ha : raw6603step1 = (fun i j => raw6603step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6603step1 raw6603step0; decide +kernel
      have hl : raw6603step1Labels = raw6603step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6603step0 raw6603step0Labels permutation32 permutation3
    mixedMoment B raw6603step1 raw6603step1Labels = mixedMoment B raw6603step2 raw6603step2Labels := by
      have ha : raw6603step2 = raw6603step1 := by apply Matrix.ext; unfold raw6603step2 raw6603step1; decide +kernel
      have hl : raw6603step1Labels = labelEmbedding6 ∘ raw6603step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6603step1 raw6603step1Labels raw6603step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4408 node4408Labels := by rfl

def raw6604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw6604Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw6604step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6604step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw6604step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6604step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw6604step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6604 raw6604Labels = mixedMoment B node5006 node5006Labels := by
  calc
    mixedMoment B raw6604 raw6604Labels = mixedMoment B raw6604step0 raw6604step0Labels := by
      have hz : ∀ j, raw6604 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6604step0 = (fun i j => raw6604 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6604step0 raw6604; decide +kernel
      have hl : raw6604step0Labels = raw6604Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6604 raw6604Labels permutation346 hz
    mixedMoment B raw6604step0 raw6604step0Labels = mixedMoment B raw6604step1 raw6604step1Labels := by
      have ha : raw6604step1 = (fun i j => raw6604step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6604step1 raw6604step0; decide +kernel
      have hl : raw6604step1Labels = raw6604step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6604step0 raw6604step0Labels permutation32 permutation3
    mixedMoment B raw6604step1 raw6604step1Labels = mixedMoment B raw6604step2 raw6604step2Labels := by
      have ha : raw6604step2 = raw6604step1 := by apply Matrix.ext; unfold raw6604step2 raw6604step1; decide +kernel
      have hl : raw6604step1Labels = labelEmbedding6 ∘ raw6604step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6604step1 raw6604step1Labels raw6604step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5006 node5006Labels := by rfl

def raw6605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw6605Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6605step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw6605step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6605step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw6605step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6605 raw6605Labels = mixedMoment B node5051 node5051Labels := by
  calc
    mixedMoment B raw6605 raw6605Labels = mixedMoment B raw6605step0 raw6605step0Labels := by
      have ha : raw6605step0 = (fun i j => raw6605 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6605step0 raw6605; decide +kernel
      have hl : raw6605step0Labels = raw6605Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6605 raw6605Labels permutation176 permutation3
    mixedMoment B raw6605step0 raw6605step0Labels = mixedMoment B raw6605step1 raw6605step1Labels := by
      have ha : raw6605step1 = raw6605step0 := by apply Matrix.ext; unfold raw6605step1 raw6605step0; decide +kernel
      have hl : raw6605step0Labels = labelEmbedding6 ∘ raw6605step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6605step0 raw6605step0Labels raw6605step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5051 node5051Labels := by rfl

def raw6606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![3, -2, -1]]
def raw6606Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6606step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, -1, 2], ![1, 0, -1], ![3, -2, -1]]
def raw6606step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6606step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw6606step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6606step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw6606step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6606step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw6606step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6606 raw6606Labels = mixedMoment B node5147 node5147Labels := by
  calc
    mixedMoment B raw6606 raw6606Labels = mixedMoment B raw6606step0 raw6606step0Labels := by
      have hz : ∀ j, raw6606 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6606step0 = (fun i j => raw6606 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6606step0 raw6606; decide +kernel
      have hl : raw6606step0Labels = raw6606Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6606 raw6606Labels permutation346 hz
    mixedMoment B raw6606step0 raw6606step0Labels = mixedMoment B raw6606step1 raw6606step1Labels := by
      have ha : raw6606step1 = (fun i j => raw6606step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6606step1 raw6606step0; decide +kernel
      have hl : raw6606step1Labels = raw6606step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6606step0 raw6606step0Labels permutation149 permutation3
    mixedMoment B raw6606step1 raw6606step1Labels = mixedMoment B raw6606step2 raw6606step2Labels := by
      have ha : raw6606step2 = -raw6606step1 := by apply Matrix.ext; change ∀ i j, raw6606step2 i j = -(raw6606step1 i j); unfold raw6606step2 raw6606step1; decide +kernel
      have hl : raw6606step2Labels = raw6606step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6606step2 raw6606step2Labels = mixedMoment B raw6606step3 raw6606step3Labels := by
      have ha : raw6606step3 = raw6606step2 := by apply Matrix.ext; unfold raw6606step3 raw6606step2; decide +kernel
      have hl : raw6606step2Labels = labelEmbedding6 ∘ raw6606step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6606step2 raw6606step2Labels raw6606step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5147 node5147Labels := by rfl

def raw6607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![3, -2, -1]]
def raw6607Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6607step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![0, 1, -1], ![3, -2, -1]]
def raw6607step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6607step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw6607step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6607step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw6607step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw6607step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw6607step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6607 raw6607Labels = mixedMoment B node5222 node5222Labels := by
  calc
    mixedMoment B raw6607 raw6607Labels = mixedMoment B raw6607step0 raw6607step0Labels := by
      have hz : ∀ j, raw6607 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6607step0 = (fun i j => raw6607 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6607step0 raw6607; decide +kernel
      have hl : raw6607step0Labels = raw6607Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6607 raw6607Labels permutation346 hz
    mixedMoment B raw6607step0 raw6607step0Labels = mixedMoment B raw6607step1 raw6607step1Labels := by
      have ha : raw6607step1 = (fun i j => raw6607step0 (permutation143 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6607step1 raw6607step0; decide +kernel
      have hl : raw6607step1Labels = raw6607step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6607step0 raw6607step0Labels permutation143 permutation3
    mixedMoment B raw6607step1 raw6607step1Labels = mixedMoment B raw6607step2 raw6607step2Labels := by
      have ha : raw6607step2 = -raw6607step1 := by apply Matrix.ext; change ∀ i j, raw6607step2 i j = -(raw6607step1 i j); unfold raw6607step2 raw6607step1; decide +kernel
      have hl : raw6607step2Labels = raw6607step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6607step2 raw6607step2Labels = mixedMoment B raw6607step3 raw6607step3Labels := by
      have ha : raw6607step3 = raw6607step2 := by apply Matrix.ext; unfold raw6607step3 raw6607step2; decide +kernel
      have hl : raw6607step2Labels = labelEmbedding6 ∘ raw6607step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6607step2 raw6607step2Labels raw6607step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5222 node5222Labels := by rfl

def raw6608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6608Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6608step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6608step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw6608step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6608step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw6608step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6608 raw6608Labels = mixedMoment B node3884 node3884Labels := by
  calc
    mixedMoment B raw6608 raw6608Labels = mixedMoment B raw6608step0 raw6608step0Labels := by
      have hz : ∀ j, raw6608 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6608step0 = (fun i j => raw6608 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6608step0 raw6608; decide +kernel
      have hl : raw6608step0Labels = raw6608Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6608 raw6608Labels permutation346 hz
    mixedMoment B raw6608step0 raw6608step0Labels = mixedMoment B raw6608step1 raw6608step1Labels := by
      have ha : raw6608step1 = (fun i j => raw6608step0 (permutation85 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6608step1 raw6608step0; decide +kernel
      have hl : raw6608step1Labels = raw6608step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6608step0 raw6608step0Labels permutation85 permutation6
    mixedMoment B raw6608step1 raw6608step1Labels = mixedMoment B raw6608step2 raw6608step2Labels := by
      have ha : raw6608step2 = -raw6608step1 := by apply Matrix.ext; change ∀ i j, raw6608step2 i j = -(raw6608step1 i j); unfold raw6608step2 raw6608step1; decide +kernel
      have hl : raw6608step2Labels = raw6608step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3884 node3884Labels := by rfl

def raw6609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6609Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6609step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw6609step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6609step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw6609step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6609 raw6609Labels = mixedMoment B node3880 node3880Labels := by
  calc
    mixedMoment B raw6609 raw6609Labels = mixedMoment B raw6609step0 raw6609step0Labels := by
      have ha : raw6609step0 = (fun i j => raw6609 (permutation442 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6609step0 raw6609; decide +kernel
      have hl : raw6609step0Labels = raw6609Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6609 raw6609Labels permutation442 permutation6
    mixedMoment B raw6609step0 raw6609step0Labels = mixedMoment B raw6609step1 raw6609step1Labels := by
      have ha : raw6609step1 = -raw6609step0 := by apply Matrix.ext; change ∀ i j, raw6609step1 i j = -(raw6609step0 i j); unfold raw6609step1 raw6609step0; decide +kernel
      have hl : raw6609step1Labels = raw6609step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3880 node3880Labels := by rfl

def raw6610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6610Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6610step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6610step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw6610step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6610step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw6610step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6610 raw6610Labels = mixedMoment B node3995 node3995Labels := by
  calc
    mixedMoment B raw6610 raw6610Labels = mixedMoment B raw6610step0 raw6610step0Labels := by
      have hz : ∀ j, raw6610 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6610step0 = (fun i j => raw6610 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6610step0 raw6610; decide +kernel
      have hl : raw6610step0Labels = raw6610Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6610 raw6610Labels permutation346 hz
    mixedMoment B raw6610step0 raw6610step0Labels = mixedMoment B raw6610step1 raw6610step1Labels := by
      have ha : raw6610step1 = (fun i j => raw6610step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6610step1 raw6610step0; decide +kernel
      have hl : raw6610step1Labels = raw6610step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6610step0 raw6610step0Labels permutation149 permutation3
    mixedMoment B raw6610step1 raw6610step1Labels = mixedMoment B raw6610step2 raw6610step2Labels := by
      have ha : raw6610step2 = -raw6610step1 := by apply Matrix.ext; change ∀ i j, raw6610step2 i j = -(raw6610step1 i j); unfold raw6610step2 raw6610step1; decide +kernel
      have hl : raw6610step2Labels = raw6610step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3995 node3995Labels := by rfl

def raw6611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1]]
def raw6611Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1]]
def raw6611step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6611step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw6611step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6611step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw6611step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6611 raw6611Labels = mixedMoment B node3885 node3885Labels := by
  calc
    mixedMoment B raw6611 raw6611Labels = mixedMoment B raw6611step0 raw6611step0Labels := by
      have hz : ∀ j, raw6611 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6611step0 = (fun i j => raw6611 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6611step0 raw6611; decide +kernel
      have hl : raw6611step0Labels = raw6611Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6611 raw6611Labels permutation346 hz
    mixedMoment B raw6611step0 raw6611step0Labels = mixedMoment B raw6611step1 raw6611step1Labels := by
      have ha : raw6611step1 = (fun i j => raw6611step0 (permutation84 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6611step1 raw6611step0; decide +kernel
      have hl : raw6611step1Labels = raw6611step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6611step0 raw6611step0Labels permutation84 permutation6
    mixedMoment B raw6611step1 raw6611step1Labels = mixedMoment B raw6611step2 raw6611step2Labels := by
      have ha : raw6611step2 = -raw6611step1 := by apply Matrix.ext; change ∀ i j, raw6611step2 i j = -(raw6611step1 i j); unfold raw6611step2 raw6611step1; decide +kernel
      have hl : raw6611step2Labels = raw6611step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3885 node3885Labels := by rfl

def raw6612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw6612Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw6612step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6612step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw6612step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6612step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw6612step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6612 raw6612Labels = mixedMoment B node3887 node3887Labels := by
  calc
    mixedMoment B raw6612 raw6612Labels = mixedMoment B raw6612step0 raw6612step0Labels := by
      have hz : ∀ j, raw6612 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6612step0 = (fun i j => raw6612 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6612step0 raw6612; decide +kernel
      have hl : raw6612step0Labels = raw6612Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6612 raw6612Labels permutation346 hz
    mixedMoment B raw6612step0 raw6612step0Labels = mixedMoment B raw6612step1 raw6612step1Labels := by
      have ha : raw6612step1 = (fun i j => raw6612step0 (permutation83 i) (permutation6 j)) := by apply Matrix.ext; unfold raw6612step1 raw6612step0; decide +kernel
      have hl : raw6612step1Labels = raw6612step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6612step0 raw6612step0Labels permutation83 permutation6
    mixedMoment B raw6612step1 raw6612step1Labels = mixedMoment B raw6612step2 raw6612step2Labels := by
      have ha : raw6612step2 = -raw6612step1 := by apply Matrix.ext; change ∀ i j, raw6612step2 i j = -(raw6612step1 i j); unfold raw6612step2 raw6612step1; decide +kernel
      have hl : raw6612step2Labels = raw6612step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3887 node3887Labels := by rfl

def raw6613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6613Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6613step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6613step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6613step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw6613step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6613 raw6613Labels = mixedMoment B node1057 node1057Labels := by
  calc
    mixedMoment B raw6613 raw6613Labels = mixedMoment B raw6613step0 raw6613step0Labels := by
      have hz : ∀ j, raw6613 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6613step0 = (fun i j => raw6613 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6613step0 raw6613; decide +kernel
      have hl : raw6613step0Labels = raw6613Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6613 raw6613Labels permutation346 hz
    mixedMoment B raw6613step0 raw6613step0Labels = mixedMoment B raw6613step1 raw6613step1Labels := by
      have ha : raw6613step1 = (fun i j => raw6613step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6613step1 raw6613step0; decide +kernel
      have hl : raw6613step1Labels = raw6613step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6613step0 raw6613step0Labels permutation38 permutation3
    _ = mixedMoment B node1057 node1057Labels := by rfl

def raw6614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6614Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6614step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw6614step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6614 raw6614Labels = mixedMoment B node2493 node2493Labels := by
  calc
    mixedMoment B raw6614 raw6614Labels = mixedMoment B raw6614step0 raw6614step0Labels := by
      have ha : raw6614step0 = (fun i j => raw6614 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6614step0 raw6614; decide +kernel
      have hl : raw6614step0Labels = raw6614Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6614 raw6614Labels permutation182 permutation3
    _ = mixedMoment B node2493 node2493Labels := by rfl

def raw6615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6615Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6615step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6615step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw6615step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6615 raw6615Labels = mixedMoment B node2637 node2637Labels := by
  calc
    mixedMoment B raw6615 raw6615Labels = mixedMoment B raw6615step0 raw6615step0Labels := by
      have hz : ∀ j, raw6615 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6615step0 = (fun i j => raw6615 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6615step0 raw6615; decide +kernel
      have hl : raw6615step0Labels = raw6615Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6615 raw6615Labels permutation346 hz
    mixedMoment B raw6615step0 raw6615step0Labels = mixedMoment B raw6615step1 raw6615step1Labels := by
      have ha : raw6615step1 = (fun i j => raw6615step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6615step1 raw6615step0; decide +kernel
      have hl : raw6615step1Labels = raw6615step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6615step0 raw6615step0Labels permutation38 permutation3
    _ = mixedMoment B node2637 node2637Labels := by rfl

def raw6616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1]]
def raw6616Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6616step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1]]
def raw6616step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6616step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6616step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6616 raw6616Labels = mixedMoment B node2731 node2731Labels := by
  calc
    mixedMoment B raw6616 raw6616Labels = mixedMoment B raw6616step0 raw6616step0Labels := by
      have hz : ∀ j, raw6616 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6616step0 = (fun i j => raw6616 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6616step0 raw6616; decide +kernel
      have hl : raw6616step0Labels = raw6616Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6616 raw6616Labels permutation346 hz
    mixedMoment B raw6616step0 raw6616step0Labels = mixedMoment B raw6616step1 raw6616step1Labels := by
      have ha : raw6616step1 = (fun i j => raw6616step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6616step1 raw6616step0; decide +kernel
      have hl : raw6616step1Labels = raw6616step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6616step0 raw6616step0Labels permutation46 permutation3
    _ = mixedMoment B node2731 node2731Labels := by rfl

def raw6617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw6617Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw6617step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6617step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw6617step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6617 raw6617Labels = mixedMoment B node2775 node2775Labels := by
  calc
    mixedMoment B raw6617 raw6617Labels = mixedMoment B raw6617step0 raw6617step0Labels := by
      have hz : ∀ j, raw6617 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6617step0 = (fun i j => raw6617 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6617step0 raw6617; decide +kernel
      have hl : raw6617step0Labels = raw6617Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6617 raw6617Labels permutation346 hz
    mixedMoment B raw6617step0 raw6617step0Labels = mixedMoment B raw6617step1 raw6617step1Labels := by
      have ha : raw6617step1 = (fun i j => raw6617step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6617step1 raw6617step0; decide +kernel
      have hl : raw6617step1Labels = raw6617step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6617step0 raw6617step0Labels permutation38 permutation3
    _ = mixedMoment B node2775 node2775Labels := by rfl

def raw6618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6618Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6618step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw6618step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6618 raw6618Labels = mixedMoment B node988 node988Labels := by
  calc
    mixedMoment B raw6618 raw6618Labels = mixedMoment B raw6618step0 raw6618step0Labels := by
      have ha : raw6618step0 = (fun i j => raw6618 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6618step0 raw6618; decide +kernel
      have hl : raw6618step0Labels = raw6618Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6618 raw6618Labels permutation160 permutation3
    _ = mixedMoment B node988 node988Labels := by rfl

def raw6619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6619Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6619step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw6619step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6619 raw6619Labels = mixedMoment B node2390 node2390Labels := by
  calc
    mixedMoment B raw6619 raw6619Labels = mixedMoment B raw6619step0 raw6619step0Labels := by
      have ha : raw6619step0 = (fun i j => raw6619 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6619step0 raw6619; decide +kernel
      have hl : raw6619step0Labels = raw6619Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6619 raw6619Labels permutation160 permutation3
    _ = mixedMoment B node2390 node2390Labels := by rfl

def raw6620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6620Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6620step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw6620step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6620 raw6620Labels = mixedMoment B node2615 node2615Labels := by
  calc
    mixedMoment B raw6620 raw6620Labels = mixedMoment B raw6620step0 raw6620step0Labels := by
      have ha : raw6620step0 = (fun i j => raw6620 (permutation202 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6620step0 raw6620; decide +kernel
      have hl : raw6620step0Labels = raw6620Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6620 raw6620Labels permutation202 permutation3
    _ = mixedMoment B node2615 node2615Labels := by rfl

def raw6621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1]]
def raw6621Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6621step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw6621step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6621 raw6621Labels = mixedMoment B node2698 node2698Labels := by
  calc
    mixedMoment B raw6621 raw6621Labels = mixedMoment B raw6621step0 raw6621step0Labels := by
      have ha : raw6621step0 = (fun i j => raw6621 (permutation166 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6621step0 raw6621; decide +kernel
      have hl : raw6621step0Labels = raw6621Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6621 raw6621Labels permutation166 permutation3
    _ = mixedMoment B node2698 node2698Labels := by rfl

def raw6622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw6622Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6622step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw6622step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6622 raw6622Labels = mixedMoment B node2730 node2730Labels := by
  calc
    mixedMoment B raw6622 raw6622Labels = mixedMoment B raw6622step0 raw6622step0Labels := by
      have ha : raw6622step0 = (fun i j => raw6622 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6622step0 raw6622; decide +kernel
      have hl : raw6622step0Labels = raw6622Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6622 raw6622Labels permutation161 permutation3
    _ = mixedMoment B node2730 node2730Labels := by rfl

def raw6623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6623Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6623step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6623step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6623step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw6623step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6623 raw6623Labels = mixedMoment B node1001 node1001Labels := by
  calc
    mixedMoment B raw6623 raw6623Labels = mixedMoment B raw6623step0 raw6623step0Labels := by
      have hz : ∀ j, raw6623 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6623step0 = (fun i j => raw6623 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6623step0 raw6623; decide +kernel
      have hl : raw6623step0Labels = raw6623Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6623 raw6623Labels permutation346 hz
    mixedMoment B raw6623step0 raw6623step0Labels = mixedMoment B raw6623step1 raw6623step1Labels := by
      have ha : raw6623step1 = (fun i j => raw6623step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6623step1 raw6623step0; decide +kernel
      have hl : raw6623step1Labels = raw6623step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6623step0 raw6623step0Labels permutation34 permutation3
    _ = mixedMoment B node1001 node1001Labels := by rfl

def raw6624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6624Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6624step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -3, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6624step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6624step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw6624step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6624 raw6624Labels = mixedMoment B node2401 node2401Labels := by
  calc
    mixedMoment B raw6624 raw6624Labels = mixedMoment B raw6624step0 raw6624step0Labels := by
      have hz : ∀ j, raw6624 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6624step0 = (fun i j => raw6624 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6624step0 raw6624; decide +kernel
      have hl : raw6624step0Labels = raw6624Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6624 raw6624Labels permutation346 hz
    mixedMoment B raw6624step0 raw6624step0Labels = mixedMoment B raw6624step1 raw6624step1Labels := by
      have ha : raw6624step1 = (fun i j => raw6624step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6624step1 raw6624step0; decide +kernel
      have hl : raw6624step1Labels = raw6624step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6624step0 raw6624step0Labels permutation34 permutation3
    _ = mixedMoment B node2401 node2401Labels := by rfl

def raw6625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6625Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6625step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw6625step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6625 raw6625Labels = mixedMoment B node2460 node2460Labels := by
  calc
    mixedMoment B raw6625 raw6625Labels = mixedMoment B raw6625step0 raw6625step0Labels := by
      have ha : raw6625step0 = (fun i j => raw6625 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6625step0 raw6625; decide +kernel
      have hl : raw6625step0Labels = raw6625Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6625 raw6625Labels permutation178 permutation3
    _ = mixedMoment B node2460 node2460Labels := by rfl

def raw6626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![0, 1, -1], ![2, -1, -1]]
def raw6626Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6626step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![0, 1, -1], ![2, -1, -1]]
def raw6626step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6626step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw6626step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6626 raw6626Labels = mixedMoment B node2706 node2706Labels := by
  calc
    mixedMoment B raw6626 raw6626Labels = mixedMoment B raw6626step0 raw6626step0Labels := by
      have hz : ∀ j, raw6626 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6626step0 = (fun i j => raw6626 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6626step0 raw6626; decide +kernel
      have hl : raw6626step0Labels = raw6626Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6626 raw6626Labels permutation346 hz
    mixedMoment B raw6626step0 raw6626step0Labels = mixedMoment B raw6626step1 raw6626step1Labels := by
      have ha : raw6626step1 = (fun i j => raw6626step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6626step1 raw6626step0; decide +kernel
      have hl : raw6626step1Labels = raw6626step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6626step0 raw6626step0Labels permutation34 permutation3
    _ = mixedMoment B node2706 node2706Labels := by rfl

def raw6627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw6627Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw6627step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6627step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw6627step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6627 raw6627Labels = mixedMoment B node2738 node2738Labels := by
  calc
    mixedMoment B raw6627 raw6627Labels = mixedMoment B raw6627step0 raw6627step0Labels := by
      have hz : ∀ j, raw6627 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6627step0 = (fun i j => raw6627 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6627step0 raw6627; decide +kernel
      have hl : raw6627step0Labels = raw6627Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6627 raw6627Labels permutation346 hz
    mixedMoment B raw6627step0 raw6627step0Labels = mixedMoment B raw6627step1 raw6627step1Labels := by
      have ha : raw6627step1 = (fun i j => raw6627step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6627step1 raw6627step0; decide +kernel
      have hl : raw6627step1Labels = raw6627step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6627step0 raw6627step0Labels permutation35 permutation3
    _ = mixedMoment B node2738 node2738Labels := by rfl

def raw6628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw6628Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6628step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw6628step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6628step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw6628step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6628 raw6628Labels = mixedMoment B node993 node993Labels := by
  calc
    mixedMoment B raw6628 raw6628Labels = mixedMoment B raw6628step0 raw6628step0Labels := by
      have hz : ∀ j, raw6628 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6628step0 = (fun i j => raw6628 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6628step0 raw6628; decide +kernel
      have hl : raw6628step0Labels = raw6628Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6628 raw6628Labels permutation346 hz
    mixedMoment B raw6628step0 raw6628step0Labels = mixedMoment B raw6628step1 raw6628step1Labels := by
      have ha : raw6628step1 = (fun i j => raw6628step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6628step1 raw6628step0; decide +kernel
      have hl : raw6628step1Labels = raw6628step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6628step0 raw6628step0Labels permutation32 permutation3
    _ = mixedMoment B node993 node993Labels := by rfl

def raw6629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw6629Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6629step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw6629step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6629step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw6629step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6629 raw6629Labels = mixedMoment B node2395 node2395Labels := by
  calc
    mixedMoment B raw6629 raw6629Labels = mixedMoment B raw6629step0 raw6629step0Labels := by
      have hz : ∀ j, raw6629 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6629step0 = (fun i j => raw6629 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6629step0 raw6629; decide +kernel
      have hl : raw6629step0Labels = raw6629Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6629 raw6629Labels permutation346 hz
    mixedMoment B raw6629step0 raw6629step0Labels = mixedMoment B raw6629step1 raw6629step1Labels := by
      have ha : raw6629step1 = (fun i j => raw6629step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6629step1 raw6629step0; decide +kernel
      have hl : raw6629step1Labels = raw6629step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6629step0 raw6629step0Labels permutation32 permutation3
    _ = mixedMoment B node2395 node2395Labels := by rfl

def raw6630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw6630Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6630step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw6630step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6630 raw6630Labels = mixedMoment B node2456 node2456Labels := by
  calc
    mixedMoment B raw6630 raw6630Labels = mixedMoment B raw6630step0 raw6630step0Labels := by
      have ha : raw6630step0 = (fun i j => raw6630 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6630step0 raw6630; decide +kernel
      have hl : raw6630step0Labels = raw6630Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6630 raw6630Labels permutation176 permutation3
    _ = mixedMoment B node2456 node2456Labels := by rfl

def raw6631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![2, -1, -1], ![2, -1, -1]]
def raw6631Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, -1, 2], ![2, -1, -1], ![2, -1, -1]]
def raw6631step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6631step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw6631step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6631 raw6631Labels = mixedMoment B node2621 node2621Labels := by
  calc
    mixedMoment B raw6631 raw6631Labels = mixedMoment B raw6631step0 raw6631step0Labels := by
      have hz : ∀ j, raw6631 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6631step0 = (fun i j => raw6631 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6631step0 raw6631; decide +kernel
      have hl : raw6631step0Labels = raw6631Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6631 raw6631Labels permutation346 hz
    mixedMoment B raw6631step0 raw6631step0Labels = mixedMoment B raw6631step1 raw6631step1Labels := by
      have ha : raw6631step1 = (fun i j => raw6631step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6631step1 raw6631step0; decide +kernel
      have hl : raw6631step1Labels = raw6631step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6631step0 raw6631step0Labels permutation38 permutation3
    _ = mixedMoment B node2621 node2621Labels := by rfl

def raw6632 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1]]
def raw6632Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1]]
def raw6632step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6632step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw6632step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6632 raw6632Labels = mixedMoment B node2731 node2731Labels := by
  calc
    mixedMoment B raw6632 raw6632Labels = mixedMoment B raw6632step0 raw6632step0Labels := by
      have hz : ∀ j, raw6632 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6632step0 = (fun i j => raw6632 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6632step0 raw6632; decide +kernel
      have hl : raw6632step0Labels = raw6632Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6632 raw6632Labels permutation346 hz
    mixedMoment B raw6632step0 raw6632step0Labels = mixedMoment B raw6632step1 raw6632step1Labels := by
      have ha : raw6632step1 = (fun i j => raw6632step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6632step1 raw6632step0; decide +kernel
      have hl : raw6632step1Labels = raw6632step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6632step0 raw6632step0Labels permutation33 permutation3
    _ = mixedMoment B node2731 node2731Labels := by rfl

def raw6633 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw6633Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6633step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw6633step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6633step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw6633step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6633 raw6633Labels = mixedMoment B node989 node989Labels := by
  calc
    mixedMoment B raw6633 raw6633Labels = mixedMoment B raw6633step0 raw6633step0Labels := by
      have hz : ∀ j, raw6633 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6633step0 = (fun i j => raw6633 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6633step0 raw6633; decide +kernel
      have hl : raw6633step0Labels = raw6633Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6633 raw6633Labels permutation346 hz
    mixedMoment B raw6633step0 raw6633step0Labels = mixedMoment B raw6633step1 raw6633step1Labels := by
      have ha : raw6633step1 = (fun i j => raw6633step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6633step1 raw6633step0; decide +kernel
      have hl : raw6633step1Labels = raw6633step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6633step0 raw6633step0Labels permutation32 permutation3
    _ = mixedMoment B node989 node989Labels := by rfl

def raw6634 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw6634Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw6634step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6634step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw6634step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6634 raw6634Labels = mixedMoment B node2391 node2391Labels := by
  calc
    mixedMoment B raw6634 raw6634Labels = mixedMoment B raw6634step0 raw6634step0Labels := by
      have hz : ∀ j, raw6634 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6634step0 = (fun i j => raw6634 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6634step0 raw6634; decide +kernel
      have hl : raw6634step0Labels = raw6634Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6634 raw6634Labels permutation346 hz
    mixedMoment B raw6634step0 raw6634step0Labels = mixedMoment B raw6634step1 raw6634step1Labels := by
      have ha : raw6634step1 = (fun i j => raw6634step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6634step1 raw6634step0; decide +kernel
      have hl : raw6634step1Labels = raw6634step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6634step0 raw6634step0Labels permutation32 permutation3
    _ = mixedMoment B node2391 node2391Labels := by rfl

def raw6635 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![3, -2, -1]]
def raw6635Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6635step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw6635step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6635 raw6635Labels = mixedMoment B node2453 node2453Labels := by
  calc
    mixedMoment B raw6635 raw6635Labels = mixedMoment B raw6635step0 raw6635step0Labels := by
      have ha : raw6635step0 = (fun i j => raw6635 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6635step0 raw6635; decide +kernel
      have hl : raw6635step0Labels = raw6635Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6635 raw6635Labels permutation176 permutation3
    _ = mixedMoment B node2453 node2453Labels := by rfl

def raw6636 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![3, -2, -1]]
def raw6636Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, -1, 2], ![1, 0, -1], ![3, -2, -1]]
def raw6636step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6636step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw6636step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6636step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw6636step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6636 raw6636Labels = mixedMoment B node2569 node2569Labels := by
  calc
    mixedMoment B raw6636 raw6636Labels = mixedMoment B raw6636step0 raw6636step0Labels := by
      have hz : ∀ j, raw6636 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6636step0 = (fun i j => raw6636 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6636step0 raw6636; decide +kernel
      have hl : raw6636step0Labels = raw6636Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6636 raw6636Labels permutation346 hz
    mixedMoment B raw6636step0 raw6636step0Labels = mixedMoment B raw6636step1 raw6636step1Labels := by
      have ha : raw6636step1 = (fun i j => raw6636step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6636step1 raw6636step0; decide +kernel
      have hl : raw6636step1Labels = raw6636step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6636step0 raw6636step0Labels permutation149 permutation3
    mixedMoment B raw6636step1 raw6636step1Labels = mixedMoment B raw6636step2 raw6636step2Labels := by
      have ha : raw6636step2 = -raw6636step1 := by apply Matrix.ext; change ∀ i j, raw6636step2 i j = -(raw6636step1 i j); unfold raw6636step2 raw6636step1; decide +kernel
      have hl : raw6636step2Labels = raw6636step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2569 node2569Labels := by rfl

def raw6637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![3, -2, -1]]
def raw6637Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![0, 1, -1], ![3, -2, -1]]
def raw6637step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw6637step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw6637step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6637step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw6637step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6637 raw6637Labels = mixedMoment B node2664 node2664Labels := by
  calc
    mixedMoment B raw6637 raw6637Labels = mixedMoment B raw6637step0 raw6637step0Labels := by
      have hz : ∀ j, raw6637 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6637step0 = (fun i j => raw6637 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6637step0 raw6637; decide +kernel
      have hl : raw6637step0Labels = raw6637Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6637 raw6637Labels permutation346 hz
    mixedMoment B raw6637step0 raw6637step0Labels = mixedMoment B raw6637step1 raw6637step1Labels := by
      have ha : raw6637step1 = (fun i j => raw6637step0 (permutation143 i) (permutation3 j)) := by apply Matrix.ext; unfold raw6637step1 raw6637step0; decide +kernel
      have hl : raw6637step1Labels = raw6637step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6637step0 raw6637step0Labels permutation143 permutation3
    mixedMoment B raw6637step1 raw6637step1Labels = mixedMoment B raw6637step2 raw6637step2Labels := by
      have ha : raw6637step2 = -raw6637step1 := by apply Matrix.ext; change ∀ i j, raw6637step2 i j = -(raw6637step1 i j); unfold raw6637step2 raw6637step1; decide +kernel
      have hl : raw6637step2Labels = raw6637step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2664 node2664Labels := by rfl

def raw6638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6638Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6638step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6638step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6638step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw6638step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6638step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6638step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6638step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6638step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6638 raw6638Labels = mixedMoment B node3959 node3959Labels := by
  calc
    mixedMoment B raw6638 raw6638Labels = mixedMoment B raw6638step0 raw6638step0Labels := by
      have hz : ∀ j, raw6638 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6638step0 = (fun i j => raw6638 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6638step0 raw6638; decide +kernel
      have hl : raw6638step0Labels = raw6638Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6638 raw6638Labels permutation346 hz
    mixedMoment B raw6638step0 raw6638step0Labels = mixedMoment B raw6638step1 raw6638step1Labels := by
      have ha : raw6638step1 = (fun i j => raw6638step0 (permutation59 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6638step1 raw6638step0; decide +kernel
      have hl : raw6638step1Labels = raw6638step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6638step0 raw6638step0Labels permutation59 permutation5
    mixedMoment B raw6638step1 raw6638step1Labels = mixedMoment B raw6638step2 raw6638step2Labels := by
      have ha : raw6638step2 = -raw6638step1 := by apply Matrix.ext; change ∀ i j, raw6638step2 i j = -(raw6638step1 i j); unfold raw6638step2 raw6638step1; decide +kernel
      have hl : raw6638step2Labels = raw6638step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6638step2 raw6638step2Labels = mixedMoment B raw6638step3 raw6638step3Labels := by
      have ha : raw6638step3 = raw6638step2 := by apply Matrix.ext; unfold raw6638step3 raw6638step2; decide +kernel
      have hl : raw6638step2Labels = labelEmbedding1 ∘ raw6638step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6638step2 raw6638step2Labels raw6638step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3959 node3959Labels := by rfl

def raw6639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6639Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6639step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw6639step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6639step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw6639step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6639 raw6639Labels = mixedMoment B node4024 node4024Labels := by
  calc
    mixedMoment B raw6639 raw6639Labels = mixedMoment B raw6639step0 raw6639step0Labels := by
      have ha : raw6639step0 = (fun i j => raw6639 (permutation517 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6639step0 raw6639; decide +kernel
      have hl : raw6639step0Labels = raw6639Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6639 raw6639Labels permutation517 permutation5
    mixedMoment B raw6639step0 raw6639step0Labels = mixedMoment B raw6639step1 raw6639step1Labels := by
      have ha : raw6639step1 = raw6639step0 := by apply Matrix.ext; unfold raw6639step1 raw6639step0; decide +kernel
      have hl : raw6639step0Labels = labelEmbedding1 ∘ raw6639step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6639step0 raw6639step0Labels raw6639step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4024 node4024Labels := by rfl

def raw6640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6640Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6640step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6640step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw6640step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6640step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw6640step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6640step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw6640step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6640 raw6640Labels = mixedMoment B node3961 node3961Labels := by
  calc
    mixedMoment B raw6640 raw6640Labels = mixedMoment B raw6640step0 raw6640step0Labels := by
      have hz : ∀ j, raw6640 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6640step0 = (fun i j => raw6640 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6640step0 raw6640; decide +kernel
      have hl : raw6640step0Labels = raw6640Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6640 raw6640Labels permutation346 hz
    mixedMoment B raw6640step0 raw6640step0Labels = mixedMoment B raw6640step1 raw6640step1Labels := by
      have ha : raw6640step1 = (fun i j => raw6640step0 (permutation80 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6640step1 raw6640step0; decide +kernel
      have hl : raw6640step1Labels = raw6640step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6640step0 raw6640step0Labels permutation80 permutation7
    mixedMoment B raw6640step1 raw6640step1Labels = mixedMoment B raw6640step2 raw6640step2Labels := by
      have ha : raw6640step2 = -raw6640step1 := by apply Matrix.ext; change ∀ i j, raw6640step2 i j = -(raw6640step1 i j); unfold raw6640step2 raw6640step1; decide +kernel
      have hl : raw6640step2Labels = raw6640step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6640step2 raw6640step2Labels = mixedMoment B raw6640step3 raw6640step3Labels := by
      have ha : raw6640step3 = raw6640step2 := by apply Matrix.ext; unfold raw6640step3 raw6640step2; decide +kernel
      have hl : raw6640step2Labels = labelEmbedding1 ∘ raw6640step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6640step2 raw6640step2Labels raw6640step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3961 node3961Labels := by rfl

def raw6641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1]]
def raw6641Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6641step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1]]
def raw6641step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6641step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw6641step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6641step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw6641step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6641 raw6641Labels = mixedMoment B node4028 node4028Labels := by
  calc
    mixedMoment B raw6641 raw6641Labels = mixedMoment B raw6641step0 raw6641step0Labels := by
      have hz : ∀ j, raw6641 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6641step0 = (fun i j => raw6641 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6641step0 raw6641; decide +kernel
      have hl : raw6641step0Labels = raw6641Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6641 raw6641Labels permutation346 hz
    mixedMoment B raw6641step0 raw6641step0Labels = mixedMoment B raw6641step1 raw6641step1Labels := by
      have ha : raw6641step1 = (fun i j => raw6641step0 (permutation101 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6641step1 raw6641step0; decide +kernel
      have hl : raw6641step1Labels = raw6641step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6641step0 raw6641step0Labels permutation101 permutation5
    mixedMoment B raw6641step1 raw6641step1Labels = mixedMoment B raw6641step2 raw6641step2Labels := by
      have ha : raw6641step2 = raw6641step1 := by apply Matrix.ext; unfold raw6641step2 raw6641step1; decide +kernel
      have hl : raw6641step1Labels = labelEmbedding1 ∘ raw6641step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6641step1 raw6641step1Labels raw6641step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4028 node4028Labels := by rfl

def raw6642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw6642Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6642step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw6642step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6642step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw6642step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6642step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw6642step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6642step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw6642step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6642 raw6642Labels = mixedMoment B node4029 node4029Labels := by
  calc
    mixedMoment B raw6642 raw6642Labels = mixedMoment B raw6642step0 raw6642step0Labels := by
      have hz : ∀ j, raw6642 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6642step0 = (fun i j => raw6642 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6642step0 raw6642; decide +kernel
      have hl : raw6642step0Labels = raw6642Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6642 raw6642Labels permutation346 hz
    mixedMoment B raw6642step0 raw6642step0Labels = mixedMoment B raw6642step1 raw6642step1Labels := by
      have ha : raw6642step1 = (fun i j => raw6642step0 (permutation80 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6642step1 raw6642step0; decide +kernel
      have hl : raw6642step1Labels = raw6642step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6642step0 raw6642step0Labels permutation80 permutation7
    mixedMoment B raw6642step1 raw6642step1Labels = mixedMoment B raw6642step2 raw6642step2Labels := by
      have ha : raw6642step2 = -raw6642step1 := by apply Matrix.ext; change ∀ i j, raw6642step2 i j = -(raw6642step1 i j); unfold raw6642step2 raw6642step1; decide +kernel
      have hl : raw6642step2Labels = raw6642step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6642step2 raw6642step2Labels = mixedMoment B raw6642step3 raw6642step3Labels := by
      have ha : raw6642step3 = raw6642step2 := by apply Matrix.ext; unfold raw6642step3 raw6642step2; decide +kernel
      have hl : raw6642step2Labels = labelEmbedding1 ∘ raw6642step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6642step2 raw6642step2Labels raw6642step3Labels labelEmbedding1 hl
    _ = mixedMoment B node4029 node4029Labels := by rfl

def raw6643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6643Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6643step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6643step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6643step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw6643step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6643step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6643step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6643step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6643step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6643 raw6643Labels = mixedMoment B node1709 node1709Labels := by
  calc
    mixedMoment B raw6643 raw6643Labels = mixedMoment B raw6643step0 raw6643step0Labels := by
      have hz : ∀ j, raw6643 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6643step0 = (fun i j => raw6643 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6643step0 raw6643; decide +kernel
      have hl : raw6643step0Labels = raw6643Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6643 raw6643Labels permutation346 hz
    mixedMoment B raw6643step0 raw6643step0Labels = mixedMoment B raw6643step1 raw6643step1Labels := by
      have ha : raw6643step1 = (fun i j => raw6643step0 (permutation35 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6643step1 raw6643step0; decide +kernel
      have hl : raw6643step1Labels = raw6643step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6643step0 raw6643step0Labels permutation35 permutation5
    mixedMoment B raw6643step1 raw6643step1Labels = mixedMoment B raw6643step2 raw6643step2Labels := by
      have ha : raw6643step2 = -raw6643step1 := by apply Matrix.ext; change ∀ i j, raw6643step2 i j = -(raw6643step1 i j); unfold raw6643step2 raw6643step1; decide +kernel
      have hl : raw6643step2Labels = raw6643step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6643step2 raw6643step2Labels = mixedMoment B raw6643step3 raw6643step3Labels := by
      have ha : raw6643step3 = raw6643step2 := by apply Matrix.ext; unfold raw6643step3 raw6643step2; decide +kernel
      have hl : raw6643step2Labels = labelEmbedding1 ∘ raw6643step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6643step2 raw6643step2Labels raw6643step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1709 node1709Labels := by rfl

def raw6644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6644Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6644step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw6644step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6644step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6644step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6644step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6644step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6644 raw6644Labels = mixedMoment B node3461 node3461Labels := by
  calc
    mixedMoment B raw6644 raw6644Labels = mixedMoment B raw6644step0 raw6644step0Labels := by
      have ha : raw6644step0 = (fun i j => raw6644 (permutation179 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6644step0 raw6644; decide +kernel
      have hl : raw6644step0Labels = raw6644Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6644 raw6644Labels permutation179 permutation5
    mixedMoment B raw6644step0 raw6644step0Labels = mixedMoment B raw6644step1 raw6644step1Labels := by
      have ha : raw6644step1 = -raw6644step0 := by apply Matrix.ext; change ∀ i j, raw6644step1 i j = -(raw6644step0 i j); unfold raw6644step1 raw6644step0; decide +kernel
      have hl : raw6644step1Labels = raw6644step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6644step1 raw6644step1Labels = mixedMoment B raw6644step2 raw6644step2Labels := by
      have ha : raw6644step2 = raw6644step1 := by apply Matrix.ext; unfold raw6644step2 raw6644step1; decide +kernel
      have hl : raw6644step1Labels = labelEmbedding1 ∘ raw6644step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6644step1 raw6644step1Labels raw6644step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3461 node3461Labels := by rfl

def raw6645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6645Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6645step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6645step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6645step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2]]
def raw6645step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6645step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw6645step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6645step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw6645step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6645 raw6645Labels = mixedMoment B node3621 node3621Labels := by
  calc
    mixedMoment B raw6645 raw6645Labels = mixedMoment B raw6645step0 raw6645step0Labels := by
      have hz : ∀ j, raw6645 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6645step0 = (fun i j => raw6645 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6645step0 raw6645; decide +kernel
      have hl : raw6645step0Labels = raw6645Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6645 raw6645Labels permutation346 hz
    mixedMoment B raw6645step0 raw6645step0Labels = mixedMoment B raw6645step1 raw6645step1Labels := by
      have ha : raw6645step1 = (fun i j => raw6645step0 (permutation34 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6645step1 raw6645step0; decide +kernel
      have hl : raw6645step1Labels = raw6645step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6645step0 raw6645step0Labels permutation34 permutation5
    mixedMoment B raw6645step1 raw6645step1Labels = mixedMoment B raw6645step2 raw6645step2Labels := by
      have ha : raw6645step2 = -raw6645step1 := by apply Matrix.ext; change ∀ i j, raw6645step2 i j = -(raw6645step1 i j); unfold raw6645step2 raw6645step1; decide +kernel
      have hl : raw6645step2Labels = raw6645step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6645step2 raw6645step2Labels = mixedMoment B raw6645step3 raw6645step3Labels := by
      have ha : raw6645step3 = raw6645step2 := by apply Matrix.ext; unfold raw6645step3 raw6645step2; decide +kernel
      have hl : raw6645step2Labels = labelEmbedding1 ∘ raw6645step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6645step2 raw6645step2Labels raw6645step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3621 node3621Labels := by rfl

def raw6646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1]]
def raw6646Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1]]
def raw6646step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6646step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw6646step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6646step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6646step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6646step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6646step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6646 raw6646Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw6646 raw6646Labels = mixedMoment B raw6646step0 raw6646step0Labels := by
      have hz : ∀ j, raw6646 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6646step0 = (fun i j => raw6646 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6646step0 raw6646; decide +kernel
      have hl : raw6646step0Labels = raw6646Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6646 raw6646Labels permutation346 hz
    mixedMoment B raw6646step0 raw6646step0Labels = mixedMoment B raw6646step1 raw6646step1Labels := by
      have ha : raw6646step1 = (fun i j => raw6646step0 (permutation45 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6646step1 raw6646step0; decide +kernel
      have hl : raw6646step1Labels = raw6646step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6646step0 raw6646step0Labels permutation45 permutation5
    mixedMoment B raw6646step1 raw6646step1Labels = mixedMoment B raw6646step2 raw6646step2Labels := by
      have ha : raw6646step2 = -raw6646step1 := by apply Matrix.ext; change ∀ i j, raw6646step2 i j = -(raw6646step1 i j); unfold raw6646step2 raw6646step1; decide +kernel
      have hl : raw6646step2Labels = raw6646step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6646step2 raw6646step2Labels = mixedMoment B raw6646step3 raw6646step3Labels := by
      have ha : raw6646step3 = raw6646step2 := by apply Matrix.ext; unfold raw6646step3 raw6646step2; decide +kernel
      have hl : raw6646step2Labels = labelEmbedding1 ∘ raw6646step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6646step2 raw6646step2Labels raw6646step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3535 node3535Labels := by rfl

def raw6647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw6647Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw6647step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6647step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw6647step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6647step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw6647step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6647step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw6647step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6647 raw6647Labels = mixedMoment B node3619 node3619Labels := by
  calc
    mixedMoment B raw6647 raw6647Labels = mixedMoment B raw6647step0 raw6647step0Labels := by
      have hz : ∀ j, raw6647 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6647step0 = (fun i j => raw6647 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6647step0 raw6647; decide +kernel
      have hl : raw6647step0Labels = raw6647Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6647 raw6647Labels permutation346 hz
    mixedMoment B raw6647step0 raw6647step0Labels = mixedMoment B raw6647step1 raw6647step1Labels := by
      have ha : raw6647step1 = (fun i j => raw6647step0 (permutation35 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6647step1 raw6647step0; decide +kernel
      have hl : raw6647step1Labels = raw6647step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6647step0 raw6647step0Labels permutation35 permutation5
    mixedMoment B raw6647step1 raw6647step1Labels = mixedMoment B raw6647step2 raw6647step2Labels := by
      have ha : raw6647step2 = -raw6647step1 := by apply Matrix.ext; change ∀ i j, raw6647step2 i j = -(raw6647step1 i j); unfold raw6647step2 raw6647step1; decide +kernel
      have hl : raw6647step2Labels = raw6647step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6647step2 raw6647step2Labels = mixedMoment B raw6647step3 raw6647step3Labels := by
      have ha : raw6647step3 = raw6647step2 := by apply Matrix.ext; unfold raw6647step3 raw6647step2; decide +kernel
      have hl : raw6647step2Labels = labelEmbedding1 ∘ raw6647step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6647step2 raw6647step2Labels raw6647step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3619 node3619Labels := by rfl

def raw6648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6648Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6648step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw6648step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6648step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6648step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6648step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6648step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6648 raw6648Labels = mixedMoment B node1601 node1601Labels := by
  calc
    mixedMoment B raw6648 raw6648Labels = mixedMoment B raw6648step0 raw6648step0Labels := by
      have ha : raw6648step0 = (fun i j => raw6648 (permutation165 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6648step0 raw6648; decide +kernel
      have hl : raw6648step0Labels = raw6648Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6648 raw6648Labels permutation165 permutation5
    mixedMoment B raw6648step0 raw6648step0Labels = mixedMoment B raw6648step1 raw6648step1Labels := by
      have ha : raw6648step1 = -raw6648step0 := by apply Matrix.ext; change ∀ i j, raw6648step1 i j = -(raw6648step0 i j); unfold raw6648step1 raw6648step0; decide +kernel
      have hl : raw6648step1Labels = raw6648step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6648step1 raw6648step1Labels = mixedMoment B raw6648step2 raw6648step2Labels := by
      have ha : raw6648step2 = raw6648step1 := by apply Matrix.ext; unfold raw6648step2 raw6648step1; decide +kernel
      have hl : raw6648step1Labels = labelEmbedding1 ∘ raw6648step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6648step1 raw6648step1Labels raw6648step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1601 node1601Labels := by rfl

def raw6649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6649Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6649step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw6649step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6649step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6649step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6649step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6649step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6649 raw6649Labels = mixedMoment B node3342 node3342Labels := by
  calc
    mixedMoment B raw6649 raw6649Labels = mixedMoment B raw6649step0 raw6649step0Labels := by
      have ha : raw6649step0 = (fun i j => raw6649 (permutation165 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6649step0 raw6649; decide +kernel
      have hl : raw6649step0Labels = raw6649Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6649 raw6649Labels permutation165 permutation5
    mixedMoment B raw6649step0 raw6649step0Labels = mixedMoment B raw6649step1 raw6649step1Labels := by
      have ha : raw6649step1 = -raw6649step0 := by apply Matrix.ext; change ∀ i j, raw6649step1 i j = -(raw6649step0 i j); unfold raw6649step1 raw6649step0; decide +kernel
      have hl : raw6649step1Labels = raw6649step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6649step1 raw6649step1Labels = mixedMoment B raw6649step2 raw6649step2Labels := by
      have ha : raw6649step2 = raw6649step1 := by apply Matrix.ext; unfold raw6649step2 raw6649step1; decide +kernel
      have hl : raw6649step1Labels = labelEmbedding1 ∘ raw6649step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6649step1 raw6649step1Labels raw6649step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3342 node3342Labels := by rfl

def raw6650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6650Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6650step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw6650step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6650step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw6650step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6650step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw6650step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6650 raw6650Labels = mixedMoment B node3529 node3529Labels := by
  calc
    mixedMoment B raw6650 raw6650Labels = mixedMoment B raw6650step0 raw6650step0Labels := by
      have ha : raw6650step0 = (fun i j => raw6650 (permutation166 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6650step0 raw6650; decide +kernel
      have hl : raw6650step0Labels = raw6650Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6650 raw6650Labels permutation166 permutation5
    mixedMoment B raw6650step0 raw6650step0Labels = mixedMoment B raw6650step1 raw6650step1Labels := by
      have ha : raw6650step1 = -raw6650step0 := by apply Matrix.ext; change ∀ i j, raw6650step1 i j = -(raw6650step0 i j); unfold raw6650step1 raw6650step0; decide +kernel
      have hl : raw6650step1Labels = raw6650step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6650step1 raw6650step1Labels = mixedMoment B raw6650step2 raw6650step2Labels := by
      have ha : raw6650step2 = raw6650step1 := by apply Matrix.ext; unfold raw6650step2 raw6650step1; decide +kernel
      have hl : raw6650step1Labels = labelEmbedding1 ∘ raw6650step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6650step1 raw6650step1Labels raw6650step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3529 node3529Labels := by rfl

def raw6651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1]]
def raw6651Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6651step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw6651step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6651step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6651step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6651step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw6651step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6651 raw6651Labels = mixedMoment B node3497 node3497Labels := by
  calc
    mixedMoment B raw6651 raw6651Labels = mixedMoment B raw6651step0 raw6651step0Labels := by
      have ha : raw6651step0 = (fun i j => raw6651 (permutation165 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6651step0 raw6651; decide +kernel
      have hl : raw6651step0Labels = raw6651Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6651 raw6651Labels permutation165 permutation5
    mixedMoment B raw6651step0 raw6651step0Labels = mixedMoment B raw6651step1 raw6651step1Labels := by
      have ha : raw6651step1 = -raw6651step0 := by apply Matrix.ext; change ∀ i j, raw6651step1 i j = -(raw6651step0 i j); unfold raw6651step1 raw6651step0; decide +kernel
      have hl : raw6651step1Labels = raw6651step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6651step1 raw6651step1Labels = mixedMoment B raw6651step2 raw6651step2Labels := by
      have ha : raw6651step2 = raw6651step1 := by apply Matrix.ext; unfold raw6651step2 raw6651step1; decide +kernel
      have hl : raw6651step1Labels = labelEmbedding1 ∘ raw6651step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6651step1 raw6651step1Labels raw6651step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3497 node3497Labels := by rfl

def raw6652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw6652Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6652step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw6652step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6652step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6652step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6652step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw6652step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6652 raw6652Labels = mixedMoment B node3526 node3526Labels := by
  calc
    mixedMoment B raw6652 raw6652Labels = mixedMoment B raw6652step0 raw6652step0Labels := by
      have ha : raw6652step0 = (fun i j => raw6652 (permutation168 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6652step0 raw6652; decide +kernel
      have hl : raw6652step0Labels = raw6652Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6652 raw6652Labels permutation168 permutation5
    mixedMoment B raw6652step0 raw6652step0Labels = mixedMoment B raw6652step1 raw6652step1Labels := by
      have ha : raw6652step1 = -raw6652step0 := by apply Matrix.ext; change ∀ i j, raw6652step1 i j = -(raw6652step0 i j); unfold raw6652step1 raw6652step0; decide +kernel
      have hl : raw6652step1Labels = raw6652step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6652step1 raw6652step1Labels = mixedMoment B raw6652step2 raw6652step2Labels := by
      have ha : raw6652step2 = raw6652step1 := by apply Matrix.ext; unfold raw6652step2 raw6652step1; decide +kernel
      have hl : raw6652step1Labels = labelEmbedding1 ∘ raw6652step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6652step1 raw6652step1Labels raw6652step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3526 node3526Labels := by rfl

def raw6653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6653Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6653step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6653step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw6653step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6653step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw6653step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6653step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw6653step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6653 raw6653Labels = mixedMoment B node1603 node1603Labels := by
  calc
    mixedMoment B raw6653 raw6653Labels = mixedMoment B raw6653step0 raw6653step0Labels := by
      have hz : ∀ j, raw6653 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6653step0 = (fun i j => raw6653 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6653step0 raw6653; decide +kernel
      have hl : raw6653step0Labels = raw6653Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6653 raw6653Labels permutation346 hz
    mixedMoment B raw6653step0 raw6653step0Labels = mixedMoment B raw6653step1 raw6653step1Labels := by
      have ha : raw6653step1 = (fun i j => raw6653step0 (permutation35 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6653step1 raw6653step0; decide +kernel
      have hl : raw6653step1Labels = raw6653step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6653step0 raw6653step0Labels permutation35 permutation5
    mixedMoment B raw6653step1 raw6653step1Labels = mixedMoment B raw6653step2 raw6653step2Labels := by
      have ha : raw6653step2 = -raw6653step1 := by apply Matrix.ext; change ∀ i j, raw6653step2 i j = -(raw6653step1 i j); unfold raw6653step2 raw6653step1; decide +kernel
      have hl : raw6653step2Labels = raw6653step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6653step2 raw6653step2Labels = mixedMoment B raw6653step3 raw6653step3Labels := by
      have ha : raw6653step3 = raw6653step2 := by apply Matrix.ext; unfold raw6653step3 raw6653step2; decide +kernel
      have hl : raw6653step2Labels = labelEmbedding1 ∘ raw6653step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6653step2 raw6653step2Labels raw6653step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1603 node1603Labels := by rfl

def raw6654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6654Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -3, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6654step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6654step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw6654step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6654step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw6654step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6654 raw6654Labels = mixedMoment B node2855 node2855Labels := by
  calc
    mixedMoment B raw6654 raw6654Labels = mixedMoment B raw6654step0 raw6654step0Labels := by
      have hz : ∀ j, raw6654 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6654step0 = (fun i j => raw6654 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6654step0 raw6654; decide +kernel
      have hl : raw6654step0Labels = raw6654Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6654 raw6654Labels permutation346 hz
    mixedMoment B raw6654step0 raw6654step0Labels = mixedMoment B raw6654step1 raw6654step1Labels := by
      have ha : raw6654step1 = (fun i j => raw6654step0 (permutation103 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6654step1 raw6654step0; decide +kernel
      have hl : raw6654step1Labels = raw6654step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6654step0 raw6654step0Labels permutation103 permutation5
    mixedMoment B raw6654step1 raw6654step1Labels = mixedMoment B raw6654step2 raw6654step2Labels := by
      have ha : raw6654step2 = raw6654step1 := by apply Matrix.ext; unfold raw6654step2 raw6654step1; decide +kernel
      have hl : raw6654step1Labels = labelEmbedding1 ∘ raw6654step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6654step1 raw6654step1Labels raw6654step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2855 node2855Labels := by rfl

def raw6655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![2, -1, -1]]
def raw6655Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw6655step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw6655step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw6655step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw6655step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6655 raw6655Labels = mixedMoment B node2851 node2851Labels := by
  calc
    mixedMoment B raw6655 raw6655Labels = mixedMoment B raw6655step0 raw6655step0Labels := by
      have ha : raw6655step0 = (fun i j => raw6655 (permutation517 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6655step0 raw6655; decide +kernel
      have hl : raw6655step0Labels = raw6655Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6655 raw6655Labels permutation517 permutation5
    mixedMoment B raw6655step0 raw6655step0Labels = mixedMoment B raw6655step1 raw6655step1Labels := by
      have ha : raw6655step1 = raw6655step0 := by apply Matrix.ext; unfold raw6655step1 raw6655step0; decide +kernel
      have hl : raw6655step0Labels = labelEmbedding1 ∘ raw6655step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6655step0 raw6655step0Labels raw6655step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2851 node2851Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
