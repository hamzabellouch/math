import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw5504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5504Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5504step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw5504step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5504step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw5504step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5504step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw5504step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5504 raw5504Labels = mixedMoment B node2250 node2250Labels := by
  calc
    mixedMoment B raw5504 raw5504Labels = mixedMoment B raw5504step0 raw5504step0Labels := by
      have ha : raw5504step0 = (fun i j => raw5504 (permutation242 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5504step0 raw5504; decide +kernel
      have hl : raw5504step0Labels = raw5504Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5504 raw5504Labels permutation242 permutation7
    mixedMoment B raw5504step0 raw5504step0Labels = mixedMoment B raw5504step1 raw5504step1Labels := by
      have ha : raw5504step1 = -raw5504step0 := by apply Matrix.ext; change ∀ i j, raw5504step1 i j = -(raw5504step0 i j); unfold raw5504step1 raw5504step0; decide +kernel
      have hl : raw5504step1Labels = raw5504step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5504step1 raw5504step1Labels = mixedMoment B raw5504step2 raw5504step2Labels := by
      have ha : raw5504step2 = raw5504step1 := by apply Matrix.ext; unfold raw5504step2 raw5504step1; decide +kernel
      have hl : raw5504step1Labels = labelEmbedding1 ∘ raw5504step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5504step1 raw5504step1Labels raw5504step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2250 node2250Labels := by rfl

def raw5505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -2, 0]]
def raw5505Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5505step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5505step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5505step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw5505step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5505step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5505step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5505step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5505step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5505 raw5505Labels = mixedMoment B node2277 node2277Labels := by
  calc
    mixedMoment B raw5505 raw5505Labels = mixedMoment B raw5505step0 raw5505step0Labels := by
      have hz : ∀ j, raw5505 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5505step0 = (fun i j => raw5505 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5505step0 raw5505; decide +kernel
      have hl : raw5505step0Labels = raw5505Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5505 raw5505Labels permutation520 hz
    mixedMoment B raw5505step0 raw5505step0Labels = mixedMoment B raw5505step1 raw5505step1Labels := by
      have ha : raw5505step1 = (fun i j => raw5505step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5505step1 raw5505step0; decide +kernel
      have hl : raw5505step1Labels = raw5505step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5505step0 raw5505step0Labels permutation50 permutation7
    mixedMoment B raw5505step1 raw5505step1Labels = mixedMoment B raw5505step2 raw5505step2Labels := by
      have ha : raw5505step2 = -raw5505step1 := by apply Matrix.ext; change ∀ i j, raw5505step2 i j = -(raw5505step1 i j); unfold raw5505step2 raw5505step1; decide +kernel
      have hl : raw5505step2Labels = raw5505step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5505step2 raw5505step2Labels = mixedMoment B raw5505step3 raw5505step3Labels := by
      have ha : raw5505step3 = raw5505step2 := by apply Matrix.ext; unfold raw5505step3 raw5505step2; decide +kernel
      have hl : raw5505step2Labels = labelEmbedding1 ∘ raw5505step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5505step2 raw5505step2Labels raw5505step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2277 node2277Labels := by rfl

def raw5506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw5506Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5506step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw5506step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5506step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5506step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5506step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5506step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5506 raw5506Labels = mixedMoment B node2243 node2243Labels := by
  calc
    mixedMoment B raw5506 raw5506Labels = mixedMoment B raw5506step0 raw5506step0Labels := by
      have ha : raw5506step0 = (fun i j => raw5506 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5506step0 raw5506; decide +kernel
      have hl : raw5506step0Labels = raw5506Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5506 raw5506Labels permutation240 permutation7
    mixedMoment B raw5506step0 raw5506step0Labels = mixedMoment B raw5506step1 raw5506step1Labels := by
      have ha : raw5506step1 = -raw5506step0 := by apply Matrix.ext; change ∀ i j, raw5506step1 i j = -(raw5506step0 i j); unfold raw5506step1 raw5506step0; decide +kernel
      have hl : raw5506step1Labels = raw5506step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5506step1 raw5506step1Labels = mixedMoment B raw5506step2 raw5506step2Labels := by
      have ha : raw5506step2 = raw5506step1 := by apply Matrix.ext; unfold raw5506step2 raw5506step1; decide +kernel
      have hl : raw5506step1Labels = labelEmbedding1 ∘ raw5506step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5506step1 raw5506step1Labels raw5506step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2243 node2243Labels := by rfl

def raw5507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw5507Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5507step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw5507step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5507step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw5507step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5507step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw5507step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5507 raw5507Labels = mixedMoment B node1731 node1731Labels := by
  calc
    mixedMoment B raw5507 raw5507Labels = mixedMoment B raw5507step0 raw5507step0Labels := by
      have ha : raw5507step0 = (fun i j => raw5507 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5507step0 raw5507; decide +kernel
      have hl : raw5507step0Labels = raw5507Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5507 raw5507Labels permutation240 permutation7
    mixedMoment B raw5507step0 raw5507step0Labels = mixedMoment B raw5507step1 raw5507step1Labels := by
      have ha : raw5507step1 = -raw5507step0 := by apply Matrix.ext; change ∀ i j, raw5507step1 i j = -(raw5507step0 i j); unfold raw5507step1 raw5507step0; decide +kernel
      have hl : raw5507step1Labels = raw5507step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5507step1 raw5507step1Labels = mixedMoment B raw5507step2 raw5507step2Labels := by
      have ha : raw5507step2 = raw5507step1 := by apply Matrix.ext; unfold raw5507step2 raw5507step1; decide +kernel
      have hl : raw5507step1Labels = labelEmbedding1 ∘ raw5507step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5507step1 raw5507step1Labels raw5507step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1731 node1731Labels := by rfl

def raw5508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw5508Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5508step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw5508step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5508step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw5508step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5508step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw5508step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5508 raw5508Labels = mixedMoment B node2269 node2269Labels := by
  calc
    mixedMoment B raw5508 raw5508Labels = mixedMoment B raw5508step0 raw5508step0Labels := by
      have ha : raw5508step0 = (fun i j => raw5508 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5508step0 raw5508; decide +kernel
      have hl : raw5508step0Labels = raw5508Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5508 raw5508Labels permutation240 permutation7
    mixedMoment B raw5508step0 raw5508step0Labels = mixedMoment B raw5508step1 raw5508step1Labels := by
      have ha : raw5508step1 = -raw5508step0 := by apply Matrix.ext; change ∀ i j, raw5508step1 i j = -(raw5508step0 i j); unfold raw5508step1 raw5508step0; decide +kernel
      have hl : raw5508step1Labels = raw5508step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5508step1 raw5508step1Labels = mixedMoment B raw5508step2 raw5508step2Labels := by
      have ha : raw5508step2 = raw5508step1 := by apply Matrix.ext; unfold raw5508step2 raw5508step1; decide +kernel
      have hl : raw5508step1Labels = labelEmbedding1 ∘ raw5508step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5508step1 raw5508step1Labels raw5508step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2269 node2269Labels := by rfl

def raw5509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw5509Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5509step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw5509step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5509step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw5509step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5509step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw5509step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5509 raw5509Labels = mixedMoment B node2269 node2269Labels := by
  calc
    mixedMoment B raw5509 raw5509Labels = mixedMoment B raw5509step0 raw5509step0Labels := by
      have ha : raw5509step0 = (fun i j => raw5509 (permutation242 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5509step0 raw5509; decide +kernel
      have hl : raw5509step0Labels = raw5509Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5509 raw5509Labels permutation242 permutation7
    mixedMoment B raw5509step0 raw5509step0Labels = mixedMoment B raw5509step1 raw5509step1Labels := by
      have ha : raw5509step1 = -raw5509step0 := by apply Matrix.ext; change ∀ i j, raw5509step1 i j = -(raw5509step0 i j); unfold raw5509step1 raw5509step0; decide +kernel
      have hl : raw5509step1Labels = raw5509step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5509step1 raw5509step1Labels = mixedMoment B raw5509step2 raw5509step2Labels := by
      have ha : raw5509step2 = raw5509step1 := by apply Matrix.ext; unfold raw5509step2 raw5509step1; decide +kernel
      have hl : raw5509step1Labels = labelEmbedding1 ∘ raw5509step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5509step1 raw5509step1Labels raw5509step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2269 node2269Labels := by rfl

def raw5510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -2, 0]]
def raw5510Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5510step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 1, 0]]
def raw5510step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5510step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw5510step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5510step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw5510step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5510 raw5510Labels = mixedMoment B node2269 node2269Labels := by
  calc
    mixedMoment B raw5510 raw5510Labels = mixedMoment B raw5510step0 raw5510step0Labels := by
      have ha : raw5510step0 = (fun i j => raw5510 (permutation244 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5510step0 raw5510; decide +kernel
      have hl : raw5510step0Labels = raw5510Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5510 raw5510Labels permutation244 permutation7
    mixedMoment B raw5510step0 raw5510step0Labels = mixedMoment B raw5510step1 raw5510step1Labels := by
      have ha : raw5510step1 = -raw5510step0 := by apply Matrix.ext; change ∀ i j, raw5510step1 i j = -(raw5510step0 i j); unfold raw5510step1 raw5510step0; decide +kernel
      have hl : raw5510step1Labels = raw5510step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5510step1 raw5510step1Labels = mixedMoment B raw5510step2 raw5510step2Labels := by
      have ha : raw5510step2 = raw5510step1 := by apply Matrix.ext; unfold raw5510step2 raw5510step1; decide +kernel
      have hl : raw5510step1Labels = labelEmbedding1 ∘ raw5510step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5510step1 raw5510step1Labels raw5510step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2269 node2269Labels := by rfl

def raw5511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw5511Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5511step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw5511step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5511step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw5511step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5511step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw5511step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5511 raw5511Labels = mixedMoment B node2252 node2252Labels := by
  calc
    mixedMoment B raw5511 raw5511Labels = mixedMoment B raw5511step0 raw5511step0Labels := by
      have ha : raw5511step0 = (fun i j => raw5511 (permutation260 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5511step0 raw5511; decide +kernel
      have hl : raw5511step0Labels = raw5511Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5511 raw5511Labels permutation260 permutation7
    mixedMoment B raw5511step0 raw5511step0Labels = mixedMoment B raw5511step1 raw5511step1Labels := by
      have ha : raw5511step1 = -raw5511step0 := by apply Matrix.ext; change ∀ i j, raw5511step1 i j = -(raw5511step0 i j); unfold raw5511step1 raw5511step0; decide +kernel
      have hl : raw5511step1Labels = raw5511step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5511step1 raw5511step1Labels = mixedMoment B raw5511step2 raw5511step2Labels := by
      have ha : raw5511step2 = raw5511step1 := by apply Matrix.ext; unfold raw5511step2 raw5511step1; decide +kernel
      have hl : raw5511step1Labels = labelEmbedding1 ∘ raw5511step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5511step1 raw5511step1Labels raw5511step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2252 node2252Labels := by rfl

def raw5512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw5512Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5512step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -3, 3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw5512step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5512step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw5512step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5512step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw5512step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5512 raw5512Labels = mixedMoment B node1717 node1717Labels := by
  calc
    mixedMoment B raw5512 raw5512Labels = mixedMoment B raw5512step0 raw5512step0Labels := by
      have ha : raw5512step0 = (fun i j => raw5512 (permutation240 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5512step0 raw5512; decide +kernel
      have hl : raw5512step0Labels = raw5512Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5512 raw5512Labels permutation240 permutation7
    mixedMoment B raw5512step0 raw5512step0Labels = mixedMoment B raw5512step1 raw5512step1Labels := by
      have ha : raw5512step1 = -raw5512step0 := by apply Matrix.ext; change ∀ i j, raw5512step1 i j = -(raw5512step0 i j); unfold raw5512step1 raw5512step0; decide +kernel
      have hl : raw5512step1Labels = raw5512step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5512step1 raw5512step1Labels = mixedMoment B raw5512step2 raw5512step2Labels := by
      have ha : raw5512step2 = raw5512step1 := by apply Matrix.ext; unfold raw5512step2 raw5512step1; decide +kernel
      have hl : raw5512step1Labels = labelEmbedding1 ∘ raw5512step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5512step1 raw5512step1Labels raw5512step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1717 node1717Labels := by rfl

def raw5513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw5513Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5513step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw5513step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5513step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw5513step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5513 raw5513Labels = mixedMoment B node1930 node1930Labels := by
  calc
    mixedMoment B raw5513 raw5513Labels = mixedMoment B raw5513step0 raw5513step0Labels := by
      have ha : raw5513step0 = (fun i j => raw5513 (permutation668 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5513step0 raw5513; decide +kernel
      have hl : raw5513step0Labels = raw5513Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5513 raw5513Labels permutation668 permutation5
    mixedMoment B raw5513step0 raw5513step0Labels = mixedMoment B raw5513step1 raw5513step1Labels := by
      have ha : raw5513step1 = raw5513step0 := by apply Matrix.ext; unfold raw5513step1 raw5513step0; decide +kernel
      have hl : raw5513step0Labels = labelEmbedding1 ∘ raw5513step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5513step0 raw5513step0Labels raw5513step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1930 node1930Labels := by rfl

def raw5514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw5514Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5514step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw5514step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5514step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw5514step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5514 raw5514Labels = mixedMoment B node1930 node1930Labels := by
  calc
    mixedMoment B raw5514 raw5514Labels = mixedMoment B raw5514step0 raw5514step0Labels := by
      have ha : raw5514step0 = (fun i j => raw5514 (permutation666 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5514step0 raw5514; decide +kernel
      have hl : raw5514step0Labels = raw5514Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5514 raw5514Labels permutation666 permutation5
    mixedMoment B raw5514step0 raw5514step0Labels = mixedMoment B raw5514step1 raw5514step1Labels := by
      have ha : raw5514step1 = raw5514step0 := by apply Matrix.ext; unfold raw5514step1 raw5514step0; decide +kernel
      have hl : raw5514step0Labels = labelEmbedding1 ∘ raw5514step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5514step0 raw5514step0Labels raw5514step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1930 node1930Labels := by rfl

def raw5515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![3, -3, 0]]
def raw5515Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5515step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw5515step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5515step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw5515step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5515 raw5515Labels = mixedMoment B node1930 node1930Labels := by
  calc
    mixedMoment B raw5515 raw5515Labels = mixedMoment B raw5515step0 raw5515step0Labels := by
      have ha : raw5515step0 = (fun i j => raw5515 (permutation665 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5515step0 raw5515; decide +kernel
      have hl : raw5515step0Labels = raw5515Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5515 raw5515Labels permutation665 permutation5
    mixedMoment B raw5515step0 raw5515step0Labels = mixedMoment B raw5515step1 raw5515step1Labels := by
      have ha : raw5515step1 = raw5515step0 := by apply Matrix.ext; unfold raw5515step1 raw5515step0; decide +kernel
      have hl : raw5515step0Labels = labelEmbedding1 ∘ raw5515step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5515step0 raw5515step0Labels raw5515step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1930 node1930Labels := by rfl

def raw5516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw5516Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5516step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw5516step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5516step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw5516step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5516step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw5516step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5516 raw5516Labels = mixedMoment B node2283 node2283Labels := by
  calc
    mixedMoment B raw5516 raw5516Labels = mixedMoment B raw5516step0 raw5516step0Labels := by
      have hz : ∀ j, raw5516 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5516step0 = (fun i j => raw5516 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5516step0 raw5516; decide +kernel
      have hl : raw5516step0Labels = raw5516Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5516 raw5516Labels permutation520 hz
    mixedMoment B raw5516step0 raw5516step0Labels = mixedMoment B raw5516step1 raw5516step1Labels := by
      have ha : raw5516step1 = (fun i j => raw5516step0 (permutation128 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5516step1 raw5516step0; decide +kernel
      have hl : raw5516step1Labels = raw5516step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5516step0 raw5516step0Labels permutation128 permutation5
    mixedMoment B raw5516step1 raw5516step1Labels = mixedMoment B raw5516step2 raw5516step2Labels := by
      have ha : raw5516step2 = raw5516step1 := by apply Matrix.ext; unfold raw5516step2 raw5516step1; decide +kernel
      have hl : raw5516step1Labels = labelEmbedding1 ∘ raw5516step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5516step1 raw5516step1Labels raw5516step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2283 node2283Labels := by rfl

def raw5517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5517Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5517 raw5517Labels = mixedMoment B node2233 node2233Labels := by
  calc
    _ = mixedMoment B node2233 node2233Labels := by rfl

def raw5518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5518Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5518 raw5518Labels = mixedMoment B node3567 node3567Labels := by
  calc
    _ = mixedMoment B node3567 node3567Labels := by rfl

def raw5519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5519Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5519step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5519step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5519 raw5519Labels = mixedMoment B node3567 node3567Labels := by
  calc
    mixedMoment B raw5519 raw5519Labels = mixedMoment B raw5519step0 raw5519step0Labels := by
      have ha : raw5519step0 = (fun i j => raw5519 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5519step0 raw5519; decide +kernel
      have hl : raw5519step0Labels = raw5519Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5519 raw5519Labels permutation176 permutation2
    _ = mixedMoment B node3567 node3567Labels := by rfl

def raw5520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5520Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5520step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5520step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5520 raw5520Labels = mixedMoment B node3567 node3567Labels := by
  calc
    mixedMoment B raw5520 raw5520Labels = mixedMoment B raw5520step0 raw5520step0Labels := by
      have ha : raw5520step0 = (fun i j => raw5520 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5520step0 raw5520; decide +kernel
      have hl : raw5520step0Labels = raw5520Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5520 raw5520Labels permutation200 permutation2
    _ = mixedMoment B node3567 node3567Labels := by rfl

def raw5521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw5521Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw5521step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5521 raw5521Labels = mixedMoment B node3619 node3619Labels := by
  calc
    mixedMoment B raw5521 raw5521Labels = mixedMoment B raw5521step0 raw5521step0Labels := by
      have hz : ∀ j, raw5521 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5521step0 = (fun i j => raw5521 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5521step0 raw5521; decide +kernel
      have hl : raw5521step0Labels = raw5521Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5521 raw5521Labels permutation520 hz
    _ = mixedMoment B node3619 node3619Labels := by rfl

def raw5522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw5522Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5522 raw5522Labels = mixedMoment B node3618 node3618Labels := by
  calc
    _ = mixedMoment B node3618 node3618Labels := by rfl

def raw5523 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1], ![0, 0], ![0, 0]]
def raw5523Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5523step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1], ![0, 0]]
def raw5523step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5523step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw5523step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical5523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5523 raw5523Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw5523 raw5523Labels = mixedMoment B raw5523step0 raw5523step0Labels := by
      have hz : ∀ j, raw5523 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw5523step0 = (fun i j => raw5523 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw5523step0 raw5523; decide +kernel
      have hl : raw5523step0Labels = raw5523Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5523 raw5523Labels permutation590 hz
    mixedMoment B raw5523step0 raw5523step0Labels = mixedMoment B raw5523step1 raw5523step1Labels := by
      have hz : ∀ j, raw5523step0 (permutation128 0) j = 0 := by decide +kernel
      have ha : raw5523step1 = (fun i j => raw5523step0 (permutation128 i.succ) j) := by apply Matrix.ext; unfold raw5523step1 raw5523step0; decide +kernel
      have hl : raw5523step1Labels = raw5523step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5523step0 raw5523step0Labels permutation128 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

def raw5524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5524Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5524step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5524step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5524 raw5524Labels = mixedMoment B node1021 node1021Labels := by
  calc
    mixedMoment B raw5524 raw5524Labels = mixedMoment B raw5524step0 raw5524step0Labels := by
      have ha : raw5524step0 = (fun i j => raw5524 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5524step0 raw5524; decide +kernel
      have hl : raw5524step0Labels = raw5524Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5524 raw5524Labels permutation184 permutation2
    _ = mixedMoment B node1021 node1021Labels := by rfl

def raw5525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5525Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5525step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5525step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5525 raw5525Labels = mixedMoment B node1021 node1021Labels := by
  calc
    mixedMoment B raw5525 raw5525Labels = mixedMoment B raw5525step0 raw5525step0Labels := by
      have ha : raw5525step0 = (fun i j => raw5525 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5525step0 raw5525; decide +kernel
      have hl : raw5525step0Labels = raw5525Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5525 raw5525Labels permutation160 permutation2
    _ = mixedMoment B node1021 node1021Labels := by rfl

def raw5526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5526Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5526step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5526step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5526 raw5526Labels = mixedMoment B node1021 node1021Labels := by
  calc
    mixedMoment B raw5526 raw5526Labels = mixedMoment B raw5526step0 raw5526step0Labels := by
      have ha : raw5526step0 = (fun i j => raw5526 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5526step0 raw5526; decide +kernel
      have hl : raw5526step0Labels = raw5526Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5526 raw5526Labels permutation154 permutation2
    _ = mixedMoment B node1021 node1021Labels := by rfl

def raw5527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw5527Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5527 raw5527Labels = mixedMoment B node1015 node1015Labels := by
  calc
    _ = mixedMoment B node1015 node1015Labels := by rfl

def raw5528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw5528Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5528 raw5528Labels = mixedMoment B node1014 node1014Labels := by
  calc
    _ = mixedMoment B node1014 node1014Labels := by rfl

def raw5529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5529Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5529step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5529step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5529 raw5529Labels = mixedMoment B node2089 node2089Labels := by
  calc
    mixedMoment B raw5529 raw5529Labels = mixedMoment B raw5529step0 raw5529step0Labels := by
      have ha : raw5529step0 = (fun i j => raw5529 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5529step0 raw5529; decide +kernel
      have hl : raw5529step0Labels = raw5529Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5529 raw5529Labels permutation184 permutation2
    _ = mixedMoment B node2089 node2089Labels := by rfl

def raw5530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5530Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5530step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5530step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5530 raw5530Labels = mixedMoment B node2089 node2089Labels := by
  calc
    mixedMoment B raw5530 raw5530Labels = mixedMoment B raw5530step0 raw5530step0Labels := by
      have ha : raw5530step0 = (fun i j => raw5530 (permutation208 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5530step0 raw5530; decide +kernel
      have hl : raw5530step0Labels = raw5530Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5530 raw5530Labels permutation208 permutation2
    _ = mixedMoment B node2089 node2089Labels := by rfl

def raw5531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw5531Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw5531step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5531step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5531step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5531 raw5531Labels = mixedMoment B node2245 node2245Labels := by
  calc
    mixedMoment B raw5531 raw5531Labels = mixedMoment B raw5531step0 raw5531step0Labels := by
      have hz : ∀ j, raw5531 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5531step0 = (fun i j => raw5531 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5531step0 raw5531; decide +kernel
      have hl : raw5531step0Labels = raw5531Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5531 raw5531Labels permutation520 hz
    mixedMoment B raw5531step0 raw5531step0Labels = mixedMoment B raw5531step1 raw5531step1Labels := by
      have ha : raw5531step1 = (fun i j => raw5531step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5531step1 raw5531step0; decide +kernel
      have hl : raw5531step1Labels = raw5531step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5531step0 raw5531step0Labels permutation40 permutation2
    _ = mixedMoment B node2245 node2245Labels := by rfl

def raw5532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw5532Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5532step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5532step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5532 raw5532Labels = mixedMoment B node2243 node2243Labels := by
  calc
    mixedMoment B raw5532 raw5532Labels = mixedMoment B raw5532step0 raw5532step0Labels := by
      have ha : raw5532step0 = (fun i j => raw5532 (permutation185 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5532step0 raw5532; decide +kernel
      have hl : raw5532step0Labels = raw5532Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5532 raw5532Labels permutation185 permutation2
    _ = mixedMoment B node2243 node2243Labels := by rfl

def raw5533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5533Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5533step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5533step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5533 raw5533Labels = mixedMoment B node2089 node2089Labels := by
  calc
    mixedMoment B raw5533 raw5533Labels = mixedMoment B raw5533step0 raw5533step0Labels := by
      have ha : raw5533step0 = (fun i j => raw5533 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5533step0 raw5533; decide +kernel
      have hl : raw5533step0Labels = raw5533Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5533 raw5533Labels permutation160 permutation2
    _ = mixedMoment B node2089 node2089Labels := by rfl

def raw5534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5534Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5534step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5534step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5534 raw5534Labels = mixedMoment B node2089 node2089Labels := by
  calc
    mixedMoment B raw5534 raw5534Labels = mixedMoment B raw5534step0 raw5534step0Labels := by
      have ha : raw5534step0 = (fun i j => raw5534 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5534step0 raw5534; decide +kernel
      have hl : raw5534step0Labels = raw5534Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5534 raw5534Labels permutation154 permutation2
    _ = mixedMoment B node2089 node2089Labels := by rfl

def raw5535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw5535Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5535 raw5535Labels = mixedMoment B node2084 node2084Labels := by
  calc
    _ = mixedMoment B node2084 node2084Labels := by rfl

def raw5536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw5536Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5536 raw5536Labels = mixedMoment B node2083 node2083Labels := by
  calc
    _ = mixedMoment B node2083 node2083Labels := by rfl

def raw5537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw5537Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5537step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw5537step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5537 raw5537Labels = mixedMoment B node2084 node2084Labels := by
  calc
    mixedMoment B raw5537 raw5537Labels = mixedMoment B raw5537step0 raw5537step0Labels := by
      have ha : raw5537step0 = (fun i j => raw5537 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5537step0 raw5537; decide +kernel
      have hl : raw5537step0Labels = raw5537Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5537 raw5537Labels permutation176 permutation2
    _ = mixedMoment B node2084 node2084Labels := by rfl

def raw5538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![2, -2, 0]]
def raw5538Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5538step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw5538step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5538 raw5538Labels = mixedMoment B node2084 node2084Labels := by
  calc
    mixedMoment B raw5538 raw5538Labels = mixedMoment B raw5538step0 raw5538step0Labels := by
      have ha : raw5538step0 = (fun i j => raw5538 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5538step0 raw5538; decide +kernel
      have hl : raw5538step0Labels = raw5538Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5538 raw5538Labels permutation200 permutation2
    _ = mixedMoment B node2084 node2084Labels := by rfl

def raw5539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw5539Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5539step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5539step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5539 raw5539Labels = mixedMoment B node2233 node2233Labels := by
  calc
    mixedMoment B raw5539 raw5539Labels = mixedMoment B raw5539step0 raw5539step0Labels := by
      have ha : raw5539step0 = (fun i j => raw5539 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5539step0 raw5539; decide +kernel
      have hl : raw5539step0Labels = raw5539Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5539 raw5539Labels permutation153 permutation2
    _ = mixedMoment B node2233 node2233Labels := by rfl

def raw5540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5540Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5540step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw5540step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5540step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5540step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5540 raw5540Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw5540 raw5540Labels = mixedMoment B raw5540step0 raw5540step0Labels := by
      have ha : raw5540step0 = (fun i j => raw5540 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5540step0 raw5540; decide +kernel
      have hl : raw5540step0Labels = raw5540Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5540 raw5540Labels permutation682 permutation2
    mixedMoment B raw5540step0 raw5540step0Labels = mixedMoment B raw5540step1 raw5540step1Labels := by
      have ha : raw5540step1 = -raw5540step0 := by apply Matrix.ext; change ∀ i j, raw5540step1 i j = -(raw5540step0 i j); unfold raw5540step1 raw5540step0; decide +kernel
      have hl : raw5540step1Labels = raw5540step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5406 node5406Labels := by rfl

def raw5541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5541Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5541step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw5541step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5541step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5541step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5541 raw5541Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw5541 raw5541Labels = mixedMoment B raw5541step0 raw5541step0Labels := by
      have ha : raw5541step0 = (fun i j => raw5541 (permutation676 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5541step0 raw5541; decide +kernel
      have hl : raw5541step0Labels = raw5541Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5541 raw5541Labels permutation676 permutation2
    mixedMoment B raw5541step0 raw5541step0Labels = mixedMoment B raw5541step1 raw5541step1Labels := by
      have ha : raw5541step1 = -raw5541step0 := by apply Matrix.ext; change ∀ i j, raw5541step1 i j = -(raw5541step0 i j); unfold raw5541step1 raw5541step0; decide +kernel
      have hl : raw5541step1Labels = raw5541step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5406 node5406Labels := by rfl

def raw5542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5542Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5542step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw5542step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5542step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5542step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5542 raw5542Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw5542 raw5542Labels = mixedMoment B raw5542step0 raw5542step0Labels := by
      have ha : raw5542step0 = (fun i j => raw5542 (permutation674 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5542step0 raw5542; decide +kernel
      have hl : raw5542step0Labels = raw5542Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5542 raw5542Labels permutation674 permutation2
    mixedMoment B raw5542step0 raw5542step0Labels = mixedMoment B raw5542step1 raw5542step1Labels := by
      have ha : raw5542step1 = -raw5542step0 := by apply Matrix.ext; change ∀ i j, raw5542step1 i j = -(raw5542step0 i j); unfold raw5542step1 raw5542step0; decide +kernel
      have hl : raw5542step1Labels = raw5542step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5406 node5406Labels := by rfl

def raw5543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw5543Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5543step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw5543step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5543step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw5543step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5543step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw5543step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5543 raw5543Labels = mixedMoment B node5437 node5437Labels := by
  calc
    mixedMoment B raw5543 raw5543Labels = mixedMoment B raw5543step0 raw5543step0Labels := by
      have ha : raw5543step0 = (fun i j => raw5543 (permutation240 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5543step0 raw5543; decide +kernel
      have hl : raw5543step0Labels = raw5543Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5543 raw5543Labels permutation240 permutation5
    mixedMoment B raw5543step0 raw5543step0Labels = mixedMoment B raw5543step1 raw5543step1Labels := by
      have ha : raw5543step1 = -raw5543step0 := by apply Matrix.ext; change ∀ i j, raw5543step1 i j = -(raw5543step0 i j); unfold raw5543step1 raw5543step0; decide +kernel
      have hl : raw5543step1Labels = raw5543step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5543step1 raw5543step1Labels = mixedMoment B raw5543step2 raw5543step2Labels := by
      have ha : raw5543step2 = raw5543step1 := by apply Matrix.ext; unfold raw5543step2 raw5543step1; decide +kernel
      have hl : raw5543step1Labels = labelEmbedding8 ∘ raw5543step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5543step1 raw5543step1Labels raw5543step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5437 node5437Labels := by rfl

def raw5544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw5544Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5544step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw5544step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5544step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw5544step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5544step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw5544step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5544 raw5544Labels = mixedMoment B node5447 node5447Labels := by
  calc
    mixedMoment B raw5544 raw5544Labels = mixedMoment B raw5544step0 raw5544step0Labels := by
      have ha : raw5544step0 = (fun i j => raw5544 (permutation260 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5544step0 raw5544; decide +kernel
      have hl : raw5544step0Labels = raw5544Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5544 raw5544Labels permutation260 permutation5
    mixedMoment B raw5544step0 raw5544step0Labels = mixedMoment B raw5544step1 raw5544step1Labels := by
      have ha : raw5544step1 = -raw5544step0 := by apply Matrix.ext; change ∀ i j, raw5544step1 i j = -(raw5544step0 i j); unfold raw5544step1 raw5544step0; decide +kernel
      have hl : raw5544step1Labels = raw5544step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5544step1 raw5544step1Labels = mixedMoment B raw5544step2 raw5544step2Labels := by
      have ha : raw5544step2 = raw5544step1 := by apply Matrix.ext; unfold raw5544step2 raw5544step1; decide +kernel
      have hl : raw5544step1Labels = labelEmbedding8 ∘ raw5544step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5544step1 raw5544step1Labels raw5544step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5447 node5447Labels := by rfl

def raw5545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5545Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5545step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5545step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5545step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5545step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5545 raw5545Labels = mixedMoment B node4250 node4250Labels := by
  calc
    mixedMoment B raw5545 raw5545Labels = mixedMoment B raw5545step0 raw5545step0Labels := by
      have ha : raw5545step0 = (fun i j => raw5545 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5545step0 raw5545; decide +kernel
      have hl : raw5545step0Labels = raw5545Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5545 raw5545Labels permutation184 permutation3
    mixedMoment B raw5545step0 raw5545step0Labels = mixedMoment B raw5545step1 raw5545step1Labels := by
      have ha : raw5545step1 = raw5545step0 := by apply Matrix.ext; unfold raw5545step1 raw5545step0; decide +kernel
      have hl : raw5545step0Labels = labelEmbedding6 ∘ raw5545step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5545step0 raw5545step0Labels raw5545step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4250 node4250Labels := by rfl

def raw5546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5546Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5546step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5546step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5546step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5546step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5546 raw5546Labels = mixedMoment B node4803 node4803Labels := by
  calc
    mixedMoment B raw5546 raw5546Labels = mixedMoment B raw5546step0 raw5546step0Labels := by
      have ha : raw5546step0 = (fun i j => raw5546 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5546step0 raw5546; decide +kernel
      have hl : raw5546step0Labels = raw5546Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5546 raw5546Labels permutation184 permutation3
    mixedMoment B raw5546step0 raw5546step0Labels = mixedMoment B raw5546step1 raw5546step1Labels := by
      have ha : raw5546step1 = raw5546step0 := by apply Matrix.ext; unfold raw5546step1 raw5546step0; decide +kernel
      have hl : raw5546step0Labels = labelEmbedding6 ∘ raw5546step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5546step0 raw5546step0Labels raw5546step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4803 node4803Labels := by rfl

def raw5547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5547Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5547step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5547step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5547step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5547step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5547 raw5547Labels = mixedMoment B node4803 node4803Labels := by
  calc
    mixedMoment B raw5547 raw5547Labels = mixedMoment B raw5547step0 raw5547step0Labels := by
      have ha : raw5547step0 = (fun i j => raw5547 (permutation208 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5547step0 raw5547; decide +kernel
      have hl : raw5547step0Labels = raw5547Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5547 raw5547Labels permutation208 permutation3
    mixedMoment B raw5547step0 raw5547step0Labels = mixedMoment B raw5547step1 raw5547step1Labels := by
      have ha : raw5547step1 = raw5547step0 := by apply Matrix.ext; unfold raw5547step1 raw5547step0; decide +kernel
      have hl : raw5547step0Labels = labelEmbedding6 ∘ raw5547step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5547step0 raw5547step0Labels raw5547step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4803 node4803Labels := by rfl

def raw5548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw5548Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5548step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw5548step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5548step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw5548step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5548step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw5548step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5548 raw5548Labels = mixedMoment B node4815 node4815Labels := by
  calc
    mixedMoment B raw5548 raw5548Labels = mixedMoment B raw5548step0 raw5548step0Labels := by
      have ha : raw5548step0 = (fun i j => raw5548 (permutation243 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5548step0 raw5548; decide +kernel
      have hl : raw5548step0Labels = raw5548Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5548 raw5548Labels permutation243 permutation5
    mixedMoment B raw5548step0 raw5548step0Labels = mixedMoment B raw5548step1 raw5548step1Labels := by
      have ha : raw5548step1 = -raw5548step0 := by apply Matrix.ext; change ∀ i j, raw5548step1 i j = -(raw5548step0 i j); unfold raw5548step1 raw5548step0; decide +kernel
      have hl : raw5548step1Labels = raw5548step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5548step1 raw5548step1Labels = mixedMoment B raw5548step2 raw5548step2Labels := by
      have ha : raw5548step2 = raw5548step1 := by apply Matrix.ext; unfold raw5548step2 raw5548step1; decide +kernel
      have hl : raw5548step1Labels = labelEmbedding8 ∘ raw5548step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5548step1 raw5548step1Labels raw5548step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4815 node4815Labels := by rfl

def raw5549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw5549Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5549step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw5549step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5549step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw5549step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5549step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw5549step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5549 raw5549Labels = mixedMoment B node4851 node4851Labels := by
  calc
    mixedMoment B raw5549 raw5549Labels = mixedMoment B raw5549step0 raw5549step0Labels := by
      have ha : raw5549step0 = (fun i j => raw5549 (permutation263 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5549step0 raw5549; decide +kernel
      have hl : raw5549step0Labels = raw5549Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5549 raw5549Labels permutation263 permutation5
    mixedMoment B raw5549step0 raw5549step0Labels = mixedMoment B raw5549step1 raw5549step1Labels := by
      have ha : raw5549step1 = -raw5549step0 := by apply Matrix.ext; change ∀ i j, raw5549step1 i j = -(raw5549step0 i j); unfold raw5549step1 raw5549step0; decide +kernel
      have hl : raw5549step1Labels = raw5549step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5549step1 raw5549step1Labels = mixedMoment B raw5549step2 raw5549step2Labels := by
      have ha : raw5549step2 = raw5549step1 := by apply Matrix.ext; unfold raw5549step2 raw5549step1; decide +kernel
      have hl : raw5549step1Labels = labelEmbedding8 ∘ raw5549step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5549step1 raw5549step1Labels raw5549step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4851 node4851Labels := by rfl

def raw5550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5550Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5550step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5550step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5550step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5550step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5550 raw5550Labels = mixedMoment B node4250 node4250Labels := by
  calc
    mixedMoment B raw5550 raw5550Labels = mixedMoment B raw5550step0 raw5550step0Labels := by
      have ha : raw5550step0 = (fun i j => raw5550 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5550step0 raw5550; decide +kernel
      have hl : raw5550step0Labels = raw5550Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5550 raw5550Labels permutation160 permutation3
    mixedMoment B raw5550step0 raw5550step0Labels = mixedMoment B raw5550step1 raw5550step1Labels := by
      have ha : raw5550step1 = raw5550step0 := by apply Matrix.ext; unfold raw5550step1 raw5550step0; decide +kernel
      have hl : raw5550step0Labels = labelEmbedding6 ∘ raw5550step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5550step0 raw5550step0Labels raw5550step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4250 node4250Labels := by rfl

def raw5551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5551Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5551step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5551step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5551step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5551step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5551 raw5551Labels = mixedMoment B node4803 node4803Labels := by
  calc
    mixedMoment B raw5551 raw5551Labels = mixedMoment B raw5551step0 raw5551step0Labels := by
      have ha : raw5551step0 = (fun i j => raw5551 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5551step0 raw5551; decide +kernel
      have hl : raw5551step0Labels = raw5551Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5551 raw5551Labels permutation160 permutation3
    mixedMoment B raw5551step0 raw5551step0Labels = mixedMoment B raw5551step1 raw5551step1Labels := by
      have ha : raw5551step1 = raw5551step0 := by apply Matrix.ext; unfold raw5551step1 raw5551step0; decide +kernel
      have hl : raw5551step0Labels = labelEmbedding6 ∘ raw5551step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5551step0 raw5551step0Labels raw5551step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4803 node4803Labels := by rfl

def raw5552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5552Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5552step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5552step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5552step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5552step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5552 raw5552Labels = mixedMoment B node4803 node4803Labels := by
  calc
    mixedMoment B raw5552 raw5552Labels = mixedMoment B raw5552step0 raw5552step0Labels := by
      have ha : raw5552step0 = (fun i j => raw5552 (permutation202 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5552step0 raw5552; decide +kernel
      have hl : raw5552step0Labels = raw5552Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5552 raw5552Labels permutation202 permutation3
    mixedMoment B raw5552step0 raw5552step0Labels = mixedMoment B raw5552step1 raw5552step1Labels := by
      have ha : raw5552step1 = raw5552step0 := by apply Matrix.ext; unfold raw5552step1 raw5552step0; decide +kernel
      have hl : raw5552step0Labels = labelEmbedding6 ∘ raw5552step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5552step0 raw5552step0Labels raw5552step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4803 node4803Labels := by rfl

def raw5553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw5553Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5553step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw5553step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5553step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw5553step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5553step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw5553step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5553 raw5553Labels = mixedMoment B node4815 node4815Labels := by
  calc
    mixedMoment B raw5553 raw5553Labels = mixedMoment B raw5553step0 raw5553step0Labels := by
      have ha : raw5553step0 = (fun i j => raw5553 (permutation241 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5553step0 raw5553; decide +kernel
      have hl : raw5553step0Labels = raw5553Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5553 raw5553Labels permutation241 permutation5
    mixedMoment B raw5553step0 raw5553step0Labels = mixedMoment B raw5553step1 raw5553step1Labels := by
      have ha : raw5553step1 = -raw5553step0 := by apply Matrix.ext; change ∀ i j, raw5553step1 i j = -(raw5553step0 i j); unfold raw5553step1 raw5553step0; decide +kernel
      have hl : raw5553step1Labels = raw5553step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5553step1 raw5553step1Labels = mixedMoment B raw5553step2 raw5553step2Labels := by
      have ha : raw5553step2 = raw5553step1 := by apply Matrix.ext; unfold raw5553step2 raw5553step1; decide +kernel
      have hl : raw5553step1Labels = labelEmbedding8 ∘ raw5553step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5553step1 raw5553step1Labels raw5553step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4815 node4815Labels := by rfl

def raw5554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw5554Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5554step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw5554step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5554step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw5554step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5554step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw5554step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5554 raw5554Labels = mixedMoment B node4851 node4851Labels := by
  calc
    mixedMoment B raw5554 raw5554Labels = mixedMoment B raw5554step0 raw5554step0Labels := by
      have ha : raw5554step0 = (fun i j => raw5554 (permutation261 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5554step0 raw5554; decide +kernel
      have hl : raw5554step0Labels = raw5554Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5554 raw5554Labels permutation261 permutation5
    mixedMoment B raw5554step0 raw5554step0Labels = mixedMoment B raw5554step1 raw5554step1Labels := by
      have ha : raw5554step1 = -raw5554step0 := by apply Matrix.ext; change ∀ i j, raw5554step1 i j = -(raw5554step0 i j); unfold raw5554step1 raw5554step0; decide +kernel
      have hl : raw5554step1Labels = raw5554step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5554step1 raw5554step1Labels = mixedMoment B raw5554step2 raw5554step2Labels := by
      have ha : raw5554step2 = raw5554step1 := by apply Matrix.ext; unfold raw5554step2 raw5554step1; decide +kernel
      have hl : raw5554step1Labels = labelEmbedding8 ∘ raw5554step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5554step1 raw5554step1Labels raw5554step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4851 node4851Labels := by rfl

def raw5555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5555Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5555step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5555step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5555step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5555step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5555 raw5555Labels = mixedMoment B node4250 node4250Labels := by
  calc
    mixedMoment B raw5555 raw5555Labels = mixedMoment B raw5555step0 raw5555step0Labels := by
      have ha : raw5555step0 = (fun i j => raw5555 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5555step0 raw5555; decide +kernel
      have hl : raw5555step0Labels = raw5555Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5555 raw5555Labels permutation154 permutation3
    mixedMoment B raw5555step0 raw5555step0Labels = mixedMoment B raw5555step1 raw5555step1Labels := by
      have ha : raw5555step1 = raw5555step0 := by apply Matrix.ext; unfold raw5555step1 raw5555step0; decide +kernel
      have hl : raw5555step0Labels = labelEmbedding6 ∘ raw5555step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5555step0 raw5555step0Labels raw5555step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4250 node4250Labels := by rfl

def raw5556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5556Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5556step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5556step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5556step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5556step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5556 raw5556Labels = mixedMoment B node4803 node4803Labels := by
  calc
    mixedMoment B raw5556 raw5556Labels = mixedMoment B raw5556step0 raw5556step0Labels := by
      have ha : raw5556step0 = (fun i j => raw5556 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5556step0 raw5556; decide +kernel
      have hl : raw5556step0Labels = raw5556Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5556 raw5556Labels permutation154 permutation3
    mixedMoment B raw5556step0 raw5556step0Labels = mixedMoment B raw5556step1 raw5556step1Labels := by
      have ha : raw5556step1 = raw5556step0 := by apply Matrix.ext; unfold raw5556step1 raw5556step0; decide +kernel
      have hl : raw5556step0Labels = labelEmbedding6 ∘ raw5556step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5556step0 raw5556step0Labels raw5556step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4803 node4803Labels := by rfl

def raw5557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5557Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5557step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5557step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5557step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5557step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5557 raw5557Labels = mixedMoment B node4803 node4803Labels := by
  calc
    mixedMoment B raw5557 raw5557Labels = mixedMoment B raw5557step0 raw5557step0Labels := by
      have ha : raw5557step0 = (fun i j => raw5557 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5557step0 raw5557; decide +kernel
      have hl : raw5557step0Labels = raw5557Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5557 raw5557Labels permutation178 permutation3
    mixedMoment B raw5557step0 raw5557step0Labels = mixedMoment B raw5557step1 raw5557step1Labels := by
      have ha : raw5557step1 = raw5557step0 := by apply Matrix.ext; unfold raw5557step1 raw5557step0; decide +kernel
      have hl : raw5557step0Labels = labelEmbedding6 ∘ raw5557step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5557step0 raw5557step0Labels raw5557step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4803 node4803Labels := by rfl

def raw5558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw5558Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5558step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw5558step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5558step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw5558step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5558step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw5558step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5558 raw5558Labels = mixedMoment B node4815 node4815Labels := by
  calc
    mixedMoment B raw5558 raw5558Labels = mixedMoment B raw5558step0 raw5558step0Labels := by
      have ha : raw5558step0 = (fun i j => raw5558 (permutation240 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5558step0 raw5558; decide +kernel
      have hl : raw5558step0Labels = raw5558Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5558 raw5558Labels permutation240 permutation5
    mixedMoment B raw5558step0 raw5558step0Labels = mixedMoment B raw5558step1 raw5558step1Labels := by
      have ha : raw5558step1 = -raw5558step0 := by apply Matrix.ext; change ∀ i j, raw5558step1 i j = -(raw5558step0 i j); unfold raw5558step1 raw5558step0; decide +kernel
      have hl : raw5558step1Labels = raw5558step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5558step1 raw5558step1Labels = mixedMoment B raw5558step2 raw5558step2Labels := by
      have ha : raw5558step2 = raw5558step1 := by apply Matrix.ext; unfold raw5558step2 raw5558step1; decide +kernel
      have hl : raw5558step1Labels = labelEmbedding8 ∘ raw5558step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5558step1 raw5558step1Labels raw5558step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4815 node4815Labels := by rfl

def raw5559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw5559Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5559step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw5559step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5559step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw5559step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5559step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw5559step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5559 raw5559Labels = mixedMoment B node4851 node4851Labels := by
  calc
    mixedMoment B raw5559 raw5559Labels = mixedMoment B raw5559step0 raw5559step0Labels := by
      have ha : raw5559step0 = (fun i j => raw5559 (permutation260 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5559step0 raw5559; decide +kernel
      have hl : raw5559step0Labels = raw5559Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5559 raw5559Labels permutation260 permutation5
    mixedMoment B raw5559step0 raw5559step0Labels = mixedMoment B raw5559step1 raw5559step1Labels := by
      have ha : raw5559step1 = -raw5559step0 := by apply Matrix.ext; change ∀ i j, raw5559step1 i j = -(raw5559step0 i j); unfold raw5559step1 raw5559step0; decide +kernel
      have hl : raw5559step1Labels = raw5559step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5559step1 raw5559step1Labels = mixedMoment B raw5559step2 raw5559step2Labels := by
      have ha : raw5559step2 = raw5559step1 := by apply Matrix.ext; unfold raw5559step2 raw5559step1; decide +kernel
      have hl : raw5559step1Labels = labelEmbedding8 ∘ raw5559step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5559step1 raw5559step1Labels raw5559step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4851 node4851Labels := by rfl

def raw5560 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw5560Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5560step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw5560step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5560step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw5560step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5560 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5560 raw5560Labels = mixedMoment B node4246 node4246Labels := by
  calc
    mixedMoment B raw5560 raw5560Labels = mixedMoment B raw5560step0 raw5560step0Labels := by
      have ha : raw5560step0 = (fun i j => raw5560 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5560step0 raw5560; decide +kernel
      have hl : raw5560step0Labels = raw5560Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5560 raw5560Labels permutation153 permutation3
    mixedMoment B raw5560step0 raw5560step0Labels = mixedMoment B raw5560step1 raw5560step1Labels := by
      have ha : raw5560step1 = raw5560step0 := by apply Matrix.ext; unfold raw5560step1 raw5560step0; decide +kernel
      have hl : raw5560step0Labels = labelEmbedding6 ∘ raw5560step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5560step0 raw5560step0Labels raw5560step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4246 node4246Labels := by rfl

def raw5561 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw5561Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5561step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw5561step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5561step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw5561step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5561 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5561 raw5561Labels = mixedMoment B node4795 node4795Labels := by
  calc
    mixedMoment B raw5561 raw5561Labels = mixedMoment B raw5561step0 raw5561step0Labels := by
      have ha : raw5561step0 = (fun i j => raw5561 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5561step0 raw5561; decide +kernel
      have hl : raw5561step0Labels = raw5561Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5561 raw5561Labels permutation153 permutation3
    mixedMoment B raw5561step0 raw5561step0Labels = mixedMoment B raw5561step1 raw5561step1Labels := by
      have ha : raw5561step1 = raw5561step0 := by apply Matrix.ext; unfold raw5561step1 raw5561step0; decide +kernel
      have hl : raw5561step0Labels = labelEmbedding6 ∘ raw5561step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5561step0 raw5561step0Labels raw5561step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4795 node4795Labels := by rfl

def raw5562 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw5562Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5562step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw5562step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5562step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw5562step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5562 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5562 raw5562Labels = mixedMoment B node4795 node4795Labels := by
  calc
    mixedMoment B raw5562 raw5562Labels = mixedMoment B raw5562step0 raw5562step0Labels := by
      have ha : raw5562step0 = (fun i j => raw5562 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5562step0 raw5562; decide +kernel
      have hl : raw5562step0Labels = raw5562Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5562 raw5562Labels permutation177 permutation3
    mixedMoment B raw5562step0 raw5562step0Labels = mixedMoment B raw5562step1 raw5562step1Labels := by
      have ha : raw5562step1 = raw5562step0 := by apply Matrix.ext; unfold raw5562step1 raw5562step0; decide +kernel
      have hl : raw5562step0Labels = labelEmbedding6 ∘ raw5562step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5562step0 raw5562step0Labels raw5562step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4795 node4795Labels := by rfl

def raw5563 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw5563Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5563step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw5563step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5563step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw5563step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5563 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5563 raw5563Labels = mixedMoment B node4795 node4795Labels := by
  calc
    mixedMoment B raw5563 raw5563Labels = mixedMoment B raw5563step0 raw5563step0Labels := by
      have ha : raw5563step0 = (fun i j => raw5563 (permutation201 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5563step0 raw5563; decide +kernel
      have hl : raw5563step0Labels = raw5563Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5563 raw5563Labels permutation201 permutation3
    mixedMoment B raw5563step0 raw5563step0Labels = mixedMoment B raw5563step1 raw5563step1Labels := by
      have ha : raw5563step1 = raw5563step0 := by apply Matrix.ext; unfold raw5563step1 raw5563step0; decide +kernel
      have hl : raw5563step0Labels = labelEmbedding6 ∘ raw5563step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5563step0 raw5563step0Labels raw5563step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4795 node4795Labels := by rfl

def raw5564 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw5564Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5564step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw5564step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5564step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw5564step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5564step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw5564step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5564 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5564 raw5564Labels = mixedMoment B node4863 node4863Labels := by
  calc
    mixedMoment B raw5564 raw5564Labels = mixedMoment B raw5564step0 raw5564step0Labels := by
      have ha : raw5564step0 = (fun i j => raw5564 (permutation246 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5564step0 raw5564; decide +kernel
      have hl : raw5564step0Labels = raw5564Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5564 raw5564Labels permutation246 permutation5
    mixedMoment B raw5564step0 raw5564step0Labels = mixedMoment B raw5564step1 raw5564step1Labels := by
      have ha : raw5564step1 = -raw5564step0 := by apply Matrix.ext; change ∀ i j, raw5564step1 i j = -(raw5564step0 i j); unfold raw5564step1 raw5564step0; decide +kernel
      have hl : raw5564step1Labels = raw5564step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5564step1 raw5564step1Labels = mixedMoment B raw5564step2 raw5564step2Labels := by
      have ha : raw5564step2 = raw5564step1 := by apply Matrix.ext; unfold raw5564step2 raw5564step1; decide +kernel
      have hl : raw5564step1Labels = labelEmbedding8 ∘ raw5564step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5564step1 raw5564step1Labels raw5564step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4863 node4863Labels := by rfl

def raw5565 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw5565Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5565step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw5565step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5565step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw5565step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5565 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5565 raw5565Labels = mixedMoment B node4244 node4244Labels := by
  calc
    mixedMoment B raw5565 raw5565Labels = mixedMoment B raw5565step0 raw5565step0Labels := by
      have ha : raw5565step0 = (fun i j => raw5565 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5565step0 raw5565; decide +kernel
      have hl : raw5565step0Labels = raw5565Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5565 raw5565Labels permutation152 permutation3
    mixedMoment B raw5565step0 raw5565step0Labels = mixedMoment B raw5565step1 raw5565step1Labels := by
      have ha : raw5565step1 = raw5565step0 := by apply Matrix.ext; unfold raw5565step1 raw5565step0; decide +kernel
      have hl : raw5565step0Labels = labelEmbedding6 ∘ raw5565step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5565step0 raw5565step0Labels raw5565step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4244 node4244Labels := by rfl

def raw5566 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw5566Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5566step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw5566step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5566step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw5566step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5566 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5566 raw5566Labels = mixedMoment B node4792 node4792Labels := by
  calc
    mixedMoment B raw5566 raw5566Labels = mixedMoment B raw5566step0 raw5566step0Labels := by
      have ha : raw5566step0 = (fun i j => raw5566 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5566step0 raw5566; decide +kernel
      have hl : raw5566step0Labels = raw5566Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5566 raw5566Labels permutation152 permutation3
    mixedMoment B raw5566step0 raw5566step0Labels = mixedMoment B raw5566step1 raw5566step1Labels := by
      have ha : raw5566step1 = raw5566step0 := by apply Matrix.ext; unfold raw5566step1 raw5566step0; decide +kernel
      have hl : raw5566step0Labels = labelEmbedding6 ∘ raw5566step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5566step0 raw5566step0Labels raw5566step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4792 node4792Labels := by rfl

def raw5567 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw5567Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5567step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw5567step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5567step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw5567step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5567 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5567 raw5567Labels = mixedMoment B node4792 node4792Labels := by
  calc
    mixedMoment B raw5567 raw5567Labels = mixedMoment B raw5567step0 raw5567step0Labels := by
      have ha : raw5567step0 = (fun i j => raw5567 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5567step0 raw5567; decide +kernel
      have hl : raw5567step0Labels = raw5567Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5567 raw5567Labels permutation176 permutation3
    mixedMoment B raw5567step0 raw5567step0Labels = mixedMoment B raw5567step1 raw5567step1Labels := by
      have ha : raw5567step1 = raw5567step0 := by apply Matrix.ext; unfold raw5567step1 raw5567step0; decide +kernel
      have hl : raw5567step0Labels = labelEmbedding6 ∘ raw5567step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5567step0 raw5567step0Labels raw5567step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4792 node4792Labels := by rfl

def raw5568 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw5568Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5568step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw5568step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5568step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw5568step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5568 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5568 raw5568Labels = mixedMoment B node4792 node4792Labels := by
  calc
    mixedMoment B raw5568 raw5568Labels = mixedMoment B raw5568step0 raw5568step0Labels := by
      have ha : raw5568step0 = (fun i j => raw5568 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5568step0 raw5568; decide +kernel
      have hl : raw5568step0Labels = raw5568Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5568 raw5568Labels permutation200 permutation3
    mixedMoment B raw5568step0 raw5568step0Labels = mixedMoment B raw5568step1 raw5568step1Labels := by
      have ha : raw5568step1 = raw5568step0 := by apply Matrix.ext; unfold raw5568step1 raw5568step0; decide +kernel
      have hl : raw5568step0Labels = labelEmbedding6 ∘ raw5568step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5568step0 raw5568step0Labels raw5568step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4792 node4792Labels := by rfl

def raw5569 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw5569Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5569step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5569step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5569step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw5569step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5569step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw5569step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5569 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5569 raw5569Labels = mixedMoment B node4830 node4830Labels := by
  calc
    mixedMoment B raw5569 raw5569Labels = mixedMoment B raw5569step0 raw5569step0Labels := by
      have ha : raw5569step0 = (fun i j => raw5569 (permutation224 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5569step0 raw5569; decide +kernel
      have hl : raw5569step0Labels = raw5569Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5569 raw5569Labels permutation224 permutation5
    mixedMoment B raw5569step0 raw5569step0Labels = mixedMoment B raw5569step1 raw5569step1Labels := by
      have ha : raw5569step1 = -raw5569step0 := by apply Matrix.ext; change ∀ i j, raw5569step1 i j = -(raw5569step0 i j); unfold raw5569step1 raw5569step0; decide +kernel
      have hl : raw5569step1Labels = raw5569step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5569step1 raw5569step1Labels = mixedMoment B raw5569step2 raw5569step2Labels := by
      have ha : raw5569step2 = raw5569step1 := by apply Matrix.ext; unfold raw5569step2 raw5569step1; decide +kernel
      have hl : raw5569step1Labels = labelEmbedding8 ∘ raw5569step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5569step1 raw5569step1Labels raw5569step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4830 node4830Labels := by rfl

def raw5570 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5570Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5570step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5570step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5570 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5570 raw5570Labels = mixedMoment B node3847 node3847Labels := by
  calc
    mixedMoment B raw5570 raw5570Labels = mixedMoment B raw5570step0 raw5570step0Labels := by
      have ha : raw5570step0 = (fun i j => raw5570 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5570step0 raw5570; decide +kernel
      have hl : raw5570step0Labels = raw5570Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5570 raw5570Labels permutation152 permutation3
    _ = mixedMoment B node3847 node3847Labels := by rfl

def raw5571 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5571Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5571step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5571step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5571 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5571 raw5571Labels = mixedMoment B node3847 node3847Labels := by
  calc
    mixedMoment B raw5571 raw5571Labels = mixedMoment B raw5571step0 raw5571step0Labels := by
      have ha : raw5571step0 = (fun i j => raw5571 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5571step0 raw5571; decide +kernel
      have hl : raw5571step0Labels = raw5571Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5571 raw5571Labels permutation176 permutation3
    _ = mixedMoment B node3847 node3847Labels := by rfl

def raw5572 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5572Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5572step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5572step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5572 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5572 raw5572Labels = mixedMoment B node3847 node3847Labels := by
  calc
    mixedMoment B raw5572 raw5572Labels = mixedMoment B raw5572step0 raw5572step0Labels := by
      have ha : raw5572step0 = (fun i j => raw5572 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5572step0 raw5572; decide +kernel
      have hl : raw5572step0Labels = raw5572Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5572 raw5572Labels permutation200 permutation3
    _ = mixedMoment B node3847 node3847Labels := by rfl

def raw5573 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw5573Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5573step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw5573step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5573 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5573 raw5573Labels = mixedMoment B node3899 node3899Labels := by
  calc
    mixedMoment B raw5573 raw5573Labels = mixedMoment B raw5573step0 raw5573step0Labels := by
      have ha : raw5573step0 = (fun i j => raw5573 (permutation224 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5573step0 raw5573; decide +kernel
      have hl : raw5573step0Labels = raw5573Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5573 raw5573Labels permutation224 permutation3
    _ = mixedMoment B node3899 node3899Labels := by rfl

def raw5574 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw5574Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5574step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0]]
def raw5574step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5574 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5574 raw5574Labels = mixedMoment B node3909 node3909Labels := by
  calc
    mixedMoment B raw5574 raw5574Labels = mixedMoment B raw5574step0 raw5574step0Labels := by
      have ha : raw5574step0 = (fun i j => raw5574 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5574step0 raw5574; decide +kernel
      have hl : raw5574step0Labels = raw5574Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5574 raw5574Labels permutation153 permutation3
    _ = mixedMoment B node3909 node3909Labels := by rfl

def raw5575 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5575Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5575step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5575step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5575 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5575 raw5575Labels = mixedMoment B node784 node784Labels := by
  calc
    mixedMoment B raw5575 raw5575Labels = mixedMoment B raw5575step0 raw5575step0Labels := by
      have ha : raw5575step0 = (fun i j => raw5575 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5575step0 raw5575; decide +kernel
      have hl : raw5575step0Labels = raw5575Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5575 raw5575Labels permutation184 permutation3
    _ = mixedMoment B node784 node784Labels := by rfl

def raw5576 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5576Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5576step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5576step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5576 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5576 raw5576Labels = mixedMoment B node2021 node2021Labels := by
  calc
    mixedMoment B raw5576 raw5576Labels = mixedMoment B raw5576step0 raw5576step0Labels := by
      have ha : raw5576step0 = (fun i j => raw5576 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5576step0 raw5576; decide +kernel
      have hl : raw5576step0Labels = raw5576Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5576 raw5576Labels permutation184 permutation3
    _ = mixedMoment B node2021 node2021Labels := by rfl

def raw5577 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5577Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5577step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5577step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5577 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5577 raw5577Labels = mixedMoment B node2021 node2021Labels := by
  calc
    mixedMoment B raw5577 raw5577Labels = mixedMoment B raw5577step0 raw5577step0Labels := by
      have ha : raw5577step0 = (fun i j => raw5577 (permutation208 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5577step0 raw5577; decide +kernel
      have hl : raw5577step0Labels = raw5577Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5577 raw5577Labels permutation208 permutation3
    _ = mixedMoment B node2021 node2021Labels := by rfl

def raw5578 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw5578Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5578step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw5578step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5578 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5578 raw5578Labels = mixedMoment B node2192 node2192Labels := by
  calc
    mixedMoment B raw5578 raw5578Labels = mixedMoment B raw5578step0 raw5578step0Labels := by
      have ha : raw5578step0 = (fun i j => raw5578 (permutation232 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5578step0 raw5578; decide +kernel
      have hl : raw5578step0Labels = raw5578Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5578 raw5578Labels permutation232 permutation3
    _ = mixedMoment B node2192 node2192Labels := by rfl

def raw5579 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw5579Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5579step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw5579step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5579 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5579 raw5579Labels = mixedMoment B node2240 node2240Labels := by
  calc
    mixedMoment B raw5579 raw5579Labels = mixedMoment B raw5579step0 raw5579step0Labels := by
      have ha : raw5579step0 = (fun i j => raw5579 (permutation187 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5579step0 raw5579; decide +kernel
      have hl : raw5579step0Labels = raw5579Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5579 raw5579Labels permutation187 permutation3
    _ = mixedMoment B node2240 node2240Labels := by rfl

def raw5580 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5580Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5580step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5580step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5580 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5580 raw5580Labels = mixedMoment B node784 node784Labels := by
  calc
    mixedMoment B raw5580 raw5580Labels = mixedMoment B raw5580step0 raw5580step0Labels := by
      have ha : raw5580step0 = (fun i j => raw5580 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5580step0 raw5580; decide +kernel
      have hl : raw5580step0Labels = raw5580Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5580 raw5580Labels permutation160 permutation3
    _ = mixedMoment B node784 node784Labels := by rfl

def raw5581 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5581Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5581step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5581step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5581 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5581 raw5581Labels = mixedMoment B node2021 node2021Labels := by
  calc
    mixedMoment B raw5581 raw5581Labels = mixedMoment B raw5581step0 raw5581step0Labels := by
      have ha : raw5581step0 = (fun i j => raw5581 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5581step0 raw5581; decide +kernel
      have hl : raw5581step0Labels = raw5581Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5581 raw5581Labels permutation160 permutation3
    _ = mixedMoment B node2021 node2021Labels := by rfl

def raw5582 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5582Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5582step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5582step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5582 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5582 raw5582Labels = mixedMoment B node2021 node2021Labels := by
  calc
    mixedMoment B raw5582 raw5582Labels = mixedMoment B raw5582step0 raw5582step0Labels := by
      have ha : raw5582step0 = (fun i j => raw5582 (permutation202 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5582step0 raw5582; decide +kernel
      have hl : raw5582step0Labels = raw5582Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5582 raw5582Labels permutation202 permutation3
    _ = mixedMoment B node2021 node2021Labels := by rfl

def raw5583 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw5583Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5583step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw5583step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5583 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5583 raw5583Labels = mixedMoment B node2192 node2192Labels := by
  calc
    mixedMoment B raw5583 raw5583Labels = mixedMoment B raw5583step0 raw5583step0Labels := by
      have ha : raw5583step0 = (fun i j => raw5583 (permutation226 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5583step0 raw5583; decide +kernel
      have hl : raw5583step0Labels = raw5583Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5583 raw5583Labels permutation226 permutation3
    _ = mixedMoment B node2192 node2192Labels := by rfl

def raw5584 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw5584Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5584step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw5584step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5584 raw5584Labels = mixedMoment B node2240 node2240Labels := by
  calc
    mixedMoment B raw5584 raw5584Labels = mixedMoment B raw5584step0 raw5584step0Labels := by
      have ha : raw5584step0 = (fun i j => raw5584 (permutation163 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5584step0 raw5584; decide +kernel
      have hl : raw5584step0Labels = raw5584Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5584 raw5584Labels permutation163 permutation3
    _ = mixedMoment B node2240 node2240Labels := by rfl

def raw5585 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5585Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5585step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5585step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5585 raw5585Labels = mixedMoment B node784 node784Labels := by
  calc
    mixedMoment B raw5585 raw5585Labels = mixedMoment B raw5585step0 raw5585step0Labels := by
      have ha : raw5585step0 = (fun i j => raw5585 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5585step0 raw5585; decide +kernel
      have hl : raw5585step0Labels = raw5585Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5585 raw5585Labels permutation154 permutation3
    _ = mixedMoment B node784 node784Labels := by rfl

def raw5586 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5586Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5586step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5586step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5586 raw5586Labels = mixedMoment B node2021 node2021Labels := by
  calc
    mixedMoment B raw5586 raw5586Labels = mixedMoment B raw5586step0 raw5586step0Labels := by
      have ha : raw5586step0 = (fun i j => raw5586 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5586step0 raw5586; decide +kernel
      have hl : raw5586step0Labels = raw5586Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5586 raw5586Labels permutation154 permutation3
    _ = mixedMoment B node2021 node2021Labels := by rfl

def raw5587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5587Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5587step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5587step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5587 raw5587Labels = mixedMoment B node2021 node2021Labels := by
  calc
    mixedMoment B raw5587 raw5587Labels = mixedMoment B raw5587step0 raw5587step0Labels := by
      have ha : raw5587step0 = (fun i j => raw5587 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5587step0 raw5587; decide +kernel
      have hl : raw5587step0Labels = raw5587Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5587 raw5587Labels permutation178 permutation3
    _ = mixedMoment B node2021 node2021Labels := by rfl

def raw5588 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw5588Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5588step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw5588step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5588 raw5588Labels = mixedMoment B node2192 node2192Labels := by
  calc
    mixedMoment B raw5588 raw5588Labels = mixedMoment B raw5588step0 raw5588step0Labels := by
      have ha : raw5588step0 = (fun i j => raw5588 (permutation224 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5588step0 raw5588; decide +kernel
      have hl : raw5588step0Labels = raw5588Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5588 raw5588Labels permutation224 permutation3
    _ = mixedMoment B node2192 node2192Labels := by rfl

def raw5589 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw5589Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5589step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw5589step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5589 raw5589Labels = mixedMoment B node2240 node2240Labels := by
  calc
    mixedMoment B raw5589 raw5589Labels = mixedMoment B raw5589step0 raw5589step0Labels := by
      have ha : raw5589step0 = (fun i j => raw5589 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5589step0 raw5589; decide +kernel
      have hl : raw5589step0Labels = raw5589Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5589 raw5589Labels permutation157 permutation3
    _ = mixedMoment B node2240 node2240Labels := by rfl

def raw5590 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw5590Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5590step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw5590step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5590 raw5590Labels = mixedMoment B node778 node778Labels := by
  calc
    mixedMoment B raw5590 raw5590Labels = mixedMoment B raw5590step0 raw5590step0Labels := by
      have ha : raw5590step0 = (fun i j => raw5590 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5590step0 raw5590; decide +kernel
      have hl : raw5590step0Labels = raw5590Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5590 raw5590Labels permutation153 permutation3
    _ = mixedMoment B node778 node778Labels := by rfl

def raw5591 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw5591Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5591step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw5591step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5591 raw5591Labels = mixedMoment B node2012 node2012Labels := by
  calc
    mixedMoment B raw5591 raw5591Labels = mixedMoment B raw5591step0 raw5591step0Labels := by
      have ha : raw5591step0 = (fun i j => raw5591 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5591step0 raw5591; decide +kernel
      have hl : raw5591step0Labels = raw5591Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5591 raw5591Labels permutation153 permutation3
    _ = mixedMoment B node2012 node2012Labels := by rfl

def raw5592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw5592Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5592step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw5592step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5592 raw5592Labels = mixedMoment B node2012 node2012Labels := by
  calc
    mixedMoment B raw5592 raw5592Labels = mixedMoment B raw5592step0 raw5592step0Labels := by
      have ha : raw5592step0 = (fun i j => raw5592 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5592step0 raw5592; decide +kernel
      have hl : raw5592step0Labels = raw5592Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5592 raw5592Labels permutation177 permutation3
    _ = mixedMoment B node2012 node2012Labels := by rfl

def raw5593 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw5593Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5593step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw5593step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5593 raw5593Labels = mixedMoment B node2012 node2012Labels := by
  calc
    mixedMoment B raw5593 raw5593Labels = mixedMoment B raw5593step0 raw5593step0Labels := by
      have ha : raw5593step0 = (fun i j => raw5593 (permutation201 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5593step0 raw5593; decide +kernel
      have hl : raw5593step0Labels = raw5593Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5593 raw5593Labels permutation201 permutation3
    _ = mixedMoment B node2012 node2012Labels := by rfl

def raw5594 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw5594Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5594step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw5594step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5594 raw5594Labels = mixedMoment B node2232 node2232Labels := by
  calc
    mixedMoment B raw5594 raw5594Labels = mixedMoment B raw5594step0 raw5594step0Labels := by
      have ha : raw5594step0 = (fun i j => raw5594 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5594step0 raw5594; decide +kernel
      have hl : raw5594step0Labels = raw5594Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5594 raw5594Labels permutation153 permutation3
    _ = mixedMoment B node2232 node2232Labels := by rfl

def raw5595 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw5595Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5595step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw5595step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5595 raw5595Labels = mixedMoment B node776 node776Labels := by
  calc
    mixedMoment B raw5595 raw5595Labels = mixedMoment B raw5595step0 raw5595step0Labels := by
      have ha : raw5595step0 = (fun i j => raw5595 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5595step0 raw5595; decide +kernel
      have hl : raw5595step0Labels = raw5595Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5595 raw5595Labels permutation152 permutation3
    _ = mixedMoment B node776 node776Labels := by rfl

def raw5596 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw5596Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5596step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw5596step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5596 raw5596Labels = mixedMoment B node2009 node2009Labels := by
  calc
    mixedMoment B raw5596 raw5596Labels = mixedMoment B raw5596step0 raw5596step0Labels := by
      have ha : raw5596step0 = (fun i j => raw5596 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5596step0 raw5596; decide +kernel
      have hl : raw5596step0Labels = raw5596Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5596 raw5596Labels permutation152 permutation3
    _ = mixedMoment B node2009 node2009Labels := by rfl

def raw5597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw5597Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5597step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw5597step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5597 raw5597Labels = mixedMoment B node2009 node2009Labels := by
  calc
    mixedMoment B raw5597 raw5597Labels = mixedMoment B raw5597step0 raw5597step0Labels := by
      have ha : raw5597step0 = (fun i j => raw5597 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5597step0 raw5597; decide +kernel
      have hl : raw5597step0Labels = raw5597Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5597 raw5597Labels permutation176 permutation3
    _ = mixedMoment B node2009 node2009Labels := by rfl

def raw5598 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw5598Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5598step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw5598step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5598 raw5598Labels = mixedMoment B node2009 node2009Labels := by
  calc
    mixedMoment B raw5598 raw5598Labels = mixedMoment B raw5598step0 raw5598step0Labels := by
      have ha : raw5598step0 = (fun i j => raw5598 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5598step0 raw5598; decide +kernel
      have hl : raw5598step0Labels = raw5598Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5598 raw5598Labels permutation200 permutation3
    _ = mixedMoment B node2009 node2009Labels := by rfl

def raw5599 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw5599Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5599step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5599step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5599 raw5599Labels = mixedMoment B node2187 node2187Labels := by
  calc
    mixedMoment B raw5599 raw5599Labels = mixedMoment B raw5599step0 raw5599step0Labels := by
      have ha : raw5599step0 = (fun i j => raw5599 (permutation224 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5599step0 raw5599; decide +kernel
      have hl : raw5599step0Labels = raw5599Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5599 raw5599Labels permutation224 permutation3
    _ = mixedMoment B node2187 node2187Labels := by rfl

def raw5600 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5600Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5600step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5600step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5600step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5600step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5600 raw5600Labels = mixedMoment B node3812 node3812Labels := by
  calc
    mixedMoment B raw5600 raw5600Labels = mixedMoment B raw5600step0 raw5600step0Labels := by
      have ha : raw5600step0 = (fun i j => raw5600 (permutation668 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5600step0 raw5600; decide +kernel
      have hl : raw5600step0Labels = raw5600Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5600 raw5600Labels permutation668 permutation7
    mixedMoment B raw5600step0 raw5600step0Labels = mixedMoment B raw5600step1 raw5600step1Labels := by
      have ha : raw5600step1 = raw5600step0 := by apply Matrix.ext; unfold raw5600step1 raw5600step0; decide +kernel
      have hl : raw5600step0Labels = labelEmbedding1 ∘ raw5600step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5600step0 raw5600step0Labels raw5600step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3812 node3812Labels := by rfl

def raw5601 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5601Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5601step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5601step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5601step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5601step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5601 raw5601Labels = mixedMoment B node3812 node3812Labels := by
  calc
    mixedMoment B raw5601 raw5601Labels = mixedMoment B raw5601step0 raw5601step0Labels := by
      have ha : raw5601step0 = (fun i j => raw5601 (permutation666 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5601step0 raw5601; decide +kernel
      have hl : raw5601step0Labels = raw5601Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5601 raw5601Labels permutation666 permutation7
    mixedMoment B raw5601step0 raw5601step0Labels = mixedMoment B raw5601step1 raw5601step1Labels := by
      have ha : raw5601step1 = raw5601step0 := by apply Matrix.ext; unfold raw5601step1 raw5601step0; decide +kernel
      have hl : raw5601step0Labels = labelEmbedding1 ∘ raw5601step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5601step0 raw5601step0Labels raw5601step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3812 node3812Labels := by rfl

def raw5602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5602Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5602step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5602step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5602step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5602step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5602 raw5602Labels = mixedMoment B node3812 node3812Labels := by
  calc
    mixedMoment B raw5602 raw5602Labels = mixedMoment B raw5602step0 raw5602step0Labels := by
      have ha : raw5602step0 = (fun i j => raw5602 (permutation665 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5602step0 raw5602; decide +kernel
      have hl : raw5602step0Labels = raw5602Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5602 raw5602Labels permutation665 permutation7
    mixedMoment B raw5602step0 raw5602step0Labels = mixedMoment B raw5602step1 raw5602step1Labels := by
      have ha : raw5602step1 = raw5602step0 := by apply Matrix.ext; unfold raw5602step1 raw5602step0; decide +kernel
      have hl : raw5602step0Labels = labelEmbedding1 ∘ raw5602step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5602step0 raw5602step0Labels raw5602step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3812 node3812Labels := by rfl

def raw5603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw5603Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5603step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw5603step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5603step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw5603step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5603step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw5603step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5603 raw5603Labels = mixedMoment B node3855 node3855Labels := by
  calc
    mixedMoment B raw5603 raw5603Labels = mixedMoment B raw5603step0 raw5603step0Labels := by
      have ha : raw5603step0 = (fun i j => raw5603 (permutation240 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5603step0 raw5603; decide +kernel
      have hl : raw5603step0Labels = raw5603Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5603 raw5603Labels permutation240 permutation5
    mixedMoment B raw5603step0 raw5603step0Labels = mixedMoment B raw5603step1 raw5603step1Labels := by
      have ha : raw5603step1 = -raw5603step0 := by apply Matrix.ext; change ∀ i j, raw5603step1 i j = -(raw5603step0 i j); unfold raw5603step1 raw5603step0; decide +kernel
      have hl : raw5603step1Labels = raw5603step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5603step1 raw5603step1Labels = mixedMoment B raw5603step2 raw5603step2Labels := by
      have ha : raw5603step2 = raw5603step1 := by apply Matrix.ext; unfold raw5603step2 raw5603step1; decide +kernel
      have hl : raw5603step1Labels = labelEmbedding1 ∘ raw5603step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5603step1 raw5603step1Labels raw5603step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3855 node3855Labels := by rfl

def raw5604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw5604Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5604step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw5604step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5604step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw5604step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5604step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw5604step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5604 raw5604Labels = mixedMoment B node3882 node3882Labels := by
  calc
    mixedMoment B raw5604 raw5604Labels = mixedMoment B raw5604step0 raw5604step0Labels := by
      have ha : raw5604step0 = (fun i j => raw5604 (permutation260 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5604step0 raw5604; decide +kernel
      have hl : raw5604step0Labels = raw5604Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5604 raw5604Labels permutation260 permutation5
    mixedMoment B raw5604step0 raw5604step0Labels = mixedMoment B raw5604step1 raw5604step1Labels := by
      have ha : raw5604step1 = -raw5604step0 := by apply Matrix.ext; change ∀ i j, raw5604step1 i j = -(raw5604step0 i j); unfold raw5604step1 raw5604step0; decide +kernel
      have hl : raw5604step1Labels = raw5604step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5604step1 raw5604step1Labels = mixedMoment B raw5604step2 raw5604step2Labels := by
      have ha : raw5604step2 = raw5604step1 := by apply Matrix.ext; unfold raw5604step2 raw5604step1; decide +kernel
      have hl : raw5604step1Labels = labelEmbedding1 ∘ raw5604step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5604step1 raw5604step1Labels raw5604step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3882 node3882Labels := by rfl

def raw5605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5605Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5605step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw5605step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5605step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw5605step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5605step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw5605step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5605 raw5605Labels = mixedMoment B node792 node792Labels := by
  calc
    mixedMoment B raw5605 raw5605Labels = mixedMoment B raw5605step0 raw5605step0Labels := by
      have ha : raw5605step0 = (fun i j => raw5605 (permutation243 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5605step0 raw5605; decide +kernel
      have hl : raw5605step0Labels = raw5605Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5605 raw5605Labels permutation243 permutation5
    mixedMoment B raw5605step0 raw5605step0Labels = mixedMoment B raw5605step1 raw5605step1Labels := by
      have ha : raw5605step1 = -raw5605step0 := by apply Matrix.ext; change ∀ i j, raw5605step1 i j = -(raw5605step0 i j); unfold raw5605step1 raw5605step0; decide +kernel
      have hl : raw5605step1Labels = raw5605step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5605step1 raw5605step1Labels = mixedMoment B raw5605step2 raw5605step2Labels := by
      have ha : raw5605step2 = raw5605step1 := by apply Matrix.ext; unfold raw5605step2 raw5605step1; decide +kernel
      have hl : raw5605step1Labels = labelEmbedding1 ∘ raw5605step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5605step1 raw5605step1Labels raw5605step2Labels labelEmbedding1 hl
    _ = mixedMoment B node792 node792Labels := by rfl

def raw5606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5606Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5606step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw5606step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5606step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw5606step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5606step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw5606step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5606 raw5606Labels = mixedMoment B node2195 node2195Labels := by
  calc
    mixedMoment B raw5606 raw5606Labels = mixedMoment B raw5606step0 raw5606step0Labels := by
      have ha : raw5606step0 = (fun i j => raw5606 (permutation193 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5606step0 raw5606; decide +kernel
      have hl : raw5606step0Labels = raw5606Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5606 raw5606Labels permutation193 permutation5
    mixedMoment B raw5606step0 raw5606step0Labels = mixedMoment B raw5606step1 raw5606step1Labels := by
      have ha : raw5606step1 = -raw5606step0 := by apply Matrix.ext; change ∀ i j, raw5606step1 i j = -(raw5606step0 i j); unfold raw5606step1 raw5606step0; decide +kernel
      have hl : raw5606step1Labels = raw5606step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5606step1 raw5606step1Labels = mixedMoment B raw5606step2 raw5606step2Labels := by
      have ha : raw5606step2 = raw5606step1 := by apply Matrix.ext; unfold raw5606step2 raw5606step1; decide +kernel
      have hl : raw5606step1Labels = labelEmbedding1 ∘ raw5606step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5606step1 raw5606step1Labels raw5606step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2195 node2195Labels := by rfl

def raw5607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5607Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5607step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw5607step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5607step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw5607step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5607step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw5607step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5607 raw5607Labels = mixedMoment B node2195 node2195Labels := by
  calc
    mixedMoment B raw5607 raw5607Labels = mixedMoment B raw5607step0 raw5607step0Labels := by
      have ha : raw5607step0 = (fun i j => raw5607 (permutation217 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5607step0 raw5607; decide +kernel
      have hl : raw5607step0Labels = raw5607Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5607 raw5607Labels permutation217 permutation5
    mixedMoment B raw5607step0 raw5607step0Labels = mixedMoment B raw5607step1 raw5607step1Labels := by
      have ha : raw5607step1 = -raw5607step0 := by apply Matrix.ext; change ∀ i j, raw5607step1 i j = -(raw5607step0 i j); unfold raw5607step1 raw5607step0; decide +kernel
      have hl : raw5607step1Labels = raw5607step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5607step1 raw5607step1Labels = mixedMoment B raw5607step2 raw5607step2Labels := by
      have ha : raw5607step2 = raw5607step1 := by apply Matrix.ext; unfold raw5607step2 raw5607step1; decide +kernel
      have hl : raw5607step1Labels = labelEmbedding1 ∘ raw5607step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5607step1 raw5607step1Labels raw5607step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2195 node2195Labels := by rfl

def raw5608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw5608Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5608step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw5608step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5608step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw5608step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5608step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw5608step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5608 raw5608Labels = mixedMoment B node2033 node2033Labels := by
  calc
    mixedMoment B raw5608 raw5608Labels = mixedMoment B raw5608step0 raw5608step0Labels := by
      have ha : raw5608step0 = (fun i j => raw5608 (permutation243 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5608step0 raw5608; decide +kernel
      have hl : raw5608step0Labels = raw5608Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5608 raw5608Labels permutation243 permutation5
    mixedMoment B raw5608step0 raw5608step0Labels = mixedMoment B raw5608step1 raw5608step1Labels := by
      have ha : raw5608step1 = -raw5608step0 := by apply Matrix.ext; change ∀ i j, raw5608step1 i j = -(raw5608step0 i j); unfold raw5608step1 raw5608step0; decide +kernel
      have hl : raw5608step1Labels = raw5608step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5608step1 raw5608step1Labels = mixedMoment B raw5608step2 raw5608step2Labels := by
      have ha : raw5608step2 = raw5608step1 := by apply Matrix.ext; unfold raw5608step2 raw5608step1; decide +kernel
      have hl : raw5608step1Labels = labelEmbedding1 ∘ raw5608step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5608step1 raw5608step1Labels raw5608step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2033 node2033Labels := by rfl

def raw5609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw5609Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5609step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw5609step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5609step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw5609step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5609step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw5609step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5609 raw5609Labels = mixedMoment B node2088 node2088Labels := by
  calc
    mixedMoment B raw5609 raw5609Labels = mixedMoment B raw5609step0 raw5609step0Labels := by
      have ha : raw5609step0 = (fun i j => raw5609 (permutation263 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5609step0 raw5609; decide +kernel
      have hl : raw5609step0Labels = raw5609Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5609 raw5609Labels permutation263 permutation5
    mixedMoment B raw5609step0 raw5609step0Labels = mixedMoment B raw5609step1 raw5609step1Labels := by
      have ha : raw5609step1 = -raw5609step0 := by apply Matrix.ext; change ∀ i j, raw5609step1 i j = -(raw5609step0 i j); unfold raw5609step1 raw5609step0; decide +kernel
      have hl : raw5609step1Labels = raw5609step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5609step1 raw5609step1Labels = mixedMoment B raw5609step2 raw5609step2Labels := by
      have ha : raw5609step2 = raw5609step1 := by apply Matrix.ext; unfold raw5609step2 raw5609step1; decide +kernel
      have hl : raw5609step1Labels = labelEmbedding1 ∘ raw5609step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5609step1 raw5609step1Labels raw5609step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2088 node2088Labels := by rfl

def raw5610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5610Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5610step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw5610step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5610step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw5610step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5610step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw5610step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5610 raw5610Labels = mixedMoment B node792 node792Labels := by
  calc
    mixedMoment B raw5610 raw5610Labels = mixedMoment B raw5610step0 raw5610step0Labels := by
      have ha : raw5610step0 = (fun i j => raw5610 (permutation241 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5610step0 raw5610; decide +kernel
      have hl : raw5610step0Labels = raw5610Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5610 raw5610Labels permutation241 permutation5
    mixedMoment B raw5610step0 raw5610step0Labels = mixedMoment B raw5610step1 raw5610step1Labels := by
      have ha : raw5610step1 = -raw5610step0 := by apply Matrix.ext; change ∀ i j, raw5610step1 i j = -(raw5610step0 i j); unfold raw5610step1 raw5610step0; decide +kernel
      have hl : raw5610step1Labels = raw5610step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5610step1 raw5610step1Labels = mixedMoment B raw5610step2 raw5610step2Labels := by
      have ha : raw5610step2 = raw5610step1 := by apply Matrix.ext; unfold raw5610step2 raw5610step1; decide +kernel
      have hl : raw5610step1Labels = labelEmbedding1 ∘ raw5610step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5610step1 raw5610step1Labels raw5610step2Labels labelEmbedding1 hl
    _ = mixedMoment B node792 node792Labels := by rfl

def raw5611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5611Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5611step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw5611step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5611step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw5611step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5611step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw5611step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5611 raw5611Labels = mixedMoment B node2195 node2195Labels := by
  calc
    mixedMoment B raw5611 raw5611Labels = mixedMoment B raw5611step0 raw5611step0Labels := by
      have ha : raw5611step0 = (fun i j => raw5611 (permutation169 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5611step0 raw5611; decide +kernel
      have hl : raw5611step0Labels = raw5611Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5611 raw5611Labels permutation169 permutation5
    mixedMoment B raw5611step0 raw5611step0Labels = mixedMoment B raw5611step1 raw5611step1Labels := by
      have ha : raw5611step1 = -raw5611step0 := by apply Matrix.ext; change ∀ i j, raw5611step1 i j = -(raw5611step0 i j); unfold raw5611step1 raw5611step0; decide +kernel
      have hl : raw5611step1Labels = raw5611step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5611step1 raw5611step1Labels = mixedMoment B raw5611step2 raw5611step2Labels := by
      have ha : raw5611step2 = raw5611step1 := by apply Matrix.ext; unfold raw5611step2 raw5611step1; decide +kernel
      have hl : raw5611step1Labels = labelEmbedding1 ∘ raw5611step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5611step1 raw5611step1Labels raw5611step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2195 node2195Labels := by rfl

def raw5612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![-1, 0, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5612Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5612step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw5612step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5612step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw5612step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5612step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw5612step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5612 raw5612Labels = mixedMoment B node2195 node2195Labels := by
  calc
    mixedMoment B raw5612 raw5612Labels = mixedMoment B raw5612step0 raw5612step0Labels := by
      have ha : raw5612step0 = (fun i j => raw5612 (permutation216 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5612step0 raw5612; decide +kernel
      have hl : raw5612step0Labels = raw5612Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5612 raw5612Labels permutation216 permutation5
    mixedMoment B raw5612step0 raw5612step0Labels = mixedMoment B raw5612step1 raw5612step1Labels := by
      have ha : raw5612step1 = -raw5612step0 := by apply Matrix.ext; change ∀ i j, raw5612step1 i j = -(raw5612step0 i j); unfold raw5612step1 raw5612step0; decide +kernel
      have hl : raw5612step1Labels = raw5612step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5612step1 raw5612step1Labels = mixedMoment B raw5612step2 raw5612step2Labels := by
      have ha : raw5612step2 = raw5612step1 := by apply Matrix.ext; unfold raw5612step2 raw5612step1; decide +kernel
      have hl : raw5612step1Labels = labelEmbedding1 ∘ raw5612step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5612step1 raw5612step1Labels raw5612step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2195 node2195Labels := by rfl

def raw5613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1], ![0, 1, -1], ![2, 0, -2]]
def raw5613Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5613step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw5613step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5613step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw5613step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5613step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw5613step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5613 raw5613Labels = mixedMoment B node2033 node2033Labels := by
  calc
    mixedMoment B raw5613 raw5613Labels = mixedMoment B raw5613step0 raw5613step0Labels := by
      have ha : raw5613step0 = (fun i j => raw5613 (permutation241 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5613step0 raw5613; decide +kernel
      have hl : raw5613step0Labels = raw5613Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5613 raw5613Labels permutation241 permutation5
    mixedMoment B raw5613step0 raw5613step0Labels = mixedMoment B raw5613step1 raw5613step1Labels := by
      have ha : raw5613step1 = -raw5613step0 := by apply Matrix.ext; change ∀ i j, raw5613step1 i j = -(raw5613step0 i j); unfold raw5613step1 raw5613step0; decide +kernel
      have hl : raw5613step1Labels = raw5613step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5613step1 raw5613step1Labels = mixedMoment B raw5613step2 raw5613step2Labels := by
      have ha : raw5613step2 = raw5613step1 := by apply Matrix.ext; unfold raw5613step2 raw5613step1; decide +kernel
      have hl : raw5613step1Labels = labelEmbedding1 ∘ raw5613step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5613step1 raw5613step1Labels raw5613step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2033 node2033Labels := by rfl

def raw5614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw5614Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5614step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw5614step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5614step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw5614step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5614step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw5614step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5614 raw5614Labels = mixedMoment B node2088 node2088Labels := by
  calc
    mixedMoment B raw5614 raw5614Labels = mixedMoment B raw5614step0 raw5614step0Labels := by
      have ha : raw5614step0 = (fun i j => raw5614 (permutation261 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5614step0 raw5614; decide +kernel
      have hl : raw5614step0Labels = raw5614Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5614 raw5614Labels permutation261 permutation5
    mixedMoment B raw5614step0 raw5614step0Labels = mixedMoment B raw5614step1 raw5614step1Labels := by
      have ha : raw5614step1 = -raw5614step0 := by apply Matrix.ext; change ∀ i j, raw5614step1 i j = -(raw5614step0 i j); unfold raw5614step1 raw5614step0; decide +kernel
      have hl : raw5614step1Labels = raw5614step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5614step1 raw5614step1Labels = mixedMoment B raw5614step2 raw5614step2Labels := by
      have ha : raw5614step2 = raw5614step1 := by apply Matrix.ext; unfold raw5614step2 raw5614step1; decide +kernel
      have hl : raw5614step1Labels = labelEmbedding1 ∘ raw5614step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5614step1 raw5614step1Labels raw5614step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2088 node2088Labels := by rfl

def raw5615 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5615Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5615step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw5615step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5615step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw5615step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5615step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw5615step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5615 raw5615Labels = mixedMoment B node792 node792Labels := by
  calc
    mixedMoment B raw5615 raw5615Labels = mixedMoment B raw5615step0 raw5615step0Labels := by
      have ha : raw5615step0 = (fun i j => raw5615 (permutation240 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5615step0 raw5615; decide +kernel
      have hl : raw5615step0Labels = raw5615Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5615 raw5615Labels permutation240 permutation5
    mixedMoment B raw5615step0 raw5615step0Labels = mixedMoment B raw5615step1 raw5615step1Labels := by
      have ha : raw5615step1 = -raw5615step0 := by apply Matrix.ext; change ∀ i j, raw5615step1 i j = -(raw5615step0 i j); unfold raw5615step1 raw5615step0; decide +kernel
      have hl : raw5615step1Labels = raw5615step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5615step1 raw5615step1Labels = mixedMoment B raw5615step2 raw5615step2Labels := by
      have ha : raw5615step2 = raw5615step1 := by apply Matrix.ext; unfold raw5615step2 raw5615step1; decide +kernel
      have hl : raw5615step1Labels = labelEmbedding1 ∘ raw5615step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5615step1 raw5615step1Labels raw5615step2Labels labelEmbedding1 hl
    _ = mixedMoment B node792 node792Labels := by rfl

def raw5616 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5616Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5616step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw5616step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5616step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw5616step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5616step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw5616step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5616 raw5616Labels = mixedMoment B node2195 node2195Labels := by
  calc
    mixedMoment B raw5616 raw5616Labels = mixedMoment B raw5616step0 raw5616step0Labels := by
      have ha : raw5616step0 = (fun i j => raw5616 (permutation168 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5616step0 raw5616; decide +kernel
      have hl : raw5616step0Labels = raw5616Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5616 raw5616Labels permutation168 permutation5
    mixedMoment B raw5616step0 raw5616step0Labels = mixedMoment B raw5616step1 raw5616step1Labels := by
      have ha : raw5616step1 = -raw5616step0 := by apply Matrix.ext; change ∀ i j, raw5616step1 i j = -(raw5616step0 i j); unfold raw5616step1 raw5616step0; decide +kernel
      have hl : raw5616step1Labels = raw5616step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5616step1 raw5616step1Labels = mixedMoment B raw5616step2 raw5616step2Labels := by
      have ha : raw5616step2 = raw5616step1 := by apply Matrix.ext; unfold raw5616step2 raw5616step1; decide +kernel
      have hl : raw5616step1Labels = labelEmbedding1 ∘ raw5616step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5616step1 raw5616step1Labels raw5616step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2195 node2195Labels := by rfl

def raw5617 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5617Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5617step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw5617step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5617step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw5617step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5617step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw5617step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5617 raw5617Labels = mixedMoment B node2195 node2195Labels := by
  calc
    mixedMoment B raw5617 raw5617Labels = mixedMoment B raw5617step0 raw5617step0Labels := by
      have ha : raw5617step0 = (fun i j => raw5617 (permutation192 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5617step0 raw5617; decide +kernel
      have hl : raw5617step0Labels = raw5617Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5617 raw5617Labels permutation192 permutation5
    mixedMoment B raw5617step0 raw5617step0Labels = mixedMoment B raw5617step1 raw5617step1Labels := by
      have ha : raw5617step1 = -raw5617step0 := by apply Matrix.ext; change ∀ i j, raw5617step1 i j = -(raw5617step0 i j); unfold raw5617step1 raw5617step0; decide +kernel
      have hl : raw5617step1Labels = raw5617step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5617step1 raw5617step1Labels = mixedMoment B raw5617step2 raw5617step2Labels := by
      have ha : raw5617step2 = raw5617step1 := by apply Matrix.ext; unfold raw5617step2 raw5617step1; decide +kernel
      have hl : raw5617step1Labels = labelEmbedding1 ∘ raw5617step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5617step1 raw5617step1Labels raw5617step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2195 node2195Labels := by rfl

def raw5618 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![0, 1, -1], ![2, 0, -2]]
def raw5618Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5618step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw5618step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5618step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw5618step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5618step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw5618step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5618 raw5618Labels = mixedMoment B node2033 node2033Labels := by
  calc
    mixedMoment B raw5618 raw5618Labels = mixedMoment B raw5618step0 raw5618step0Labels := by
      have ha : raw5618step0 = (fun i j => raw5618 (permutation240 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5618step0 raw5618; decide +kernel
      have hl : raw5618step0Labels = raw5618Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5618 raw5618Labels permutation240 permutation5
    mixedMoment B raw5618step0 raw5618step0Labels = mixedMoment B raw5618step1 raw5618step1Labels := by
      have ha : raw5618step1 = -raw5618step0 := by apply Matrix.ext; change ∀ i j, raw5618step1 i j = -(raw5618step0 i j); unfold raw5618step1 raw5618step0; decide +kernel
      have hl : raw5618step1Labels = raw5618step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5618step1 raw5618step1Labels = mixedMoment B raw5618step2 raw5618step2Labels := by
      have ha : raw5618step2 = raw5618step1 := by apply Matrix.ext; unfold raw5618step2 raw5618step1; decide +kernel
      have hl : raw5618step1Labels = labelEmbedding1 ∘ raw5618step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5618step1 raw5618step1Labels raw5618step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2033 node2033Labels := by rfl

def raw5619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw5619Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5619step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw5619step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5619step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw5619step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5619step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw5619step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5619 raw5619Labels = mixedMoment B node2088 node2088Labels := by
  calc
    mixedMoment B raw5619 raw5619Labels = mixedMoment B raw5619step0 raw5619step0Labels := by
      have ha : raw5619step0 = (fun i j => raw5619 (permutation260 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5619step0 raw5619; decide +kernel
      have hl : raw5619step0Labels = raw5619Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5619 raw5619Labels permutation260 permutation5
    mixedMoment B raw5619step0 raw5619step0Labels = mixedMoment B raw5619step1 raw5619step1Labels := by
      have ha : raw5619step1 = -raw5619step0 := by apply Matrix.ext; change ∀ i j, raw5619step1 i j = -(raw5619step0 i j); unfold raw5619step1 raw5619step0; decide +kernel
      have hl : raw5619step1Labels = raw5619step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5619step1 raw5619step1Labels = mixedMoment B raw5619step2 raw5619step2Labels := by
      have ha : raw5619step2 = raw5619step1 := by apply Matrix.ext; unfold raw5619step2 raw5619step1; decide +kernel
      have hl : raw5619step1Labels = labelEmbedding1 ∘ raw5619step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5619step1 raw5619step1Labels raw5619step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2088 node2088Labels := by rfl

def raw5620 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw5620Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5620step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw5620step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5620step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw5620step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5620step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw5620step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5620 raw5620Labels = mixedMoment B node821 node821Labels := by
  calc
    mixedMoment B raw5620 raw5620Labels = mixedMoment B raw5620step0 raw5620step0Labels := by
      have ha : raw5620step0 = (fun i j => raw5620 (permutation246 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5620step0 raw5620; decide +kernel
      have hl : raw5620step0Labels = raw5620Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5620 raw5620Labels permutation246 permutation5
    mixedMoment B raw5620step0 raw5620step0Labels = mixedMoment B raw5620step1 raw5620step1Labels := by
      have ha : raw5620step1 = -raw5620step0 := by apply Matrix.ext; change ∀ i j, raw5620step1 i j = -(raw5620step0 i j); unfold raw5620step1 raw5620step0; decide +kernel
      have hl : raw5620step1Labels = raw5620step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5620step1 raw5620step1Labels = mixedMoment B raw5620step2 raw5620step2Labels := by
      have ha : raw5620step2 = raw5620step1 := by apply Matrix.ext; unfold raw5620step2 raw5620step1; decide +kernel
      have hl : raw5620step1Labels = labelEmbedding1 ∘ raw5620step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5620step1 raw5620step1Labels raw5620step2Labels labelEmbedding1 hl
    _ = mixedMoment B node821 node821Labels := by rfl

def raw5621 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw5621Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5621step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw5621step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5621step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw5621step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5621step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw5621step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5621 raw5621Labels = mixedMoment B node2213 node2213Labels := by
  calc
    mixedMoment B raw5621 raw5621Labels = mixedMoment B raw5621step0 raw5621step0Labels := by
      have ha : raw5621step0 = (fun i j => raw5621 (permutation170 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5621step0 raw5621; decide +kernel
      have hl : raw5621step0Labels = raw5621Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5621 raw5621Labels permutation170 permutation5
    mixedMoment B raw5621step0 raw5621step0Labels = mixedMoment B raw5621step1 raw5621step1Labels := by
      have ha : raw5621step1 = -raw5621step0 := by apply Matrix.ext; change ∀ i j, raw5621step1 i j = -(raw5621step0 i j); unfold raw5621step1 raw5621step0; decide +kernel
      have hl : raw5621step1Labels = raw5621step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5621step1 raw5621step1Labels = mixedMoment B raw5621step2 raw5621step2Labels := by
      have ha : raw5621step2 = raw5621step1 := by apply Matrix.ext; unfold raw5621step2 raw5621step1; decide +kernel
      have hl : raw5621step1Labels = labelEmbedding1 ∘ raw5621step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5621step1 raw5621step1Labels raw5621step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2213 node2213Labels := by rfl

def raw5622 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw5622Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5622step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw5622step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5622step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw5622step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5622step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw5622step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5622 raw5622Labels = mixedMoment B node2213 node2213Labels := by
  calc
    mixedMoment B raw5622 raw5622Labels = mixedMoment B raw5622step0 raw5622step0Labels := by
      have ha : raw5622step0 = (fun i j => raw5622 (permutation194 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5622step0 raw5622; decide +kernel
      have hl : raw5622step0Labels = raw5622Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5622 raw5622Labels permutation194 permutation5
    mixedMoment B raw5622step0 raw5622step0Labels = mixedMoment B raw5622step1 raw5622step1Labels := by
      have ha : raw5622step1 = -raw5622step0 := by apply Matrix.ext; change ∀ i j, raw5622step1 i j = -(raw5622step0 i j); unfold raw5622step1 raw5622step0; decide +kernel
      have hl : raw5622step1Labels = raw5622step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5622step1 raw5622step1Labels = mixedMoment B raw5622step2 raw5622step2Labels := by
      have ha : raw5622step2 = raw5622step1 := by apply Matrix.ext; unfold raw5622step2 raw5622step1; decide +kernel
      have hl : raw5622step1Labels = labelEmbedding1 ∘ raw5622step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5622step1 raw5622step1Labels raw5622step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2213 node2213Labels := by rfl

def raw5623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw5623Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5623step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw5623step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5623step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw5623step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5623step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw5623step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5623 raw5623Labels = mixedMoment B node2213 node2213Labels := by
  calc
    mixedMoment B raw5623 raw5623Labels = mixedMoment B raw5623step0 raw5623step0Labels := by
      have ha : raw5623step0 = (fun i j => raw5623 (permutation218 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5623step0 raw5623; decide +kernel
      have hl : raw5623step0Labels = raw5623Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5623 raw5623Labels permutation218 permutation5
    mixedMoment B raw5623step0 raw5623step0Labels = mixedMoment B raw5623step1 raw5623step1Labels := by
      have ha : raw5623step1 = -raw5623step0 := by apply Matrix.ext; change ∀ i j, raw5623step1 i j = -(raw5623step0 i j); unfold raw5623step1 raw5623step0; decide +kernel
      have hl : raw5623step1Labels = raw5623step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5623step1 raw5623step1Labels = mixedMoment B raw5623step2 raw5623step2Labels := by
      have ha : raw5623step2 = raw5623step1 := by apply Matrix.ext; unfold raw5623step2 raw5623step1; decide +kernel
      have hl : raw5623step1Labels = labelEmbedding1 ∘ raw5623step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5623step1 raw5623step1Labels raw5623step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2213 node2213Labels := by rfl

def raw5624 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 1, -2]]
def raw5624Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5624step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw5624step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5624step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw5624step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5624step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw5624step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5624 raw5624Labels = mixedMoment B node2104 node2104Labels := by
  calc
    mixedMoment B raw5624 raw5624Labels = mixedMoment B raw5624step0 raw5624step0Labels := by
      have ha : raw5624step0 = (fun i j => raw5624 (permutation246 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5624step0 raw5624; decide +kernel
      have hl : raw5624step0Labels = raw5624Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5624 raw5624Labels permutation246 permutation5
    mixedMoment B raw5624step0 raw5624step0Labels = mixedMoment B raw5624step1 raw5624step1Labels := by
      have ha : raw5624step1 = -raw5624step0 := by apply Matrix.ext; change ∀ i j, raw5624step1 i j = -(raw5624step0 i j); unfold raw5624step1 raw5624step0; decide +kernel
      have hl : raw5624step1Labels = raw5624step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5624step1 raw5624step1Labels = mixedMoment B raw5624step2 raw5624step2Labels := by
      have ha : raw5624step2 = raw5624step1 := by apply Matrix.ext; unfold raw5624step2 raw5624step1; decide +kernel
      have hl : raw5624step1Labels = labelEmbedding1 ∘ raw5624step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5624step1 raw5624step1Labels raw5624step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2104 node2104Labels := by rfl

def raw5625 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw5625Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5625step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5625step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5625step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw5625step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5625step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw5625step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5625 raw5625Labels = mixedMoment B node802 node802Labels := by
  calc
    mixedMoment B raw5625 raw5625Labels = mixedMoment B raw5625step0 raw5625step0Labels := by
      have ha : raw5625step0 = (fun i j => raw5625 (permutation224 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5625step0 raw5625; decide +kernel
      have hl : raw5625step0Labels = raw5625Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5625 raw5625Labels permutation224 permutation5
    mixedMoment B raw5625step0 raw5625step0Labels = mixedMoment B raw5625step1 raw5625step1Labels := by
      have ha : raw5625step1 = -raw5625step0 := by apply Matrix.ext; change ∀ i j, raw5625step1 i j = -(raw5625step0 i j); unfold raw5625step1 raw5625step0; decide +kernel
      have hl : raw5625step1Labels = raw5625step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5625step1 raw5625step1Labels = mixedMoment B raw5625step2 raw5625step2Labels := by
      have ha : raw5625step2 = raw5625step1 := by apply Matrix.ext; unfold raw5625step2 raw5625step1; decide +kernel
      have hl : raw5625step1Labels = labelEmbedding1 ∘ raw5625step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5625step1 raw5625step1Labels raw5625step2Labels labelEmbedding1 hl
    _ = mixedMoment B node802 node802Labels := by rfl

def raw5626 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw5626Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5626step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5626step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5626step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw5626step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5626step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw5626step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5626 raw5626Labels = mixedMoment B node2201 node2201Labels := by
  calc
    mixedMoment B raw5626 raw5626Labels = mixedMoment B raw5626step0 raw5626step0Labels := by
      have ha : raw5626step0 = (fun i j => raw5626 (permutation164 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5626step0 raw5626; decide +kernel
      have hl : raw5626step0Labels = raw5626Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5626 raw5626Labels permutation164 permutation5
    mixedMoment B raw5626step0 raw5626step0Labels = mixedMoment B raw5626step1 raw5626step1Labels := by
      have ha : raw5626step1 = -raw5626step0 := by apply Matrix.ext; change ∀ i j, raw5626step1 i j = -(raw5626step0 i j); unfold raw5626step1 raw5626step0; decide +kernel
      have hl : raw5626step1Labels = raw5626step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5626step1 raw5626step1Labels = mixedMoment B raw5626step2 raw5626step2Labels := by
      have ha : raw5626step2 = raw5626step1 := by apply Matrix.ext; unfold raw5626step2 raw5626step1; decide +kernel
      have hl : raw5626step1Labels = labelEmbedding1 ∘ raw5626step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5626step1 raw5626step1Labels raw5626step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2201 node2201Labels := by rfl

def raw5627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw5627Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5627step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5627step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5627step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw5627step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5627step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw5627step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5627 raw5627Labels = mixedMoment B node2201 node2201Labels := by
  calc
    mixedMoment B raw5627 raw5627Labels = mixedMoment B raw5627step0 raw5627step0Labels := by
      have ha : raw5627step0 = (fun i j => raw5627 (permutation188 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5627step0 raw5627; decide +kernel
      have hl : raw5627step0Labels = raw5627Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5627 raw5627Labels permutation188 permutation5
    mixedMoment B raw5627step0 raw5627step0Labels = mixedMoment B raw5627step1 raw5627step1Labels := by
      have ha : raw5627step1 = -raw5627step0 := by apply Matrix.ext; change ∀ i j, raw5627step1 i j = -(raw5627step0 i j); unfold raw5627step1 raw5627step0; decide +kernel
      have hl : raw5627step1Labels = raw5627step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5627step1 raw5627step1Labels = mixedMoment B raw5627step2 raw5627step2Labels := by
      have ha : raw5627step2 = raw5627step1 := by apply Matrix.ext; unfold raw5627step2 raw5627step1; decide +kernel
      have hl : raw5627step1Labels = labelEmbedding1 ∘ raw5627step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5627step1 raw5627step1Labels raw5627step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2201 node2201Labels := by rfl

def raw5628 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw5628Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5628step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5628step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5628step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw5628step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5628step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw5628step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5628 raw5628Labels = mixedMoment B node2201 node2201Labels := by
  calc
    mixedMoment B raw5628 raw5628Labels = mixedMoment B raw5628step0 raw5628step0Labels := by
      have ha : raw5628step0 = (fun i j => raw5628 (permutation212 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5628step0 raw5628; decide +kernel
      have hl : raw5628step0Labels = raw5628Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5628 raw5628Labels permutation212 permutation5
    mixedMoment B raw5628step0 raw5628step0Labels = mixedMoment B raw5628step1 raw5628step1Labels := by
      have ha : raw5628step1 = -raw5628step0 := by apply Matrix.ext; change ∀ i j, raw5628step1 i j = -(raw5628step0 i j); unfold raw5628step1 raw5628step0; decide +kernel
      have hl : raw5628step1Labels = raw5628step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5628step1 raw5628step1Labels = mixedMoment B raw5628step2 raw5628step2Labels := by
      have ha : raw5628step2 = raw5628step1 := by apply Matrix.ext; unfold raw5628step2 raw5628step1; decide +kernel
      have hl : raw5628step1Labels = labelEmbedding1 ∘ raw5628step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5628step1 raw5628step1Labels raw5628step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2201 node2201Labels := by rfl

def raw5629 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw5629Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5629step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5629step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5629step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw5629step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5629step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw5629step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5629 raw5629Labels = mixedMoment B node2050 node2050Labels := by
  calc
    mixedMoment B raw5629 raw5629Labels = mixedMoment B raw5629step0 raw5629step0Labels := by
      have ha : raw5629step0 = (fun i j => raw5629 (permutation224 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5629step0 raw5629; decide +kernel
      have hl : raw5629step0Labels = raw5629Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5629 raw5629Labels permutation224 permutation5
    mixedMoment B raw5629step0 raw5629step0Labels = mixedMoment B raw5629step1 raw5629step1Labels := by
      have ha : raw5629step1 = -raw5629step0 := by apply Matrix.ext; change ∀ i j, raw5629step1 i j = -(raw5629step0 i j); unfold raw5629step1 raw5629step0; decide +kernel
      have hl : raw5629step1Labels = raw5629step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5629step1 raw5629step1Labels = mixedMoment B raw5629step2 raw5629step2Labels := by
      have ha : raw5629step2 = raw5629step1 := by apply Matrix.ext; unfold raw5629step2 raw5629step1; decide +kernel
      have hl : raw5629step1Labels = labelEmbedding1 ∘ raw5629step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5629step1 raw5629step1Labels raw5629step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2050 node2050Labels := by rfl

def raw5630 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5630Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5630step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw5630step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5630step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw5630step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5630 raw5630Labels = mixedMoment B node3221 node3221Labels := by
  calc
    mixedMoment B raw5630 raw5630Labels = mixedMoment B raw5630step0 raw5630step0Labels := by
      have ha : raw5630step0 = (fun i j => raw5630 (permutation260 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5630step0 raw5630; decide +kernel
      have hl : raw5630step0Labels = raw5630Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5630 raw5630Labels permutation260 permutation4
    mixedMoment B raw5630step0 raw5630step0Labels = mixedMoment B raw5630step1 raw5630step1Labels := by
      have ha : raw5630step1 = -raw5630step0 := by apply Matrix.ext; change ∀ i j, raw5630step1 i j = -(raw5630step0 i j); unfold raw5630step1 raw5630step0; decide +kernel
      have hl : raw5630step1Labels = raw5630step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3221 node3221Labels := by rfl

def raw5631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5631Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5631step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw5631step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5631step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5631step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5631 raw5631Labels = mixedMoment B node3801 node3801Labels := by
  calc
    mixedMoment B raw5631 raw5631Labels = mixedMoment B raw5631step0 raw5631step0Labels := by
      have ha : raw5631step0 = (fun i j => raw5631 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5631step0 raw5631; decide +kernel
      have hl : raw5631step0Labels = raw5631Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5631 raw5631Labels permutation682 permutation2
    mixedMoment B raw5631step0 raw5631step0Labels = mixedMoment B raw5631step1 raw5631step1Labels := by
      have ha : raw5631step1 = -raw5631step0 := by apply Matrix.ext; change ∀ i j, raw5631step1 i j = -(raw5631step0 i j); unfold raw5631step1 raw5631step0; decide +kernel
      have hl : raw5631step1Labels = raw5631step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3801 node3801Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
