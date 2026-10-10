import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw34816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw34816Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34816step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw34816step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34816step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34816step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34816step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34816step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34816 raw34816Labels = mixedMoment B node2817 node2817Labels := by
  calc
    mixedMoment B raw34816 raw34816Labels = mixedMoment B raw34816step0 raw34816step0Labels := by
      have hz : ∀ j, raw34816 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34816step0 = (fun i j => raw34816 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34816step0 raw34816; decide +kernel
      have hl : raw34816step0Labels = raw34816Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34816 raw34816Labels permutation346 hz
    mixedMoment B raw34816step0 raw34816step0Labels = mixedMoment B raw34816step1 raw34816step1Labels := by
      have ha : raw34816step1 = (fun i j => raw34816step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34816step1 raw34816step0; decide +kernel
      have hl : raw34816step1Labels = raw34816step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34816step0 raw34816step0Labels permutation150 permutation3
    mixedMoment B raw34816step1 raw34816step1Labels = mixedMoment B raw34816step2 raw34816step2Labels := by
      have ha : raw34816step2 = -raw34816step1 := by apply Matrix.ext; change ∀ i j, raw34816step2 i j = -(raw34816step1 i j); unfold raw34816step2 raw34816step1; decide +kernel
      have hl : raw34816step2Labels = raw34816step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2817 node2817Labels := by rfl

def raw34817 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34817Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34817step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34817step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34817step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-2, 0, 2], ![0, -2, 2]]
def raw34817step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34817step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw34817step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34817step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34817step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34817step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34817step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34817 raw34817Labels = mixedMoment B node5390 node5390Labels := by
  calc
    mixedMoment B raw34817 raw34817Labels = mixedMoment B raw34817step0 raw34817step0Labels := by
      have hz : ∀ j, raw34817 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34817step0 = (fun i j => raw34817 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34817step0 raw34817; decide +kernel
      have hl : raw34817step0Labels = raw34817Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34817 raw34817Labels permutation434 hz
    mixedMoment B raw34817step0 raw34817step0Labels = mixedMoment B raw34817step1 raw34817step1Labels := by
      have hz : ∀ j, raw34817step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34817step1 = (fun i j => raw34817step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34817step1 raw34817step0; decide +kernel
      have hl : raw34817step1Labels = raw34817step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34817step0 raw34817step0Labels permutation80 hz
    mixedMoment B raw34817step1 raw34817step1Labels = mixedMoment B raw34817step2 raw34817step2Labels := by
      have ha : raw34817step2 = (fun i j => raw34817step1 (permutation30 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34817step2 raw34817step1; decide +kernel
      have hl : raw34817step2Labels = raw34817step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34817step1 raw34817step1Labels permutation30 permutation6
    mixedMoment B raw34817step2 raw34817step2Labels = mixedMoment B raw34817step3 raw34817step3Labels := by
      have ha : raw34817step3 = -raw34817step2 := by apply Matrix.ext; change ∀ i j, raw34817step3 i j = -(raw34817step2 i j); unfold raw34817step3 raw34817step2; decide +kernel
      have hl : raw34817step3Labels = raw34817step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34817step3 raw34817step3Labels = mixedMoment B raw34817step4 raw34817step4Labels := by
      have ha : raw34817step4 = raw34817step3 := by apply Matrix.ext; unfold raw34817step4 raw34817step3; decide +kernel
      have hl : raw34817step3Labels = labelEmbedding9 ∘ raw34817step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34817step3 raw34817step3Labels raw34817step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5390 node5390Labels := by rfl

def raw34818 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34818Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34818step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34818step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34818step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34818step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34818step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34818step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34818 raw34818Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw34818 raw34818Labels = mixedMoment B raw34818step0 raw34818step0Labels := by
      have hz : ∀ j, raw34818 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34818step0 = (fun i j => raw34818 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34818step0 raw34818; decide +kernel
      have hl : raw34818step0Labels = raw34818Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34818 raw34818Labels permutation434 hz
    mixedMoment B raw34818step0 raw34818step0Labels = mixedMoment B raw34818step1 raw34818step1Labels := by
      have ha : raw34818step1 = (fun i j => raw34818step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34818step1 raw34818step0; decide +kernel
      have hl : raw34818step1Labels = raw34818step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34818step0 raw34818step0Labels permutation57 permutation7
    mixedMoment B raw34818step1 raw34818step1Labels = mixedMoment B raw34818step2 raw34818step2Labels := by
      have ha : raw34818step2 = raw34818step1 := by apply Matrix.ext; unfold raw34818step2 raw34818step1; decide +kernel
      have hl : raw34818step1Labels = labelEmbedding10 ∘ raw34818step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34818step1 raw34818step1Labels raw34818step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

def raw34819 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34819Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34819step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34819step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34819step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34819step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34819step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34819 raw34819Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw34819 raw34819Labels = mixedMoment B raw34819step0 raw34819step0Labels := by
      have hz : ∀ j, raw34819 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34819step0 = (fun i j => raw34819 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34819step0 raw34819; decide +kernel
      have hl : raw34819step0Labels = raw34819Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34819 raw34819Labels permutation346 hz
    mixedMoment B raw34819step0 raw34819step0Labels = mixedMoment B raw34819step1 raw34819step1Labels := by
      have ha : raw34819step1 = (fun i j => raw34819step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34819step1 raw34819step0; decide +kernel
      have hl : raw34819step1Labels = raw34819step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34819step0 raw34819step0Labels permutation57 permutation7
    mixedMoment B raw34819step1 raw34819step1Labels = mixedMoment B raw34819step2 raw34819step2Labels := by
      have ha : raw34819step2 = raw34819step1 := by apply Matrix.ext; unfold raw34819step2 raw34819step1; decide +kernel
      have hl : raw34819step1Labels = labelEmbedding10 ∘ raw34819step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34819step1 raw34819step1Labels raw34819step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

def raw34820 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw34820Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw34820step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34820step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-3, 1, 2], ![0, -2, 2]]
def raw34820step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34820step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw34820step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34820 raw34820Labels = mixedMoment B node5238 node5238Labels := by
  calc
    mixedMoment B raw34820 raw34820Labels = mixedMoment B raw34820step0 raw34820step0Labels := by
      have hz : ∀ j, raw34820 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34820step0 = (fun i j => raw34820 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34820step0 raw34820; decide +kernel
      have hl : raw34820step0Labels = raw34820Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34820 raw34820Labels permutation434 hz
    mixedMoment B raw34820step0 raw34820step0Labels = mixedMoment B raw34820step1 raw34820step1Labels := by
      have hz : ∀ j, raw34820step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34820step1 = (fun i j => raw34820step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34820step1 raw34820step0; decide +kernel
      have hl : raw34820step1Labels = raw34820step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34820step0 raw34820step0Labels permutation80 hz
    mixedMoment B raw34820step1 raw34820step1Labels = mixedMoment B raw34820step2 raw34820step2Labels := by
      have ha : raw34820step2 = (fun i j => raw34820step1 (permutation24 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34820step2 raw34820step1; decide +kernel
      have hl : raw34820step2Labels = raw34820step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34820step1 raw34820step1Labels permutation24 permutation2
    _ = mixedMoment B node5238 node5238Labels := by rfl

def raw34821 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw34821Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw34821step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34821step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-2, 0, 2], ![-1, -1, 2]]
def raw34821step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34821step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw34821step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34821step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw34821step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34821 raw34821Labels = mixedMoment B node5371 node5371Labels := by
  calc
    mixedMoment B raw34821 raw34821Labels = mixedMoment B raw34821step0 raw34821step0Labels := by
      have hz : ∀ j, raw34821 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34821step0 = (fun i j => raw34821 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34821step0 raw34821; decide +kernel
      have hl : raw34821step0Labels = raw34821Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34821 raw34821Labels permutation434 hz
    mixedMoment B raw34821step0 raw34821step0Labels = mixedMoment B raw34821step1 raw34821step1Labels := by
      have hz : ∀ j, raw34821step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34821step1 = (fun i j => raw34821step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34821step1 raw34821step0; decide +kernel
      have hl : raw34821step1Labels = raw34821step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34821step0 raw34821step0Labels permutation80 hz
    mixedMoment B raw34821step1 raw34821step1Labels = mixedMoment B raw34821step2 raw34821step2Labels := by
      have ha : raw34821step2 = (fun i j => raw34821step1 (permutation15 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34821step2 raw34821step1; decide +kernel
      have hl : raw34821step2Labels = raw34821step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34821step1 raw34821step1Labels permutation15 permutation7
    mixedMoment B raw34821step2 raw34821step2Labels = mixedMoment B raw34821step3 raw34821step3Labels := by
      have ha : raw34821step3 = raw34821step2 := by apply Matrix.ext; unfold raw34821step3 raw34821step2; decide +kernel
      have hl : raw34821step2Labels = labelEmbedding10 ∘ raw34821step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34821step2 raw34821step2Labels raw34821step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5371 node5371Labels := by rfl

def raw34822 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -1, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34822Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34822step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -1, -2], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34822step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34822step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -1, -2], ![-2, 0, 2], ![0, -2, 2]]
def raw34822step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34822step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 3, -2], ![-2, 0, 2]]
def raw34822step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34822step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw34822step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34822 raw34822Labels = mixedMoment B node5297 node5297Labels := by
  calc
    mixedMoment B raw34822 raw34822Labels = mixedMoment B raw34822step0 raw34822step0Labels := by
      have hz : ∀ j, raw34822 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34822step0 = (fun i j => raw34822 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34822step0 raw34822; decide +kernel
      have hl : raw34822step0Labels = raw34822Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34822 raw34822Labels permutation434 hz
    mixedMoment B raw34822step0 raw34822step0Labels = mixedMoment B raw34822step1 raw34822step1Labels := by
      have hz : ∀ j, raw34822step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34822step1 = (fun i j => raw34822step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34822step1 raw34822step0; decide +kernel
      have hl : raw34822step1Labels = raw34822step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34822step0 raw34822step0Labels permutation80 hz
    mixedMoment B raw34822step1 raw34822step1Labels = mixedMoment B raw34822step2 raw34822step2Labels := by
      have ha : raw34822step2 = (fun i j => raw34822step1 (permutation18 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34822step2 raw34822step1; decide +kernel
      have hl : raw34822step2Labels = raw34822step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34822step1 raw34822step1Labels permutation18 permutation2
    mixedMoment B raw34822step2 raw34822step2Labels = mixedMoment B raw34822step3 raw34822step3Labels := by
      have ha : raw34822step3 = -raw34822step2 := by apply Matrix.ext; change ∀ i j, raw34822step3 i j = -(raw34822step2 i j); unfold raw34822step3 raw34822step2; decide +kernel
      have hl : raw34822step3Labels = raw34822step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5297 node5297Labels := by rfl

def raw34823 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34823Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34823step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34823step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34823step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw34823step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34823step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34823step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34823 raw34823Labels = mixedMoment B node5232 node5232Labels := by
  calc
    mixedMoment B raw34823 raw34823Labels = mixedMoment B raw34823step0 raw34823step0Labels := by
      have hz : ∀ j, raw34823 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34823step0 = (fun i j => raw34823 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34823step0 raw34823; decide +kernel
      have hl : raw34823step0Labels = raw34823Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34823 raw34823Labels permutation434 hz
    mixedMoment B raw34823step0 raw34823step0Labels = mixedMoment B raw34823step1 raw34823step1Labels := by
      have ha : raw34823step1 = (fun i j => raw34823step0 (permutation60 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34823step1 raw34823step0; decide +kernel
      have hl : raw34823step1Labels = raw34823step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34823step0 raw34823step0Labels permutation60 permutation2
    mixedMoment B raw34823step1 raw34823step1Labels = mixedMoment B raw34823step2 raw34823step2Labels := by
      have ha : raw34823step2 = -raw34823step1 := by apply Matrix.ext; change ∀ i j, raw34823step2 i j = -(raw34823step1 i j); unfold raw34823step2 raw34823step1; decide +kernel
      have hl : raw34823step2Labels = raw34823step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5232 node5232Labels := by rfl

def raw34824 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34824Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34824step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34824step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw34824step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34824step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34824step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34824 raw34824Labels = mixedMoment B node5232 node5232Labels := by
  calc
    mixedMoment B raw34824 raw34824Labels = mixedMoment B raw34824step0 raw34824step0Labels := by
      have hz : ∀ j, raw34824 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34824step0 = (fun i j => raw34824 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34824step0 raw34824; decide +kernel
      have hl : raw34824step0Labels = raw34824Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34824 raw34824Labels permutation346 hz
    mixedMoment B raw34824step0 raw34824step0Labels = mixedMoment B raw34824step1 raw34824step1Labels := by
      have ha : raw34824step1 = (fun i j => raw34824step0 (permutation60 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34824step1 raw34824step0; decide +kernel
      have hl : raw34824step1Labels = raw34824step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34824step0 raw34824step0Labels permutation60 permutation2
    mixedMoment B raw34824step1 raw34824step1Labels = mixedMoment B raw34824step2 raw34824step2Labels := by
      have ha : raw34824step2 = -raw34824step1 := by apply Matrix.ext; change ∀ i j, raw34824step2 i j = -(raw34824step1 i j); unfold raw34824step2 raw34824step1; decide +kernel
      have hl : raw34824step2Labels = raw34824step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5232 node5232Labels := by rfl

def raw34825 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw34825Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw34825step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34825step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![-3, 1, 2], ![0, -2, 2]]
def raw34825step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34825step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw34825step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34825 raw34825Labels = mixedMoment B node5235 node5235Labels := by
  calc
    mixedMoment B raw34825 raw34825Labels = mixedMoment B raw34825step0 raw34825step0Labels := by
      have hz : ∀ j, raw34825 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34825step0 = (fun i j => raw34825 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34825step0 raw34825; decide +kernel
      have hl : raw34825step0Labels = raw34825Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34825 raw34825Labels permutation434 hz
    mixedMoment B raw34825step0 raw34825step0Labels = mixedMoment B raw34825step1 raw34825step1Labels := by
      have hz : ∀ j, raw34825step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34825step1 = (fun i j => raw34825step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34825step1 raw34825step0; decide +kernel
      have hl : raw34825step1Labels = raw34825step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34825step0 raw34825step0Labels permutation80 hz
    mixedMoment B raw34825step1 raw34825step1Labels = mixedMoment B raw34825step2 raw34825step2Labels := by
      have ha : raw34825step2 = (fun i j => raw34825step1 (permutation24 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34825step2 raw34825step1; decide +kernel
      have hl : raw34825step2Labels = raw34825step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34825step1 raw34825step1Labels permutation24 permutation2
    _ = mixedMoment B node5235 node5235Labels := by rfl

def raw34826 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw34826Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34826step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw34826step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34826step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![-2, 0, 2], ![-1, -1, 2]]
def raw34826step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34826step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw34826step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34826step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw34826step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34826 raw34826Labels = mixedMoment B node5238 node5238Labels := by
  calc
    mixedMoment B raw34826 raw34826Labels = mixedMoment B raw34826step0 raw34826step0Labels := by
      have hz : ∀ j, raw34826 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34826step0 = (fun i j => raw34826 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34826step0 raw34826; decide +kernel
      have hl : raw34826step0Labels = raw34826Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34826 raw34826Labels permutation434 hz
    mixedMoment B raw34826step0 raw34826step0Labels = mixedMoment B raw34826step1 raw34826step1Labels := by
      have hz : ∀ j, raw34826step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34826step1 = (fun i j => raw34826step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34826step1 raw34826step0; decide +kernel
      have hl : raw34826step1Labels = raw34826step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34826step0 raw34826step0Labels permutation80 hz
    mixedMoment B raw34826step1 raw34826step1Labels = mixedMoment B raw34826step2 raw34826step2Labels := by
      have ha : raw34826step2 = (fun i j => raw34826step1 (permutation15 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34826step2 raw34826step1; decide +kernel
      have hl : raw34826step2Labels = raw34826step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34826step1 raw34826step1Labels permutation15 permutation2
    mixedMoment B raw34826step2 raw34826step2Labels = mixedMoment B raw34826step3 raw34826step3Labels := by
      have ha : raw34826step3 = -raw34826step2 := by apply Matrix.ext; change ∀ i j, raw34826step3 i j = -(raw34826step2 i j); unfold raw34826step3 raw34826step2; decide +kernel
      have hl : raw34826step3Labels = raw34826step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5238 node5238Labels := by rfl

def raw34827 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34827Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34827step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34827step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34827step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw34827step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34827step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34827step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34827step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34827step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34827 raw34827Labels = mixedMoment B node5232 node5232Labels := by
  calc
    mixedMoment B raw34827 raw34827Labels = mixedMoment B raw34827step0 raw34827step0Labels := by
      have hz : ∀ j, raw34827 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34827step0 = (fun i j => raw34827 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34827step0 raw34827; decide +kernel
      have hl : raw34827step0Labels = raw34827Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34827 raw34827Labels permutation434 hz
    mixedMoment B raw34827step0 raw34827step0Labels = mixedMoment B raw34827step1 raw34827step1Labels := by
      have ha : raw34827step1 = (fun i j => raw34827step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34827step1 raw34827step0; decide +kernel
      have hl : raw34827step1Labels = raw34827step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34827step0 raw34827step0Labels permutation34 permutation4
    mixedMoment B raw34827step1 raw34827step1Labels = mixedMoment B raw34827step2 raw34827step2Labels := by
      have ha : raw34827step2 = -raw34827step1 := by apply Matrix.ext; change ∀ i j, raw34827step2 i j = -(raw34827step1 i j); unfold raw34827step2 raw34827step1; decide +kernel
      have hl : raw34827step2Labels = raw34827step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34827step2 raw34827step2Labels = mixedMoment B raw34827step3 raw34827step3Labels := by
      have ha : raw34827step3 = raw34827step2 := by apply Matrix.ext; unfold raw34827step3 raw34827step2; decide +kernel
      have hl : raw34827step2Labels = labelEmbedding7 ∘ raw34827step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34827step2 raw34827step2Labels raw34827step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5232 node5232Labels := by rfl

def raw34828 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34828Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34828step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34828step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34828step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34828step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34828step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34828step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34828 raw34828Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw34828 raw34828Labels = mixedMoment B raw34828step0 raw34828step0Labels := by
      have hz : ∀ j, raw34828 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34828step0 = (fun i j => raw34828 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34828step0 raw34828; decide +kernel
      have hl : raw34828step0Labels = raw34828Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34828 raw34828Labels permutation434 hz
    mixedMoment B raw34828step0 raw34828step0Labels = mixedMoment B raw34828step1 raw34828step1Labels := by
      have ha : raw34828step1 = (fun i j => raw34828step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34828step1 raw34828step0; decide +kernel
      have hl : raw34828step1Labels = raw34828step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34828step0 raw34828step0Labels permutation32 permutation6
    mixedMoment B raw34828step1 raw34828step1Labels = mixedMoment B raw34828step2 raw34828step2Labels := by
      have ha : raw34828step2 = raw34828step1 := by apply Matrix.ext; unfold raw34828step2 raw34828step1; decide +kernel
      have hl : raw34828step1Labels = labelEmbedding9 ∘ raw34828step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34828step1 raw34828step1Labels raw34828step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

def raw34829 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34829Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34829step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34829step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34829step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34829step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34829 raw34829Labels = mixedMoment B node5376 node5376Labels := by
  calc
    mixedMoment B raw34829 raw34829Labels = mixedMoment B raw34829step0 raw34829step0Labels := by
      have ha : raw34829step0 = (fun i j => raw34829 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34829step0 raw34829; decide +kernel
      have hl : raw34829step0Labels = raw34829Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34829 raw34829Labels permutation158 permutation6
    mixedMoment B raw34829step0 raw34829step0Labels = mixedMoment B raw34829step1 raw34829step1Labels := by
      have ha : raw34829step1 = raw34829step0 := by apply Matrix.ext; unfold raw34829step1 raw34829step0; decide +kernel
      have hl : raw34829step0Labels = labelEmbedding9 ∘ raw34829step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34829step0 raw34829step0Labels raw34829step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5376 node5376Labels := by rfl

def raw34830 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![0, 0, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw34830Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34830step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw34830step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34830step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34830step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34830 raw34830Labels = mixedMoment B node5232 node5232Labels := by
  calc
    mixedMoment B raw34830 raw34830Labels = mixedMoment B raw34830step0 raw34830step0Labels := by
      have hz : ∀ j, raw34830 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34830step0 = (fun i j => raw34830 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34830step0 raw34830; decide +kernel
      have hl : raw34830step0Labels = raw34830Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34830 raw34830Labels permutation434 hz
    mixedMoment B raw34830step0 raw34830step0Labels = mixedMoment B raw34830step1 raw34830step1Labels := by
      have ha : raw34830step1 = (fun i j => raw34830step0 (permutation123 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34830step1 raw34830step0; decide +kernel
      have hl : raw34830step1Labels = raw34830step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34830step0 raw34830step0Labels permutation123 permutation2
    _ = mixedMoment B node5232 node5232Labels := by rfl

def raw34831 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw34831Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw34831step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34831step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34831step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34831step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34831step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34831step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34831step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34831 raw34831Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw34831 raw34831Labels = mixedMoment B raw34831step0 raw34831step0Labels := by
      have hz : ∀ j, raw34831 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34831step0 = (fun i j => raw34831 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34831step0 raw34831; decide +kernel
      have hl : raw34831step0Labels = raw34831Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34831 raw34831Labels permutation434 hz
    mixedMoment B raw34831step0 raw34831step0Labels = mixedMoment B raw34831step1 raw34831step1Labels := by
      have ha : raw34831step1 = (fun i j => raw34831step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34831step1 raw34831step0; decide +kernel
      have hl : raw34831step1Labels = raw34831step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34831step0 raw34831step0Labels permutation126 permutation7
    mixedMoment B raw34831step1 raw34831step1Labels = mixedMoment B raw34831step2 raw34831step2Labels := by
      have ha : raw34831step2 = -raw34831step1 := by apply Matrix.ext; change ∀ i j, raw34831step2 i j = -(raw34831step1 i j); unfold raw34831step2 raw34831step1; decide +kernel
      have hl : raw34831step2Labels = raw34831step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34831step2 raw34831step2Labels = mixedMoment B raw34831step3 raw34831step3Labels := by
      have ha : raw34831step3 = raw34831step2 := by apply Matrix.ext; unfold raw34831step3 raw34831step2; decide +kernel
      have hl : raw34831step2Labels = labelEmbedding10 ∘ raw34831step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34831step2 raw34831step2Labels raw34831step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

def raw34832 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34832Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34832step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34832step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34832step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw34832step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34832step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34832step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34832step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34832step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34832 raw34832Labels = mixedMoment B node5232 node5232Labels := by
  calc
    mixedMoment B raw34832 raw34832Labels = mixedMoment B raw34832step0 raw34832step0Labels := by
      have hz : ∀ j, raw34832 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34832step0 = (fun i j => raw34832 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34832step0 raw34832; decide +kernel
      have hl : raw34832step0Labels = raw34832Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34832 raw34832Labels permutation346 hz
    mixedMoment B raw34832step0 raw34832step0Labels = mixedMoment B raw34832step1 raw34832step1Labels := by
      have ha : raw34832step1 = (fun i j => raw34832step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34832step1 raw34832step0; decide +kernel
      have hl : raw34832step1Labels = raw34832step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34832step0 raw34832step0Labels permutation34 permutation4
    mixedMoment B raw34832step1 raw34832step1Labels = mixedMoment B raw34832step2 raw34832step2Labels := by
      have ha : raw34832step2 = -raw34832step1 := by apply Matrix.ext; change ∀ i j, raw34832step2 i j = -(raw34832step1 i j); unfold raw34832step2 raw34832step1; decide +kernel
      have hl : raw34832step2Labels = raw34832step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34832step2 raw34832step2Labels = mixedMoment B raw34832step3 raw34832step3Labels := by
      have ha : raw34832step3 = raw34832step2 := by apply Matrix.ext; unfold raw34832step3 raw34832step2; decide +kernel
      have hl : raw34832step2Labels = labelEmbedding7 ∘ raw34832step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34832step2 raw34832step2Labels raw34832step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5232 node5232Labels := by rfl

def raw34833 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34833Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34833step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34833step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34833step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34833step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34833step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34833 raw34833Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw34833 raw34833Labels = mixedMoment B raw34833step0 raw34833step0Labels := by
      have hz : ∀ j, raw34833 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34833step0 = (fun i j => raw34833 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34833step0 raw34833; decide +kernel
      have hl : raw34833step0Labels = raw34833Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34833 raw34833Labels permutation346 hz
    mixedMoment B raw34833step0 raw34833step0Labels = mixedMoment B raw34833step1 raw34833step1Labels := by
      have ha : raw34833step1 = (fun i j => raw34833step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34833step1 raw34833step0; decide +kernel
      have hl : raw34833step1Labels = raw34833step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34833step0 raw34833step0Labels permutation32 permutation6
    mixedMoment B raw34833step1 raw34833step1Labels = mixedMoment B raw34833step2 raw34833step2Labels := by
      have ha : raw34833step2 = raw34833step1 := by apply Matrix.ext; unfold raw34833step2 raw34833step1; decide +kernel
      have hl : raw34833step1Labels = labelEmbedding9 ∘ raw34833step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34833step1 raw34833step1Labels raw34833step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

def raw34834 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 1, 0], ![1, -1, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34834Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34834step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34834step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34834step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34834step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34834 raw34834Labels = mixedMoment B node5376 node5376Labels := by
  calc
    mixedMoment B raw34834 raw34834Labels = mixedMoment B raw34834step0 raw34834step0Labels := by
      have ha : raw34834step0 = (fun i j => raw34834 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34834step0 raw34834; decide +kernel
      have hl : raw34834step0Labels = raw34834Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34834 raw34834Labels permutation152 permutation6
    mixedMoment B raw34834step0 raw34834step0Labels = mixedMoment B raw34834step1 raw34834step1Labels := by
      have ha : raw34834step1 = raw34834step0 := by apply Matrix.ext; unfold raw34834step1 raw34834step0; decide +kernel
      have hl : raw34834step0Labels = labelEmbedding9 ∘ raw34834step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34834step0 raw34834step0Labels raw34834step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5376 node5376Labels := by rfl

def raw34835 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw34835Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![-3, 1, 2], ![0, -2, 2]]
def raw34835step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34835step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34835step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34835 raw34835Labels = mixedMoment B node5232 node5232Labels := by
  calc
    mixedMoment B raw34835 raw34835Labels = mixedMoment B raw34835step0 raw34835step0Labels := by
      have hz : ∀ j, raw34835 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34835step0 = (fun i j => raw34835 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34835step0 raw34835; decide +kernel
      have hl : raw34835step0Labels = raw34835Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34835 raw34835Labels permutation346 hz
    mixedMoment B raw34835step0 raw34835step0Labels = mixedMoment B raw34835step1 raw34835step1Labels := by
      have ha : raw34835step1 = (fun i j => raw34835step0 (permutation123 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34835step1 raw34835step0; decide +kernel
      have hl : raw34835step1Labels = raw34835step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34835step0 raw34835step0Labels permutation123 permutation2
    _ = mixedMoment B node5232 node5232Labels := by rfl

def raw34836 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw34836Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34836step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw34836step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34836step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34836step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34836step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34836step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34836step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34836step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34836 raw34836Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw34836 raw34836Labels = mixedMoment B raw34836step0 raw34836step0Labels := by
      have hz : ∀ j, raw34836 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34836step0 = (fun i j => raw34836 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34836step0 raw34836; decide +kernel
      have hl : raw34836step0Labels = raw34836Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34836 raw34836Labels permutation346 hz
    mixedMoment B raw34836step0 raw34836step0Labels = mixedMoment B raw34836step1 raw34836step1Labels := by
      have ha : raw34836step1 = (fun i j => raw34836step0 (permutation126 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34836step1 raw34836step0; decide +kernel
      have hl : raw34836step1Labels = raw34836step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34836step0 raw34836step0Labels permutation126 permutation7
    mixedMoment B raw34836step1 raw34836step1Labels = mixedMoment B raw34836step2 raw34836step2Labels := by
      have ha : raw34836step2 = -raw34836step1 := by apply Matrix.ext; change ∀ i j, raw34836step2 i j = -(raw34836step1 i j); unfold raw34836step2 raw34836step1; decide +kernel
      have hl : raw34836step2Labels = raw34836step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34836step2 raw34836step2Labels = mixedMoment B raw34836step3 raw34836step3Labels := by
      have ha : raw34836step3 = raw34836step2 := by apply Matrix.ext; unfold raw34836step3 raw34836step2; decide +kernel
      have hl : raw34836step2Labels = labelEmbedding10 ∘ raw34836step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34836step2 raw34836step2Labels raw34836step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

def raw34837 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw34837Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34837step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw34837step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34837step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![-1, -1, 2], ![0, -2, 2]]
def raw34837step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34837step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw34837step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34837step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw34837step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34837step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw34837step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34837 raw34837Labels = mixedMoment B node5238 node5238Labels := by
  calc
    mixedMoment B raw34837 raw34837Labels = mixedMoment B raw34837step0 raw34837step0Labels := by
      have hz : ∀ j, raw34837 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34837step0 = (fun i j => raw34837 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34837step0 raw34837; decide +kernel
      have hl : raw34837step0Labels = raw34837Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34837 raw34837Labels permutation434 hz
    mixedMoment B raw34837step0 raw34837step0Labels = mixedMoment B raw34837step1 raw34837step1Labels := by
      have hz : ∀ j, raw34837step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34837step1 = (fun i j => raw34837step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34837step1 raw34837step0; decide +kernel
      have hl : raw34837step1Labels = raw34837step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34837step0 raw34837step0Labels permutation80 hz
    mixedMoment B raw34837step1 raw34837step1Labels = mixedMoment B raw34837step2 raw34837step2Labels := by
      have ha : raw34837step2 = (fun i j => raw34837step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34837step2 raw34837step1; decide +kernel
      have hl : raw34837step2Labels = raw34837step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34837step1 raw34837step1Labels permutation8 permutation4
    mixedMoment B raw34837step2 raw34837step2Labels = mixedMoment B raw34837step3 raw34837step3Labels := by
      have ha : raw34837step3 = -raw34837step2 := by apply Matrix.ext; change ∀ i j, raw34837step3 i j = -(raw34837step2 i j); unfold raw34837step3 raw34837step2; decide +kernel
      have hl : raw34837step3Labels = raw34837step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34837step3 raw34837step3Labels = mixedMoment B raw34837step4 raw34837step4Labels := by
      have ha : raw34837step4 = raw34837step3 := by apply Matrix.ext; unfold raw34837step4 raw34837step3; decide +kernel
      have hl : raw34837step3Labels = labelEmbedding7 ∘ raw34837step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34837step3 raw34837step3Labels raw34837step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5238 node5238Labels := by rfl

def raw34838 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw34838Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34838step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw34838step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34838step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![-1, -1, 2], ![0, -2, 2]]
def raw34838step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34838step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw34838step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34838step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw34838step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34838 raw34838Labels = mixedMoment B node5371 node5371Labels := by
  calc
    mixedMoment B raw34838 raw34838Labels = mixedMoment B raw34838step0 raw34838step0Labels := by
      have hz : ∀ j, raw34838 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34838step0 = (fun i j => raw34838 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34838step0 raw34838; decide +kernel
      have hl : raw34838step0Labels = raw34838Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34838 raw34838Labels permutation434 hz
    mixedMoment B raw34838step0 raw34838step0Labels = mixedMoment B raw34838step1 raw34838step1Labels := by
      have hz : ∀ j, raw34838step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34838step1 = (fun i j => raw34838step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34838step1 raw34838step0; decide +kernel
      have hl : raw34838step1Labels = raw34838step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34838step0 raw34838step0Labels permutation80 hz
    mixedMoment B raw34838step1 raw34838step1Labels = mixedMoment B raw34838step2 raw34838step2Labels := by
      have ha : raw34838step2 = (fun i j => raw34838step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34838step2 raw34838step1; decide +kernel
      have hl : raw34838step2Labels = raw34838step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34838step1 raw34838step1Labels permutation8 permutation6
    mixedMoment B raw34838step2 raw34838step2Labels = mixedMoment B raw34838step3 raw34838step3Labels := by
      have ha : raw34838step3 = raw34838step2 := by apply Matrix.ext; unfold raw34838step3 raw34838step2; decide +kernel
      have hl : raw34838step2Labels = labelEmbedding9 ∘ raw34838step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34838step2 raw34838step2Labels raw34838step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5371 node5371Labels := by rfl

def raw34839 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw34839Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34839step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw34839step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34839step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34839step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34839step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34839step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34839step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34839step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34839 raw34839Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw34839 raw34839Labels = mixedMoment B raw34839step0 raw34839step0Labels := by
      have hz : ∀ j, raw34839 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34839step0 = (fun i j => raw34839 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34839step0 raw34839; decide +kernel
      have hl : raw34839step0Labels = raw34839Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34839 raw34839Labels permutation434 hz
    mixedMoment B raw34839step0 raw34839step0Labels = mixedMoment B raw34839step1 raw34839step1Labels := by
      have ha : raw34839step1 = (fun i j => raw34839step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34839step1 raw34839step0; decide +kernel
      have hl : raw34839step1Labels = raw34839step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34839step0 raw34839step0Labels permutation151 permutation6
    mixedMoment B raw34839step1 raw34839step1Labels = mixedMoment B raw34839step2 raw34839step2Labels := by
      have ha : raw34839step2 = -raw34839step1 := by apply Matrix.ext; change ∀ i j, raw34839step2 i j = -(raw34839step1 i j); unfold raw34839step2 raw34839step1; decide +kernel
      have hl : raw34839step2Labels = raw34839step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34839step2 raw34839step2Labels = mixedMoment B raw34839step3 raw34839step3Labels := by
      have ha : raw34839step3 = raw34839step2 := by apply Matrix.ext; unfold raw34839step3 raw34839step2; decide +kernel
      have hl : raw34839step2Labels = labelEmbedding9 ∘ raw34839step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34839step2 raw34839step2Labels raw34839step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

def raw34840 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw34840Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34840step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw34840step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34840step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34840step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34840step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34840step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34840step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34840step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34840 raw34840Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw34840 raw34840Labels = mixedMoment B raw34840step0 raw34840step0Labels := by
      have hz : ∀ j, raw34840 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34840step0 = (fun i j => raw34840 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34840step0 raw34840; decide +kernel
      have hl : raw34840step0Labels = raw34840Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34840 raw34840Labels permutation346 hz
    mixedMoment B raw34840step0 raw34840step0Labels = mixedMoment B raw34840step1 raw34840step1Labels := by
      have ha : raw34840step1 = (fun i j => raw34840step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34840step1 raw34840step0; decide +kernel
      have hl : raw34840step1Labels = raw34840step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34840step0 raw34840step0Labels permutation151 permutation6
    mixedMoment B raw34840step1 raw34840step1Labels = mixedMoment B raw34840step2 raw34840step2Labels := by
      have ha : raw34840step2 = -raw34840step1 := by apply Matrix.ext; change ∀ i j, raw34840step2 i j = -(raw34840step1 i j); unfold raw34840step2 raw34840step1; decide +kernel
      have hl : raw34840step2Labels = raw34840step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34840step2 raw34840step2Labels = mixedMoment B raw34840step3 raw34840step3Labels := by
      have ha : raw34840step3 = raw34840step2 := by apply Matrix.ext; unfold raw34840step3 raw34840step2; decide +kernel
      have hl : raw34840step2Labels = labelEmbedding9 ∘ raw34840step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34840step2 raw34840step2Labels raw34840step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

def raw34841 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34841Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34841step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34841step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, -1, 2], ![-1, -1, 2]]
def raw34841step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34841step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34841step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34841step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34841step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34841 raw34841Labels = mixedMoment B node5390 node5390Labels := by
  calc
    mixedMoment B raw34841 raw34841Labels = mixedMoment B raw34841step0 raw34841step0Labels := by
      have hz : ∀ j, raw34841 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34841step0 = (fun i j => raw34841 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34841step0 raw34841; decide +kernel
      have hl : raw34841step0Labels = raw34841Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34841 raw34841Labels permutation434 hz
    mixedMoment B raw34841step0 raw34841step0Labels = mixedMoment B raw34841step1 raw34841step1Labels := by
      have hz : ∀ j, raw34841step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34841step1 = (fun i j => raw34841step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34841step1 raw34841step0; decide +kernel
      have hl : raw34841step1Labels = raw34841step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34841step0 raw34841step0Labels permutation80 hz
    mixedMoment B raw34841step1 raw34841step1Labels = mixedMoment B raw34841step2 raw34841step2Labels := by
      have ha : raw34841step2 = (fun i j => raw34841step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34841step2 raw34841step1; decide +kernel
      have hl : raw34841step2Labels = raw34841step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34841step1 raw34841step1Labels permutation8 permutation6
    mixedMoment B raw34841step2 raw34841step2Labels = mixedMoment B raw34841step3 raw34841step3Labels := by
      have ha : raw34841step3 = raw34841step2 := by apply Matrix.ext; unfold raw34841step3 raw34841step2; decide +kernel
      have hl : raw34841step2Labels = labelEmbedding9 ∘ raw34841step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34841step2 raw34841step2Labels raw34841step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5390 node5390Labels := by rfl

def raw34842 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw34842Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34842step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw34842step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34842step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![-2, 0, 2], ![1, -3, 2]]
def raw34842step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34842step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw34842step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34842step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw34842step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34842 raw34842Labels = mixedMoment B node5235 node5235Labels := by
  calc
    mixedMoment B raw34842 raw34842Labels = mixedMoment B raw34842step0 raw34842step0Labels := by
      have hz : ∀ j, raw34842 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34842step0 = (fun i j => raw34842 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34842step0 raw34842; decide +kernel
      have hl : raw34842step0Labels = raw34842Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34842 raw34842Labels permutation434 hz
    mixedMoment B raw34842step0 raw34842step0Labels = mixedMoment B raw34842step1 raw34842step1Labels := by
      have hz : ∀ j, raw34842step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34842step1 = (fun i j => raw34842step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34842step1 raw34842step0; decide +kernel
      have hl : raw34842step1Labels = raw34842step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34842step0 raw34842step0Labels permutation80 hz
    mixedMoment B raw34842step1 raw34842step1Labels = mixedMoment B raw34842step2 raw34842step2Labels := by
      have ha : raw34842step2 = (fun i j => raw34842step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34842step2 raw34842step1; decide +kernel
      have hl : raw34842step2Labels = raw34842step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34842step1 raw34842step1Labels permutation31 permutation4
    mixedMoment B raw34842step2 raw34842step2Labels = mixedMoment B raw34842step3 raw34842step3Labels := by
      have ha : raw34842step3 = raw34842step2 := by apply Matrix.ext; unfold raw34842step3 raw34842step2; decide +kernel
      have hl : raw34842step2Labels = labelEmbedding7 ∘ raw34842step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34842step2 raw34842step2Labels raw34842step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5235 node5235Labels := by rfl

def raw34843 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw34843Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34843step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw34843step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34843step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![-2, 0, 2], ![1, -3, 2]]
def raw34843step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34843step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw34843step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34843step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw34843step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34843 raw34843Labels = mixedMoment B node5238 node5238Labels := by
  calc
    mixedMoment B raw34843 raw34843Labels = mixedMoment B raw34843step0 raw34843step0Labels := by
      have hz : ∀ j, raw34843 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34843step0 = (fun i j => raw34843 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34843step0 raw34843; decide +kernel
      have hl : raw34843step0Labels = raw34843Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34843 raw34843Labels permutation434 hz
    mixedMoment B raw34843step0 raw34843step0Labels = mixedMoment B raw34843step1 raw34843step1Labels := by
      have hz : ∀ j, raw34843step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34843step1 = (fun i j => raw34843step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34843step1 raw34843step0; decide +kernel
      have hl : raw34843step1Labels = raw34843step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34843step0 raw34843step0Labels permutation80 hz
    mixedMoment B raw34843step1 raw34843step1Labels = mixedMoment B raw34843step2 raw34843step2Labels := by
      have ha : raw34843step2 = (fun i j => raw34843step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34843step2 raw34843step1; decide +kernel
      have hl : raw34843step2Labels = raw34843step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34843step1 raw34843step1Labels permutation31 permutation4
    mixedMoment B raw34843step2 raw34843step2Labels = mixedMoment B raw34843step3 raw34843step3Labels := by
      have ha : raw34843step3 = raw34843step2 := by apply Matrix.ext; unfold raw34843step3 raw34843step2; decide +kernel
      have hl : raw34843step2Labels = labelEmbedding7 ∘ raw34843step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34843step2 raw34843step2Labels raw34843step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5238 node5238Labels := by rfl

def raw34844 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 1, 0], ![0, 0, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw34844Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34844step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw34844step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34844step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34844step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34844step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34844step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34844 raw34844Labels = mixedMoment B node5232 node5232Labels := by
  calc
    mixedMoment B raw34844 raw34844Labels = mixedMoment B raw34844step0 raw34844step0Labels := by
      have hz : ∀ j, raw34844 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34844step0 = (fun i j => raw34844 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34844step0 raw34844; decide +kernel
      have hl : raw34844step0Labels = raw34844Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34844 raw34844Labels permutation434 hz
    mixedMoment B raw34844step0 raw34844step0Labels = mixedMoment B raw34844step1 raw34844step1Labels := by
      have ha : raw34844step1 = (fun i j => raw34844step0 (permutation149 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34844step1 raw34844step0; decide +kernel
      have hl : raw34844step1Labels = raw34844step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34844step0 raw34844step0Labels permutation149 permutation4
    mixedMoment B raw34844step1 raw34844step1Labels = mixedMoment B raw34844step2 raw34844step2Labels := by
      have ha : raw34844step2 = raw34844step1 := by apply Matrix.ext; unfold raw34844step2 raw34844step1; decide +kernel
      have hl : raw34844step1Labels = labelEmbedding7 ∘ raw34844step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34844step1 raw34844step1Labels raw34844step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5232 node5232Labels := by rfl

def raw34845 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw34845Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34845step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 1, 0], ![-2, 0, 2], ![1, -3, 2]]
def raw34845step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34845step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34845step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34845step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw34845step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34845 raw34845Labels = mixedMoment B node5232 node5232Labels := by
  calc
    mixedMoment B raw34845 raw34845Labels = mixedMoment B raw34845step0 raw34845step0Labels := by
      have hz : ∀ j, raw34845 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34845step0 = (fun i j => raw34845 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34845step0 raw34845; decide +kernel
      have hl : raw34845step0Labels = raw34845Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34845 raw34845Labels permutation346 hz
    mixedMoment B raw34845step0 raw34845step0Labels = mixedMoment B raw34845step1 raw34845step1Labels := by
      have ha : raw34845step1 = (fun i j => raw34845step0 (permutation149 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34845step1 raw34845step0; decide +kernel
      have hl : raw34845step1Labels = raw34845step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34845step0 raw34845step0Labels permutation149 permutation4
    mixedMoment B raw34845step1 raw34845step1Labels = mixedMoment B raw34845step2 raw34845step2Labels := by
      have ha : raw34845step2 = raw34845step1 := by apply Matrix.ext; unfold raw34845step2 raw34845step1; decide +kernel
      have hl : raw34845step1Labels = labelEmbedding7 ∘ raw34845step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34845step1 raw34845step1Labels raw34845step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5232 node5232Labels := by rfl

def raw34846 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw34846Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34846step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![-3, 1, 2], ![1, -3, 2]]
def raw34846step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34846step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-3, 1, 2], ![1, -3, 2]]
def raw34846step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34846step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw34846step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34846 raw34846Labels = mixedMoment B node5297 node5297Labels := by
  calc
    mixedMoment B raw34846 raw34846Labels = mixedMoment B raw34846step0 raw34846step0Labels := by
      have hz : ∀ j, raw34846 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34846step0 = (fun i j => raw34846 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34846step0 raw34846; decide +kernel
      have hl : raw34846step0Labels = raw34846Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34846 raw34846Labels permutation434 hz
    mixedMoment B raw34846step0 raw34846step0Labels = mixedMoment B raw34846step1 raw34846step1Labels := by
      have hz : ∀ j, raw34846step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34846step1 = (fun i j => raw34846step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34846step1 raw34846step0; decide +kernel
      have hl : raw34846step1Labels = raw34846step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34846step0 raw34846step0Labels permutation80 hz
    mixedMoment B raw34846step1 raw34846step1Labels = mixedMoment B raw34846step2 raw34846step2Labels := by
      have ha : raw34846step2 = (fun i j => raw34846step1 (permutation21 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34846step2 raw34846step1; decide +kernel
      have hl : raw34846step2Labels = raw34846step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34846step1 raw34846step1Labels permutation21 permutation2
    _ = mixedMoment B node5297 node5297Labels := by rfl

def raw34847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34847Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34847step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34847step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34847step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34847step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34847step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34847step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34847step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34847step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34847 raw34847Labels = mixedMoment B node4875 node4875Labels := by
  calc
    mixedMoment B raw34847 raw34847Labels = mixedMoment B raw34847step0 raw34847step0Labels := by
      have hz : ∀ j, raw34847 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34847step0 = (fun i j => raw34847 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34847step0 raw34847; decide +kernel
      have hl : raw34847step0Labels = raw34847Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34847 raw34847Labels permutation434 hz
    mixedMoment B raw34847step0 raw34847step0Labels = mixedMoment B raw34847step1 raw34847step1Labels := by
      have hz : ∀ j, raw34847step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34847step1 = (fun i j => raw34847step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34847step1 raw34847step0; decide +kernel
      have hl : raw34847step1Labels = raw34847step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34847step0 raw34847step0Labels permutation80 hz
    mixedMoment B raw34847step1 raw34847step1Labels = mixedMoment B raw34847step2 raw34847step2Labels := by
      have ha : raw34847step2 = (fun i j => raw34847step1 (permutation14 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34847step2 raw34847step1; decide +kernel
      have hl : raw34847step2Labels = raw34847step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34847step1 raw34847step1Labels permutation14 permutation3
    mixedMoment B raw34847step2 raw34847step2Labels = mixedMoment B raw34847step3 raw34847step3Labels := by
      have ha : raw34847step3 = raw34847step2 := by apply Matrix.ext; unfold raw34847step3 raw34847step2; decide +kernel
      have hl : raw34847step2Labels = labelEmbedding6 ∘ raw34847step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34847step2 raw34847step2Labels raw34847step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4875 node4875Labels := by rfl

def raw34848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34848Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34848step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34848step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34848step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34848step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34848step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34848step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34848 raw34848Labels = mixedMoment B node5404 node5404Labels := by
  calc
    mixedMoment B raw34848 raw34848Labels = mixedMoment B raw34848step0 raw34848step0Labels := by
      have hz : ∀ j, raw34848 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34848step0 = (fun i j => raw34848 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34848step0 raw34848; decide +kernel
      have hl : raw34848step0Labels = raw34848Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34848 raw34848Labels permutation434 hz
    mixedMoment B raw34848step0 raw34848step0Labels = mixedMoment B raw34848step1 raw34848step1Labels := by
      have ha : raw34848step1 = (fun i j => raw34848step0 (permutation62 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34848step1 raw34848step0; decide +kernel
      have hl : raw34848step1Labels = raw34848step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34848step0 raw34848step0Labels permutation62 permutation3
    mixedMoment B raw34848step1 raw34848step1Labels = mixedMoment B raw34848step2 raw34848step2Labels := by
      have ha : raw34848step2 = raw34848step1 := by apply Matrix.ext; unfold raw34848step2 raw34848step1; decide +kernel
      have hl : raw34848step1Labels = labelEmbedding6 ∘ raw34848step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34848step1 raw34848step1Labels raw34848step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5404 node5404Labels := by rfl

def raw34849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34849Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34849step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34849step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34849step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34849step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34849step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34849step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34849 raw34849Labels = mixedMoment B node5404 node5404Labels := by
  calc
    mixedMoment B raw34849 raw34849Labels = mixedMoment B raw34849step0 raw34849step0Labels := by
      have hz : ∀ j, raw34849 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34849step0 = (fun i j => raw34849 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34849step0 raw34849; decide +kernel
      have hl : raw34849step0Labels = raw34849Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34849 raw34849Labels permutation346 hz
    mixedMoment B raw34849step0 raw34849step0Labels = mixedMoment B raw34849step1 raw34849step1Labels := by
      have ha : raw34849step1 = (fun i j => raw34849step0 (permutation62 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34849step1 raw34849step0; decide +kernel
      have hl : raw34849step1Labels = raw34849step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34849step0 raw34849step0Labels permutation62 permutation3
    mixedMoment B raw34849step1 raw34849step1Labels = mixedMoment B raw34849step2 raw34849step2Labels := by
      have ha : raw34849step2 = raw34849step1 := by apply Matrix.ext; unfold raw34849step2 raw34849step1; decide +kernel
      have hl : raw34849step1Labels = labelEmbedding6 ∘ raw34849step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34849step1 raw34849step1Labels raw34849step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5404 node5404Labels := by rfl

def raw34850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34850Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34850step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34850step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34850step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34850step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34850step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw34850step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34850step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw34850step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34850 raw34850Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw34850 raw34850Labels = mixedMoment B raw34850step0 raw34850step0Labels := by
      have hz : ∀ j, raw34850 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34850step0 = (fun i j => raw34850 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34850step0 raw34850; decide +kernel
      have hl : raw34850step0Labels = raw34850Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34850 raw34850Labels permutation434 hz
    mixedMoment B raw34850step0 raw34850step0Labels = mixedMoment B raw34850step1 raw34850step1Labels := by
      have hz : ∀ j, raw34850step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34850step1 = (fun i j => raw34850step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34850step1 raw34850step0; decide +kernel
      have hl : raw34850step1Labels = raw34850step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34850step0 raw34850step0Labels permutation80 hz
    mixedMoment B raw34850step1 raw34850step1Labels = mixedMoment B raw34850step2 raw34850step2Labels := by
      have ha : raw34850step2 = (fun i j => raw34850step1 (permutation14 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34850step2 raw34850step1; decide +kernel
      have hl : raw34850step2Labels = raw34850step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34850step1 raw34850step1Labels permutation14 permutation3
    mixedMoment B raw34850step2 raw34850step2Labels = mixedMoment B raw34850step3 raw34850step3Labels := by
      have ha : raw34850step3 = raw34850step2 := by apply Matrix.ext; unfold raw34850step3 raw34850step2; decide +kernel
      have hl : raw34850step2Labels = labelEmbedding6 ∘ raw34850step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34850step2 raw34850step2Labels raw34850step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5451 node5451Labels := by rfl

def raw34851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw34851Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34851step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw34851step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34851step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![2, -1, -1], ![1, 0, -1]]
def raw34851step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34851step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw34851step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34851step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw34851step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34851 raw34851Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw34851 raw34851Labels = mixedMoment B raw34851step0 raw34851step0Labels := by
      have hz : ∀ j, raw34851 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34851step0 = (fun i j => raw34851 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34851step0 raw34851; decide +kernel
      have hl : raw34851step0Labels = raw34851Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34851 raw34851Labels permutation434 hz
    mixedMoment B raw34851step0 raw34851step0Labels = mixedMoment B raw34851step1 raw34851step1Labels := by
      have hz : ∀ j, raw34851step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34851step1 = (fun i j => raw34851step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34851step1 raw34851step0; decide +kernel
      have hl : raw34851step1Labels = raw34851step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34851step0 raw34851step0Labels permutation80 hz
    mixedMoment B raw34851step1 raw34851step1Labels = mixedMoment B raw34851step2 raw34851step2Labels := by
      have ha : raw34851step2 = (fun i j => raw34851step1 (permutation15 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34851step2 raw34851step1; decide +kernel
      have hl : raw34851step2Labels = raw34851step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34851step1 raw34851step1Labels permutation15 permutation3
    mixedMoment B raw34851step2 raw34851step2Labels = mixedMoment B raw34851step3 raw34851step3Labels := by
      have ha : raw34851step3 = raw34851step2 := by apply Matrix.ext; unfold raw34851step3 raw34851step2; decide +kernel
      have hl : raw34851step2Labels = labelEmbedding6 ∘ raw34851step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34851step2 raw34851step2Labels raw34851step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5451 node5451Labels := by rfl

def raw34852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34852Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34852step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34852step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34852step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34852step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34852step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34852step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34852 raw34852Labels = mixedMoment B node4689 node4689Labels := by
  calc
    mixedMoment B raw34852 raw34852Labels = mixedMoment B raw34852step0 raw34852step0Labels := by
      have hz : ∀ j, raw34852 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34852step0 = (fun i j => raw34852 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34852step0 raw34852; decide +kernel
      have hl : raw34852step0Labels = raw34852Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34852 raw34852Labels permutation434 hz
    mixedMoment B raw34852step0 raw34852step0Labels = mixedMoment B raw34852step1 raw34852step1Labels := by
      have ha : raw34852step1 = (fun i j => raw34852step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34852step1 raw34852step0; decide +kernel
      have hl : raw34852step1Labels = raw34852step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34852step0 raw34852step0Labels permutation56 permutation3
    mixedMoment B raw34852step1 raw34852step1Labels = mixedMoment B raw34852step2 raw34852step2Labels := by
      have ha : raw34852step2 = raw34852step1 := by apply Matrix.ext; unfold raw34852step2 raw34852step1; decide +kernel
      have hl : raw34852step1Labels = labelEmbedding6 ∘ raw34852step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34852step1 raw34852step1Labels raw34852step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4689 node4689Labels := by rfl

def raw34853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34853Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34853step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34853step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34853step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34853step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34853 raw34853Labels = mixedMoment B node5373 node5373Labels := by
  calc
    mixedMoment B raw34853 raw34853Labels = mixedMoment B raw34853step0 raw34853step0Labels := by
      have ha : raw34853step0 = (fun i j => raw34853 (permutation271 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34853step0 raw34853; decide +kernel
      have hl : raw34853step0Labels = raw34853Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34853 raw34853Labels permutation271 permutation3
    mixedMoment B raw34853step0 raw34853step0Labels = mixedMoment B raw34853step1 raw34853step1Labels := by
      have ha : raw34853step1 = raw34853step0 := by apply Matrix.ext; unfold raw34853step1 raw34853step0; decide +kernel
      have hl : raw34853step0Labels = labelEmbedding6 ∘ raw34853step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34853step0 raw34853step0Labels raw34853step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5373 node5373Labels := by rfl

def raw34854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34854Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34854step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34854step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34854 raw34854Labels = mixedMoment B node5388 node5388Labels := by
  calc
    mixedMoment B raw34854 raw34854Labels = mixedMoment B raw34854step0 raw34854step0Labels := by
      have hz : ∀ j, raw34854 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34854step0 = (fun i j => raw34854 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34854step0 raw34854; decide +kernel
      have hl : raw34854step0Labels = raw34854Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34854 raw34854Labels permutation434 hz
    _ = mixedMoment B node5388 node5388Labels := by rfl

def raw34855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw34855Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34855step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw34855step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34855step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34855step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34855 raw34855Labels = mixedMoment B node5388 node5388Labels := by
  calc
    mixedMoment B raw34855 raw34855Labels = mixedMoment B raw34855step0 raw34855step0Labels := by
      have hz : ∀ j, raw34855 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34855step0 = (fun i j => raw34855 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34855step0 raw34855; decide +kernel
      have hl : raw34855step0Labels = raw34855Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34855 raw34855Labels permutation434 hz
    mixedMoment B raw34855step0 raw34855step0Labels = mixedMoment B raw34855step1 raw34855step1Labels := by
      have ha : raw34855step1 = (fun i j => raw34855step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34855step1 raw34855step0; decide +kernel
      have hl : raw34855step1Labels = raw34855step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34855step0 raw34855step0Labels permutation33 permutation2
    _ = mixedMoment B node5388 node5388Labels := by rfl

def raw34856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34856Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34856step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34856step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34856step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34856step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34856step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34856step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34856 raw34856Labels = mixedMoment B node4689 node4689Labels := by
  calc
    mixedMoment B raw34856 raw34856Labels = mixedMoment B raw34856step0 raw34856step0Labels := by
      have hz : ∀ j, raw34856 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34856step0 = (fun i j => raw34856 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34856step0 raw34856; decide +kernel
      have hl : raw34856step0Labels = raw34856Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34856 raw34856Labels permutation346 hz
    mixedMoment B raw34856step0 raw34856step0Labels = mixedMoment B raw34856step1 raw34856step1Labels := by
      have ha : raw34856step1 = (fun i j => raw34856step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34856step1 raw34856step0; decide +kernel
      have hl : raw34856step1Labels = raw34856step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34856step0 raw34856step0Labels permutation56 permutation3
    mixedMoment B raw34856step1 raw34856step1Labels = mixedMoment B raw34856step2 raw34856step2Labels := by
      have ha : raw34856step2 = raw34856step1 := by apply Matrix.ext; unfold raw34856step2 raw34856step1; decide +kernel
      have hl : raw34856step1Labels = labelEmbedding6 ∘ raw34856step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34856step1 raw34856step1Labels raw34856step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4689 node4689Labels := by rfl

def raw34857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34857Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34857step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34857step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34857step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34857step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34857 raw34857Labels = mixedMoment B node5373 node5373Labels := by
  calc
    mixedMoment B raw34857 raw34857Labels = mixedMoment B raw34857step0 raw34857step0Labels := by
      have ha : raw34857step0 = (fun i j => raw34857 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34857step0 raw34857; decide +kernel
      have hl : raw34857step0Labels = raw34857Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34857 raw34857Labels permutation265 permutation3
    mixedMoment B raw34857step0 raw34857step0Labels = mixedMoment B raw34857step1 raw34857step1Labels := by
      have ha : raw34857step1 = raw34857step0 := by apply Matrix.ext; unfold raw34857step1 raw34857step0; decide +kernel
      have hl : raw34857step0Labels = labelEmbedding6 ∘ raw34857step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34857step0 raw34857step0Labels raw34857step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5373 node5373Labels := by rfl

def raw34858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw34858Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34858step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw34858step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34858step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34858step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34858 raw34858Labels = mixedMoment B node5388 node5388Labels := by
  calc
    mixedMoment B raw34858 raw34858Labels = mixedMoment B raw34858step0 raw34858step0Labels := by
      have hz : ∀ j, raw34858 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34858step0 = (fun i j => raw34858 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34858step0 raw34858; decide +kernel
      have hl : raw34858step0Labels = raw34858Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34858 raw34858Labels permutation346 hz
    mixedMoment B raw34858step0 raw34858step0Labels = mixedMoment B raw34858step1 raw34858step1Labels := by
      have ha : raw34858step1 = (fun i j => raw34858step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34858step1 raw34858step0; decide +kernel
      have hl : raw34858step1Labels = raw34858step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34858step0 raw34858step0Labels permutation33 permutation2
    _ = mixedMoment B node5388 node5388Labels := by rfl

def raw34859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw34859Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34859step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw34859step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34859step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![3, -2, -1], ![2, -1, -1]]
def raw34859step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34859step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw34859step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34859step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw34859step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34859 raw34859Labels = mixedMoment B node4692 node4692Labels := by
  calc
    mixedMoment B raw34859 raw34859Labels = mixedMoment B raw34859step0 raw34859step0Labels := by
      have hz : ∀ j, raw34859 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34859step0 = (fun i j => raw34859 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34859step0 raw34859; decide +kernel
      have hl : raw34859step0Labels = raw34859Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34859 raw34859Labels permutation434 hz
    mixedMoment B raw34859step0 raw34859step0Labels = mixedMoment B raw34859step1 raw34859step1Labels := by
      have hz : ∀ j, raw34859step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34859step1 = (fun i j => raw34859step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34859step1 raw34859step0; decide +kernel
      have hl : raw34859step1Labels = raw34859step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34859step0 raw34859step0Labels permutation80 hz
    mixedMoment B raw34859step1 raw34859step1Labels = mixedMoment B raw34859step2 raw34859step2Labels := by
      have ha : raw34859step2 = (fun i j => raw34859step1 (permutation15 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34859step2 raw34859step1; decide +kernel
      have hl : raw34859step2Labels = raw34859step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34859step1 raw34859step1Labels permutation15 permutation3
    mixedMoment B raw34859step2 raw34859step2Labels = mixedMoment B raw34859step3 raw34859step3Labels := by
      have ha : raw34859step3 = raw34859step2 := by apply Matrix.ext; unfold raw34859step3 raw34859step2; decide +kernel
      have hl : raw34859step2Labels = labelEmbedding6 ∘ raw34859step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34859step2 raw34859step2Labels raw34859step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4692 node4692Labels := by rfl

def raw34860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw34860Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34860step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw34860step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34860step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34860step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34860step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34860step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34860step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34860step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34860 raw34860Labels = mixedMoment B node4949 node4949Labels := by
  calc
    mixedMoment B raw34860 raw34860Labels = mixedMoment B raw34860step0 raw34860step0Labels := by
      have hz : ∀ j, raw34860 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34860step0 = (fun i j => raw34860 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34860step0 raw34860; decide +kernel
      have hl : raw34860step0Labels = raw34860Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34860 raw34860Labels permutation434 hz
    mixedMoment B raw34860step0 raw34860step0Labels = mixedMoment B raw34860step1 raw34860step1Labels := by
      have ha : raw34860step1 = (fun i j => raw34860step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34860step1 raw34860step0; decide +kernel
      have hl : raw34860step1Labels = raw34860step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34860step0 raw34860step0Labels permutation126 permutation3
    mixedMoment B raw34860step1 raw34860step1Labels = mixedMoment B raw34860step2 raw34860step2Labels := by
      have ha : raw34860step2 = -raw34860step1 := by apply Matrix.ext; change ∀ i j, raw34860step2 i j = -(raw34860step1 i j); unfold raw34860step2 raw34860step1; decide +kernel
      have hl : raw34860step2Labels = raw34860step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34860step2 raw34860step2Labels = mixedMoment B raw34860step3 raw34860step3Labels := by
      have ha : raw34860step3 = raw34860step2 := by apply Matrix.ext; unfold raw34860step3 raw34860step2; decide +kernel
      have hl : raw34860step2Labels = labelEmbedding6 ∘ raw34860step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34860step2 raw34860step2Labels raw34860step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4949 node4949Labels := by rfl

def raw34861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw34861Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw34861step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34861step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34861step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34861step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34861step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34861step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34861step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34861 raw34861Labels = mixedMoment B node4949 node4949Labels := by
  calc
    mixedMoment B raw34861 raw34861Labels = mixedMoment B raw34861step0 raw34861step0Labels := by
      have hz : ∀ j, raw34861 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34861step0 = (fun i j => raw34861 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34861step0 raw34861; decide +kernel
      have hl : raw34861step0Labels = raw34861Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34861 raw34861Labels permutation346 hz
    mixedMoment B raw34861step0 raw34861step0Labels = mixedMoment B raw34861step1 raw34861step1Labels := by
      have ha : raw34861step1 = (fun i j => raw34861step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34861step1 raw34861step0; decide +kernel
      have hl : raw34861step1Labels = raw34861step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34861step0 raw34861step0Labels permutation126 permutation3
    mixedMoment B raw34861step1 raw34861step1Labels = mixedMoment B raw34861step2 raw34861step2Labels := by
      have ha : raw34861step2 = -raw34861step1 := by apply Matrix.ext; change ∀ i j, raw34861step2 i j = -(raw34861step1 i j); unfold raw34861step2 raw34861step1; decide +kernel
      have hl : raw34861step2Labels = raw34861step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34861step2 raw34861step2Labels = mixedMoment B raw34861step3 raw34861step3Labels := by
      have ha : raw34861step3 = raw34861step2 := by apply Matrix.ext; unfold raw34861step3 raw34861step2; decide +kernel
      have hl : raw34861step2Labels = labelEmbedding6 ∘ raw34861step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34861step2 raw34861step2Labels raw34861step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4949 node4949Labels := by rfl

def raw34862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw34862Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34862step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw34862step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34862step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![3, -2, -1], ![1, 0, -1]]
def raw34862step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34862step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw34862step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34862step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34862step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34862step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34862step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34862 raw34862Labels = mixedMoment B node5176 node5176Labels := by
  calc
    mixedMoment B raw34862 raw34862Labels = mixedMoment B raw34862step0 raw34862step0Labels := by
      have hz : ∀ j, raw34862 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34862step0 = (fun i j => raw34862 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34862step0 raw34862; decide +kernel
      have hl : raw34862step0Labels = raw34862Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34862 raw34862Labels permutation434 hz
    mixedMoment B raw34862step0 raw34862step0Labels = mixedMoment B raw34862step1 raw34862step1Labels := by
      have hz : ∀ j, raw34862step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34862step1 = (fun i j => raw34862step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34862step1 raw34862step0; decide +kernel
      have hl : raw34862step1Labels = raw34862step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34862step0 raw34862step0Labels permutation80 hz
    mixedMoment B raw34862step1 raw34862step1Labels = mixedMoment B raw34862step2 raw34862step2Labels := by
      have ha : raw34862step2 = (fun i j => raw34862step1 (permutation24 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34862step2 raw34862step1; decide +kernel
      have hl : raw34862step2Labels = raw34862step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34862step1 raw34862step1Labels permutation24 permutation3
    mixedMoment B raw34862step2 raw34862step2Labels = mixedMoment B raw34862step3 raw34862step3Labels := by
      have ha : raw34862step3 = -raw34862step2 := by apply Matrix.ext; change ∀ i j, raw34862step3 i j = -(raw34862step2 i j); unfold raw34862step3 raw34862step2; decide +kernel
      have hl : raw34862step3Labels = raw34862step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34862step3 raw34862step3Labels = mixedMoment B raw34862step4 raw34862step4Labels := by
      have ha : raw34862step4 = raw34862step3 := by apply Matrix.ext; unfold raw34862step4 raw34862step3; decide +kernel
      have hl : raw34862step3Labels = labelEmbedding6 ∘ raw34862step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34862step3 raw34862step3Labels raw34862step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5176 node5176Labels := by rfl

def raw34863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw34863Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34863step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw34863step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34863step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![2, -1, -1], ![3, -2, -1]]
def raw34863step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34863step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw34863step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34863step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw34863step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34863 raw34863Labels = mixedMoment B node4692 node4692Labels := by
  calc
    mixedMoment B raw34863 raw34863Labels = mixedMoment B raw34863step0 raw34863step0Labels := by
      have hz : ∀ j, raw34863 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34863step0 = (fun i j => raw34863 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34863step0 raw34863; decide +kernel
      have hl : raw34863step0Labels = raw34863Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34863 raw34863Labels permutation434 hz
    mixedMoment B raw34863step0 raw34863step0Labels = mixedMoment B raw34863step1 raw34863step1Labels := by
      have hz : ∀ j, raw34863step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34863step1 = (fun i j => raw34863step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34863step1 raw34863step0; decide +kernel
      have hl : raw34863step1Labels = raw34863step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34863step0 raw34863step0Labels permutation80 hz
    mixedMoment B raw34863step1 raw34863step1Labels = mixedMoment B raw34863step2 raw34863step2Labels := by
      have ha : raw34863step2 = (fun i j => raw34863step1 (permutation14 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34863step2 raw34863step1; decide +kernel
      have hl : raw34863step2Labels = raw34863step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34863step1 raw34863step1Labels permutation14 permutation3
    mixedMoment B raw34863step2 raw34863step2Labels = mixedMoment B raw34863step3 raw34863step3Labels := by
      have ha : raw34863step3 = raw34863step2 := by apply Matrix.ext; unfold raw34863step3 raw34863step2; decide +kernel
      have hl : raw34863step2Labels = labelEmbedding6 ∘ raw34863step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34863step2 raw34863step2Labels raw34863step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4692 node4692Labels := by rfl

def raw34864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw34864Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34864step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw34864step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34864step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34864step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34864step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34864step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34864step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34864step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34864 raw34864Labels = mixedMoment B node4949 node4949Labels := by
  calc
    mixedMoment B raw34864 raw34864Labels = mixedMoment B raw34864step0 raw34864step0Labels := by
      have hz : ∀ j, raw34864 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34864step0 = (fun i j => raw34864 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34864step0 raw34864; decide +kernel
      have hl : raw34864step0Labels = raw34864Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34864 raw34864Labels permutation434 hz
    mixedMoment B raw34864step0 raw34864step0Labels = mixedMoment B raw34864step1 raw34864step1Labels := by
      have ha : raw34864step1 = (fun i j => raw34864step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34864step1 raw34864step0; decide +kernel
      have hl : raw34864step1Labels = raw34864step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34864step0 raw34864step0Labels permutation150 permutation3
    mixedMoment B raw34864step1 raw34864step1Labels = mixedMoment B raw34864step2 raw34864step2Labels := by
      have ha : raw34864step2 = -raw34864step1 := by apply Matrix.ext; change ∀ i j, raw34864step2 i j = -(raw34864step1 i j); unfold raw34864step2 raw34864step1; decide +kernel
      have hl : raw34864step2Labels = raw34864step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34864step2 raw34864step2Labels = mixedMoment B raw34864step3 raw34864step3Labels := by
      have ha : raw34864step3 = raw34864step2 := by apply Matrix.ext; unfold raw34864step3 raw34864step2; decide +kernel
      have hl : raw34864step2Labels = labelEmbedding6 ∘ raw34864step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34864step2 raw34864step2Labels raw34864step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4949 node4949Labels := by rfl

def raw34865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw34865Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34865step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw34865step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34865step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34865step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34865step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34865step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34865step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34865step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34865 raw34865Labels = mixedMoment B node4949 node4949Labels := by
  calc
    mixedMoment B raw34865 raw34865Labels = mixedMoment B raw34865step0 raw34865step0Labels := by
      have hz : ∀ j, raw34865 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34865step0 = (fun i j => raw34865 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34865step0 raw34865; decide +kernel
      have hl : raw34865step0Labels = raw34865Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34865 raw34865Labels permutation346 hz
    mixedMoment B raw34865step0 raw34865step0Labels = mixedMoment B raw34865step1 raw34865step1Labels := by
      have ha : raw34865step1 = (fun i j => raw34865step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34865step1 raw34865step0; decide +kernel
      have hl : raw34865step1Labels = raw34865step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34865step0 raw34865step0Labels permutation150 permutation3
    mixedMoment B raw34865step1 raw34865step1Labels = mixedMoment B raw34865step2 raw34865step2Labels := by
      have ha : raw34865step2 = -raw34865step1 := by apply Matrix.ext; change ∀ i j, raw34865step2 i j = -(raw34865step1 i j); unfold raw34865step2 raw34865step1; decide +kernel
      have hl : raw34865step2Labels = raw34865step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34865step2 raw34865step2Labels = mixedMoment B raw34865step3 raw34865step3Labels := by
      have ha : raw34865step3 = raw34865step2 := by apply Matrix.ext; unfold raw34865step3 raw34865step2; decide +kernel
      have hl : raw34865step2Labels = labelEmbedding6 ∘ raw34865step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34865step2 raw34865step2Labels raw34865step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4949 node4949Labels := by rfl

def raw34866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34866Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34866step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34866step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34866step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34866step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34866step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34866step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34866 raw34866Labels = mixedMoment B node2116 node2116Labels := by
  calc
    mixedMoment B raw34866 raw34866Labels = mixedMoment B raw34866step0 raw34866step0Labels := by
      have hz : ∀ j, raw34866 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34866step0 = (fun i j => raw34866 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34866step0 raw34866; decide +kernel
      have hl : raw34866step0Labels = raw34866Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34866 raw34866Labels permutation434 hz
    mixedMoment B raw34866step0 raw34866step0Labels = mixedMoment B raw34866step1 raw34866step1Labels := by
      have hz : ∀ j, raw34866step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34866step1 = (fun i j => raw34866step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34866step1 raw34866step0; decide +kernel
      have hl : raw34866step1Labels = raw34866step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34866step0 raw34866step0Labels permutation80 hz
    mixedMoment B raw34866step1 raw34866step1Labels = mixedMoment B raw34866step2 raw34866step2Labels := by
      have ha : raw34866step2 = (fun i j => raw34866step1 (permutation14 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34866step2 raw34866step1; decide +kernel
      have hl : raw34866step2Labels = raw34866step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34866step1 raw34866step1Labels permutation14 permutation3
    _ = mixedMoment B node2116 node2116Labels := by rfl

def raw34867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34867Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34867step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34867step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34867step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34867step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34867 raw34867Labels = mixedMoment B node3790 node3790Labels := by
  calc
    mixedMoment B raw34867 raw34867Labels = mixedMoment B raw34867step0 raw34867step0Labels := by
      have hz : ∀ j, raw34867 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34867step0 = (fun i j => raw34867 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34867step0 raw34867; decide +kernel
      have hl : raw34867step0Labels = raw34867Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34867 raw34867Labels permutation434 hz
    mixedMoment B raw34867step0 raw34867step0Labels = mixedMoment B raw34867step1 raw34867step1Labels := by
      have ha : raw34867step1 = (fun i j => raw34867step0 (permutation62 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34867step1 raw34867step0; decide +kernel
      have hl : raw34867step1Labels = raw34867step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34867step0 raw34867step0Labels permutation62 permutation3
    _ = mixedMoment B node3790 node3790Labels := by rfl

def raw34868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34868Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34868step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34868step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34868step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34868step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34868 raw34868Labels = mixedMoment B node3790 node3790Labels := by
  calc
    mixedMoment B raw34868 raw34868Labels = mixedMoment B raw34868step0 raw34868step0Labels := by
      have hz : ∀ j, raw34868 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34868step0 = (fun i j => raw34868 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34868step0 raw34868; decide +kernel
      have hl : raw34868step0Labels = raw34868Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34868 raw34868Labels permutation346 hz
    mixedMoment B raw34868step0 raw34868step0Labels = mixedMoment B raw34868step1 raw34868step1Labels := by
      have ha : raw34868step1 = (fun i j => raw34868step0 (permutation62 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34868step1 raw34868step0; decide +kernel
      have hl : raw34868step1Labels = raw34868step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34868step0 raw34868step0Labels permutation62 permutation3
    _ = mixedMoment B node3790 node3790Labels := by rfl

def raw34869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34869Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34869step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34869step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34869step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34869step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34869step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw34869step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34869 raw34869Labels = mixedMoment B node3888 node3888Labels := by
  calc
    mixedMoment B raw34869 raw34869Labels = mixedMoment B raw34869step0 raw34869step0Labels := by
      have hz : ∀ j, raw34869 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34869step0 = (fun i j => raw34869 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34869step0 raw34869; decide +kernel
      have hl : raw34869step0Labels = raw34869Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34869 raw34869Labels permutation434 hz
    mixedMoment B raw34869step0 raw34869step0Labels = mixedMoment B raw34869step1 raw34869step1Labels := by
      have hz : ∀ j, raw34869step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34869step1 = (fun i j => raw34869step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34869step1 raw34869step0; decide +kernel
      have hl : raw34869step1Labels = raw34869step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34869step0 raw34869step0Labels permutation80 hz
    mixedMoment B raw34869step1 raw34869step1Labels = mixedMoment B raw34869step2 raw34869step2Labels := by
      have ha : raw34869step2 = (fun i j => raw34869step1 (permutation14 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34869step2 raw34869step1; decide +kernel
      have hl : raw34869step2Labels = raw34869step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34869step1 raw34869step1Labels permutation14 permutation3
    _ = mixedMoment B node3888 node3888Labels := by rfl

def raw34870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw34870Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34870step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw34870step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34870step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![2, -1, -1], ![1, 0, -1]]
def raw34870step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34870step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw34870step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34870 raw34870Labels = mixedMoment B node3888 node3888Labels := by
  calc
    mixedMoment B raw34870 raw34870Labels = mixedMoment B raw34870step0 raw34870step0Labels := by
      have hz : ∀ j, raw34870 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34870step0 = (fun i j => raw34870 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34870step0 raw34870; decide +kernel
      have hl : raw34870step0Labels = raw34870Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34870 raw34870Labels permutation434 hz
    mixedMoment B raw34870step0 raw34870step0Labels = mixedMoment B raw34870step1 raw34870step1Labels := by
      have hz : ∀ j, raw34870step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34870step1 = (fun i j => raw34870step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34870step1 raw34870step0; decide +kernel
      have hl : raw34870step1Labels = raw34870step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34870step0 raw34870step0Labels permutation80 hz
    mixedMoment B raw34870step1 raw34870step1Labels = mixedMoment B raw34870step2 raw34870step2Labels := by
      have ha : raw34870step2 = (fun i j => raw34870step1 (permutation15 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34870step2 raw34870step1; decide +kernel
      have hl : raw34870step2Labels = raw34870step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34870step1 raw34870step1Labels permutation15 permutation3
    _ = mixedMoment B node3888 node3888Labels := by rfl

def raw34871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34871Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34871step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34871step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34871step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34871step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34871 raw34871Labels = mixedMoment B node1815 node1815Labels := by
  calc
    mixedMoment B raw34871 raw34871Labels = mixedMoment B raw34871step0 raw34871step0Labels := by
      have hz : ∀ j, raw34871 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34871step0 = (fun i j => raw34871 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34871step0 raw34871; decide +kernel
      have hl : raw34871step0Labels = raw34871Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34871 raw34871Labels permutation434 hz
    mixedMoment B raw34871step0 raw34871step0Labels = mixedMoment B raw34871step1 raw34871step1Labels := by
      have ha : raw34871step1 = (fun i j => raw34871step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34871step1 raw34871step0; decide +kernel
      have hl : raw34871step1Labels = raw34871step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34871step0 raw34871step0Labels permutation56 permutation3
    _ = mixedMoment B node1815 node1815Labels := by rfl

def raw34872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34872Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34872step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34872step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34872 raw34872Labels = mixedMoment B node3709 node3709Labels := by
  calc
    mixedMoment B raw34872 raw34872Labels = mixedMoment B raw34872step0 raw34872step0Labels := by
      have ha : raw34872step0 = (fun i j => raw34872 (permutation271 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34872step0 raw34872; decide +kernel
      have hl : raw34872step0Labels = raw34872Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34872 raw34872Labels permutation271 permutation3
    _ = mixedMoment B node3709 node3709Labels := by rfl

def raw34873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34873Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34873step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34873step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34873step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34873step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34873 raw34873Labels = mixedMoment B node3737 node3737Labels := by
  calc
    mixedMoment B raw34873 raw34873Labels = mixedMoment B raw34873step0 raw34873step0Labels := by
      have hz : ∀ j, raw34873 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34873step0 = (fun i j => raw34873 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34873step0 raw34873; decide +kernel
      have hl : raw34873step0Labels = raw34873Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34873 raw34873Labels permutation434 hz
    mixedMoment B raw34873step0 raw34873step0Labels = mixedMoment B raw34873step1 raw34873step1Labels := by
      have ha : raw34873step1 = (fun i j => raw34873step0 (permutation58 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34873step1 raw34873step0; decide +kernel
      have hl : raw34873step1Labels = raw34873step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34873step0 raw34873step0Labels permutation58 permutation3
    _ = mixedMoment B node3737 node3737Labels := by rfl

def raw34874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw34874Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34874step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw34874step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34874step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34874step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34874 raw34874Labels = mixedMoment B node3737 node3737Labels := by
  calc
    mixedMoment B raw34874 raw34874Labels = mixedMoment B raw34874step0 raw34874step0Labels := by
      have hz : ∀ j, raw34874 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34874step0 = (fun i j => raw34874 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34874step0 raw34874; decide +kernel
      have hl : raw34874step0Labels = raw34874Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34874 raw34874Labels permutation434 hz
    mixedMoment B raw34874step0 raw34874step0Labels = mixedMoment B raw34874step1 raw34874step1Labels := by
      have ha : raw34874step1 = (fun i j => raw34874step0 (permutation60 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34874step1 raw34874step0; decide +kernel
      have hl : raw34874step1Labels = raw34874step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34874step0 raw34874step0Labels permutation60 permutation3
    _ = mixedMoment B node3737 node3737Labels := by rfl

def raw34875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34875Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34875step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34875step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34875step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34875step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34875 raw34875Labels = mixedMoment B node1815 node1815Labels := by
  calc
    mixedMoment B raw34875 raw34875Labels = mixedMoment B raw34875step0 raw34875step0Labels := by
      have hz : ∀ j, raw34875 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34875step0 = (fun i j => raw34875 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34875step0 raw34875; decide +kernel
      have hl : raw34875step0Labels = raw34875Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34875 raw34875Labels permutation346 hz
    mixedMoment B raw34875step0 raw34875step0Labels = mixedMoment B raw34875step1 raw34875step1Labels := by
      have ha : raw34875step1 = (fun i j => raw34875step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34875step1 raw34875step0; decide +kernel
      have hl : raw34875step1Labels = raw34875step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34875step0 raw34875step0Labels permutation56 permutation3
    _ = mixedMoment B node1815 node1815Labels := by rfl

def raw34876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw34876Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34876step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34876step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34876 raw34876Labels = mixedMoment B node3709 node3709Labels := by
  calc
    mixedMoment B raw34876 raw34876Labels = mixedMoment B raw34876step0 raw34876step0Labels := by
      have ha : raw34876step0 = (fun i j => raw34876 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34876step0 raw34876; decide +kernel
      have hl : raw34876step0Labels = raw34876Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34876 raw34876Labels permutation265 permutation3
    _ = mixedMoment B node3709 node3709Labels := by rfl

def raw34877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw34877Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34877step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw34877step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34877step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw34877step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34877 raw34877Labels = mixedMoment B node3737 node3737Labels := by
  calc
    mixedMoment B raw34877 raw34877Labels = mixedMoment B raw34877step0 raw34877step0Labels := by
      have hz : ∀ j, raw34877 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34877step0 = (fun i j => raw34877 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34877step0 raw34877; decide +kernel
      have hl : raw34877step0Labels = raw34877Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34877 raw34877Labels permutation346 hz
    mixedMoment B raw34877step0 raw34877step0Labels = mixedMoment B raw34877step1 raw34877step1Labels := by
      have ha : raw34877step1 = (fun i j => raw34877step0 (permutation60 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34877step1 raw34877step0; decide +kernel
      have hl : raw34877step1Labels = raw34877step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34877step0 raw34877step0Labels permutation60 permutation3
    _ = mixedMoment B node3737 node3737Labels := by rfl

def raw34878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw34878Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34878step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw34878step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34878step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![3, -2, -1], ![2, -1, -1]]
def raw34878step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34878step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw34878step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34878 raw34878Labels = mixedMoment B node1818 node1818Labels := by
  calc
    mixedMoment B raw34878 raw34878Labels = mixedMoment B raw34878step0 raw34878step0Labels := by
      have hz : ∀ j, raw34878 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34878step0 = (fun i j => raw34878 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34878step0 raw34878; decide +kernel
      have hl : raw34878step0Labels = raw34878Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34878 raw34878Labels permutation434 hz
    mixedMoment B raw34878step0 raw34878step0Labels = mixedMoment B raw34878step1 raw34878step1Labels := by
      have hz : ∀ j, raw34878step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34878step1 = (fun i j => raw34878step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34878step1 raw34878step0; decide +kernel
      have hl : raw34878step1Labels = raw34878step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34878step0 raw34878step0Labels permutation80 hz
    mixedMoment B raw34878step1 raw34878step1Labels = mixedMoment B raw34878step2 raw34878step2Labels := by
      have ha : raw34878step2 = (fun i j => raw34878step1 (permutation15 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34878step2 raw34878step1; decide +kernel
      have hl : raw34878step2Labels = raw34878step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34878step1 raw34878step1Labels permutation15 permutation3
    _ = mixedMoment B node1818 node1818Labels := by rfl

def raw34879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw34879Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34879step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw34879step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34879step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34879step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34879step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34879step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34879 raw34879Labels = mixedMoment B node2341 node2341Labels := by
  calc
    mixedMoment B raw34879 raw34879Labels = mixedMoment B raw34879step0 raw34879step0Labels := by
      have hz : ∀ j, raw34879 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34879step0 = (fun i j => raw34879 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34879step0 raw34879; decide +kernel
      have hl : raw34879step0Labels = raw34879Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34879 raw34879Labels permutation434 hz
    mixedMoment B raw34879step0 raw34879step0Labels = mixedMoment B raw34879step1 raw34879step1Labels := by
      have ha : raw34879step1 = (fun i j => raw34879step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34879step1 raw34879step0; decide +kernel
      have hl : raw34879step1Labels = raw34879step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34879step0 raw34879step0Labels permutation126 permutation3
    mixedMoment B raw34879step1 raw34879step1Labels = mixedMoment B raw34879step2 raw34879step2Labels := by
      have ha : raw34879step2 = -raw34879step1 := by apply Matrix.ext; change ∀ i j, raw34879step2 i j = -(raw34879step1 i j); unfold raw34879step2 raw34879step1; decide +kernel
      have hl : raw34879step2Labels = raw34879step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2341 node2341Labels := by rfl

def raw34880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw34880Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34880step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw34880step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34880step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34880step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34880step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34880step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34880 raw34880Labels = mixedMoment B node2341 node2341Labels := by
  calc
    mixedMoment B raw34880 raw34880Labels = mixedMoment B raw34880step0 raw34880step0Labels := by
      have hz : ∀ j, raw34880 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34880step0 = (fun i j => raw34880 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34880step0 raw34880; decide +kernel
      have hl : raw34880step0Labels = raw34880Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34880 raw34880Labels permutation346 hz
    mixedMoment B raw34880step0 raw34880step0Labels = mixedMoment B raw34880step1 raw34880step1Labels := by
      have ha : raw34880step1 = (fun i j => raw34880step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34880step1 raw34880step0; decide +kernel
      have hl : raw34880step1Labels = raw34880step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34880step0 raw34880step0Labels permutation126 permutation3
    mixedMoment B raw34880step1 raw34880step1Labels = mixedMoment B raw34880step2 raw34880step2Labels := by
      have ha : raw34880step2 = -raw34880step1 := by apply Matrix.ext; change ∀ i j, raw34880step2 i j = -(raw34880step1 i j); unfold raw34880step2 raw34880step1; decide +kernel
      have hl : raw34880step2Labels = raw34880step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2341 node2341Labels := by rfl

def raw34881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw34881Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34881step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw34881step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34881step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![3, -2, -1], ![1, 0, -1]]
def raw34881step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34881step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw34881step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34881step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34881step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34881 raw34881Labels = mixedMoment B node2604 node2604Labels := by
  calc
    mixedMoment B raw34881 raw34881Labels = mixedMoment B raw34881step0 raw34881step0Labels := by
      have hz : ∀ j, raw34881 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34881step0 = (fun i j => raw34881 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34881step0 raw34881; decide +kernel
      have hl : raw34881step0Labels = raw34881Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34881 raw34881Labels permutation434 hz
    mixedMoment B raw34881step0 raw34881step0Labels = mixedMoment B raw34881step1 raw34881step1Labels := by
      have hz : ∀ j, raw34881step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34881step1 = (fun i j => raw34881step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34881step1 raw34881step0; decide +kernel
      have hl : raw34881step1Labels = raw34881step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34881step0 raw34881step0Labels permutation80 hz
    mixedMoment B raw34881step1 raw34881step1Labels = mixedMoment B raw34881step2 raw34881step2Labels := by
      have ha : raw34881step2 = (fun i j => raw34881step1 (permutation24 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34881step2 raw34881step1; decide +kernel
      have hl : raw34881step2Labels = raw34881step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34881step1 raw34881step1Labels permutation24 permutation3
    mixedMoment B raw34881step2 raw34881step2Labels = mixedMoment B raw34881step3 raw34881step3Labels := by
      have ha : raw34881step3 = -raw34881step2 := by apply Matrix.ext; change ∀ i j, raw34881step3 i j = -(raw34881step2 i j); unfold raw34881step3 raw34881step2; decide +kernel
      have hl : raw34881step3Labels = raw34881step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2604 node2604Labels := by rfl

def raw34882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw34882Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34882step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw34882step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34882step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![2, -1, -1], ![3, -2, -1]]
def raw34882step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34882step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -1, -1], ![3, -1, -2]]
def raw34882step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34882 raw34882Labels = mixedMoment B node1818 node1818Labels := by
  calc
    mixedMoment B raw34882 raw34882Labels = mixedMoment B raw34882step0 raw34882step0Labels := by
      have hz : ∀ j, raw34882 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34882step0 = (fun i j => raw34882 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34882step0 raw34882; decide +kernel
      have hl : raw34882step0Labels = raw34882Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34882 raw34882Labels permutation434 hz
    mixedMoment B raw34882step0 raw34882step0Labels = mixedMoment B raw34882step1 raw34882step1Labels := by
      have hz : ∀ j, raw34882step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34882step1 = (fun i j => raw34882step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34882step1 raw34882step0; decide +kernel
      have hl : raw34882step1Labels = raw34882step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34882step0 raw34882step0Labels permutation80 hz
    mixedMoment B raw34882step1 raw34882step1Labels = mixedMoment B raw34882step2 raw34882step2Labels := by
      have ha : raw34882step2 = (fun i j => raw34882step1 (permutation14 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34882step2 raw34882step1; decide +kernel
      have hl : raw34882step2Labels = raw34882step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34882step1 raw34882step1Labels permutation14 permutation3
    _ = mixedMoment B node1818 node1818Labels := by rfl

def raw34883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw34883Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw34883step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34883step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34883step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34883step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34883step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34883 raw34883Labels = mixedMoment B node2341 node2341Labels := by
  calc
    mixedMoment B raw34883 raw34883Labels = mixedMoment B raw34883step0 raw34883step0Labels := by
      have hz : ∀ j, raw34883 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34883step0 = (fun i j => raw34883 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34883step0 raw34883; decide +kernel
      have hl : raw34883step0Labels = raw34883Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34883 raw34883Labels permutation434 hz
    mixedMoment B raw34883step0 raw34883step0Labels = mixedMoment B raw34883step1 raw34883step1Labels := by
      have ha : raw34883step1 = (fun i j => raw34883step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34883step1 raw34883step0; decide +kernel
      have hl : raw34883step1Labels = raw34883step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34883step0 raw34883step0Labels permutation150 permutation3
    mixedMoment B raw34883step1 raw34883step1Labels = mixedMoment B raw34883step2 raw34883step2Labels := by
      have ha : raw34883step2 = -raw34883step1 := by apply Matrix.ext; change ∀ i j, raw34883step2 i j = -(raw34883step1 i j); unfold raw34883step2 raw34883step1; decide +kernel
      have hl : raw34883step2Labels = raw34883step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2341 node2341Labels := by rfl

def raw34884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw34884Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw34884step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34884step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34884step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34884step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34884step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34884 raw34884Labels = mixedMoment B node2341 node2341Labels := by
  calc
    mixedMoment B raw34884 raw34884Labels = mixedMoment B raw34884step0 raw34884step0Labels := by
      have hz : ∀ j, raw34884 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34884step0 = (fun i j => raw34884 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34884step0 raw34884; decide +kernel
      have hl : raw34884step0Labels = raw34884Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34884 raw34884Labels permutation346 hz
    mixedMoment B raw34884step0 raw34884step0Labels = mixedMoment B raw34884step1 raw34884step1Labels := by
      have ha : raw34884step1 = (fun i j => raw34884step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34884step1 raw34884step0; decide +kernel
      have hl : raw34884step1Labels = raw34884step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34884step0 raw34884step0Labels permutation150 permutation3
    mixedMoment B raw34884step1 raw34884step1Labels = mixedMoment B raw34884step2 raw34884step2Labels := by
      have ha : raw34884step2 = -raw34884step1 := by apply Matrix.ext; change ∀ i j, raw34884step2 i j = -(raw34884step1 i j); unfold raw34884step2 raw34884step1; decide +kernel
      have hl : raw34884step2Labels = raw34884step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2341 node2341Labels := by rfl

def raw34885 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34885Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34885step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34885step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34885step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-1, -1, 2], ![-1, -1, 2]]
def raw34885step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34885step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw34885step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34885step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw34885step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34885 raw34885Labels = mixedMoment B node5466 node5466Labels := by
  calc
    mixedMoment B raw34885 raw34885Labels = mixedMoment B raw34885step0 raw34885step0Labels := by
      have hz : ∀ j, raw34885 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34885step0 = (fun i j => raw34885 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34885step0 raw34885; decide +kernel
      have hl : raw34885step0Labels = raw34885Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34885 raw34885Labels permutation434 hz
    mixedMoment B raw34885step0 raw34885step0Labels = mixedMoment B raw34885step1 raw34885step1Labels := by
      have hz : ∀ j, raw34885step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34885step1 = (fun i j => raw34885step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34885step1 raw34885step0; decide +kernel
      have hl : raw34885step1Labels = raw34885step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34885step0 raw34885step0Labels permutation80 hz
    mixedMoment B raw34885step1 raw34885step1Labels = mixedMoment B raw34885step2 raw34885step2Labels := by
      have ha : raw34885step2 = (fun i j => raw34885step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34885step2 raw34885step1; decide +kernel
      have hl : raw34885step2Labels = raw34885step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34885step1 raw34885step1Labels permutation8 permutation6
    mixedMoment B raw34885step2 raw34885step2Labels = mixedMoment B raw34885step3 raw34885step3Labels := by
      have ha : raw34885step3 = raw34885step2 := by apply Matrix.ext; unfold raw34885step3 raw34885step2; decide +kernel
      have hl : raw34885step2Labels = labelEmbedding9 ∘ raw34885step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34885step2 raw34885step2Labels raw34885step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5466 node5466Labels := by rfl

def raw34886 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34886Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34886step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34886step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34886step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34886step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34886step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34886step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34886 raw34886Labels = mixedMoment B node5356 node5356Labels := by
  calc
    mixedMoment B raw34886 raw34886Labels = mixedMoment B raw34886step0 raw34886step0Labels := by
      have hz : ∀ j, raw34886 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34886step0 = (fun i j => raw34886 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34886step0 raw34886; decide +kernel
      have hl : raw34886step0Labels = raw34886Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34886 raw34886Labels permutation434 hz
    mixedMoment B raw34886step0 raw34886step0Labels = mixedMoment B raw34886step1 raw34886step1Labels := by
      have ha : raw34886step1 = (fun i j => raw34886step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34886step1 raw34886step0; decide +kernel
      have hl : raw34886step1Labels = raw34886step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34886step0 raw34886step0Labels permutation56 permutation7
    mixedMoment B raw34886step1 raw34886step1Labels = mixedMoment B raw34886step2 raw34886step2Labels := by
      have ha : raw34886step2 = raw34886step1 := by apply Matrix.ext; unfold raw34886step2 raw34886step1; decide +kernel
      have hl : raw34886step1Labels = labelEmbedding10 ∘ raw34886step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34886step1 raw34886step1Labels raw34886step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5356 node5356Labels := by rfl

def raw34887 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34887Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34887step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34887step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34887step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34887step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34887step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34887step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34887 raw34887Labels = mixedMoment B node5356 node5356Labels := by
  calc
    mixedMoment B raw34887 raw34887Labels = mixedMoment B raw34887step0 raw34887step0Labels := by
      have hz : ∀ j, raw34887 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34887step0 = (fun i j => raw34887 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34887step0 raw34887; decide +kernel
      have hl : raw34887step0Labels = raw34887Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34887 raw34887Labels permutation346 hz
    mixedMoment B raw34887step0 raw34887step0Labels = mixedMoment B raw34887step1 raw34887step1Labels := by
      have ha : raw34887step1 = (fun i j => raw34887step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34887step1 raw34887step0; decide +kernel
      have hl : raw34887step1Labels = raw34887step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34887step0 raw34887step0Labels permutation56 permutation7
    mixedMoment B raw34887step1 raw34887step1Labels = mixedMoment B raw34887step2 raw34887step2Labels := by
      have ha : raw34887step2 = raw34887step1 := by apply Matrix.ext; unfold raw34887step2 raw34887step1; decide +kernel
      have hl : raw34887step1Labels = labelEmbedding10 ∘ raw34887step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34887step1 raw34887step1Labels raw34887step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5356 node5356Labels := by rfl

def raw34888 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw34888Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw34888step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34888step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw34888step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34888step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw34888step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34888step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw34888step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34888 raw34888Labels = mixedMoment B node5371 node5371Labels := by
  calc
    mixedMoment B raw34888 raw34888Labels = mixedMoment B raw34888step0 raw34888step0Labels := by
      have hz : ∀ j, raw34888 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34888step0 = (fun i j => raw34888 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34888step0 raw34888; decide +kernel
      have hl : raw34888step0Labels = raw34888Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34888 raw34888Labels permutation434 hz
    mixedMoment B raw34888step0 raw34888step0Labels = mixedMoment B raw34888step1 raw34888step1Labels := by
      have hz : ∀ j, raw34888step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34888step1 = (fun i j => raw34888step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34888step1 raw34888step0; decide +kernel
      have hl : raw34888step1Labels = raw34888step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34888step0 raw34888step0Labels permutation80 hz
    mixedMoment B raw34888step1 raw34888step1Labels = mixedMoment B raw34888step2 raw34888step2Labels := by
      have ha : raw34888step2 = (fun i j => raw34888step1 (permutation14 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34888step2 raw34888step1; decide +kernel
      have hl : raw34888step2Labels = raw34888step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34888step1 raw34888step1Labels permutation14 permutation7
    mixedMoment B raw34888step2 raw34888step2Labels = mixedMoment B raw34888step3 raw34888step3Labels := by
      have ha : raw34888step3 = raw34888step2 := by apply Matrix.ext; unfold raw34888step3 raw34888step2; decide +kernel
      have hl : raw34888step2Labels = labelEmbedding10 ∘ raw34888step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34888step2 raw34888step2Labels raw34888step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5371 node5371Labels := by rfl

def raw34889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -1, -2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34889Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -1, -2], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34889step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34889step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -1, -2], ![-1, -1, 2], ![-1, -1, 2]]
def raw34889step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34889step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 3, -2], ![-1, -1, 2], ![-1, -1, 2]]
def raw34889step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34889step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -3, 2], ![1, 1, -2], ![1, 1, -2]]
def raw34889step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34889 raw34889Labels = mixedMoment B node5303 node5303Labels := by
  calc
    mixedMoment B raw34889 raw34889Labels = mixedMoment B raw34889step0 raw34889step0Labels := by
      have hz : ∀ j, raw34889 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34889step0 = (fun i j => raw34889 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34889step0 raw34889; decide +kernel
      have hl : raw34889step0Labels = raw34889Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34889 raw34889Labels permutation434 hz
    mixedMoment B raw34889step0 raw34889step0Labels = mixedMoment B raw34889step1 raw34889step1Labels := by
      have hz : ∀ j, raw34889step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34889step1 = (fun i j => raw34889step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34889step1 raw34889step0; decide +kernel
      have hl : raw34889step1Labels = raw34889step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34889step0 raw34889step0Labels permutation80 hz
    mixedMoment B raw34889step1 raw34889step1Labels = mixedMoment B raw34889step2 raw34889step2Labels := by
      have ha : raw34889step2 = (fun i j => raw34889step1 (permutation14 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34889step2 raw34889step1; decide +kernel
      have hl : raw34889step2Labels = raw34889step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34889step1 raw34889step1Labels permutation14 permutation2
    mixedMoment B raw34889step2 raw34889step2Labels = mixedMoment B raw34889step3 raw34889step3Labels := by
      have ha : raw34889step3 = -raw34889step2 := by apply Matrix.ext; change ∀ i j, raw34889step3 i j = -(raw34889step2 i j); unfold raw34889step3 raw34889step2; decide +kernel
      have hl : raw34889step3Labels = raw34889step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5303 node5303Labels := by rfl

def raw34890 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34890Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34890step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34890step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34890step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34890step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34890step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw34890step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34890 raw34890Labels = mixedMoment B node5236 node5236Labels := by
  calc
    mixedMoment B raw34890 raw34890Labels = mixedMoment B raw34890step0 raw34890step0Labels := by
      have hz : ∀ j, raw34890 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34890step0 = (fun i j => raw34890 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34890step0 raw34890; decide +kernel
      have hl : raw34890step0Labels = raw34890Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34890 raw34890Labels permutation434 hz
    mixedMoment B raw34890step0 raw34890step0Labels = mixedMoment B raw34890step1 raw34890step1Labels := by
      have ha : raw34890step1 = (fun i j => raw34890step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34890step1 raw34890step0; decide +kernel
      have hl : raw34890step1Labels = raw34890step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34890step0 raw34890step0Labels permutation56 permutation2
    mixedMoment B raw34890step1 raw34890step1Labels = mixedMoment B raw34890step2 raw34890step2Labels := by
      have ha : raw34890step2 = -raw34890step1 := by apply Matrix.ext; change ∀ i j, raw34890step2 i j = -(raw34890step1 i j); unfold raw34890step2 raw34890step1; decide +kernel
      have hl : raw34890step2Labels = raw34890step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5236 node5236Labels := by rfl

def raw34891 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34891Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34891step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34891step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34891step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34891step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw34891step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34891 raw34891Labels = mixedMoment B node5236 node5236Labels := by
  calc
    mixedMoment B raw34891 raw34891Labels = mixedMoment B raw34891step0 raw34891step0Labels := by
      have hz : ∀ j, raw34891 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34891step0 = (fun i j => raw34891 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34891step0 raw34891; decide +kernel
      have hl : raw34891step0Labels = raw34891Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34891 raw34891Labels permutation346 hz
    mixedMoment B raw34891step0 raw34891step0Labels = mixedMoment B raw34891step1 raw34891step1Labels := by
      have ha : raw34891step1 = (fun i j => raw34891step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34891step1 raw34891step0; decide +kernel
      have hl : raw34891step1Labels = raw34891step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34891step0 raw34891step0Labels permutation56 permutation2
    mixedMoment B raw34891step1 raw34891step1Labels = mixedMoment B raw34891step2 raw34891step2Labels := by
      have ha : raw34891step2 = -raw34891step1 := by apply Matrix.ext; change ∀ i j, raw34891step2 i j = -(raw34891step1 i j); unfold raw34891step2 raw34891step1; decide +kernel
      have hl : raw34891step2Labels = raw34891step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5236 node5236Labels := by rfl

def raw34892 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw34892Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw34892step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34892step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw34892step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34892step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw34892step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34892step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw34892step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34892 raw34892Labels = mixedMoment B node5238 node5238Labels := by
  calc
    mixedMoment B raw34892 raw34892Labels = mixedMoment B raw34892step0 raw34892step0Labels := by
      have hz : ∀ j, raw34892 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34892step0 = (fun i j => raw34892 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34892step0 raw34892; decide +kernel
      have hl : raw34892step0Labels = raw34892Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34892 raw34892Labels permutation434 hz
    mixedMoment B raw34892step0 raw34892step0Labels = mixedMoment B raw34892step1 raw34892step1Labels := by
      have hz : ∀ j, raw34892step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34892step1 = (fun i j => raw34892step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34892step1 raw34892step0; decide +kernel
      have hl : raw34892step1Labels = raw34892step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34892step0 raw34892step0Labels permutation80 hz
    mixedMoment B raw34892step1 raw34892step1Labels = mixedMoment B raw34892step2 raw34892step2Labels := by
      have ha : raw34892step2 = (fun i j => raw34892step1 (permutation14 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34892step2 raw34892step1; decide +kernel
      have hl : raw34892step2Labels = raw34892step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34892step1 raw34892step1Labels permutation14 permutation2
    mixedMoment B raw34892step2 raw34892step2Labels = mixedMoment B raw34892step3 raw34892step3Labels := by
      have ha : raw34892step3 = -raw34892step2 := by apply Matrix.ext; change ∀ i j, raw34892step3 i j = -(raw34892step2 i j); unfold raw34892step3 raw34892step2; decide +kernel
      have hl : raw34892step3Labels = raw34892step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5238 node5238Labels := by rfl

def raw34893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34893Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34893step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34893step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34893step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34893step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw34893step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34893step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw34893step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34893 raw34893Labels = mixedMoment B node5236 node5236Labels := by
  calc
    mixedMoment B raw34893 raw34893Labels = mixedMoment B raw34893step0 raw34893step0Labels := by
      have hz : ∀ j, raw34893 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34893step0 = (fun i j => raw34893 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34893step0 raw34893; decide +kernel
      have hl : raw34893step0Labels = raw34893Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34893 raw34893Labels permutation434 hz
    mixedMoment B raw34893step0 raw34893step0Labels = mixedMoment B raw34893step1 raw34893step1Labels := by
      have ha : raw34893step1 = (fun i j => raw34893step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34893step1 raw34893step0; decide +kernel
      have hl : raw34893step1Labels = raw34893step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34893step0 raw34893step0Labels permutation32 permutation4
    mixedMoment B raw34893step1 raw34893step1Labels = mixedMoment B raw34893step2 raw34893step2Labels := by
      have ha : raw34893step2 = -raw34893step1 := by apply Matrix.ext; change ∀ i j, raw34893step2 i j = -(raw34893step1 i j); unfold raw34893step2 raw34893step1; decide +kernel
      have hl : raw34893step2Labels = raw34893step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34893step2 raw34893step2Labels = mixedMoment B raw34893step3 raw34893step3Labels := by
      have ha : raw34893step3 = raw34893step2 := by apply Matrix.ext; unfold raw34893step3 raw34893step2; decide +kernel
      have hl : raw34893step2Labels = labelEmbedding7 ∘ raw34893step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34893step2 raw34893step2Labels raw34893step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5236 node5236Labels := by rfl

def raw34894 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34894Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34894step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34894step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34894step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34894step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34894step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34894 raw34894Labels = mixedMoment B node5356 node5356Labels := by
  calc
    mixedMoment B raw34894 raw34894Labels = mixedMoment B raw34894step0 raw34894step0Labels := by
      have hz : ∀ j, raw34894 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34894step0 = (fun i j => raw34894 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34894step0 raw34894; decide +kernel
      have hl : raw34894step0Labels = raw34894Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34894 raw34894Labels permutation434 hz
    mixedMoment B raw34894step0 raw34894step0Labels = mixedMoment B raw34894step1 raw34894step1Labels := by
      have ha : raw34894step1 = (fun i j => raw34894step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34894step1 raw34894step0; decide +kernel
      have hl : raw34894step1Labels = raw34894step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34894step0 raw34894step0Labels permutation32 permutation6
    mixedMoment B raw34894step1 raw34894step1Labels = mixedMoment B raw34894step2 raw34894step2Labels := by
      have ha : raw34894step2 = raw34894step1 := by apply Matrix.ext; unfold raw34894step2 raw34894step1; decide +kernel
      have hl : raw34894step1Labels = labelEmbedding9 ∘ raw34894step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34894step1 raw34894step1Labels raw34894step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5356 node5356Labels := by rfl

def raw34895 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34895Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34895step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34895step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34895step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34895step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34895 raw34895Labels = mixedMoment B node5377 node5377Labels := by
  calc
    mixedMoment B raw34895 raw34895Labels = mixedMoment B raw34895step0 raw34895step0Labels := by
      have ha : raw34895step0 = (fun i j => raw34895 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34895step0 raw34895; decide +kernel
      have hl : raw34895step0Labels = raw34895Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34895 raw34895Labels permutation158 permutation6
    mixedMoment B raw34895step0 raw34895step0Labels = mixedMoment B raw34895step1 raw34895step1Labels := by
      have ha : raw34895step1 = raw34895step0 := by apply Matrix.ext; unfold raw34895step1 raw34895step0; decide +kernel
      have hl : raw34895step0Labels = labelEmbedding9 ∘ raw34895step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34895step0 raw34895step0Labels raw34895step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5377 node5377Labels := by rfl

def raw34896 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw34896Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw34896step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34896step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34896step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34896step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34896step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34896step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34896step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34896 raw34896Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw34896 raw34896Labels = mixedMoment B raw34896step0 raw34896step0Labels := by
      have hz : ∀ j, raw34896 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34896step0 = (fun i j => raw34896 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34896step0 raw34896; decide +kernel
      have hl : raw34896step0Labels = raw34896Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34896 raw34896Labels permutation434 hz
    mixedMoment B raw34896step0 raw34896step0Labels = mixedMoment B raw34896step1 raw34896step1Labels := by
      have ha : raw34896step1 = (fun i j => raw34896step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34896step1 raw34896step0; decide +kernel
      have hl : raw34896step1Labels = raw34896step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34896step0 raw34896step0Labels permutation150 permutation7
    mixedMoment B raw34896step1 raw34896step1Labels = mixedMoment B raw34896step2 raw34896step2Labels := by
      have ha : raw34896step2 = -raw34896step1 := by apply Matrix.ext; change ∀ i j, raw34896step2 i j = -(raw34896step1 i j); unfold raw34896step2 raw34896step1; decide +kernel
      have hl : raw34896step2Labels = raw34896step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34896step2 raw34896step2Labels = mixedMoment B raw34896step3 raw34896step3Labels := by
      have ha : raw34896step3 = raw34896step2 := by apply Matrix.ext; unfold raw34896step3 raw34896step2; decide +kernel
      have hl : raw34896step2Labels = labelEmbedding10 ∘ raw34896step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34896step2 raw34896step2Labels raw34896step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

def raw34897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34897Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34897step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34897step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34897step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34897step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw34897step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34897step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw34897step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34897 raw34897Labels = mixedMoment B node5236 node5236Labels := by
  calc
    mixedMoment B raw34897 raw34897Labels = mixedMoment B raw34897step0 raw34897step0Labels := by
      have hz : ∀ j, raw34897 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34897step0 = (fun i j => raw34897 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34897step0 raw34897; decide +kernel
      have hl : raw34897step0Labels = raw34897Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34897 raw34897Labels permutation346 hz
    mixedMoment B raw34897step0 raw34897step0Labels = mixedMoment B raw34897step1 raw34897step1Labels := by
      have ha : raw34897step1 = (fun i j => raw34897step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34897step1 raw34897step0; decide +kernel
      have hl : raw34897step1Labels = raw34897step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34897step0 raw34897step0Labels permutation32 permutation4
    mixedMoment B raw34897step1 raw34897step1Labels = mixedMoment B raw34897step2 raw34897step2Labels := by
      have ha : raw34897step2 = -raw34897step1 := by apply Matrix.ext; change ∀ i j, raw34897step2 i j = -(raw34897step1 i j); unfold raw34897step2 raw34897step1; decide +kernel
      have hl : raw34897step2Labels = raw34897step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34897step2 raw34897step2Labels = mixedMoment B raw34897step3 raw34897step3Labels := by
      have ha : raw34897step3 = raw34897step2 := by apply Matrix.ext; unfold raw34897step3 raw34897step2; decide +kernel
      have hl : raw34897step2Labels = labelEmbedding7 ∘ raw34897step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34897step2 raw34897step2Labels raw34897step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5236 node5236Labels := by rfl

def raw34898 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34898Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34898step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34898step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34898step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34898step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34898step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34898 raw34898Labels = mixedMoment B node5356 node5356Labels := by
  calc
    mixedMoment B raw34898 raw34898Labels = mixedMoment B raw34898step0 raw34898step0Labels := by
      have hz : ∀ j, raw34898 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34898step0 = (fun i j => raw34898 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34898step0 raw34898; decide +kernel
      have hl : raw34898step0Labels = raw34898Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34898 raw34898Labels permutation346 hz
    mixedMoment B raw34898step0 raw34898step0Labels = mixedMoment B raw34898step1 raw34898step1Labels := by
      have ha : raw34898step1 = (fun i j => raw34898step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34898step1 raw34898step0; decide +kernel
      have hl : raw34898step1Labels = raw34898step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34898step0 raw34898step0Labels permutation32 permutation6
    mixedMoment B raw34898step1 raw34898step1Labels = mixedMoment B raw34898step2 raw34898step2Labels := by
      have ha : raw34898step2 = raw34898step1 := by apply Matrix.ext; unfold raw34898step2 raw34898step1; decide +kernel
      have hl : raw34898step1Labels = labelEmbedding9 ∘ raw34898step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34898step1 raw34898step1Labels raw34898step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5356 node5356Labels := by rfl

def raw34899 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw34899Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34899step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34899step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34899step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw34899step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34899 raw34899Labels = mixedMoment B node5377 node5377Labels := by
  calc
    mixedMoment B raw34899 raw34899Labels = mixedMoment B raw34899step0 raw34899step0Labels := by
      have ha : raw34899step0 = (fun i j => raw34899 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34899step0 raw34899; decide +kernel
      have hl : raw34899step0Labels = raw34899Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34899 raw34899Labels permutation152 permutation6
    mixedMoment B raw34899step0 raw34899step0Labels = mixedMoment B raw34899step1 raw34899step1Labels := by
      have ha : raw34899step1 = raw34899step0 := by apply Matrix.ext; unfold raw34899step1 raw34899step0; decide +kernel
      have hl : raw34899step0Labels = labelEmbedding9 ∘ raw34899step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34899step0 raw34899step0Labels raw34899step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5377 node5377Labels := by rfl

def raw34900 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw34900Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw34900step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34900step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34900step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34900step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34900step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw34900step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34900step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34900 raw34900Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw34900 raw34900Labels = mixedMoment B raw34900step0 raw34900step0Labels := by
      have hz : ∀ j, raw34900 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34900step0 = (fun i j => raw34900 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34900step0 raw34900; decide +kernel
      have hl : raw34900step0Labels = raw34900Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34900 raw34900Labels permutation346 hz
    mixedMoment B raw34900step0 raw34900step0Labels = mixedMoment B raw34900step1 raw34900step1Labels := by
      have ha : raw34900step1 = (fun i j => raw34900step0 (permutation150 i) (permutation7 j)) := by apply Matrix.ext; unfold raw34900step1 raw34900step0; decide +kernel
      have hl : raw34900step1Labels = raw34900step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34900step0 raw34900step0Labels permutation150 permutation7
    mixedMoment B raw34900step1 raw34900step1Labels = mixedMoment B raw34900step2 raw34900step2Labels := by
      have ha : raw34900step2 = -raw34900step1 := by apply Matrix.ext; change ∀ i j, raw34900step2 i j = -(raw34900step1 i j); unfold raw34900step2 raw34900step1; decide +kernel
      have hl : raw34900step2Labels = raw34900step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34900step2 raw34900step2Labels = mixedMoment B raw34900step3 raw34900step3Labels := by
      have ha : raw34900step3 = raw34900step2 := by apply Matrix.ext; unfold raw34900step3 raw34900step2; decide +kernel
      have hl : raw34900step2Labels = labelEmbedding10 ∘ raw34900step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34900step2 raw34900step2Labels raw34900step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

def raw34901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw34901Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw34901step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34901step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![0, -2, 2], ![-1, -1, 2]]
def raw34901step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34901step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw34901step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34901step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw34901step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw34901step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw34901step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34901 raw34901Labels = mixedMoment B node5238 node5238Labels := by
  calc
    mixedMoment B raw34901 raw34901Labels = mixedMoment B raw34901step0 raw34901step0Labels := by
      have hz : ∀ j, raw34901 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34901step0 = (fun i j => raw34901 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34901step0 raw34901; decide +kernel
      have hl : raw34901step0Labels = raw34901Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34901 raw34901Labels permutation434 hz
    mixedMoment B raw34901step0 raw34901step0Labels = mixedMoment B raw34901step1 raw34901step1Labels := by
      have hz : ∀ j, raw34901step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34901step1 = (fun i j => raw34901step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34901step1 raw34901step0; decide +kernel
      have hl : raw34901step1Labels = raw34901step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34901step0 raw34901step0Labels permutation80 hz
    mixedMoment B raw34901step1 raw34901step1Labels = mixedMoment B raw34901step2 raw34901step2Labels := by
      have ha : raw34901step2 = (fun i j => raw34901step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw34901step2 raw34901step1; decide +kernel
      have hl : raw34901step2Labels = raw34901step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34901step1 raw34901step1Labels permutation9 permutation4
    mixedMoment B raw34901step2 raw34901step2Labels = mixedMoment B raw34901step3 raw34901step3Labels := by
      have ha : raw34901step3 = -raw34901step2 := by apply Matrix.ext; change ∀ i j, raw34901step3 i j = -(raw34901step2 i j); unfold raw34901step3 raw34901step2; decide +kernel
      have hl : raw34901step3Labels = raw34901step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34901step3 raw34901step3Labels = mixedMoment B raw34901step4 raw34901step4Labels := by
      have ha : raw34901step4 = raw34901step3 := by apply Matrix.ext; unfold raw34901step4 raw34901step3; decide +kernel
      have hl : raw34901step3Labels = labelEmbedding7 ∘ raw34901step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34901step3 raw34901step3Labels raw34901step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5238 node5238Labels := by rfl

def raw34902 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw34902Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw34902step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34902step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![0, -2, 2], ![-1, -1, 2]]
def raw34902step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34902step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw34902step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34902step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw34902step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34902 raw34902Labels = mixedMoment B node5371 node5371Labels := by
  calc
    mixedMoment B raw34902 raw34902Labels = mixedMoment B raw34902step0 raw34902step0Labels := by
      have hz : ∀ j, raw34902 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34902step0 = (fun i j => raw34902 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34902step0 raw34902; decide +kernel
      have hl : raw34902step0Labels = raw34902Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34902 raw34902Labels permutation434 hz
    mixedMoment B raw34902step0 raw34902step0Labels = mixedMoment B raw34902step1 raw34902step1Labels := by
      have hz : ∀ j, raw34902step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34902step1 = (fun i j => raw34902step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34902step1 raw34902step0; decide +kernel
      have hl : raw34902step1Labels = raw34902step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34902step0 raw34902step0Labels permutation80 hz
    mixedMoment B raw34902step1 raw34902step1Labels = mixedMoment B raw34902step2 raw34902step2Labels := by
      have ha : raw34902step2 = (fun i j => raw34902step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34902step2 raw34902step1; decide +kernel
      have hl : raw34902step2Labels = raw34902step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34902step1 raw34902step1Labels permutation9 permutation6
    mixedMoment B raw34902step2 raw34902step2Labels = mixedMoment B raw34902step3 raw34902step3Labels := by
      have ha : raw34902step3 = raw34902step2 := by apply Matrix.ext; unfold raw34902step3 raw34902step2; decide +kernel
      have hl : raw34902step2Labels = labelEmbedding9 ∘ raw34902step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34902step2 raw34902step2Labels raw34902step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5371 node5371Labels := by rfl

def raw34903 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw34903Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw34903step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34903step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34903step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34903step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34903step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34903step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34903step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34903 raw34903Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw34903 raw34903Labels = mixedMoment B raw34903step0 raw34903step0Labels := by
      have hz : ∀ j, raw34903 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34903step0 = (fun i j => raw34903 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34903step0 raw34903; decide +kernel
      have hl : raw34903step0Labels = raw34903Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34903 raw34903Labels permutation434 hz
    mixedMoment B raw34903step0 raw34903step0Labels = mixedMoment B raw34903step1 raw34903step1Labels := by
      have ha : raw34903step1 = (fun i j => raw34903step0 (permutation127 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34903step1 raw34903step0; decide +kernel
      have hl : raw34903step1Labels = raw34903step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34903step0 raw34903step0Labels permutation127 permutation6
    mixedMoment B raw34903step1 raw34903step1Labels = mixedMoment B raw34903step2 raw34903step2Labels := by
      have ha : raw34903step2 = -raw34903step1 := by apply Matrix.ext; change ∀ i j, raw34903step2 i j = -(raw34903step1 i j); unfold raw34903step2 raw34903step1; decide +kernel
      have hl : raw34903step2Labels = raw34903step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34903step2 raw34903step2Labels = mixedMoment B raw34903step3 raw34903step3Labels := by
      have ha : raw34903step3 = raw34903step2 := by apply Matrix.ext; unfold raw34903step3 raw34903step2; decide +kernel
      have hl : raw34903step2Labels = labelEmbedding9 ∘ raw34903step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34903step2 raw34903step2Labels raw34903step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

def raw34904 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw34904Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw34904step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34904step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34904step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34904step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34904step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34904step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34904step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34904 raw34904Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw34904 raw34904Labels = mixedMoment B raw34904step0 raw34904step0Labels := by
      have hz : ∀ j, raw34904 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34904step0 = (fun i j => raw34904 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34904step0 raw34904; decide +kernel
      have hl : raw34904step0Labels = raw34904Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34904 raw34904Labels permutation346 hz
    mixedMoment B raw34904step0 raw34904step0Labels = mixedMoment B raw34904step1 raw34904step1Labels := by
      have ha : raw34904step1 = (fun i j => raw34904step0 (permutation127 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34904step1 raw34904step0; decide +kernel
      have hl : raw34904step1Labels = raw34904step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34904step0 raw34904step0Labels permutation127 permutation6
    mixedMoment B raw34904step1 raw34904step1Labels = mixedMoment B raw34904step2 raw34904step2Labels := by
      have ha : raw34904step2 = -raw34904step1 := by apply Matrix.ext; change ∀ i j, raw34904step2 i j = -(raw34904step1 i j); unfold raw34904step2 raw34904step1; decide +kernel
      have hl : raw34904step2Labels = raw34904step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34904step2 raw34904step2Labels = mixedMoment B raw34904step3 raw34904step3Labels := by
      have ha : raw34904step3 = raw34904step2 := by apply Matrix.ext; unfold raw34904step3 raw34904step2; decide +kernel
      have hl : raw34904step2Labels = labelEmbedding9 ∘ raw34904step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34904step2 raw34904step2Labels raw34904step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

def raw34905 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw34905Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34905step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw34905step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34905step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, -2, 2], ![-2, 0, 2]]
def raw34905step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34905step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34905step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34905step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34905step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34905 raw34905Labels = mixedMoment B node5389 node5389Labels := by
  calc
    mixedMoment B raw34905 raw34905Labels = mixedMoment B raw34905step0 raw34905step0Labels := by
      have hz : ∀ j, raw34905 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34905step0 = (fun i j => raw34905 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34905step0 raw34905; decide +kernel
      have hl : raw34905step0Labels = raw34905Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34905 raw34905Labels permutation434 hz
    mixedMoment B raw34905step0 raw34905step0Labels = mixedMoment B raw34905step1 raw34905step1Labels := by
      have hz : ∀ j, raw34905step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34905step1 = (fun i j => raw34905step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34905step1 raw34905step0; decide +kernel
      have hl : raw34905step1Labels = raw34905step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34905step0 raw34905step0Labels permutation80 hz
    mixedMoment B raw34905step1 raw34905step1Labels = mixedMoment B raw34905step2 raw34905step2Labels := by
      have ha : raw34905step2 = (fun i j => raw34905step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34905step2 raw34905step1; decide +kernel
      have hl : raw34905step2Labels = raw34905step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34905step1 raw34905step1Labels permutation9 permutation6
    mixedMoment B raw34905step2 raw34905step2Labels = mixedMoment B raw34905step3 raw34905step3Labels := by
      have ha : raw34905step3 = raw34905step2 := by apply Matrix.ext; unfold raw34905step3 raw34905step2; decide +kernel
      have hl : raw34905step2Labels = labelEmbedding9 ∘ raw34905step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34905step2 raw34905step2Labels raw34905step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5389 node5389Labels := by rfl

def raw34906 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34906Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw34906step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34906step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-2, 0, 2], ![0, -2, 2]]
def raw34906step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34906step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34906step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw34906step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw34906step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34906 raw34906Labels = mixedMoment B node5389 node5389Labels := by
  calc
    mixedMoment B raw34906 raw34906Labels = mixedMoment B raw34906step0 raw34906step0Labels := by
      have hz : ∀ j, raw34906 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw34906step0 = (fun i j => raw34906 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw34906step0 raw34906; decide +kernel
      have hl : raw34906step0Labels = raw34906Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34906 raw34906Labels permutation434 hz
    mixedMoment B raw34906step0 raw34906step0Labels = mixedMoment B raw34906step1 raw34906step1Labels := by
      have hz : ∀ j, raw34906step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw34906step1 = (fun i j => raw34906step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw34906step1 raw34906step0; decide +kernel
      have hl : raw34906step1Labels = raw34906step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34906step0 raw34906step0Labels permutation80 hz
    mixedMoment B raw34906step1 raw34906step1Labels = mixedMoment B raw34906step2 raw34906step2Labels := by
      have ha : raw34906step2 = (fun i j => raw34906step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw34906step2 raw34906step1; decide +kernel
      have hl : raw34906step2Labels = raw34906step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34906step1 raw34906step1Labels permutation8 permutation6
    mixedMoment B raw34906step2 raw34906step2Labels = mixedMoment B raw34906step3 raw34906step3Labels := by
      have ha : raw34906step3 = raw34906step2 := by apply Matrix.ext; unfold raw34906step3 raw34906step2; decide +kernel
      have hl : raw34906step2Labels = labelEmbedding9 ∘ raw34906step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34906step2 raw34906step2Labels raw34906step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5389 node5389Labels := by rfl

def raw34907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34907Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34907step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34907step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34907step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw34907step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34907step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw34907step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw34907step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw34907step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34907 raw34907Labels = mixedMoment B node4828 node4828Labels := by
  calc
    mixedMoment B raw34907 raw34907Labels = mixedMoment B raw34907step0 raw34907step0Labels := by
      have hz : ∀ j, raw34907 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34907step0 = (fun i j => raw34907 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34907step0 raw34907; decide +kernel
      have hl : raw34907step0Labels = raw34907Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34907 raw34907Labels permutation346 hz
    mixedMoment B raw34907step0 raw34907step0Labels = mixedMoment B raw34907step1 raw34907step1Labels := by
      have ha : raw34907step1 = (fun i j => raw34907step0 (permutation63 i) (permutation5 j)) := by apply Matrix.ext; unfold raw34907step1 raw34907step0; decide +kernel
      have hl : raw34907step1Labels = raw34907step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34907step0 raw34907step0Labels permutation63 permutation5
    mixedMoment B raw34907step1 raw34907step1Labels = mixedMoment B raw34907step2 raw34907step2Labels := by
      have ha : raw34907step2 = -raw34907step1 := by apply Matrix.ext; change ∀ i j, raw34907step2 i j = -(raw34907step1 i j); unfold raw34907step2 raw34907step1; decide +kernel
      have hl : raw34907step2Labels = raw34907step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34907step2 raw34907step2Labels = mixedMoment B raw34907step3 raw34907step3Labels := by
      have ha : raw34907step3 = raw34907step2 := by apply Matrix.ext; unfold raw34907step3 raw34907step2; decide +kernel
      have hl : raw34907step2Labels = labelEmbedding8 ∘ raw34907step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34907step2 raw34907step2Labels raw34907step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4828 node4828Labels := by rfl

def raw34908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34908Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34908step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34908step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34908step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34908step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34908step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34908step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34908 raw34908Labels = mixedMoment B node5349 node5349Labels := by
  calc
    mixedMoment B raw34908 raw34908Labels = mixedMoment B raw34908step0 raw34908step0Labels := by
      have ha : raw34908step0 = (fun i j => raw34908 (permutation585 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34908step0 raw34908; decide +kernel
      have hl : raw34908step0Labels = raw34908Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34908 raw34908Labels permutation585 permutation3
    mixedMoment B raw34908step0 raw34908step0Labels = mixedMoment B raw34908step1 raw34908step1Labels := by
      have ha : raw34908step1 = -raw34908step0 := by apply Matrix.ext; change ∀ i j, raw34908step1 i j = -(raw34908step0 i j); unfold raw34908step1 raw34908step0; decide +kernel
      have hl : raw34908step1Labels = raw34908step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34908step1 raw34908step1Labels = mixedMoment B raw34908step2 raw34908step2Labels := by
      have ha : raw34908step2 = raw34908step1 := by apply Matrix.ext; unfold raw34908step2 raw34908step1; decide +kernel
      have hl : raw34908step1Labels = labelEmbedding6 ∘ raw34908step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34908step1 raw34908step1Labels raw34908step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5349 node5349Labels := by rfl

def raw34909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34909Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34909step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34909step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34909step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw34909step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34909step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw34909step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34909step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw34909step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34909 raw34909Labels = mixedMoment B node5364 node5364Labels := by
  calc
    mixedMoment B raw34909 raw34909Labels = mixedMoment B raw34909step0 raw34909step0Labels := by
      have hz : ∀ j, raw34909 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34909step0 = (fun i j => raw34909 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34909step0 raw34909; decide +kernel
      have hl : raw34909step0Labels = raw34909Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34909 raw34909Labels permutation346 hz
    mixedMoment B raw34909step0 raw34909step0Labels = mixedMoment B raw34909step1 raw34909step1Labels := by
      have ha : raw34909step1 = (fun i j => raw34909step0 (permutation123 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34909step1 raw34909step0; decide +kernel
      have hl : raw34909step1Labels = raw34909step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34909step0 raw34909step0Labels permutation123 permutation3
    mixedMoment B raw34909step1 raw34909step1Labels = mixedMoment B raw34909step2 raw34909step2Labels := by
      have ha : raw34909step2 = -raw34909step1 := by apply Matrix.ext; change ∀ i j, raw34909step2 i j = -(raw34909step1 i j); unfold raw34909step2 raw34909step1; decide +kernel
      have hl : raw34909step2Labels = raw34909step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34909step2 raw34909step2Labels = mixedMoment B raw34909step3 raw34909step3Labels := by
      have ha : raw34909step3 = raw34909step2 := by apply Matrix.ext; unfold raw34909step3 raw34909step2; decide +kernel
      have hl : raw34909step2Labels = labelEmbedding6 ∘ raw34909step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34909step2 raw34909step2Labels raw34909step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5364 node5364Labels := by rfl

def raw34910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw34910Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw34910step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34910step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw34910step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34910step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw34910step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34910step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw34910step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34910 raw34910Labels = mixedMoment B node5432 node5432Labels := by
  calc
    mixedMoment B raw34910 raw34910Labels = mixedMoment B raw34910step0 raw34910step0Labels := by
      have hz : ∀ j, raw34910 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34910step0 = (fun i j => raw34910 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34910step0 raw34910; decide +kernel
      have hl : raw34910step0Labels = raw34910Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34910 raw34910Labels permutation346 hz
    mixedMoment B raw34910step0 raw34910step0Labels = mixedMoment B raw34910step1 raw34910step1Labels := by
      have ha : raw34910step1 = (fun i j => raw34910step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34910step1 raw34910step0; decide +kernel
      have hl : raw34910step1Labels = raw34910step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34910step0 raw34910step0Labels permutation126 permutation3
    mixedMoment B raw34910step1 raw34910step1Labels = mixedMoment B raw34910step2 raw34910step2Labels := by
      have ha : raw34910step2 = -raw34910step1 := by apply Matrix.ext; change ∀ i j, raw34910step2 i j = -(raw34910step1 i j); unfold raw34910step2 raw34910step1; decide +kernel
      have hl : raw34910step2Labels = raw34910step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34910step2 raw34910step2Labels = mixedMoment B raw34910step3 raw34910step3Labels := by
      have ha : raw34910step3 = raw34910step2 := by apply Matrix.ext; unfold raw34910step3 raw34910step2; decide +kernel
      have hl : raw34910step2Labels = labelEmbedding6 ∘ raw34910step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34910step2 raw34910step2Labels raw34910step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5432 node5432Labels := by rfl

def raw34911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34911Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34911step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw34911step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34911step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw34911step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34911 raw34911Labels = mixedMoment B node4661 node4661Labels := by
  calc
    mixedMoment B raw34911 raw34911Labels = mixedMoment B raw34911step0 raw34911step0Labels := by
      have ha : raw34911step0 = (fun i j => raw34911 (permutation272 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34911step0 raw34911; decide +kernel
      have hl : raw34911step0Labels = raw34911Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34911 raw34911Labels permutation272 permutation3
    mixedMoment B raw34911step0 raw34911step0Labels = mixedMoment B raw34911step1 raw34911step1Labels := by
      have ha : raw34911step1 = raw34911step0 := by apply Matrix.ext; unfold raw34911step1 raw34911step0; decide +kernel
      have hl : raw34911step0Labels = labelEmbedding6 ∘ raw34911step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34911step0 raw34911step0Labels raw34911step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4661 node4661Labels := by rfl

def raw34912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34912Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34912step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, 0, -1], ![-1, -1, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw34912step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34912step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw34912step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34912step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw34912step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34912 raw34912Labels = mixedMoment B node5333 node5333Labels := by
  calc
    mixedMoment B raw34912 raw34912Labels = mixedMoment B raw34912step0 raw34912step0Labels := by
      have ha : raw34912step0 = (fun i j => raw34912 (permutation583 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34912step0 raw34912; decide +kernel
      have hl : raw34912step0Labels = raw34912Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34912 raw34912Labels permutation583 permutation3
    mixedMoment B raw34912step0 raw34912step0Labels = mixedMoment B raw34912step1 raw34912step1Labels := by
      have ha : raw34912step1 = -raw34912step0 := by apply Matrix.ext; change ∀ i j, raw34912step1 i j = -(raw34912step0 i j); unfold raw34912step1 raw34912step0; decide +kernel
      have hl : raw34912step1Labels = raw34912step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34912step1 raw34912step1Labels = mixedMoment B raw34912step2 raw34912step2Labels := by
      have ha : raw34912step2 = raw34912step1 := by apply Matrix.ext; unfold raw34912step2 raw34912step1; decide +kernel
      have hl : raw34912step1Labels = labelEmbedding6 ∘ raw34912step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34912step1 raw34912step1Labels raw34912step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5333 node5333Labels := by rfl

def raw34913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw34913Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34913step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34913step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34913step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34913step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34913 raw34913Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw34913 raw34913Labels = mixedMoment B raw34913step0 raw34913step0Labels := by
      have ha : raw34913step0 = (fun i j => raw34913 (permutation275 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34913step0 raw34913; decide +kernel
      have hl : raw34913step0Labels = raw34913Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34913 raw34913Labels permutation275 permutation3
    mixedMoment B raw34913step0 raw34913step0Labels = mixedMoment B raw34913step1 raw34913step1Labels := by
      have ha : raw34913step1 = raw34913step0 := by apply Matrix.ext; unfold raw34913step1 raw34913step0; decide +kernel
      have hl : raw34913step0Labels = labelEmbedding6 ∘ raw34913step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34913step0 raw34913step0Labels raw34913step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

def raw34914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34914Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34914step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34914step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34914step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34914step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34914step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34914 raw34914Labels = mixedMoment B node4684 node4684Labels := by
  calc
    mixedMoment B raw34914 raw34914Labels = mixedMoment B raw34914step0 raw34914step0Labels := by
      have hz : ∀ j, raw34914 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34914step0 = (fun i j => raw34914 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34914step0 raw34914; decide +kernel
      have hl : raw34914step0Labels = raw34914Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34914 raw34914Labels permutation346 hz
    mixedMoment B raw34914step0 raw34914step0Labels = mixedMoment B raw34914step1 raw34914step1Labels := by
      have ha : raw34914step1 = (fun i j => raw34914step0 (permutation57 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34914step1 raw34914step0; decide +kernel
      have hl : raw34914step1Labels = raw34914step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34914step0 raw34914step0Labels permutation57 permutation3
    mixedMoment B raw34914step1 raw34914step1Labels = mixedMoment B raw34914step2 raw34914step2Labels := by
      have ha : raw34914step2 = raw34914step1 := by apply Matrix.ext; unfold raw34914step2 raw34914step1; decide +kernel
      have hl : raw34914step1Labels = labelEmbedding6 ∘ raw34914step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34914step1 raw34914step1Labels raw34914step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4684 node4684Labels := by rfl

def raw34915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34915Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34915step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34915step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34915step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34915step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34915step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34915step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34915 raw34915Labels = mixedMoment B node5336 node5336Labels := by
  calc
    mixedMoment B raw34915 raw34915Labels = mixedMoment B raw34915step0 raw34915step0Labels := by
      have ha : raw34915step0 = (fun i j => raw34915 (permutation588 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34915step0 raw34915; decide +kernel
      have hl : raw34915step0Labels = raw34915Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34915 raw34915Labels permutation588 permutation3
    mixedMoment B raw34915step0 raw34915step0Labels = mixedMoment B raw34915step1 raw34915step1Labels := by
      have ha : raw34915step1 = -raw34915step0 := by apply Matrix.ext; change ∀ i j, raw34915step1 i j = -(raw34915step0 i j); unfold raw34915step1 raw34915step0; decide +kernel
      have hl : raw34915step1Labels = raw34915step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34915step1 raw34915step1Labels = mixedMoment B raw34915step2 raw34915step2Labels := by
      have ha : raw34915step2 = raw34915step1 := by apply Matrix.ext; unfold raw34915step2 raw34915step1; decide +kernel
      have hl : raw34915step1Labels = labelEmbedding6 ∘ raw34915step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34915step1 raw34915step1Labels raw34915step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5336 node5336Labels := by rfl

def raw34916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw34916Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34916step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw34916step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34916step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34916step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34916step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34916step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34916 raw34916Labels = mixedMoment B node5387 node5387Labels := by
  calc
    mixedMoment B raw34916 raw34916Labels = mixedMoment B raw34916step0 raw34916step0Labels := by
      have hz : ∀ j, raw34916 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34916step0 = (fun i j => raw34916 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34916step0 raw34916; decide +kernel
      have hl : raw34916step0Labels = raw34916Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34916 raw34916Labels permutation346 hz
    mixedMoment B raw34916step0 raw34916step0Labels = mixedMoment B raw34916step1 raw34916step1Labels := by
      have ha : raw34916step1 = (fun i j => raw34916step0 (permutation57 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34916step1 raw34916step0; decide +kernel
      have hl : raw34916step1Labels = raw34916step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34916step0 raw34916step0Labels permutation57 permutation3
    mixedMoment B raw34916step1 raw34916step1Labels = mixedMoment B raw34916step2 raw34916step2Labels := by
      have ha : raw34916step2 = raw34916step1 := by apply Matrix.ext; unfold raw34916step2 raw34916step1; decide +kernel
      have hl : raw34916step1Labels = labelEmbedding6 ∘ raw34916step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34916step1 raw34916step1Labels raw34916step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5387 node5387Labels := by rfl

def raw34917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw34917Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw34917step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34917step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-3, 0, 3]]
def raw34917step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34917step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw34917step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34917step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw34917step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34917 raw34917Labels = mixedMoment B node4636 node4636Labels := by
  calc
    mixedMoment B raw34917 raw34917Labels = mixedMoment B raw34917step0 raw34917step0Labels := by
      have hz : ∀ j, raw34917 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34917step0 = (fun i j => raw34917 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34917step0 raw34917; decide +kernel
      have hl : raw34917step0Labels = raw34917Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34917 raw34917Labels permutation346 hz
    mixedMoment B raw34917step0 raw34917step0Labels = mixedMoment B raw34917step1 raw34917step1Labels := by
      have ha : raw34917step1 = (fun i j => raw34917step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34917step1 raw34917step0; decide +kernel
      have hl : raw34917step1Labels = raw34917step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34917step0 raw34917step0Labels permutation126 permutation3
    mixedMoment B raw34917step1 raw34917step1Labels = mixedMoment B raw34917step2 raw34917step2Labels := by
      have ha : raw34917step2 = -raw34917step1 := by apply Matrix.ext; change ∀ i j, raw34917step2 i j = -(raw34917step1 i j); unfold raw34917step2 raw34917step1; decide +kernel
      have hl : raw34917step2Labels = raw34917step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34917step2 raw34917step2Labels = mixedMoment B raw34917step3 raw34917step3Labels := by
      have ha : raw34917step3 = raw34917step2 := by apply Matrix.ext; unfold raw34917step3 raw34917step2; decide +kernel
      have hl : raw34917step2Labels = labelEmbedding6 ∘ raw34917step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34917step2 raw34917step2Labels raw34917step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4636 node4636Labels := by rfl

def raw34918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw34918Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34918step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34918step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34918step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34918step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34918step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34918step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34918 raw34918Labels = mixedMoment B node4634 node4634Labels := by
  calc
    mixedMoment B raw34918 raw34918Labels = mixedMoment B raw34918step0 raw34918step0Labels := by
      have ha : raw34918step0 = (fun i j => raw34918 (permutation588 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34918step0 raw34918; decide +kernel
      have hl : raw34918step0Labels = raw34918Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34918 raw34918Labels permutation588 permutation3
    mixedMoment B raw34918step0 raw34918step0Labels = mixedMoment B raw34918step1 raw34918step1Labels := by
      have ha : raw34918step1 = -raw34918step0 := by apply Matrix.ext; change ∀ i j, raw34918step1 i j = -(raw34918step0 i j); unfold raw34918step1 raw34918step0; decide +kernel
      have hl : raw34918step1Labels = raw34918step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34918step1 raw34918step1Labels = mixedMoment B raw34918step2 raw34918step2Labels := by
      have ha : raw34918step2 = raw34918step1 := by apply Matrix.ext; unfold raw34918step2 raw34918step1; decide +kernel
      have hl : raw34918step1Labels = labelEmbedding6 ∘ raw34918step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34918step1 raw34918step1Labels raw34918step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4634 node4634Labels := by rfl

def raw34919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![-1, 2, -1], ![3, -3, 0], ![2, -1, -1]]
def raw34919Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 2, -1], ![3, -3, 0], ![2, -1, -1]]
def raw34919step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34919step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, -1, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw34919step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34919step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw34919step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34919step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw34919step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34919 raw34919Labels = mixedMoment B node4653 node4653Labels := by
  calc
    mixedMoment B raw34919 raw34919Labels = mixedMoment B raw34919step0 raw34919step0Labels := by
      have hz : ∀ j, raw34919 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34919step0 = (fun i j => raw34919 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34919step0 raw34919; decide +kernel
      have hl : raw34919step0Labels = raw34919Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34919 raw34919Labels permutation346 hz
    mixedMoment B raw34919step0 raw34919step0Labels = mixedMoment B raw34919step1 raw34919step1Labels := by
      have ha : raw34919step1 = (fun i j => raw34919step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34919step1 raw34919step0; decide +kernel
      have hl : raw34919step1Labels = raw34919step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34919step0 raw34919step0Labels permutation126 permutation3
    mixedMoment B raw34919step1 raw34919step1Labels = mixedMoment B raw34919step2 raw34919step2Labels := by
      have ha : raw34919step2 = -raw34919step1 := by apply Matrix.ext; change ∀ i j, raw34919step2 i j = -(raw34919step1 i j); unfold raw34919step2 raw34919step1; decide +kernel
      have hl : raw34919step2Labels = raw34919step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34919step2 raw34919step2Labels = mixedMoment B raw34919step3 raw34919step3Labels := by
      have ha : raw34919step3 = raw34919step2 := by apply Matrix.ext; unfold raw34919step3 raw34919step2; decide +kernel
      have hl : raw34919step2Labels = labelEmbedding6 ∘ raw34919step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34919step2 raw34919step2Labels raw34919step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4653 node4653Labels := by rfl

def raw34920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![1, 0, -1]]
def raw34920Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![3, -3, 0], ![1, 0, -1]]
def raw34920step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34920step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34920step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34920step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34920step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34920step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34920step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34920 raw34920Labels = mixedMoment B node4810 node4810Labels := by
  calc
    mixedMoment B raw34920 raw34920Labels = mixedMoment B raw34920step0 raw34920step0Labels := by
      have hz : ∀ j, raw34920 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34920step0 = (fun i j => raw34920 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34920step0 raw34920; decide +kernel
      have hl : raw34920step0Labels = raw34920Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34920 raw34920Labels permutation346 hz
    mixedMoment B raw34920step0 raw34920step0Labels = mixedMoment B raw34920step1 raw34920step1Labels := by
      have ha : raw34920step1 = (fun i j => raw34920step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34920step1 raw34920step0; decide +kernel
      have hl : raw34920step1Labels = raw34920step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34920step0 raw34920step0Labels permutation126 permutation3
    mixedMoment B raw34920step1 raw34920step1Labels = mixedMoment B raw34920step2 raw34920step2Labels := by
      have ha : raw34920step2 = -raw34920step1 := by apply Matrix.ext; change ∀ i j, raw34920step2 i j = -(raw34920step1 i j); unfold raw34920step2 raw34920step1; decide +kernel
      have hl : raw34920step2Labels = raw34920step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34920step2 raw34920step2Labels = mixedMoment B raw34920step3 raw34920step3Labels := by
      have ha : raw34920step3 = raw34920step2 := by apply Matrix.ext; unfold raw34920step3 raw34920step2; decide +kernel
      have hl : raw34920step2Labels = labelEmbedding6 ∘ raw34920step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34920step2 raw34920step2Labels raw34920step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4810 node4810Labels := by rfl

def raw34921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw34921Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw34921step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34921step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw34921step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34921step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw34921step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34921 raw34921Labels = mixedMoment B node4662 node4662Labels := by
  calc
    mixedMoment B raw34921 raw34921Labels = mixedMoment B raw34921step0 raw34921step0Labels := by
      have hz : ∀ j, raw34921 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34921step0 = (fun i j => raw34921 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34921step0 raw34921; decide +kernel
      have hl : raw34921step0Labels = raw34921Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34921 raw34921Labels permutation346 hz
    mixedMoment B raw34921step0 raw34921step0Labels = mixedMoment B raw34921step1 raw34921step1Labels := by
      have ha : raw34921step1 = (fun i j => raw34921step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34921step1 raw34921step0; decide +kernel
      have hl : raw34921step1Labels = raw34921step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34921step0 raw34921step0Labels permutation56 permutation3
    mixedMoment B raw34921step1 raw34921step1Labels = mixedMoment B raw34921step2 raw34921step2Labels := by
      have ha : raw34921step2 = raw34921step1 := by apply Matrix.ext; unfold raw34921step2 raw34921step1; decide +kernel
      have hl : raw34921step1Labels = labelEmbedding6 ∘ raw34921step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34921step1 raw34921step1Labels raw34921step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4662 node4662Labels := by rfl

def raw34922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw34922Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34922step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34922step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34922step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34922step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34922step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34922step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34922 raw34922Labels = mixedMoment B node4905 node4905Labels := by
  calc
    mixedMoment B raw34922 raw34922Labels = mixedMoment B raw34922step0 raw34922step0Labels := by
      have ha : raw34922step0 = (fun i j => raw34922 (permutation687 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34922step0 raw34922; decide +kernel
      have hl : raw34922step0Labels = raw34922Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34922 raw34922Labels permutation687 permutation3
    mixedMoment B raw34922step0 raw34922step0Labels = mixedMoment B raw34922step1 raw34922step1Labels := by
      have ha : raw34922step1 = -raw34922step0 := by apply Matrix.ext; change ∀ i j, raw34922step1 i j = -(raw34922step0 i j); unfold raw34922step1 raw34922step0; decide +kernel
      have hl : raw34922step1Labels = raw34922step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34922step1 raw34922step1Labels = mixedMoment B raw34922step2 raw34922step2Labels := by
      have ha : raw34922step2 = raw34922step1 := by apply Matrix.ext; unfold raw34922step2 raw34922step1; decide +kernel
      have hl : raw34922step1Labels = labelEmbedding6 ∘ raw34922step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34922step1 raw34922step1Labels raw34922step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4905 node4905Labels := by rfl

def raw34923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -2, -1]]
def raw34923Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -2, -1]]
def raw34923step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34923step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-1, -1, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw34923step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34923step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw34923step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw34923step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw34923step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34923 raw34923Labels = mixedMoment B node4922 node4922Labels := by
  calc
    mixedMoment B raw34923 raw34923Labels = mixedMoment B raw34923step0 raw34923step0Labels := by
      have hz : ∀ j, raw34923 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34923step0 = (fun i j => raw34923 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34923step0 raw34923; decide +kernel
      have hl : raw34923step0Labels = raw34923Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34923 raw34923Labels permutation346 hz
    mixedMoment B raw34923step0 raw34923step0Labels = mixedMoment B raw34923step1 raw34923step1Labels := by
      have ha : raw34923step1 = (fun i j => raw34923step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34923step1 raw34923step0; decide +kernel
      have hl : raw34923step1Labels = raw34923step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34923step0 raw34923step0Labels permutation150 permutation3
    mixedMoment B raw34923step1 raw34923step1Labels = mixedMoment B raw34923step2 raw34923step2Labels := by
      have ha : raw34923step2 = -raw34923step1 := by apply Matrix.ext; change ∀ i j, raw34923step2 i j = -(raw34923step1 i j); unfold raw34923step2 raw34923step1; decide +kernel
      have hl : raw34923step2Labels = raw34923step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw34923step2 raw34923step2Labels = mixedMoment B raw34923step3 raw34923step3Labels := by
      have ha : raw34923step3 = raw34923step2 := by apply Matrix.ext; unfold raw34923step3 raw34923step2; decide +kernel
      have hl : raw34923step2Labels = labelEmbedding6 ∘ raw34923step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw34923step2 raw34923step2Labels raw34923step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4922 node4922Labels := by rfl

def raw34924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34924Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34924step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34924step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34924step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw34924step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34924 raw34924Labels = mixedMoment B node2082 node2082Labels := by
  calc
    mixedMoment B raw34924 raw34924Labels = mixedMoment B raw34924step0 raw34924step0Labels := by
      have hz : ∀ j, raw34924 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34924step0 = (fun i j => raw34924 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34924step0 raw34924; decide +kernel
      have hl : raw34924step0Labels = raw34924Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34924 raw34924Labels permutation346 hz
    mixedMoment B raw34924step0 raw34924step0Labels = mixedMoment B raw34924step1 raw34924step1Labels := by
      have ha : raw34924step1 = (fun i j => raw34924step0 (permutation57 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34924step1 raw34924step0; decide +kernel
      have hl : raw34924step1Labels = raw34924step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34924step0 raw34924step0Labels permutation57 permutation3
    _ = mixedMoment B node2082 node2082Labels := by rfl

def raw34925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34925Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34925step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw34925step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34925step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw34925step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34925 raw34925Labels = mixedMoment B node3687 node3687Labels := by
  calc
    mixedMoment B raw34925 raw34925Labels = mixedMoment B raw34925step0 raw34925step0Labels := by
      have ha : raw34925step0 = (fun i j => raw34925 (permutation585 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34925step0 raw34925; decide +kernel
      have hl : raw34925step0Labels = raw34925Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34925 raw34925Labels permutation585 permutation3
    mixedMoment B raw34925step0 raw34925step0Labels = mixedMoment B raw34925step1 raw34925step1Labels := by
      have ha : raw34925step1 = -raw34925step0 := by apply Matrix.ext; change ∀ i j, raw34925step1 i j = -(raw34925step0 i j); unfold raw34925step1 raw34925step0; decide +kernel
      have hl : raw34925step1Labels = raw34925step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3687 node3687Labels := by rfl

def raw34926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34926Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34926step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34926step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw34926step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34926step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw34926step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34926 raw34926Labels = mixedMoment B node3702 node3702Labels := by
  calc
    mixedMoment B raw34926 raw34926Labels = mixedMoment B raw34926step0 raw34926step0Labels := by
      have hz : ∀ j, raw34926 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34926step0 = (fun i j => raw34926 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34926step0 raw34926; decide +kernel
      have hl : raw34926step0Labels = raw34926Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34926 raw34926Labels permutation346 hz
    mixedMoment B raw34926step0 raw34926step0Labels = mixedMoment B raw34926step1 raw34926step1Labels := by
      have ha : raw34926step1 = (fun i j => raw34926step0 (permutation123 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34926step1 raw34926step0; decide +kernel
      have hl : raw34926step1Labels = raw34926step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34926step0 raw34926step0Labels permutation123 permutation3
    mixedMoment B raw34926step1 raw34926step1Labels = mixedMoment B raw34926step2 raw34926step2Labels := by
      have ha : raw34926step2 = -raw34926step1 := by apply Matrix.ext; change ∀ i j, raw34926step2 i j = -(raw34926step1 i j); unfold raw34926step2 raw34926step1; decide +kernel
      have hl : raw34926step2Labels = raw34926step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3702 node3702Labels := by rfl

def raw34927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw34927Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw34927step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34927step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw34927step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34927step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw34927step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34927 raw34927Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw34927 raw34927Labels = mixedMoment B raw34927step0 raw34927step0Labels := by
      have hz : ∀ j, raw34927 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34927step0 = (fun i j => raw34927 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34927step0 raw34927; decide +kernel
      have hl : raw34927step0Labels = raw34927Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34927 raw34927Labels permutation346 hz
    mixedMoment B raw34927step0 raw34927step0Labels = mixedMoment B raw34927step1 raw34927step1Labels := by
      have ha : raw34927step1 = (fun i j => raw34927step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34927step1 raw34927step0; decide +kernel
      have hl : raw34927step1Labels = raw34927step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34927step0 raw34927step0Labels permutation126 permutation3
    mixedMoment B raw34927step1 raw34927step1Labels = mixedMoment B raw34927step2 raw34927step2Labels := by
      have ha : raw34927step2 = -raw34927step1 := by apply Matrix.ext; change ∀ i j, raw34927step2 i j = -(raw34927step1 i j); unfold raw34927step2 raw34927step1; decide +kernel
      have hl : raw34927step2Labels = raw34927step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3850 node3850Labels := by rfl

def raw34928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34928Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34928step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw34928step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34928 raw34928Labels = mixedMoment B node1787 node1787Labels := by
  calc
    mixedMoment B raw34928 raw34928Labels = mixedMoment B raw34928step0 raw34928step0Labels := by
      have ha : raw34928step0 = (fun i j => raw34928 (permutation272 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34928step0 raw34928; decide +kernel
      have hl : raw34928step0Labels = raw34928Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34928 raw34928Labels permutation272 permutation3
    _ = mixedMoment B node1787 node1787Labels := by rfl

def raw34929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34929Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34929step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, 0, -1], ![-1, -1, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw34929step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34929step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw34929step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34929 raw34929Labels = mixedMoment B node3668 node3668Labels := by
  calc
    mixedMoment B raw34929 raw34929Labels = mixedMoment B raw34929step0 raw34929step0Labels := by
      have ha : raw34929step0 = (fun i j => raw34929 (permutation583 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34929step0 raw34929; decide +kernel
      have hl : raw34929step0Labels = raw34929Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34929 raw34929Labels permutation583 permutation3
    mixedMoment B raw34929step0 raw34929step0Labels = mixedMoment B raw34929step1 raw34929step1Labels := by
      have ha : raw34929step1 = -raw34929step0 := by apply Matrix.ext; change ∀ i j, raw34929step1 i j = -(raw34929step0 i j); unfold raw34929step1 raw34929step0; decide +kernel
      have hl : raw34929step1Labels = raw34929step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3668 node3668Labels := by rfl

def raw34930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw34930Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34930step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34930step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34930 raw34930Labels = mixedMoment B node3719 node3719Labels := by
  calc
    mixedMoment B raw34930 raw34930Labels = mixedMoment B raw34930step0 raw34930step0Labels := by
      have ha : raw34930step0 = (fun i j => raw34930 (permutation275 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34930step0 raw34930; decide +kernel
      have hl : raw34930step0Labels = raw34930Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34930 raw34930Labels permutation275 permutation3
    _ = mixedMoment B node3719 node3719Labels := by rfl

def raw34931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34931Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34931step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34931step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw34931step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34931 raw34931Labels = mixedMoment B node1810 node1810Labels := by
  calc
    mixedMoment B raw34931 raw34931Labels = mixedMoment B raw34931step0 raw34931step0Labels := by
      have hz : ∀ j, raw34931 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34931step0 = (fun i j => raw34931 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34931step0 raw34931; decide +kernel
      have hl : raw34931step0Labels = raw34931Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34931 raw34931Labels permutation346 hz
    mixedMoment B raw34931step0 raw34931step0Labels = mixedMoment B raw34931step1 raw34931step1Labels := by
      have ha : raw34931step1 = (fun i j => raw34931step0 (permutation57 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34931step1 raw34931step0; decide +kernel
      have hl : raw34931step1Labels = raw34931step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34931step0 raw34931step0Labels permutation57 permutation3
    _ = mixedMoment B node1810 node1810Labels := by rfl

def raw34932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw34932Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34932step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34932step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34932step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34932step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34932 raw34932Labels = mixedMoment B node3671 node3671Labels := by
  calc
    mixedMoment B raw34932 raw34932Labels = mixedMoment B raw34932step0 raw34932step0Labels := by
      have ha : raw34932step0 = (fun i j => raw34932 (permutation588 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34932step0 raw34932; decide +kernel
      have hl : raw34932step0Labels = raw34932Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34932 raw34932Labels permutation588 permutation3
    mixedMoment B raw34932step0 raw34932step0Labels = mixedMoment B raw34932step1 raw34932step1Labels := by
      have ha : raw34932step1 = -raw34932step0 := by apply Matrix.ext; change ∀ i j, raw34932step1 i j = -(raw34932step0 i j); unfold raw34932step1 raw34932step0; decide +kernel
      have hl : raw34932step1Labels = raw34932step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3671 node3671Labels := by rfl

def raw34933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw34933Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw34933step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34933step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34933step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34933 raw34933Labels = mixedMoment B node3736 node3736Labels := by
  calc
    mixedMoment B raw34933 raw34933Labels = mixedMoment B raw34933step0 raw34933step0Labels := by
      have hz : ∀ j, raw34933 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34933step0 = (fun i j => raw34933 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34933step0 raw34933; decide +kernel
      have hl : raw34933step0Labels = raw34933Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34933 raw34933Labels permutation346 hz
    mixedMoment B raw34933step0 raw34933step0Labels = mixedMoment B raw34933step1 raw34933step1Labels := by
      have ha : raw34933step1 = (fun i j => raw34933step0 (permutation57 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34933step1 raw34933step0; decide +kernel
      have hl : raw34933step1Labels = raw34933step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34933step0 raw34933step0Labels permutation57 permutation3
    _ = mixedMoment B node3736 node3736Labels := by rfl

def raw34934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw34934Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw34934step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34934step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-3, 0, 3]]
def raw34934step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34934step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw34934step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34934 raw34934Labels = mixedMoment B node1765 node1765Labels := by
  calc
    mixedMoment B raw34934 raw34934Labels = mixedMoment B raw34934step0 raw34934step0Labels := by
      have hz : ∀ j, raw34934 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34934step0 = (fun i j => raw34934 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34934step0 raw34934; decide +kernel
      have hl : raw34934step0Labels = raw34934Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34934 raw34934Labels permutation346 hz
    mixedMoment B raw34934step0 raw34934step0Labels = mixedMoment B raw34934step1 raw34934step1Labels := by
      have ha : raw34934step1 = (fun i j => raw34934step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34934step1 raw34934step0; decide +kernel
      have hl : raw34934step1Labels = raw34934step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34934step0 raw34934step0Labels permutation126 permutation3
    mixedMoment B raw34934step1 raw34934step1Labels = mixedMoment B raw34934step2 raw34934step2Labels := by
      have ha : raw34934step2 = -raw34934step1 := by apply Matrix.ext; change ∀ i j, raw34934step2 i j = -(raw34934step1 i j); unfold raw34934step2 raw34934step1; decide +kernel
      have hl : raw34934step2Labels = raw34934step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1765 node1765Labels := by rfl

def raw34935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![0, 1, -1], ![3, -3, 0], ![2, -1, -1]]
def raw34935Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34935step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34935step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34935step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34935step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34935 raw34935Labels = mixedMoment B node1763 node1763Labels := by
  calc
    mixedMoment B raw34935 raw34935Labels = mixedMoment B raw34935step0 raw34935step0Labels := by
      have ha : raw34935step0 = (fun i j => raw34935 (permutation588 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34935step0 raw34935; decide +kernel
      have hl : raw34935step0Labels = raw34935Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34935 raw34935Labels permutation588 permutation3
    mixedMoment B raw34935step0 raw34935step0Labels = mixedMoment B raw34935step1 raw34935step1Labels := by
      have ha : raw34935step1 = -raw34935step0 := by apply Matrix.ext; change ∀ i j, raw34935step1 i j = -(raw34935step0 i j); unfold raw34935step1 raw34935step0; decide +kernel
      have hl : raw34935step1Labels = raw34935step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1763 node1763Labels := by rfl

def raw34936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![-1, 2, -1], ![3, -3, 0], ![2, -1, -1]]
def raw34936Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 2, -1], ![3, -3, 0], ![2, -1, -1]]
def raw34936step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34936step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, -1, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw34936step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34936step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw34936step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34936 raw34936Labels = mixedMoment B node1781 node1781Labels := by
  calc
    mixedMoment B raw34936 raw34936Labels = mixedMoment B raw34936step0 raw34936step0Labels := by
      have hz : ∀ j, raw34936 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34936step0 = (fun i j => raw34936 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34936step0 raw34936; decide +kernel
      have hl : raw34936step0Labels = raw34936Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34936 raw34936Labels permutation346 hz
    mixedMoment B raw34936step0 raw34936step0Labels = mixedMoment B raw34936step1 raw34936step1Labels := by
      have ha : raw34936step1 = (fun i j => raw34936step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34936step1 raw34936step0; decide +kernel
      have hl : raw34936step1Labels = raw34936step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34936step0 raw34936step0Labels permutation126 permutation3
    mixedMoment B raw34936step1 raw34936step1Labels = mixedMoment B raw34936step2 raw34936step2Labels := by
      have ha : raw34936step2 = -raw34936step1 := by apply Matrix.ext; change ∀ i j, raw34936step2 i j = -(raw34936step1 i j); unfold raw34936step2 raw34936step1; decide +kernel
      have hl : raw34936step2Labels = raw34936step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1781 node1781Labels := by rfl

def raw34937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 1, -1], ![3, -3, 0], ![1, 0, -1]]
def raw34937Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![3, -3, 0], ![1, 0, -1]]
def raw34937step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34937step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34937step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34937step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34937step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34937 raw34937Labels = mixedMoment B node2028 node2028Labels := by
  calc
    mixedMoment B raw34937 raw34937Labels = mixedMoment B raw34937step0 raw34937step0Labels := by
      have hz : ∀ j, raw34937 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34937step0 = (fun i j => raw34937 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34937step0 raw34937; decide +kernel
      have hl : raw34937step0Labels = raw34937Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34937 raw34937Labels permutation346 hz
    mixedMoment B raw34937step0 raw34937step0Labels = mixedMoment B raw34937step1 raw34937step1Labels := by
      have ha : raw34937step1 = (fun i j => raw34937step0 (permutation126 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34937step1 raw34937step0; decide +kernel
      have hl : raw34937step1Labels = raw34937step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34937step0 raw34937step0Labels permutation126 permutation3
    mixedMoment B raw34937step1 raw34937step1Labels = mixedMoment B raw34937step2 raw34937step2Labels := by
      have ha : raw34937step2 = -raw34937step1 := by apply Matrix.ext; change ∀ i j, raw34937step2 i j = -(raw34937step1 i j); unfold raw34937step2 raw34937step1; decide +kernel
      have hl : raw34937step2Labels = raw34937step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2028 node2028Labels := by rfl

def raw34938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw34938Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw34938step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34938step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw34938step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34938 raw34938Labels = mixedMoment B node1788 node1788Labels := by
  calc
    mixedMoment B raw34938 raw34938Labels = mixedMoment B raw34938step0 raw34938step0Labels := by
      have hz : ∀ j, raw34938 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34938step0 = (fun i j => raw34938 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34938step0 raw34938; decide +kernel
      have hl : raw34938step0Labels = raw34938Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34938 raw34938Labels permutation346 hz
    mixedMoment B raw34938step0 raw34938step0Labels = mixedMoment B raw34938step1 raw34938step1Labels := by
      have ha : raw34938step1 = (fun i j => raw34938step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34938step1 raw34938step0; decide +kernel
      have hl : raw34938step1Labels = raw34938step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34938step0 raw34938step0Labels permutation56 permutation3
    _ = mixedMoment B node1788 node1788Labels := by rfl

def raw34939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -2, -1]]
def raw34939Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34939step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw34939step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34939step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw34939step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34939 raw34939Labels = mixedMoment B node2298 node2298Labels := by
  calc
    mixedMoment B raw34939 raw34939Labels = mixedMoment B raw34939step0 raw34939step0Labels := by
      have ha : raw34939step0 = (fun i j => raw34939 (permutation687 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34939step0 raw34939; decide +kernel
      have hl : raw34939step0Labels = raw34939Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34939 raw34939Labels permutation687 permutation3
    mixedMoment B raw34939step0 raw34939step0Labels = mixedMoment B raw34939step1 raw34939step1Labels := by
      have ha : raw34939step1 = -raw34939step0 := by apply Matrix.ext; change ∀ i j, raw34939step1 i j = -(raw34939step0 i j); unfold raw34939step1 raw34939step0; decide +kernel
      have hl : raw34939step1Labels = raw34939step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2298 node2298Labels := by rfl

def raw34940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -2, -1]]
def raw34940Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -2, -1]]
def raw34940step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw34940step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, 0, -2], ![-1, -1, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw34940step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw34940step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw34940step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical34940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34940 raw34940Labels = mixedMoment B node2313 node2313Labels := by
  calc
    mixedMoment B raw34940 raw34940Labels = mixedMoment B raw34940step0 raw34940step0Labels := by
      have hz : ∀ j, raw34940 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34940step0 = (fun i j => raw34940 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34940step0 raw34940; decide +kernel
      have hl : raw34940step0Labels = raw34940Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34940 raw34940Labels permutation346 hz
    mixedMoment B raw34940step0 raw34940step0Labels = mixedMoment B raw34940step1 raw34940step1Labels := by
      have ha : raw34940step1 = (fun i j => raw34940step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw34940step1 raw34940step0; decide +kernel
      have hl : raw34940step1Labels = raw34940step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34940step0 raw34940step0Labels permutation150 permutation3
    mixedMoment B raw34940step1 raw34940step1Labels = mixedMoment B raw34940step2 raw34940step2Labels := by
      have ha : raw34940step2 = -raw34940step1 := by apply Matrix.ext; change ∀ i j, raw34940step2 i j = -(raw34940step1 i j); unfold raw34940step2 raw34940step1; decide +kernel
      have hl : raw34940step2Labels = raw34940step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2313 node2313Labels := by rfl

def raw34941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34941Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 1, 2], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34941step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34941step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw34941step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34941 raw34941Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw34941 raw34941Labels = mixedMoment B raw34941step0 raw34941step0Labels := by
      have hz : ∀ j, raw34941 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34941step0 = (fun i j => raw34941 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34941step0 raw34941; decide +kernel
      have hl : raw34941step0Labels = raw34941Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34941 raw34941Labels permutation346 hz
    mixedMoment B raw34941step0 raw34941step0Labels = mixedMoment B raw34941step1 raw34941step1Labels := by
      have ha : raw34941step1 = (fun i j => raw34941step0 (permutation57 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34941step1 raw34941step0; decide +kernel
      have hl : raw34941step1Labels = raw34941step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34941step0 raw34941step0Labels permutation57 permutation2
    _ = mixedMoment B node5141 node5141Labels := by rfl

def raw34942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34942Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34942step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw34942step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34942step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw34942step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34942 raw34942Labels = mixedMoment B node5351 node5351Labels := by
  calc
    mixedMoment B raw34942 raw34942Labels = mixedMoment B raw34942step0 raw34942step0Labels := by
      have ha : raw34942step0 = (fun i j => raw34942 (permutation585 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34942step0 raw34942; decide +kernel
      have hl : raw34942step0Labels = raw34942Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34942 raw34942Labels permutation585 permutation2
    mixedMoment B raw34942step0 raw34942step0Labels = mixedMoment B raw34942step1 raw34942step1Labels := by
      have ha : raw34942step1 = -raw34942step0 := by apply Matrix.ext; change ∀ i j, raw34942step1 i j = -(raw34942step0 i j); unfold raw34942step1 raw34942step0; decide +kernel
      have hl : raw34942step1Labels = raw34942step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5351 node5351Labels := by rfl

def raw34943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34943Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw34943step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34943step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw34943step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw34943step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw34943step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical34943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw34943 raw34943Labels = mixedMoment B node5367 node5367Labels := by
  calc
    mixedMoment B raw34943 raw34943Labels = mixedMoment B raw34943step0 raw34943step0Labels := by
      have hz : ∀ j, raw34943 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw34943step0 = (fun i j => raw34943 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw34943step0 raw34943; decide +kernel
      have hl : raw34943step0Labels = raw34943Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw34943 raw34943Labels permutation346 hz
    mixedMoment B raw34943step0 raw34943step0Labels = mixedMoment B raw34943step1 raw34943step1Labels := by
      have ha : raw34943step1 = (fun i j => raw34943step0 (permutation123 i) (permutation2 j)) := by apply Matrix.ext; unfold raw34943step1 raw34943step0; decide +kernel
      have hl : raw34943step1Labels = raw34943step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw34943step0 raw34943step0Labels permutation123 permutation2
    mixedMoment B raw34943step1 raw34943step1Labels = mixedMoment B raw34943step2 raw34943step2Labels := by
      have ha : raw34943step2 = -raw34943step1 := by apply Matrix.ext; change ∀ i j, raw34943step2 i j = -(raw34943step1 i j); unfold raw34943step2 raw34943step1; decide +kernel
      have hl : raw34943step2Labels = raw34943step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5367 node5367Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
