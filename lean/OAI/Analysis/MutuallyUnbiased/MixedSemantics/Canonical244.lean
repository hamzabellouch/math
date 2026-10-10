import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw31232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31232Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31232step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31232step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31232step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31232 raw31232Labels = mixedMoment B node1880 node1880Labels := by
  calc
    mixedMoment B raw31232 raw31232Labels = mixedMoment B raw31232step0 raw31232step0Labels := by
      have hz : ∀ j, raw31232 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31232step0 = (fun i j => raw31232 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31232step0 raw31232; decide +kernel
      have hl : raw31232step0Labels = raw31232Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31232 raw31232Labels permutation434 hz
    mixedMoment B raw31232step0 raw31232step0Labels = mixedMoment B raw31232step1 raw31232step1Labels := by
      have ha : raw31232step1 = (fun i j => raw31232step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31232step1 raw31232step0; decide +kernel
      have hl : raw31232step1Labels = raw31232step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31232step0 raw31232step0Labels permutation38 permutation3
    _ = mixedMoment B node1880 node1880Labels := by rfl

def raw31233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31233Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw31233step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31233step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31233step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31233 raw31233Labels = mixedMoment B node1880 node1880Labels := by
  calc
    mixedMoment B raw31233 raw31233Labels = mixedMoment B raw31233step0 raw31233step0Labels := by
      have hz : ∀ j, raw31233 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31233step0 = (fun i j => raw31233 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31233step0 raw31233; decide +kernel
      have hl : raw31233step0Labels = raw31233Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31233 raw31233Labels permutation346 hz
    mixedMoment B raw31233step0 raw31233step0Labels = mixedMoment B raw31233step1 raw31233step1Labels := by
      have ha : raw31233step1 = (fun i j => raw31233step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31233step1 raw31233step0; decide +kernel
      have hl : raw31233step1Labels = raw31233step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31233step0 raw31233step0Labels permutation38 permutation3
    _ = mixedMoment B node1880 node1880Labels := by rfl

def raw31234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31234Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -2, -1], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31234step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31234step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw31234step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31234step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, -1, 2], ![-1, -1, 2], ![-2, 3, -1]]
def raw31234step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31234step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def raw31234step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31234step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def raw31234step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31234 raw31234Labels = mixedMoment B node4506 node4506Labels := by
  calc
    mixedMoment B raw31234 raw31234Labels = mixedMoment B raw31234step0 raw31234step0Labels := by
      have hz : ∀ j, raw31234 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31234step0 = (fun i j => raw31234 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31234step0 raw31234; decide +kernel
      have hl : raw31234step0Labels = raw31234Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31234 raw31234Labels permutation434 hz
    mixedMoment B raw31234step0 raw31234step0Labels = mixedMoment B raw31234step1 raw31234step1Labels := by
      have hz : ∀ j, raw31234step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31234step1 = (fun i j => raw31234step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31234step1 raw31234step0; decide +kernel
      have hl : raw31234step1Labels = raw31234step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31234step0 raw31234step0Labels permutation80 hz
    mixedMoment B raw31234step1 raw31234step1Labels = mixedMoment B raw31234step2 raw31234step2Labels := by
      have ha : raw31234step2 = (fun i j => raw31234step1 (permutation11 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31234step2 raw31234step1; decide +kernel
      have hl : raw31234step2Labels = raw31234step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31234step1 raw31234step1Labels permutation11 permutation4
    mixedMoment B raw31234step2 raw31234step2Labels = mixedMoment B raw31234step3 raw31234step3Labels := by
      have ha : raw31234step3 = -raw31234step2 := by apply Matrix.ext; change ∀ i j, raw31234step3 i j = -(raw31234step2 i j); unfold raw31234step3 raw31234step2; decide +kernel
      have hl : raw31234step3Labels = raw31234step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31234step3 raw31234step3Labels = mixedMoment B raw31234step4 raw31234step4Labels := by
      have ha : raw31234step4 = raw31234step3 := by apply Matrix.ext; unfold raw31234step4 raw31234step3; decide +kernel
      have hl : raw31234step3Labels = labelEmbedding7 ∘ raw31234step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31234step3 raw31234step3Labels raw31234step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4506 node4506Labels := by rfl

def raw31235 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31235Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31235step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31235step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2], ![-2, 3, -1]]
def raw31235step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31235step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def raw31235step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31235step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def raw31235step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31235 raw31235Labels = mixedMoment B node4842 node4842Labels := by
  calc
    mixedMoment B raw31235 raw31235Labels = mixedMoment B raw31235step0 raw31235step0Labels := by
      have hz : ∀ j, raw31235 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31235step0 = (fun i j => raw31235 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31235step0 raw31235; decide +kernel
      have hl : raw31235step0Labels = raw31235Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31235 raw31235Labels permutation434 hz
    mixedMoment B raw31235step0 raw31235step0Labels = mixedMoment B raw31235step1 raw31235step1Labels := by
      have ha : raw31235step1 = (fun i j => raw31235step0 (permutation41 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31235step1 raw31235step0; decide +kernel
      have hl : raw31235step1Labels = raw31235step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31235step0 raw31235step0Labels permutation41 permutation4
    mixedMoment B raw31235step1 raw31235step1Labels = mixedMoment B raw31235step2 raw31235step2Labels := by
      have ha : raw31235step2 = -raw31235step1 := by apply Matrix.ext; change ∀ i j, raw31235step2 i j = -(raw31235step1 i j); unfold raw31235step2 raw31235step1; decide +kernel
      have hl : raw31235step2Labels = raw31235step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31235step2 raw31235step2Labels = mixedMoment B raw31235step3 raw31235step3Labels := by
      have ha : raw31235step3 = raw31235step2 := by apply Matrix.ext; unfold raw31235step3 raw31235step2; decide +kernel
      have hl : raw31235step2Labels = labelEmbedding7 ∘ raw31235step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31235step2 raw31235step2Labels raw31235step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4842 node4842Labels := by rfl

def raw31236 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31236Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31236step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31236step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31236step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2], ![-2, 3, -1]]
def raw31236step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31236step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def raw31236step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31236step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![1, 1, -2], ![2, -3, 1]]
def raw31236step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31236 raw31236Labels = mixedMoment B node4842 node4842Labels := by
  calc
    mixedMoment B raw31236 raw31236Labels = mixedMoment B raw31236step0 raw31236step0Labels := by
      have hz : ∀ j, raw31236 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31236step0 = (fun i j => raw31236 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31236step0 raw31236; decide +kernel
      have hl : raw31236step0Labels = raw31236Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31236 raw31236Labels permutation346 hz
    mixedMoment B raw31236step0 raw31236step0Labels = mixedMoment B raw31236step1 raw31236step1Labels := by
      have ha : raw31236step1 = (fun i j => raw31236step0 (permutation41 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31236step1 raw31236step0; decide +kernel
      have hl : raw31236step1Labels = raw31236step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31236step0 raw31236step0Labels permutation41 permutation4
    mixedMoment B raw31236step1 raw31236step1Labels = mixedMoment B raw31236step2 raw31236step2Labels := by
      have ha : raw31236step2 = -raw31236step1 := by apply Matrix.ext; change ∀ i j, raw31236step2 i j = -(raw31236step1 i j); unfold raw31236step2 raw31236step1; decide +kernel
      have hl : raw31236step2Labels = raw31236step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31236step2 raw31236step2Labels = mixedMoment B raw31236step3 raw31236step3Labels := by
      have ha : raw31236step3 = raw31236step2 := by apply Matrix.ext; unfold raw31236step3 raw31236step2; decide +kernel
      have hl : raw31236step2Labels = labelEmbedding7 ∘ raw31236step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31236step2 raw31236step2Labels raw31236step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4842 node4842Labels := by rfl

def raw31237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31237Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31237step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31237step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31237step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31237step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw31237step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31237step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw31237step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31237 raw31237Labels = mixedMoment B node4487 node4487Labels := by
  calc
    mixedMoment B raw31237 raw31237Labels = mixedMoment B raw31237step0 raw31237step0Labels := by
      have hz : ∀ j, raw31237 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31237step0 = (fun i j => raw31237 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31237step0 raw31237; decide +kernel
      have hl : raw31237step0Labels = raw31237Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31237 raw31237Labels permutation434 hz
    mixedMoment B raw31237step0 raw31237step0Labels = mixedMoment B raw31237step1 raw31237step1Labels := by
      have ha : raw31237step1 = (fun i j => raw31237step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31237step1 raw31237step0; decide +kernel
      have hl : raw31237step1Labels = raw31237step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31237step0 raw31237step0Labels permutation32 permutation4
    mixedMoment B raw31237step1 raw31237step1Labels = mixedMoment B raw31237step2 raw31237step2Labels := by
      have ha : raw31237step2 = -raw31237step1 := by apply Matrix.ext; change ∀ i j, raw31237step2 i j = -(raw31237step1 i j); unfold raw31237step2 raw31237step1; decide +kernel
      have hl : raw31237step2Labels = raw31237step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31237step2 raw31237step2Labels = mixedMoment B raw31237step3 raw31237step3Labels := by
      have ha : raw31237step3 = raw31237step2 := by apply Matrix.ext; unfold raw31237step3 raw31237step2; decide +kernel
      have hl : raw31237step2Labels = labelEmbedding7 ∘ raw31237step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31237step2 raw31237step2Labels raw31237step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4487 node4487Labels := by rfl

def raw31238 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31238Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31238step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31238step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31238step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw31238step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31238step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw31238step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31238 raw31238Labels = mixedMoment B node4825 node4825Labels := by
  calc
    mixedMoment B raw31238 raw31238Labels = mixedMoment B raw31238step0 raw31238step0Labels := by
      have ha : raw31238step0 = (fun i j => raw31238 (permutation200 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31238step0 raw31238; decide +kernel
      have hl : raw31238step0Labels = raw31238Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31238 raw31238Labels permutation200 permutation4
    mixedMoment B raw31238step0 raw31238step0Labels = mixedMoment B raw31238step1 raw31238step1Labels := by
      have ha : raw31238step1 = -raw31238step0 := by apply Matrix.ext; change ∀ i j, raw31238step1 i j = -(raw31238step0 i j); unfold raw31238step1 raw31238step0; decide +kernel
      have hl : raw31238step1Labels = raw31238step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31238step1 raw31238step1Labels = mixedMoment B raw31238step2 raw31238step2Labels := by
      have ha : raw31238step2 = raw31238step1 := by apply Matrix.ext; unfold raw31238step2 raw31238step1; decide +kernel
      have hl : raw31238step1Labels = labelEmbedding7 ∘ raw31238step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31238step1 raw31238step1Labels raw31238step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4825 node4825Labels := by rfl

def raw31239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31239Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31239step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31239step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31239step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31239step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31239step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw31239step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31239step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw31239step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31239 raw31239Labels = mixedMoment B node4487 node4487Labels := by
  calc
    mixedMoment B raw31239 raw31239Labels = mixedMoment B raw31239step0 raw31239step0Labels := by
      have hz : ∀ j, raw31239 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31239step0 = (fun i j => raw31239 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31239step0 raw31239; decide +kernel
      have hl : raw31239step0Labels = raw31239Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31239 raw31239Labels permutation346 hz
    mixedMoment B raw31239step0 raw31239step0Labels = mixedMoment B raw31239step1 raw31239step1Labels := by
      have ha : raw31239step1 = (fun i j => raw31239step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31239step1 raw31239step0; decide +kernel
      have hl : raw31239step1Labels = raw31239step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31239step0 raw31239step0Labels permutation32 permutation4
    mixedMoment B raw31239step1 raw31239step1Labels = mixedMoment B raw31239step2 raw31239step2Labels := by
      have ha : raw31239step2 = -raw31239step1 := by apply Matrix.ext; change ∀ i j, raw31239step2 i j = -(raw31239step1 i j); unfold raw31239step2 raw31239step1; decide +kernel
      have hl : raw31239step2Labels = raw31239step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31239step2 raw31239step2Labels = mixedMoment B raw31239step3 raw31239step3Labels := by
      have ha : raw31239step3 = raw31239step2 := by apply Matrix.ext; unfold raw31239step3 raw31239step2; decide +kernel
      have hl : raw31239step2Labels = labelEmbedding7 ∘ raw31239step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31239step2 raw31239step2Labels raw31239step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4487 node4487Labels := by rfl

def raw31240 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31240Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31240step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31240step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31240step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw31240step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31240step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw31240step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31240 raw31240Labels = mixedMoment B node4825 node4825Labels := by
  calc
    mixedMoment B raw31240 raw31240Labels = mixedMoment B raw31240step0 raw31240step0Labels := by
      have ha : raw31240step0 = (fun i j => raw31240 (permutation176 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31240step0 raw31240; decide +kernel
      have hl : raw31240step0Labels = raw31240Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31240 raw31240Labels permutation176 permutation4
    mixedMoment B raw31240step0 raw31240step0Labels = mixedMoment B raw31240step1 raw31240step1Labels := by
      have ha : raw31240step1 = -raw31240step0 := by apply Matrix.ext; change ∀ i j, raw31240step1 i j = -(raw31240step0 i j); unfold raw31240step1 raw31240step0; decide +kernel
      have hl : raw31240step1Labels = raw31240step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31240step1 raw31240step1Labels = mixedMoment B raw31240step2 raw31240step2Labels := by
      have ha : raw31240step2 = raw31240step1 := by apply Matrix.ext; unfold raw31240step2 raw31240step1; decide +kernel
      have hl : raw31240step1Labels = labelEmbedding7 ∘ raw31240step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31240step1 raw31240step1Labels raw31240step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4825 node4825Labels := by rfl

def raw31241 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31241Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31241step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31241step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31241step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, -2, 2], ![-2, 0, 2]]
def raw31241step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31241step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31241step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw31241step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31241step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31241 raw31241Labels = mixedMoment B node4874 node4874Labels := by
  calc
    mixedMoment B raw31241 raw31241Labels = mixedMoment B raw31241step0 raw31241step0Labels := by
      have hz : ∀ j, raw31241 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31241step0 = (fun i j => raw31241 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31241step0 raw31241; decide +kernel
      have hl : raw31241step0Labels = raw31241Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31241 raw31241Labels permutation434 hz
    mixedMoment B raw31241step0 raw31241step0Labels = mixedMoment B raw31241step1 raw31241step1Labels := by
      have hz : ∀ j, raw31241step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31241step1 = (fun i j => raw31241step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31241step1 raw31241step0; decide +kernel
      have hl : raw31241step1Labels = raw31241step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31241step0 raw31241step0Labels permutation80 hz
    mixedMoment B raw31241step1 raw31241step1Labels = mixedMoment B raw31241step2 raw31241step2Labels := by
      have ha : raw31241step2 = (fun i j => raw31241step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31241step2 raw31241step1; decide +kernel
      have hl : raw31241step2Labels = raw31241step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31241step1 raw31241step1Labels permutation9 permutation6
    mixedMoment B raw31241step2 raw31241step2Labels = mixedMoment B raw31241step3 raw31241step3Labels := by
      have ha : raw31241step3 = raw31241step2 := by apply Matrix.ext; unfold raw31241step3 raw31241step2; decide +kernel
      have hl : raw31241step2Labels = labelEmbedding9 ∘ raw31241step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31241step2 raw31241step2Labels raw31241step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4874 node4874Labels := by rfl

def raw31242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw31242Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31242step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw31242step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31242step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![-1, -1, 2], ![0, -2, 2]]
def raw31242step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31242step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw31242step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31242step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31242step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31242step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31242step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31242 raw31242Labels = mixedMoment B node4491 node4491Labels := by
  calc
    mixedMoment B raw31242 raw31242Labels = mixedMoment B raw31242step0 raw31242step0Labels := by
      have hz : ∀ j, raw31242 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31242step0 = (fun i j => raw31242 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31242step0 raw31242; decide +kernel
      have hl : raw31242step0Labels = raw31242Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31242 raw31242Labels permutation434 hz
    mixedMoment B raw31242step0 raw31242step0Labels = mixedMoment B raw31242step1 raw31242step1Labels := by
      have hz : ∀ j, raw31242step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31242step1 = (fun i j => raw31242step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31242step1 raw31242step0; decide +kernel
      have hl : raw31242step1Labels = raw31242step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31242step0 raw31242step0Labels permutation80 hz
    mixedMoment B raw31242step1 raw31242step1Labels = mixedMoment B raw31242step2 raw31242step2Labels := by
      have ha : raw31242step2 = (fun i j => raw31242step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31242step2 raw31242step1; decide +kernel
      have hl : raw31242step2Labels = raw31242step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31242step1 raw31242step1Labels permutation8 permutation4
    mixedMoment B raw31242step2 raw31242step2Labels = mixedMoment B raw31242step3 raw31242step3Labels := by
      have ha : raw31242step3 = -raw31242step2 := by apply Matrix.ext; change ∀ i j, raw31242step3 i j = -(raw31242step2 i j); unfold raw31242step3 raw31242step2; decide +kernel
      have hl : raw31242step3Labels = raw31242step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31242step3 raw31242step3Labels = mixedMoment B raw31242step4 raw31242step4Labels := by
      have ha : raw31242step4 = raw31242step3 := by apply Matrix.ext; unfold raw31242step4 raw31242step3; decide +kernel
      have hl : raw31242step3Labels = labelEmbedding7 ∘ raw31242step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31242step3 raw31242step3Labels raw31242step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4491 node4491Labels := by rfl

def raw31243 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw31243Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw31243step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31243step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw31243step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31243step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31243step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31243step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31243step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31243 raw31243Labels = mixedMoment B node4828 node4828Labels := by
  calc
    mixedMoment B raw31243 raw31243Labels = mixedMoment B raw31243step0 raw31243step0Labels := by
      have hz : ∀ j, raw31243 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31243step0 = (fun i j => raw31243 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31243step0 raw31243; decide +kernel
      have hl : raw31243step0Labels = raw31243Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31243 raw31243Labels permutation434 hz
    mixedMoment B raw31243step0 raw31243step0Labels = mixedMoment B raw31243step1 raw31243step1Labels := by
      have ha : raw31243step1 = (fun i j => raw31243step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31243step1 raw31243step0; decide +kernel
      have hl : raw31243step1Labels = raw31243step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31243step0 raw31243step0Labels permutation38 permutation4
    mixedMoment B raw31243step1 raw31243step1Labels = mixedMoment B raw31243step2 raw31243step2Labels := by
      have ha : raw31243step2 = -raw31243step1 := by apply Matrix.ext; change ∀ i j, raw31243step2 i j = -(raw31243step1 i j); unfold raw31243step2 raw31243step1; decide +kernel
      have hl : raw31243step2Labels = raw31243step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31243step2 raw31243step2Labels = mixedMoment B raw31243step3 raw31243step3Labels := by
      have ha : raw31243step3 = raw31243step2 := by apply Matrix.ext; unfold raw31243step3 raw31243step2; decide +kernel
      have hl : raw31243step2Labels = labelEmbedding7 ∘ raw31243step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31243step2 raw31243step2Labels raw31243step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4828 node4828Labels := by rfl

def raw31244 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw31244Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw31244step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31244step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw31244step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31244step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31244step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31244step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31244step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31244 raw31244Labels = mixedMoment B node4828 node4828Labels := by
  calc
    mixedMoment B raw31244 raw31244Labels = mixedMoment B raw31244step0 raw31244step0Labels := by
      have hz : ∀ j, raw31244 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31244step0 = (fun i j => raw31244 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31244step0 raw31244; decide +kernel
      have hl : raw31244step0Labels = raw31244Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31244 raw31244Labels permutation346 hz
    mixedMoment B raw31244step0 raw31244step0Labels = mixedMoment B raw31244step1 raw31244step1Labels := by
      have ha : raw31244step1 = (fun i j => raw31244step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31244step1 raw31244step0; decide +kernel
      have hl : raw31244step1Labels = raw31244step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31244step0 raw31244step0Labels permutation38 permutation4
    mixedMoment B raw31244step1 raw31244step1Labels = mixedMoment B raw31244step2 raw31244step2Labels := by
      have ha : raw31244step2 = -raw31244step1 := by apply Matrix.ext; change ∀ i j, raw31244step2 i j = -(raw31244step1 i j); unfold raw31244step2 raw31244step1; decide +kernel
      have hl : raw31244step2Labels = raw31244step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31244step2 raw31244step2Labels = mixedMoment B raw31244step3 raw31244step3Labels := by
      have ha : raw31244step3 = raw31244step2 := by apply Matrix.ext; unfold raw31244step3 raw31244step2; decide +kernel
      have hl : raw31244step2Labels = labelEmbedding7 ∘ raw31244step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31244step2 raw31244step2Labels raw31244step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4828 node4828Labels := by rfl

def raw31245 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31245Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31245step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31245step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw31245step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31245 raw31245Labels = mixedMoment B node2621 node2621Labels := by
  calc
    mixedMoment B raw31245 raw31245Labels = mixedMoment B raw31245step0 raw31245step0Labels := by
      have hz : ∀ j, raw31245 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31245step0 = (fun i j => raw31245 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31245step0 raw31245; decide +kernel
      have hl : raw31245step0Labels = raw31245Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31245 raw31245Labels permutation434 hz
    mixedMoment B raw31245step0 raw31245step0Labels = mixedMoment B raw31245step1 raw31245step1Labels := by
      have ha : raw31245step1 = (fun i j => raw31245step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31245step1 raw31245step0; decide +kernel
      have hl : raw31245step1Labels = raw31245step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31245step0 raw31245step0Labels permutation32 permutation6
    _ = mixedMoment B node2621 node2621Labels := by rfl

def raw31246 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31246Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31246step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31246step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31246step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw31246step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31246 raw31246Labels = mixedMoment B node2621 node2621Labels := by
  calc
    mixedMoment B raw31246 raw31246Labels = mixedMoment B raw31246step0 raw31246step0Labels := by
      have hz : ∀ j, raw31246 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31246step0 = (fun i j => raw31246 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31246step0 raw31246; decide +kernel
      have hl : raw31246step0Labels = raw31246Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31246 raw31246Labels permutation346 hz
    mixedMoment B raw31246step0 raw31246step0Labels = mixedMoment B raw31246step1 raw31246step1Labels := by
      have ha : raw31246step1 = (fun i j => raw31246step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31246step1 raw31246step0; decide +kernel
      have hl : raw31246step1Labels = raw31246step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31246step0 raw31246step0Labels permutation32 permutation6
    _ = mixedMoment B node2621 node2621Labels := by rfl

def raw31247 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw31247Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31247step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw31247step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31247step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-2, 0, 2], ![-1, -1, 2]]
def raw31247step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31247step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw31247step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31247 raw31247Labels = mixedMoment B node2644 node2644Labels := by
  calc
    mixedMoment B raw31247 raw31247Labels = mixedMoment B raw31247step0 raw31247step0Labels := by
      have hz : ∀ j, raw31247 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31247step0 = (fun i j => raw31247 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31247step0 raw31247; decide +kernel
      have hl : raw31247step0Labels = raw31247Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31247 raw31247Labels permutation434 hz
    mixedMoment B raw31247step0 raw31247step0Labels = mixedMoment B raw31247step1 raw31247step1Labels := by
      have hz : ∀ j, raw31247step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31247step1 = (fun i j => raw31247step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31247step1 raw31247step0; decide +kernel
      have hl : raw31247step1Labels = raw31247step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31247step0 raw31247step0Labels permutation80 hz
    mixedMoment B raw31247step1 raw31247step1Labels = mixedMoment B raw31247step2 raw31247step2Labels := by
      have ha : raw31247step2 = (fun i j => raw31247step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31247step2 raw31247step1; decide +kernel
      have hl : raw31247step2Labels = raw31247step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31247step1 raw31247step1Labels permutation8 permutation6
    _ = mixedMoment B node2644 node2644Labels := by rfl

def raw31248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31248Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -2, -1], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31248step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31248step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw31248step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31248step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![2, -1, -1], ![2, -1, -1]]
def raw31248step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31248 raw31248Labels = mixedMoment B node1661 node1661Labels := by
  calc
    mixedMoment B raw31248 raw31248Labels = mixedMoment B raw31248step0 raw31248step0Labels := by
      have hz : ∀ j, raw31248 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31248step0 = (fun i j => raw31248 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31248step0 raw31248; decide +kernel
      have hl : raw31248step0Labels = raw31248Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31248 raw31248Labels permutation434 hz
    mixedMoment B raw31248step0 raw31248step0Labels = mixedMoment B raw31248step1 raw31248step1Labels := by
      have hz : ∀ j, raw31248step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31248step1 = (fun i j => raw31248step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31248step1 raw31248step0; decide +kernel
      have hl : raw31248step1Labels = raw31248step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31248step0 raw31248step0Labels permutation80 hz
    mixedMoment B raw31248step1 raw31248step1Labels = mixedMoment B raw31248step2 raw31248step2Labels := by
      have ha : raw31248step2 = (fun i j => raw31248step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31248step2 raw31248step1; decide +kernel
      have hl : raw31248step2Labels = raw31248step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31248step1 raw31248step1Labels permutation8 permutation6
    _ = mixedMoment B node1661 node1661Labels := by rfl

def raw31249 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31249Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31249step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31249step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31249step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw31249step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31249 raw31249Labels = mixedMoment B node2123 node2123Labels := by
  calc
    mixedMoment B raw31249 raw31249Labels = mixedMoment B raw31249step0 raw31249step0Labels := by
      have hz : ∀ j, raw31249 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31249step0 = (fun i j => raw31249 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31249step0 raw31249; decide +kernel
      have hl : raw31249step0Labels = raw31249Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31249 raw31249Labels permutation434 hz
    mixedMoment B raw31249step0 raw31249step0Labels = mixedMoment B raw31249step1 raw31249step1Labels := by
      have ha : raw31249step1 = (fun i j => raw31249step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31249step1 raw31249step0; decide +kernel
      have hl : raw31249step1Labels = raw31249step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31249step0 raw31249step0Labels permutation32 permutation6
    _ = mixedMoment B node2123 node2123Labels := by rfl

def raw31250 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31250Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31250step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31250step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw31250step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31250 raw31250Labels = mixedMoment B node2123 node2123Labels := by
  calc
    mixedMoment B raw31250 raw31250Labels = mixedMoment B raw31250step0 raw31250step0Labels := by
      have hz : ∀ j, raw31250 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31250step0 = (fun i j => raw31250 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31250step0 raw31250; decide +kernel
      have hl : raw31250step0Labels = raw31250Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31250 raw31250Labels permutation346 hz
    mixedMoment B raw31250step0 raw31250step0Labels = mixedMoment B raw31250step1 raw31250step1Labels := by
      have ha : raw31250step1 = (fun i j => raw31250step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31250step1 raw31250step0; decide +kernel
      have hl : raw31250step1Labels = raw31250step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31250step0 raw31250step0Labels permutation32 permutation6
    _ = mixedMoment B node2123 node2123Labels := by rfl

def raw31251 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw31251Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw31251step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31251step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-2, 0, 2], ![-1, -1, 2]]
def raw31251step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31251step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw31251step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31251 raw31251Labels = mixedMoment B node2138 node2138Labels := by
  calc
    mixedMoment B raw31251 raw31251Labels = mixedMoment B raw31251step0 raw31251step0Labels := by
      have hz : ∀ j, raw31251 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31251step0 = (fun i j => raw31251 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31251step0 raw31251; decide +kernel
      have hl : raw31251step0Labels = raw31251Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31251 raw31251Labels permutation434 hz
    mixedMoment B raw31251step0 raw31251step0Labels = mixedMoment B raw31251step1 raw31251step1Labels := by
      have hz : ∀ j, raw31251step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31251step1 = (fun i j => raw31251step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31251step1 raw31251step0; decide +kernel
      have hl : raw31251step1Labels = raw31251step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31251step0 raw31251step0Labels permutation80 hz
    mixedMoment B raw31251step1 raw31251step1Labels = mixedMoment B raw31251step2 raw31251step2Labels := by
      have ha : raw31251step2 = (fun i j => raw31251step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31251step2 raw31251step1; decide +kernel
      have hl : raw31251step2Labels = raw31251step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31251step1 raw31251step1Labels permutation8 permutation6
    _ = mixedMoment B node2138 node2138Labels := by rfl

def raw31252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31252Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31252step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31252step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31252step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31252 raw31252Labels = mixedMoment B node1641 node1641Labels := by
  calc
    mixedMoment B raw31252 raw31252Labels = mixedMoment B raw31252step0 raw31252step0Labels := by
      have hz : ∀ j, raw31252 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31252step0 = (fun i j => raw31252 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31252step0 raw31252; decide +kernel
      have hl : raw31252step0Labels = raw31252Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31252 raw31252Labels permutation434 hz
    mixedMoment B raw31252step0 raw31252step0Labels = mixedMoment B raw31252step1 raw31252step1Labels := by
      have ha : raw31252step1 = (fun i j => raw31252step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31252step1 raw31252step0; decide +kernel
      have hl : raw31252step1Labels = raw31252step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31252step0 raw31252step0Labels permutation32 permutation6
    _ = mixedMoment B node1641 node1641Labels := by rfl

def raw31253 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31253Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31253step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31253step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31253 raw31253Labels = mixedMoment B node2073 node2073Labels := by
  calc
    mixedMoment B raw31253 raw31253Labels = mixedMoment B raw31253step0 raw31253step0Labels := by
      have ha : raw31253step0 = (fun i j => raw31253 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31253step0 raw31253; decide +kernel
      have hl : raw31253step0Labels = raw31253Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31253 raw31253Labels permutation158 permutation6
    _ = mixedMoment B node2073 node2073Labels := by rfl

def raw31254 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw31254Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31254step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw31254step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31254step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw31254step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31254 raw31254Labels = mixedMoment B node2094 node2094Labels := by
  calc
    mixedMoment B raw31254 raw31254Labels = mixedMoment B raw31254step0 raw31254step0Labels := by
      have hz : ∀ j, raw31254 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31254step0 = (fun i j => raw31254 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31254step0 raw31254; decide +kernel
      have hl : raw31254step0Labels = raw31254Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31254 raw31254Labels permutation434 hz
    mixedMoment B raw31254step0 raw31254step0Labels = mixedMoment B raw31254step1 raw31254step1Labels := by
      have ha : raw31254step1 = (fun i j => raw31254step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31254step1 raw31254step0; decide +kernel
      have hl : raw31254step1Labels = raw31254step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31254step0 raw31254step0Labels permutation32 permutation6
    _ = mixedMoment B node2094 node2094Labels := by rfl

def raw31255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31255Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31255step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31255step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31255step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31255 raw31255Labels = mixedMoment B node1641 node1641Labels := by
  calc
    mixedMoment B raw31255 raw31255Labels = mixedMoment B raw31255step0 raw31255step0Labels := by
      have hz : ∀ j, raw31255 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31255step0 = (fun i j => raw31255 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31255step0 raw31255; decide +kernel
      have hl : raw31255step0Labels = raw31255Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31255 raw31255Labels permutation346 hz
    mixedMoment B raw31255step0 raw31255step0Labels = mixedMoment B raw31255step1 raw31255step1Labels := by
      have ha : raw31255step1 = (fun i j => raw31255step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31255step1 raw31255step0; decide +kernel
      have hl : raw31255step1Labels = raw31255step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31255step0 raw31255step0Labels permutation32 permutation6
    _ = mixedMoment B node1641 node1641Labels := by rfl

def raw31256 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31256Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31256step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31256step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31256step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31256 raw31256Labels = mixedMoment B node2029 node2029Labels := by
  calc
    mixedMoment B raw31256 raw31256Labels = mixedMoment B raw31256step0 raw31256step0Labels := by
      have hz : ∀ j, raw31256 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31256step0 = (fun i j => raw31256 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31256step0 raw31256; decide +kernel
      have hl : raw31256step0Labels = raw31256Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31256 raw31256Labels permutation346 hz
    mixedMoment B raw31256step0 raw31256step0Labels = mixedMoment B raw31256step1 raw31256step1Labels := by
      have ha : raw31256step1 = (fun i j => raw31256step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31256step1 raw31256step0; decide +kernel
      have hl : raw31256step1Labels = raw31256step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31256step0 raw31256step0Labels permutation32 permutation6
    _ = mixedMoment B node2029 node2029Labels := by rfl

def raw31257 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw31257Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31257step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw31257step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31257 raw31257Labels = mixedMoment B node2073 node2073Labels := by
  calc
    mixedMoment B raw31257 raw31257Labels = mixedMoment B raw31257step0 raw31257step0Labels := by
      have ha : raw31257step0 = (fun i j => raw31257 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31257step0 raw31257; decide +kernel
      have hl : raw31257step0Labels = raw31257Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31257 raw31257Labels permutation152 permutation6
    _ = mixedMoment B node2073 node2073Labels := by rfl

def raw31258 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw31258Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-2, 0, 2], ![-1, -1, 2]]
def raw31258step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31258step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw31258step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31258 raw31258Labels = mixedMoment B node2094 node2094Labels := by
  calc
    mixedMoment B raw31258 raw31258Labels = mixedMoment B raw31258step0 raw31258step0Labels := by
      have hz : ∀ j, raw31258 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31258step0 = (fun i j => raw31258 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31258step0 raw31258; decide +kernel
      have hl : raw31258step0Labels = raw31258Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31258 raw31258Labels permutation346 hz
    mixedMoment B raw31258step0 raw31258step0Labels = mixedMoment B raw31258step1 raw31258step1Labels := by
      have ha : raw31258step1 = (fun i j => raw31258step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31258step1 raw31258step0; decide +kernel
      have hl : raw31258step1Labels = raw31258step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31258step0 raw31258step0Labels permutation32 permutation6
    _ = mixedMoment B node2094 node2094Labels := by rfl

def raw31259 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31259Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31259step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31259step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31259step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, -2, 2], ![-2, 0, 2]]
def raw31259step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31259step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31259step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31259 raw31259Labels = mixedMoment B node2115 node2115Labels := by
  calc
    mixedMoment B raw31259 raw31259Labels = mixedMoment B raw31259step0 raw31259step0Labels := by
      have hz : ∀ j, raw31259 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31259step0 = (fun i j => raw31259 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31259step0 raw31259; decide +kernel
      have hl : raw31259step0Labels = raw31259Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31259 raw31259Labels permutation434 hz
    mixedMoment B raw31259step0 raw31259step0Labels = mixedMoment B raw31259step1 raw31259step1Labels := by
      have hz : ∀ j, raw31259step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31259step1 = (fun i j => raw31259step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31259step1 raw31259step0; decide +kernel
      have hl : raw31259step1Labels = raw31259step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31259step0 raw31259step0Labels permutation80 hz
    mixedMoment B raw31259step1 raw31259step1Labels = mixedMoment B raw31259step2 raw31259step2Labels := by
      have ha : raw31259step2 = (fun i j => raw31259step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31259step2 raw31259step1; decide +kernel
      have hl : raw31259step2Labels = raw31259step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31259step1 raw31259step1Labels permutation9 permutation6
    _ = mixedMoment B node2115 node2115Labels := by rfl

def raw31260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw31260Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw31260step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31260step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![-1, -1, 2], ![0, -2, 2]]
def raw31260step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31260step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def raw31260step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31260 raw31260Labels = mixedMoment B node1653 node1653Labels := by
  calc
    mixedMoment B raw31260 raw31260Labels = mixedMoment B raw31260step0 raw31260step0Labels := by
      have hz : ∀ j, raw31260 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31260step0 = (fun i j => raw31260 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31260step0 raw31260; decide +kernel
      have hl : raw31260step0Labels = raw31260Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31260 raw31260Labels permutation434 hz
    mixedMoment B raw31260step0 raw31260step0Labels = mixedMoment B raw31260step1 raw31260step1Labels := by
      have hz : ∀ j, raw31260step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31260step1 = (fun i j => raw31260step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31260step1 raw31260step0; decide +kernel
      have hl : raw31260step1Labels = raw31260step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31260step0 raw31260step0Labels permutation80 hz
    mixedMoment B raw31260step1 raw31260step1Labels = mixedMoment B raw31260step2 raw31260step2Labels := by
      have ha : raw31260step2 = (fun i j => raw31260step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31260step2 raw31260step1; decide +kernel
      have hl : raw31260step2Labels = raw31260step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31260step1 raw31260step1Labels permutation8 permutation6
    _ = mixedMoment B node1653 node1653Labels := by rfl

def raw31261 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw31261Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw31261step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31261step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, -1, 2], ![0, -2, 2]]
def raw31261step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31261step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw31261step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31261 raw31261Labels = mixedMoment B node2066 node2066Labels := by
  calc
    mixedMoment B raw31261 raw31261Labels = mixedMoment B raw31261step0 raw31261step0Labels := by
      have hz : ∀ j, raw31261 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31261step0 = (fun i j => raw31261 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31261step0 raw31261; decide +kernel
      have hl : raw31261step0Labels = raw31261Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31261 raw31261Labels permutation434 hz
    mixedMoment B raw31261step0 raw31261step0Labels = mixedMoment B raw31261step1 raw31261step1Labels := by
      have hz : ∀ j, raw31261step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31261step1 = (fun i j => raw31261step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31261step1 raw31261step0; decide +kernel
      have hl : raw31261step1Labels = raw31261step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31261step0 raw31261step0Labels permutation80 hz
    mixedMoment B raw31261step1 raw31261step1Labels = mixedMoment B raw31261step2 raw31261step2Labels := by
      have ha : raw31261step2 = (fun i j => raw31261step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31261step2 raw31261step1; decide +kernel
      have hl : raw31261step2Labels = raw31261step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31261step1 raw31261step1Labels permutation8 permutation6
    _ = mixedMoment B node2066 node2066Labels := by rfl

def raw31262 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw31262Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31262step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw31262step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31262step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw31262step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31262 raw31262Labels = mixedMoment B node2082 node2082Labels := by
  calc
    mixedMoment B raw31262 raw31262Labels = mixedMoment B raw31262step0 raw31262step0Labels := by
      have hz : ∀ j, raw31262 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31262step0 = (fun i j => raw31262 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31262step0 raw31262; decide +kernel
      have hl : raw31262step0Labels = raw31262Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31262 raw31262Labels permutation434 hz
    mixedMoment B raw31262step0 raw31262step0Labels = mixedMoment B raw31262step1 raw31262step1Labels := by
      have ha : raw31262step1 = (fun i j => raw31262step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31262step1 raw31262step0; decide +kernel
      have hl : raw31262step1Labels = raw31262step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31262step0 raw31262step0Labels permutation32 permutation6
    _ = mixedMoment B node2082 node2082Labels := by rfl

def raw31263 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw31263Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw31263step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31263step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw31263step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31263 raw31263Labels = mixedMoment B node2082 node2082Labels := by
  calc
    mixedMoment B raw31263 raw31263Labels = mixedMoment B raw31263step0 raw31263step0Labels := by
      have hz : ∀ j, raw31263 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31263step0 = (fun i j => raw31263 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31263step0 raw31263; decide +kernel
      have hl : raw31263step0Labels = raw31263Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31263 raw31263Labels permutation346 hz
    mixedMoment B raw31263step0 raw31263step0Labels = mixedMoment B raw31263step1 raw31263step1Labels := by
      have ha : raw31263step1 = (fun i j => raw31263step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31263step1 raw31263step0; decide +kernel
      have hl : raw31263step1Labels = raw31263step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31263step0 raw31263step0Labels permutation32 permutation6
    _ = mixedMoment B node2082 node2082Labels := by rfl

def raw31264 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw31264Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31264step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-2, 0, 2], ![0, -2, 2]]
def raw31264step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31264step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-2, 0, 2], ![0, -2, 2]]
def raw31264step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31264step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31264step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31264 raw31264Labels = mixedMoment B node2115 node2115Labels := by
  calc
    mixedMoment B raw31264 raw31264Labels = mixedMoment B raw31264step0 raw31264step0Labels := by
      have hz : ∀ j, raw31264 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31264step0 = (fun i j => raw31264 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31264step0 raw31264; decide +kernel
      have hl : raw31264step0Labels = raw31264Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31264 raw31264Labels permutation434 hz
    mixedMoment B raw31264step0 raw31264step0Labels = mixedMoment B raw31264step1 raw31264step1Labels := by
      have hz : ∀ j, raw31264step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31264step1 = (fun i j => raw31264step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31264step1 raw31264step0; decide +kernel
      have hl : raw31264step1Labels = raw31264step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31264step0 raw31264step0Labels permutation80 hz
    mixedMoment B raw31264step1 raw31264step1Labels = mixedMoment B raw31264step2 raw31264step2Labels := by
      have ha : raw31264step2 = (fun i j => raw31264step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31264step2 raw31264step1; decide +kernel
      have hl : raw31264step2Labels = raw31264step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31264step1 raw31264step1Labels permutation8 permutation6
    _ = mixedMoment B node2115 node2115Labels := by rfl

def raw31265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw31265Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31265step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw31265step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31265step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -2, 3]]
def raw31265step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31265step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw31265step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31265 raw31265Labels = mixedMoment B node3047 node3047Labels := by
  calc
    mixedMoment B raw31265 raw31265Labels = mixedMoment B raw31265step0 raw31265step0Labels := by
      have hz : ∀ j, raw31265 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31265step0 = (fun i j => raw31265 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31265step0 raw31265; decide +kernel
      have hl : raw31265step0Labels = raw31265Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31265 raw31265Labels permutation346 hz
    mixedMoment B raw31265step0 raw31265step0Labels = mixedMoment B raw31265step1 raw31265step1Labels := by
      have ha : raw31265step1 = (fun i j => raw31265step0 (permutation73 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31265step1 raw31265step0; decide +kernel
      have hl : raw31265step1Labels = raw31265step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31265step0 raw31265step0Labels permutation73 permutation4
    mixedMoment B raw31265step1 raw31265step1Labels = mixedMoment B raw31265step2 raw31265step2Labels := by
      have ha : raw31265step2 = -raw31265step1 := by apply Matrix.ext; change ∀ i j, raw31265step2 i j = -(raw31265step1 i j); unfold raw31265step2 raw31265step1; decide +kernel
      have hl : raw31265step2Labels = raw31265step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3047 node3047Labels := by rfl

def raw31266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw31266Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31266step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw31266step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31266 raw31266Labels = mixedMoment B node3499 node3499Labels := by
  calc
    mixedMoment B raw31266 raw31266Labels = mixedMoment B raw31266step0 raw31266step0Labels := by
      have ha : raw31266step0 = (fun i j => raw31266 (permutation177 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31266step0 raw31266; decide +kernel
      have hl : raw31266step0Labels = raw31266Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31266 raw31266Labels permutation177 permutation2
    _ = mixedMoment B node3499 node3499Labels := by rfl

def raw31267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw31267Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw31267step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31267step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, 0, -2]]
def raw31267step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31267 raw31267Labels = mixedMoment B node3448 node3448Labels := by
  calc
    mixedMoment B raw31267 raw31267Labels = mixedMoment B raw31267step0 raw31267step0Labels := by
      have hz : ∀ j, raw31267 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31267step0 = (fun i j => raw31267 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31267step0 raw31267; decide +kernel
      have hl : raw31267step0Labels = raw31267Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31267 raw31267Labels permutation346 hz
    mixedMoment B raw31267step0 raw31267step0Labels = mixedMoment B raw31267step1 raw31267step1Labels := by
      have ha : raw31267step1 = (fun i j => raw31267step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31267step1 raw31267step0; decide +kernel
      have hl : raw31267step1Labels = raw31267step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31267step0 raw31267step0Labels permutation39 permutation2
    _ = mixedMoment B node3448 node3448Labels := by rfl

def raw31268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw31268Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw31268step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31268 raw31268Labels = mixedMoment B node3565 node3565Labels := by
  calc
    mixedMoment B raw31268 raw31268Labels = mixedMoment B raw31268step0 raw31268step0Labels := by
      have hz : ∀ j, raw31268 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31268step0 = (fun i j => raw31268 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31268step0 raw31268; decide +kernel
      have hl : raw31268step0Labels = raw31268Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31268 raw31268Labels permutation346 hz
    _ = mixedMoment B node3565 node3565Labels := by rfl

def raw31269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw31269Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31269step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![2, 0, -2], ![1, 0, -1]]
def raw31269step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31269step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw31269step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31269 raw31269Labels = mixedMoment B node3564 node3564Labels := by
  calc
    mixedMoment B raw31269 raw31269Labels = mixedMoment B raw31269step0 raw31269step0Labels := by
      have hz : ∀ j, raw31269 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31269step0 = (fun i j => raw31269 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31269step0 raw31269; decide +kernel
      have hl : raw31269step0Labels = raw31269Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31269 raw31269Labels permutation346 hz
    mixedMoment B raw31269step0 raw31269step0Labels = mixedMoment B raw31269step1 raw31269step1Labels := by
      have ha : raw31269step1 = (fun i j => raw31269step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31269step1 raw31269step0; decide +kernel
      have hl : raw31269step1Labels = raw31269step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31269step0 raw31269step0Labels permutation33 permutation2
    _ = mixedMoment B node3564 node3564Labels := by rfl

def raw31270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -1, -1]]
def raw31270Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31270step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw31270step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31270 raw31270Labels = mixedMoment B node1876 node1876Labels := by
  calc
    mixedMoment B raw31270 raw31270Labels = mixedMoment B raw31270step0 raw31270step0Labels := by
      have ha : raw31270step0 = (fun i j => raw31270 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31270step0 raw31270; decide +kernel
      have hl : raw31270step0Labels = raw31270Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31270 raw31270Labels permutation201 permutation2
    _ = mixedMoment B node1876 node1876Labels := by rfl

def raw31271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw31271Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31271step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 0, 1], ![3, -1, -2], ![2, -1, -1]]
def raw31271step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31271step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw31271step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31271 raw31271Labels = mixedMoment B node1880 node1880Labels := by
  calc
    mixedMoment B raw31271 raw31271Labels = mixedMoment B raw31271step0 raw31271step0Labels := by
      have hz : ∀ j, raw31271 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31271step0 = (fun i j => raw31271 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31271step0 raw31271; decide +kernel
      have hl : raw31271step0Labels = raw31271Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31271 raw31271Labels permutation346 hz
    mixedMoment B raw31271step0 raw31271step0Labels = mixedMoment B raw31271step1 raw31271step1Labels := by
      have ha : raw31271step1 = (fun i j => raw31271step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31271step1 raw31271step0; decide +kernel
      have hl : raw31271step1Labels = raw31271step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31271step0 raw31271step0Labels permutation39 permutation2
    _ = mixedMoment B node1880 node1880Labels := by rfl

def raw31272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw31272Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw31272step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31272step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw31272step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31272 raw31272Labels = mixedMoment B node1881 node1881Labels := by
  calc
    mixedMoment B raw31272 raw31272Labels = mixedMoment B raw31272step0 raw31272step0Labels := by
      have hz : ∀ j, raw31272 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31272step0 = (fun i j => raw31272 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31272step0 raw31272; decide +kernel
      have hl : raw31272step0Labels = raw31272Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31272 raw31272Labels permutation346 hz
    mixedMoment B raw31272step0 raw31272step0Labels = mixedMoment B raw31272step1 raw31272step1Labels := by
      have ha : raw31272step1 = (fun i j => raw31272step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31272step1 raw31272step0; decide +kernel
      have hl : raw31272step1Labels = raw31272step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31272step0 raw31272step0Labels permutation38 permutation2
    _ = mixedMoment B node1881 node1881Labels := by rfl

def raw31273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw31273Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![-1, 1, 0], ![0, -2, 2], ![0, -2, 2]]
def raw31273step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31273step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 2, -1], ![-2, 0, 2], ![-2, 0, 2]]
def raw31273step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31273step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw31273step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31273 raw31273Labels = mixedMoment B node917 node917Labels := by
  calc
    mixedMoment B raw31273 raw31273Labels = mixedMoment B raw31273step0 raw31273step0Labels := by
      have hz : ∀ j, raw31273 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31273step0 = (fun i j => raw31273 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31273step0 raw31273; decide +kernel
      have hl : raw31273step0Labels = raw31273Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31273 raw31273Labels permutation346 hz
    mixedMoment B raw31273step0 raw31273step0Labels = mixedMoment B raw31273step1 raw31273step1Labels := by
      have ha : raw31273step1 = (fun i j => raw31273step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31273step1 raw31273step0; decide +kernel
      have hl : raw31273step1Labels = raw31273step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31273step0 raw31273step0Labels permutation38 permutation4
    mixedMoment B raw31273step1 raw31273step1Labels = mixedMoment B raw31273step2 raw31273step2Labels := by
      have ha : raw31273step2 = -raw31273step1 := by apply Matrix.ext; change ∀ i j, raw31273step2 i j = -(raw31273step1 i j); unfold raw31273step2 raw31273step1; decide +kernel
      have hl : raw31273step2Labels = raw31273step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node917 node917Labels := by rfl

def raw31274 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw31274Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31274step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![0, -2, 2]]
def raw31274step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31274step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw31274step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31274step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31274step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31274 raw31274Labels = mixedMoment B node2048 node2048Labels := by
  calc
    mixedMoment B raw31274 raw31274Labels = mixedMoment B raw31274step0 raw31274step0Labels := by
      have hz : ∀ j, raw31274 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31274step0 = (fun i j => raw31274 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31274step0 raw31274; decide +kernel
      have hl : raw31274step0Labels = raw31274Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31274 raw31274Labels permutation346 hz
    mixedMoment B raw31274step0 raw31274step0Labels = mixedMoment B raw31274step1 raw31274step1Labels := by
      have ha : raw31274step1 = (fun i j => raw31274step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31274step1 raw31274step0; decide +kernel
      have hl : raw31274step1Labels = raw31274step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31274step0 raw31274step0Labels permutation38 permutation4
    mixedMoment B raw31274step1 raw31274step1Labels = mixedMoment B raw31274step2 raw31274step2Labels := by
      have ha : raw31274step2 = -raw31274step1 := by apply Matrix.ext; change ∀ i j, raw31274step2 i j = -(raw31274step1 i j); unfold raw31274step2 raw31274step1; decide +kernel
      have hl : raw31274step2Labels = raw31274step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2048 node2048Labels := by rfl

def raw31275 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31275Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31275step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31275step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31275step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw31275step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31275step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31275step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31275 raw31275Labels = mixedMoment B node2048 node2048Labels := by
  calc
    mixedMoment B raw31275 raw31275Labels = mixedMoment B raw31275step0 raw31275step0Labels := by
      have hz : ∀ j, raw31275 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31275step0 = (fun i j => raw31275 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31275step0 raw31275; decide +kernel
      have hl : raw31275step0Labels = raw31275Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31275 raw31275Labels permutation346 hz
    mixedMoment B raw31275step0 raw31275step0Labels = mixedMoment B raw31275step1 raw31275step1Labels := by
      have ha : raw31275step1 = (fun i j => raw31275step0 (permutation39 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31275step1 raw31275step0; decide +kernel
      have hl : raw31275step1Labels = raw31275step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31275step0 raw31275step0Labels permutation39 permutation4
    mixedMoment B raw31275step1 raw31275step1Labels = mixedMoment B raw31275step2 raw31275step2Labels := by
      have ha : raw31275step2 = -raw31275step1 := by apply Matrix.ext; change ∀ i j, raw31275step2 i j = -(raw31275step1 i j); unfold raw31275step2 raw31275step1; decide +kernel
      have hl : raw31275step2Labels = raw31275step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2048 node2048Labels := by rfl

def raw31276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31276Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31276step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31276step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31276step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw31276step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31276step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw31276step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31276step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw31276step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31276 raw31276Labels = mixedMoment B node5232 node5232Labels := by
  calc
    mixedMoment B raw31276 raw31276Labels = mixedMoment B raw31276step0 raw31276step0Labels := by
      have hz : ∀ j, raw31276 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31276step0 = (fun i j => raw31276 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31276step0 raw31276; decide +kernel
      have hl : raw31276step0Labels = raw31276Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31276 raw31276Labels permutation434 hz
    mixedMoment B raw31276step0 raw31276step0Labels = mixedMoment B raw31276step1 raw31276step1Labels := by
      have ha : raw31276step1 = (fun i j => raw31276step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31276step1 raw31276step0; decide +kernel
      have hl : raw31276step1Labels = raw31276step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31276step0 raw31276step0Labels permutation36 permutation7
    mixedMoment B raw31276step1 raw31276step1Labels = mixedMoment B raw31276step2 raw31276step2Labels := by
      have ha : raw31276step2 = -raw31276step1 := by apply Matrix.ext; change ∀ i j, raw31276step2 i j = -(raw31276step1 i j); unfold raw31276step2 raw31276step1; decide +kernel
      have hl : raw31276step2Labels = raw31276step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31276step2 raw31276step2Labels = mixedMoment B raw31276step3 raw31276step3Labels := by
      have ha : raw31276step3 = raw31276step2 := by apply Matrix.ext; unfold raw31276step3 raw31276step2; decide +kernel
      have hl : raw31276step2Labels = labelEmbedding10 ∘ raw31276step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31276step2 raw31276step2Labels raw31276step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5232 node5232Labels := by rfl

def raw31277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31277Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31277step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31277step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw31277step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31277step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw31277step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31277step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw31277step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31277 raw31277Labels = mixedMoment B node5264 node5264Labels := by
  calc
    mixedMoment B raw31277 raw31277Labels = mixedMoment B raw31277step0 raw31277step0Labels := by
      have hz : ∀ j, raw31277 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31277step0 = (fun i j => raw31277 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31277step0 raw31277; decide +kernel
      have hl : raw31277step0Labels = raw31277Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31277 raw31277Labels permutation434 hz
    mixedMoment B raw31277step0 raw31277step0Labels = mixedMoment B raw31277step1 raw31277step1Labels := by
      have ha : raw31277step1 = (fun i j => raw31277step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31277step1 raw31277step0; decide +kernel
      have hl : raw31277step1Labels = raw31277step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31277step0 raw31277step0Labels permutation36 permutation7
    mixedMoment B raw31277step1 raw31277step1Labels = mixedMoment B raw31277step2 raw31277step2Labels := by
      have ha : raw31277step2 = -raw31277step1 := by apply Matrix.ext; change ∀ i j, raw31277step2 i j = -(raw31277step1 i j); unfold raw31277step2 raw31277step1; decide +kernel
      have hl : raw31277step2Labels = raw31277step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31277step2 raw31277step2Labels = mixedMoment B raw31277step3 raw31277step3Labels := by
      have ha : raw31277step3 = raw31277step2 := by apply Matrix.ext; unfold raw31277step3 raw31277step2; decide +kernel
      have hl : raw31277step2Labels = labelEmbedding10 ∘ raw31277step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31277step2 raw31277step2Labels raw31277step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5264 node5264Labels := by rfl

def raw31278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31278Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31278step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw31278step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31278step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw31278step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31278step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw31278step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31278 raw31278Labels = mixedMoment B node5243 node5243Labels := by
  calc
    mixedMoment B raw31278 raw31278Labels = mixedMoment B raw31278step0 raw31278step0Labels := by
      have ha : raw31278step0 = (fun i j => raw31278 (permutation162 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31278step0 raw31278; decide +kernel
      have hl : raw31278step0Labels = raw31278Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31278 raw31278Labels permutation162 permutation7
    mixedMoment B raw31278step0 raw31278step0Labels = mixedMoment B raw31278step1 raw31278step1Labels := by
      have ha : raw31278step1 = -raw31278step0 := by apply Matrix.ext; change ∀ i j, raw31278step1 i j = -(raw31278step0 i j); unfold raw31278step1 raw31278step0; decide +kernel
      have hl : raw31278step1Labels = raw31278step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31278step1 raw31278step1Labels = mixedMoment B raw31278step2 raw31278step2Labels := by
      have ha : raw31278step2 = raw31278step1 := by apply Matrix.ext; unfold raw31278step2 raw31278step1; decide +kernel
      have hl : raw31278step1Labels = labelEmbedding10 ∘ raw31278step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31278step1 raw31278step1Labels raw31278step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5243 node5243Labels := by rfl

def raw31279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw31279Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31279step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31279step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31279step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw31279step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31279step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw31279step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31279step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw31279step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31279 raw31279Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw31279 raw31279Labels = mixedMoment B raw31279step0 raw31279step0Labels := by
      have hz : ∀ j, raw31279 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31279step0 = (fun i j => raw31279 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31279step0 raw31279; decide +kernel
      have hl : raw31279step0Labels = raw31279Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31279 raw31279Labels permutation434 hz
    mixedMoment B raw31279step0 raw31279step0Labels = mixedMoment B raw31279step1 raw31279step1Labels := by
      have ha : raw31279step1 = (fun i j => raw31279step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31279step1 raw31279step0; decide +kernel
      have hl : raw31279step1Labels = raw31279step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31279step0 raw31279step0Labels permutation36 permutation7
    mixedMoment B raw31279step1 raw31279step1Labels = mixedMoment B raw31279step2 raw31279step2Labels := by
      have ha : raw31279step2 = -raw31279step1 := by apply Matrix.ext; change ∀ i j, raw31279step2 i j = -(raw31279step1 i j); unfold raw31279step2 raw31279step1; decide +kernel
      have hl : raw31279step2Labels = raw31279step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31279step2 raw31279step2Labels = mixedMoment B raw31279step3 raw31279step3Labels := by
      have ha : raw31279step3 = raw31279step2 := by apply Matrix.ext; unfold raw31279step3 raw31279step2; decide +kernel
      have hl : raw31279step2Labels = labelEmbedding10 ∘ raw31279step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31279step2 raw31279step2Labels raw31279step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

def raw31280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw31280Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw31280step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31280step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw31280step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31280step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw31280step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw31280step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw31280step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31280 raw31280Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw31280 raw31280Labels = mixedMoment B raw31280step0 raw31280step0Labels := by
      have hz : ∀ j, raw31280 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31280step0 = (fun i j => raw31280 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31280step0 raw31280; decide +kernel
      have hl : raw31280step0Labels = raw31280Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31280 raw31280Labels permutation434 hz
    mixedMoment B raw31280step0 raw31280step0Labels = mixedMoment B raw31280step1 raw31280step1Labels := by
      have ha : raw31280step1 = (fun i j => raw31280step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31280step1 raw31280step0; decide +kernel
      have hl : raw31280step1Labels = raw31280step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31280step0 raw31280step0Labels permutation36 permutation7
    mixedMoment B raw31280step1 raw31280step1Labels = mixedMoment B raw31280step2 raw31280step2Labels := by
      have ha : raw31280step2 = -raw31280step1 := by apply Matrix.ext; change ∀ i j, raw31280step2 i j = -(raw31280step1 i j); unfold raw31280step2 raw31280step1; decide +kernel
      have hl : raw31280step2Labels = raw31280step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31280step2 raw31280step2Labels = mixedMoment B raw31280step3 raw31280step3Labels := by
      have ha : raw31280step3 = raw31280step2 := by apply Matrix.ext; unfold raw31280step3 raw31280step2; decide +kernel
      have hl : raw31280step2Labels = labelEmbedding10 ∘ raw31280step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31280step2 raw31280step2Labels raw31280step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw31281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31281Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31281step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31281step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31281step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31281step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31281step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31281step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31281 raw31281Labels = mixedMoment B node4466 node4466Labels := by
  calc
    mixedMoment B raw31281 raw31281Labels = mixedMoment B raw31281step0 raw31281step0Labels := by
      have hz : ∀ j, raw31281 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31281step0 = (fun i j => raw31281 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31281step0 raw31281; decide +kernel
      have hl : raw31281step0Labels = raw31281Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31281 raw31281Labels permutation434 hz
    mixedMoment B raw31281step0 raw31281step0Labels = mixedMoment B raw31281step1 raw31281step1Labels := by
      have hz : ∀ j, raw31281step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw31281step1 = (fun i j => raw31281step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw31281step1 raw31281step0; decide +kernel
      have hl : raw31281step1Labels = raw31281step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31281step0 raw31281step0Labels permutation56 hz
    mixedMoment B raw31281step1 raw31281step1Labels = mixedMoment B raw31281step2 raw31281step2Labels := by
      have ha : raw31281step2 = (fun i j => raw31281step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31281step2 raw31281step1; decide +kernel
      have hl : raw31281step2Labels = raw31281step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31281step1 raw31281step1Labels permutation9 permutation2
    _ = mixedMoment B node4466 node4466Labels := by rfl

def raw31282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31282Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31282step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31282step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31282step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31282step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31282step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31282 raw31282Labels = mixedMoment B node4874 node4874Labels := by
  calc
    mixedMoment B raw31282 raw31282Labels = mixedMoment B raw31282step0 raw31282step0Labels := by
      have hz : ∀ j, raw31282 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31282step0 = (fun i j => raw31282 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31282step0 raw31282; decide +kernel
      have hl : raw31282step0Labels = raw31282Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31282 raw31282Labels permutation434 hz
    mixedMoment B raw31282step0 raw31282step0Labels = mixedMoment B raw31282step1 raw31282step1Labels := by
      have hz : ∀ j, raw31282step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw31282step1 = (fun i j => raw31282step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw31282step1 raw31282step0; decide +kernel
      have hl : raw31282step1Labels = raw31282step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31282step0 raw31282step0Labels permutation56 hz
    mixedMoment B raw31282step1 raw31282step1Labels = mixedMoment B raw31282step2 raw31282step2Labels := by
      have ha : raw31282step2 = (fun i j => raw31282step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31282step2 raw31282step1; decide +kernel
      have hl : raw31282step2Labels = raw31282step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31282step1 raw31282step1Labels permutation9 permutation2
    _ = mixedMoment B node4874 node4874Labels := by rfl

def raw31283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31283Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31283step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31283step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31283step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31283 raw31283Labels = mixedMoment B node4810 node4810Labels := by
  calc
    mixedMoment B raw31283 raw31283Labels = mixedMoment B raw31283step0 raw31283step0Labels := by
      have hz : ∀ j, raw31283 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw31283step0 = (fun i j => raw31283 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw31283step0 raw31283; decide +kernel
      have hl : raw31283step0Labels = raw31283Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31283 raw31283Labels permutation265 hz
    mixedMoment B raw31283step0 raw31283step0Labels = mixedMoment B raw31283step1 raw31283step1Labels := by
      have ha : raw31283step1 = (fun i j => raw31283step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31283step1 raw31283step0; decide +kernel
      have hl : raw31283step1Labels = raw31283step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31283step0 raw31283step0Labels permutation39 permutation2
    _ = mixedMoment B node4810 node4810Labels := by rfl

def raw31284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw31284Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31284step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31284step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31284step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31284step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31284 raw31284Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw31284 raw31284Labels = mixedMoment B raw31284step0 raw31284step0Labels := by
      have hz : ∀ j, raw31284 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31284step0 = (fun i j => raw31284 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31284step0 raw31284; decide +kernel
      have hl : raw31284step0Labels = raw31284Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31284 raw31284Labels permutation434 hz
    mixedMoment B raw31284step0 raw31284step0Labels = mixedMoment B raw31284step1 raw31284step1Labels := by
      have hz : ∀ j, raw31284step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw31284step1 = (fun i j => raw31284step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw31284step1 raw31284step0; decide +kernel
      have hl : raw31284step1Labels = raw31284step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31284step0 raw31284step0Labels permutation56 hz
    _ = mixedMoment B node4896 node4896Labels := by rfl

def raw31285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw31285Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31285step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw31285step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31285step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw31285step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31285step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw31285step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31285 raw31285Labels = mixedMoment B node4894 node4894Labels := by
  calc
    mixedMoment B raw31285 raw31285Labels = mixedMoment B raw31285step0 raw31285step0Labels := by
      have hz : ∀ j, raw31285 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31285step0 = (fun i j => raw31285 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31285step0 raw31285; decide +kernel
      have hl : raw31285step0Labels = raw31285Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31285 raw31285Labels permutation434 hz
    mixedMoment B raw31285step0 raw31285step0Labels = mixedMoment B raw31285step1 raw31285step1Labels := by
      have hz : ∀ j, raw31285step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw31285step1 = (fun i j => raw31285step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw31285step1 raw31285step0; decide +kernel
      have hl : raw31285step1Labels = raw31285step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31285step0 raw31285step0Labels permutation56 hz
    mixedMoment B raw31285step1 raw31285step1Labels = mixedMoment B raw31285step2 raw31285step2Labels := by
      have ha : raw31285step2 = (fun i j => raw31285step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31285step2 raw31285step1; decide +kernel
      have hl : raw31285step2Labels = raw31285step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31285step1 raw31285step1Labels permutation9 permutation2
    _ = mixedMoment B node4894 node4894Labels := by rfl

def raw31286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31286Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31286step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31286step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31286step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31286step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31286 raw31286Labels = mixedMoment B node4354 node4354Labels := by
  calc
    mixedMoment B raw31286 raw31286Labels = mixedMoment B raw31286step0 raw31286step0Labels := by
      have hz : ∀ j, raw31286 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31286step0 = (fun i j => raw31286 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31286step0 raw31286; decide +kernel
      have hl : raw31286step0Labels = raw31286Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31286 raw31286Labels permutation434 hz
    mixedMoment B raw31286step0 raw31286step0Labels = mixedMoment B raw31286step1 raw31286step1Labels := by
      have ha : raw31286step1 = (fun i j => raw31286step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31286step1 raw31286step0; decide +kernel
      have hl : raw31286step1Labels = raw31286step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31286step0 raw31286step0Labels permutation33 permutation2
    _ = mixedMoment B node4354 node4354Labels := by rfl

def raw31287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31287Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31287step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31287step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31287step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31287 raw31287Labels = mixedMoment B node4688 node4688Labels := by
  calc
    mixedMoment B raw31287 raw31287Labels = mixedMoment B raw31287step0 raw31287step0Labels := by
      have hz : ∀ j, raw31287 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31287step0 = (fun i j => raw31287 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31287step0 raw31287; decide +kernel
      have hl : raw31287step0Labels = raw31287Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31287 raw31287Labels permutation434 hz
    mixedMoment B raw31287step0 raw31287step0Labels = mixedMoment B raw31287step1 raw31287step1Labels := by
      have ha : raw31287step1 = (fun i j => raw31287step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31287step1 raw31287step0; decide +kernel
      have hl : raw31287step1Labels = raw31287step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31287step0 raw31287step0Labels permutation33 permutation2
    _ = mixedMoment B node4688 node4688Labels := by rfl

def raw31288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31288Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31288step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31288step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31288 raw31288Labels = mixedMoment B node4766 node4766Labels := by
  calc
    mixedMoment B raw31288 raw31288Labels = mixedMoment B raw31288step0 raw31288step0Labels := by
      have ha : raw31288step0 = (fun i j => raw31288 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31288step0 raw31288; decide +kernel
      have hl : raw31288step0Labels = raw31288Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31288 raw31288Labels permutation159 permutation2
    _ = mixedMoment B node4766 node4766Labels := by rfl

def raw31289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw31289Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31289step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31289step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31289 raw31289Labels = mixedMoment B node4839 node4839Labels := by
  calc
    mixedMoment B raw31289 raw31289Labels = mixedMoment B raw31289step0 raw31289step0Labels := by
      have hz : ∀ j, raw31289 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31289step0 = (fun i j => raw31289 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31289step0 raw31289; decide +kernel
      have hl : raw31289step0Labels = raw31289Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31289 raw31289Labels permutation434 hz
    _ = mixedMoment B node4839 node4839Labels := by rfl

def raw31290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw31290Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31290step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2], ![1, -1, 0]]
def raw31290step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31290step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw31290step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31290 raw31290Labels = mixedMoment B node4834 node4834Labels := by
  calc
    mixedMoment B raw31290 raw31290Labels = mixedMoment B raw31290step0 raw31290step0Labels := by
      have hz : ∀ j, raw31290 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31290step0 = (fun i j => raw31290 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31290step0 raw31290; decide +kernel
      have hl : raw31290step0Labels = raw31290Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31290 raw31290Labels permutation434 hz
    mixedMoment B raw31290step0 raw31290step0Labels = mixedMoment B raw31290step1 raw31290step1Labels := by
      have ha : raw31290step1 = (fun i j => raw31290step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31290step1 raw31290step0; decide +kernel
      have hl : raw31290step1Labels = raw31290step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31290step0 raw31290step0Labels permutation36 permutation2
    _ = mixedMoment B node4834 node4834Labels := by rfl

def raw31291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31291Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31291step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31291step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31291 raw31291Labels = mixedMoment B node4328 node4328Labels := by
  calc
    mixedMoment B raw31291 raw31291Labels = mixedMoment B raw31291step0 raw31291step0Labels := by
      have ha : raw31291step0 = (fun i j => raw31291 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31291step0 raw31291; decide +kernel
      have hl : raw31291step0Labels = raw31291Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31291 raw31291Labels permutation153 permutation2
    _ = mixedMoment B node4328 node4328Labels := by rfl

def raw31292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31292Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31292step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31292step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31292 raw31292Labels = mixedMoment B node4665 node4665Labels := by
  calc
    mixedMoment B raw31292 raw31292Labels = mixedMoment B raw31292step0 raw31292step0Labels := by
      have ha : raw31292step0 = (fun i j => raw31292 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31292step0 raw31292; decide +kernel
      have hl : raw31292step0Labels = raw31292Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31292 raw31292Labels permutation153 permutation2
    _ = mixedMoment B node4665 node4665Labels := by rfl

def raw31293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31293Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31293step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31293step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31293 raw31293Labels = mixedMoment B node4773 node4773Labels := by
  calc
    mixedMoment B raw31293 raw31293Labels = mixedMoment B raw31293step0 raw31293step0Labels := by
      have ha : raw31293step0 = (fun i j => raw31293 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31293step0 raw31293; decide +kernel
      have hl : raw31293step0Labels = raw31293Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31293 raw31293Labels permutation153 permutation2
    _ = mixedMoment B node4773 node4773Labels := by rfl

def raw31294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw31294Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31294 raw31294Labels = mixedMoment B node4803 node4803Labels := by
  calc
    _ = mixedMoment B node4803 node4803Labels := by rfl

def raw31295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw31295Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31295step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw31295step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31295 raw31295Labels = mixedMoment B node4801 node4801Labels := by
  calc
    mixedMoment B raw31295 raw31295Labels = mixedMoment B raw31295step0 raw31295step0Labels := by
      have ha : raw31295step0 = (fun i j => raw31295 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31295step0 raw31295; decide +kernel
      have hl : raw31295step0Labels = raw31295Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31295 raw31295Labels permutation153 permutation2
    _ = mixedMoment B node4801 node4801Labels := by rfl

def raw31296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw31296Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31296step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![3, -1, -2], ![2, -2, 0]]
def raw31296step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31296step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw31296step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31296 raw31296Labels = mixedMoment B node4334 node4334Labels := by
  calc
    mixedMoment B raw31296 raw31296Labels = mixedMoment B raw31296step0 raw31296step0Labels := by
      have hz : ∀ j, raw31296 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31296step0 = (fun i j => raw31296 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31296step0 raw31296; decide +kernel
      have hl : raw31296step0Labels = raw31296Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31296 raw31296Labels permutation434 hz
    mixedMoment B raw31296step0 raw31296step0Labels = mixedMoment B raw31296step1 raw31296step1Labels := by
      have ha : raw31296step1 = (fun i j => raw31296step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31296step1 raw31296step0; decide +kernel
      have hl : raw31296step1Labels = raw31296step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31296step0 raw31296step0Labels permutation33 permutation2
    _ = mixedMoment B node4334 node4334Labels := by rfl

def raw31297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw31297Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![3, -1, -2], ![2, -2, 0]]
def raw31297step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31297step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw31297step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31297 raw31297Labels = mixedMoment B node4669 node4669Labels := by
  calc
    mixedMoment B raw31297 raw31297Labels = mixedMoment B raw31297step0 raw31297step0Labels := by
      have hz : ∀ j, raw31297 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31297step0 = (fun i j => raw31297 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31297step0 raw31297; decide +kernel
      have hl : raw31297step0Labels = raw31297Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31297 raw31297Labels permutation434 hz
    mixedMoment B raw31297step0 raw31297step0Labels = mixedMoment B raw31297step1 raw31297step1Labels := by
      have ha : raw31297step1 = (fun i j => raw31297step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31297step1 raw31297step0; decide +kernel
      have hl : raw31297step1Labels = raw31297step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31297step0 raw31297step0Labels permutation33 permutation2
    _ = mixedMoment B node4669 node4669Labels := by rfl

def raw31298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw31298Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![3, -1, -2], ![2, -2, 0]]
def raw31298step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31298step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![3, -1, -2]]
def raw31298step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31298 raw31298Labels = mixedMoment B node4776 node4776Labels := by
  calc
    mixedMoment B raw31298 raw31298Labels = mixedMoment B raw31298step0 raw31298step0Labels := by
      have hz : ∀ j, raw31298 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31298step0 = (fun i j => raw31298 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31298step0 raw31298; decide +kernel
      have hl : raw31298step0Labels = raw31298Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31298 raw31298Labels permutation434 hz
    mixedMoment B raw31298step0 raw31298step0Labels = mixedMoment B raw31298step1 raw31298step1Labels := by
      have ha : raw31298step1 = (fun i j => raw31298step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31298step1 raw31298step0; decide +kernel
      have hl : raw31298step1Labels = raw31298step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31298step0 raw31298step0Labels permutation33 permutation2
    _ = mixedMoment B node4776 node4776Labels := by rfl

def raw31299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw31299Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31299step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw31299step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31299 raw31299Labels = mixedMoment B node4756 node4756Labels := by
  calc
    mixedMoment B raw31299 raw31299Labels = mixedMoment B raw31299step0 raw31299step0Labels := by
      have ha : raw31299step0 = (fun i j => raw31299 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31299step0 raw31299; decide +kernel
      have hl : raw31299step0Labels = raw31299Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31299 raw31299Labels permutation159 permutation2
    _ = mixedMoment B node4756 node4756Labels := by rfl

def raw31300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw31300Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![3, -1, -2], ![1, -1, 0]]
def raw31300step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31300step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw31300step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31300 raw31300Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw31300 raw31300Labels = mixedMoment B raw31300step0 raw31300step0Labels := by
      have hz : ∀ j, raw31300 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31300step0 = (fun i j => raw31300 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31300step0 raw31300; decide +kernel
      have hl : raw31300step0Labels = raw31300Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31300 raw31300Labels permutation434 hz
    mixedMoment B raw31300step0 raw31300step0Labels = mixedMoment B raw31300step1 raw31300step1Labels := by
      have ha : raw31300step1 = (fun i j => raw31300step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31300step1 raw31300step0; decide +kernel
      have hl : raw31300step1Labels = raw31300step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31300step0 raw31300step0Labels permutation33 permutation2
    _ = mixedMoment B node4804 node4804Labels := by rfl

def raw31301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw31301Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw31301step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31301 raw31301Labels = mixedMoment B node4336 node4336Labels := by
  calc
    mixedMoment B raw31301 raw31301Labels = mixedMoment B raw31301step0 raw31301step0Labels := by
      have hz : ∀ j, raw31301 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31301step0 = (fun i j => raw31301 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31301step0 raw31301; decide +kernel
      have hl : raw31301step0Labels = raw31301Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31301 raw31301Labels permutation434 hz
    _ = mixedMoment B node4336 node4336Labels := by rfl

def raw31302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw31302Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw31302step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31302 raw31302Labels = mixedMoment B node4671 node4671Labels := by
  calc
    mixedMoment B raw31302 raw31302Labels = mixedMoment B raw31302step0 raw31302step0Labels := by
      have hz : ∀ j, raw31302 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31302step0 = (fun i j => raw31302 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31302step0 raw31302; decide +kernel
      have hl : raw31302step0Labels = raw31302Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31302 raw31302Labels permutation434 hz
    _ = mixedMoment B node4671 node4671Labels := by rfl

def raw31303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw31303Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw31303step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31303step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw31303step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31303step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw31303step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31303step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw31303step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31303 raw31303Labels = mixedMoment B node4687 node4687Labels := by
  calc
    mixedMoment B raw31303 raw31303Labels = mixedMoment B raw31303step0 raw31303step0Labels := by
      have hz : ∀ j, raw31303 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31303step0 = (fun i j => raw31303 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31303step0 raw31303; decide +kernel
      have hl : raw31303step0Labels = raw31303Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31303 raw31303Labels permutation434 hz
    mixedMoment B raw31303step0 raw31303step0Labels = mixedMoment B raw31303step1 raw31303step1Labels := by
      have ha : raw31303step1 = (fun i j => raw31303step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31303step1 raw31303step0; decide +kernel
      have hl : raw31303step1Labels = raw31303step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31303step0 raw31303step0Labels permutation149 permutation3
    mixedMoment B raw31303step1 raw31303step1Labels = mixedMoment B raw31303step2 raw31303step2Labels := by
      have ha : raw31303step2 = -raw31303step1 := by apply Matrix.ext; change ∀ i j, raw31303step2 i j = -(raw31303step1 i j); unfold raw31303step2 raw31303step1; decide +kernel
      have hl : raw31303step2Labels = raw31303step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31303step2 raw31303step2Labels = mixedMoment B raw31303step3 raw31303step3Labels := by
      have ha : raw31303step3 = raw31303step2 := by apply Matrix.ext; unfold raw31303step3 raw31303step2; decide +kernel
      have hl : raw31303step2Labels = labelEmbedding6 ∘ raw31303step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31303step2 raw31303step2Labels raw31303step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4687 node4687Labels := by rfl

def raw31304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw31304Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31304step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw31304step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31304step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw31304step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31304step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw31304step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31304 raw31304Labels = mixedMoment B node4667 node4667Labels := by
  calc
    mixedMoment B raw31304 raw31304Labels = mixedMoment B raw31304step0 raw31304step0Labels := by
      have ha : raw31304step0 = (fun i j => raw31304 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31304step0 raw31304; decide +kernel
      have hl : raw31304step0Labels = raw31304Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31304 raw31304Labels permutation680 permutation3
    mixedMoment B raw31304step0 raw31304step0Labels = mixedMoment B raw31304step1 raw31304step1Labels := by
      have ha : raw31304step1 = -raw31304step0 := by apply Matrix.ext; change ∀ i j, raw31304step1 i j = -(raw31304step0 i j); unfold raw31304step1 raw31304step0; decide +kernel
      have hl : raw31304step1Labels = raw31304step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31304step1 raw31304step1Labels = mixedMoment B raw31304step2 raw31304step2Labels := by
      have ha : raw31304step2 = raw31304step1 := by apply Matrix.ext; unfold raw31304step2 raw31304step1; decide +kernel
      have hl : raw31304step1Labels = labelEmbedding6 ∘ raw31304step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31304step1 raw31304step1Labels raw31304step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4667 node4667Labels := by rfl

def raw31305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw31305Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31305step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw31305step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31305 raw31305Labels = mixedMoment B node4808 node4808Labels := by
  calc
    mixedMoment B raw31305 raw31305Labels = mixedMoment B raw31305step0 raw31305step0Labels := by
      have hz : ∀ j, raw31305 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31305step0 = (fun i j => raw31305 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31305step0 raw31305; decide +kernel
      have hl : raw31305step0Labels = raw31305Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31305 raw31305Labels permutation434 hz
    _ = mixedMoment B node4808 node4808Labels := by rfl

def raw31306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31306Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31306step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31306step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw31306step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31306step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw31306step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31306 raw31306Labels = mixedMoment B node3045 node3045Labels := by
  calc
    mixedMoment B raw31306 raw31306Labels = mixedMoment B raw31306step0 raw31306step0Labels := by
      have hz : ∀ j, raw31306 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31306step0 = (fun i j => raw31306 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31306step0 raw31306; decide +kernel
      have hl : raw31306step0Labels = raw31306Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31306 raw31306Labels permutation434 hz
    mixedMoment B raw31306step0 raw31306step0Labels = mixedMoment B raw31306step1 raw31306step1Labels := by
      have ha : raw31306step1 = (fun i j => raw31306step0 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31306step1 raw31306step0; decide +kernel
      have hl : raw31306step1Labels = raw31306step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31306step0 raw31306step0Labels permutation50 permutation6
    mixedMoment B raw31306step1 raw31306step1Labels = mixedMoment B raw31306step2 raw31306step2Labels := by
      have ha : raw31306step2 = -raw31306step1 := by apply Matrix.ext; change ∀ i j, raw31306step2 i j = -(raw31306step1 i j); unfold raw31306step2 raw31306step1; decide +kernel
      have hl : raw31306step2Labels = raw31306step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3045 node3045Labels := by rfl

def raw31307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31307Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31307step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31307step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw31307step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31307step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31307step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31307 raw31307Labels = mixedMoment B node3040 node3040Labels := by
  calc
    mixedMoment B raw31307 raw31307Labels = mixedMoment B raw31307step0 raw31307step0Labels := by
      have hz : ∀ j, raw31307 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31307step0 = (fun i j => raw31307 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31307step0 raw31307; decide +kernel
      have hl : raw31307step0Labels = raw31307Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31307 raw31307Labels permutation434 hz
    mixedMoment B raw31307step0 raw31307step0Labels = mixedMoment B raw31307step1 raw31307step1Labels := by
      have ha : raw31307step1 = (fun i j => raw31307step0 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31307step1 raw31307step0; decide +kernel
      have hl : raw31307step1Labels = raw31307step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31307step0 raw31307step0Labels permutation50 permutation6
    mixedMoment B raw31307step1 raw31307step1Labels = mixedMoment B raw31307step2 raw31307step2Labels := by
      have ha : raw31307step2 = -raw31307step1 := by apply Matrix.ext; change ∀ i j, raw31307step2 i j = -(raw31307step1 i j); unfold raw31307step2 raw31307step1; decide +kernel
      have hl : raw31307step2Labels = raw31307step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3040 node3040Labels := by rfl

def raw31308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31308Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31308step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw31308step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31308step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw31308step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31308 raw31308Labels = mixedMoment B node3030 node3030Labels := by
  calc
    mixedMoment B raw31308 raw31308Labels = mixedMoment B raw31308step0 raw31308step0Labels := by
      have ha : raw31308step0 = (fun i j => raw31308 (permutation248 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31308step0 raw31308; decide +kernel
      have hl : raw31308step0Labels = raw31308Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31308 raw31308Labels permutation248 permutation6
    mixedMoment B raw31308step0 raw31308step0Labels = mixedMoment B raw31308step1 raw31308step1Labels := by
      have ha : raw31308step1 = -raw31308step0 := by apply Matrix.ext; change ∀ i j, raw31308step1 i j = -(raw31308step0 i j); unfold raw31308step1 raw31308step0; decide +kernel
      have hl : raw31308step1Labels = raw31308step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3030 node3030Labels := by rfl

def raw31309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw31309Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31309step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31309step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw31309step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31309step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw31309step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31309 raw31309Labels = mixedMoment B node3039 node3039Labels := by
  calc
    mixedMoment B raw31309 raw31309Labels = mixedMoment B raw31309step0 raw31309step0Labels := by
      have hz : ∀ j, raw31309 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31309step0 = (fun i j => raw31309 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31309step0 raw31309; decide +kernel
      have hl : raw31309step0Labels = raw31309Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31309 raw31309Labels permutation434 hz
    mixedMoment B raw31309step0 raw31309step0Labels = mixedMoment B raw31309step1 raw31309step1Labels := by
      have ha : raw31309step1 = (fun i j => raw31309step0 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31309step1 raw31309step0; decide +kernel
      have hl : raw31309step1Labels = raw31309step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31309step0 raw31309step0Labels permutation50 permutation6
    mixedMoment B raw31309step1 raw31309step1Labels = mixedMoment B raw31309step2 raw31309step2Labels := by
      have ha : raw31309step2 = -raw31309step1 := by apply Matrix.ext; change ∀ i j, raw31309step2 i j = -(raw31309step1 i j); unfold raw31309step2 raw31309step1; decide +kernel
      have hl : raw31309step2Labels = raw31309step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3039 node3039Labels := by rfl

def raw31310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw31310Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw31310step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31310step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw31310step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31310step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw31310step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31310 raw31310Labels = mixedMoment B node3089 node3089Labels := by
  calc
    mixedMoment B raw31310 raw31310Labels = mixedMoment B raw31310step0 raw31310step0Labels := by
      have hz : ∀ j, raw31310 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31310step0 = (fun i j => raw31310 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31310step0 raw31310; decide +kernel
      have hl : raw31310step0Labels = raw31310Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31310 raw31310Labels permutation434 hz
    mixedMoment B raw31310step0 raw31310step0Labels = mixedMoment B raw31310step1 raw31310step1Labels := by
      have ha : raw31310step1 = (fun i j => raw31310step0 (permutation50 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31310step1 raw31310step0; decide +kernel
      have hl : raw31310step1Labels = raw31310step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31310step0 raw31310step0Labels permutation50 permutation6
    mixedMoment B raw31310step1 raw31310step1Labels = mixedMoment B raw31310step2 raw31310step2Labels := by
      have ha : raw31310step2 = -raw31310step1 := by apply Matrix.ext; change ∀ i j, raw31310step2 i j = -(raw31310step1 i j); unfold raw31310step2 raw31310step1; decide +kernel
      have hl : raw31310step2Labels = raw31310step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3089 node3089Labels := by rfl

def raw31311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31311Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31311step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31311step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31311step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31311step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw31311step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31311 raw31311Labels = mixedMoment B node1419 node1419Labels := by
  calc
    mixedMoment B raw31311 raw31311Labels = mixedMoment B raw31311step0 raw31311step0Labels := by
      have hz : ∀ j, raw31311 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31311step0 = (fun i j => raw31311 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31311step0 raw31311; decide +kernel
      have hl : raw31311step0Labels = raw31311Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31311 raw31311Labels permutation434 hz
    mixedMoment B raw31311step0 raw31311step0Labels = mixedMoment B raw31311step1 raw31311step1Labels := by
      have hz : ∀ j, raw31311step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw31311step1 = (fun i j => raw31311step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw31311step1 raw31311step0; decide +kernel
      have hl : raw31311step1Labels = raw31311step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31311step0 raw31311step0Labels permutation56 hz
    mixedMoment B raw31311step1 raw31311step1Labels = mixedMoment B raw31311step2 raw31311step2Labels := by
      have ha : raw31311step2 = (fun i j => raw31311step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31311step2 raw31311step1; decide +kernel
      have hl : raw31311step2Labels = raw31311step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31311step1 raw31311step1Labels permutation8 permutation3
    _ = mixedMoment B node1419 node1419Labels := by rfl

def raw31312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31312Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31312step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31312step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31312step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31312step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw31312step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31312 raw31312Labels = mixedMoment B node3187 node3187Labels := by
  calc
    mixedMoment B raw31312 raw31312Labels = mixedMoment B raw31312step0 raw31312step0Labels := by
      have hz : ∀ j, raw31312 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31312step0 = (fun i j => raw31312 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31312step0 raw31312; decide +kernel
      have hl : raw31312step0Labels = raw31312Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31312 raw31312Labels permutation434 hz
    mixedMoment B raw31312step0 raw31312step0Labels = mixedMoment B raw31312step1 raw31312step1Labels := by
      have hz : ∀ j, raw31312step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw31312step1 = (fun i j => raw31312step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw31312step1 raw31312step0; decide +kernel
      have hl : raw31312step1Labels = raw31312step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31312step0 raw31312step0Labels permutation56 hz
    mixedMoment B raw31312step1 raw31312step1Labels = mixedMoment B raw31312step2 raw31312step2Labels := by
      have ha : raw31312step2 = (fun i j => raw31312step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31312step2 raw31312step1; decide +kernel
      have hl : raw31312step2Labels = raw31312step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31312step1 raw31312step1Labels permutation8 permutation3
    _ = mixedMoment B node3187 node3187Labels := by rfl

def raw31313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31313Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31313step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31313step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw31313step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31313 raw31313Labels = mixedMoment B node3206 node3206Labels := by
  calc
    mixedMoment B raw31313 raw31313Labels = mixedMoment B raw31313step0 raw31313step0Labels := by
      have hz : ∀ j, raw31313 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw31313step0 = (fun i j => raw31313 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw31313step0 raw31313; decide +kernel
      have hl : raw31313step0Labels = raw31313Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31313 raw31313Labels permutation265 hz
    mixedMoment B raw31313step0 raw31313step0Labels = mixedMoment B raw31313step1 raw31313step1Labels := by
      have ha : raw31313step1 = (fun i j => raw31313step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31313step1 raw31313step0; decide +kernel
      have hl : raw31313step1Labels = raw31313step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31313step0 raw31313step0Labels permutation38 permutation3
    _ = mixedMoment B node3206 node3206Labels := by rfl

def raw31314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw31314Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31314step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31314step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31314step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31314step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 0, 1], ![-2, 1, 1]]
def raw31314step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31314step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw31314step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31314 raw31314Labels = mixedMoment B node3225 node3225Labels := by
  calc
    mixedMoment B raw31314 raw31314Labels = mixedMoment B raw31314step0 raw31314step0Labels := by
      have hz : ∀ j, raw31314 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31314step0 = (fun i j => raw31314 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31314step0 raw31314; decide +kernel
      have hl : raw31314step0Labels = raw31314Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31314 raw31314Labels permutation434 hz
    mixedMoment B raw31314step0 raw31314step0Labels = mixedMoment B raw31314step1 raw31314step1Labels := by
      have hz : ∀ j, raw31314step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw31314step1 = (fun i j => raw31314step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw31314step1 raw31314step0; decide +kernel
      have hl : raw31314step1Labels = raw31314step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31314step0 raw31314step0Labels permutation56 hz
    mixedMoment B raw31314step1 raw31314step1Labels = mixedMoment B raw31314step2 raw31314step2Labels := by
      have ha : raw31314step2 = (fun i j => raw31314step1 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31314step2 raw31314step1; decide +kernel
      have hl : raw31314step2Labels = raw31314step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31314step1 raw31314step1Labels permutation12 permutation6
    mixedMoment B raw31314step2 raw31314step2Labels = mixedMoment B raw31314step3 raw31314step3Labels := by
      have ha : raw31314step3 = -raw31314step2 := by apply Matrix.ext; change ∀ i j, raw31314step3 i j = -(raw31314step2 i j); unfold raw31314step3 raw31314step2; decide +kernel
      have hl : raw31314step3Labels = raw31314step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3225 node3225Labels := by rfl

def raw31315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw31315Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw31315step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31315step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw31315step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31315step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw31315step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31315 raw31315Labels = mixedMoment B node3230 node3230Labels := by
  calc
    mixedMoment B raw31315 raw31315Labels = mixedMoment B raw31315step0 raw31315step0Labels := by
      have hz : ∀ j, raw31315 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31315step0 = (fun i j => raw31315 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31315step0 raw31315; decide +kernel
      have hl : raw31315step0Labels = raw31315Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31315 raw31315Labels permutation434 hz
    mixedMoment B raw31315step0 raw31315step0Labels = mixedMoment B raw31315step1 raw31315step1Labels := by
      have hz : ∀ j, raw31315step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw31315step1 = (fun i j => raw31315step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw31315step1 raw31315step0; decide +kernel
      have hl : raw31315step1Labels = raw31315step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31315step0 raw31315step0Labels permutation56 hz
    mixedMoment B raw31315step1 raw31315step1Labels = mixedMoment B raw31315step2 raw31315step2Labels := by
      have ha : raw31315step2 = (fun i j => raw31315step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31315step2 raw31315step1; decide +kernel
      have hl : raw31315step2Labels = raw31315step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31315step1 raw31315step1Labels permutation9 permutation3
    _ = mixedMoment B node3230 node3230Labels := by rfl

def raw31316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31316Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31316step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31316step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31316step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31316step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31316 raw31316Labels = mixedMoment B node1343 node1343Labels := by
  calc
    mixedMoment B raw31316 raw31316Labels = mixedMoment B raw31316step0 raw31316step0Labels := by
      have hz : ∀ j, raw31316 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31316step0 = (fun i j => raw31316 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31316step0 raw31316; decide +kernel
      have hl : raw31316step0Labels = raw31316Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31316 raw31316Labels permutation434 hz
    mixedMoment B raw31316step0 raw31316step0Labels = mixedMoment B raw31316step1 raw31316step1Labels := by
      have ha : raw31316step1 = (fun i j => raw31316step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31316step1 raw31316step0; decide +kernel
      have hl : raw31316step1Labels = raw31316step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31316step0 raw31316step0Labels permutation32 permutation3
    _ = mixedMoment B node1343 node1343Labels := by rfl

def raw31317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31317Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31317step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31317step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31317step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31317 raw31317Labels = mixedMoment B node3141 node3141Labels := by
  calc
    mixedMoment B raw31317 raw31317Labels = mixedMoment B raw31317step0 raw31317step0Labels := by
      have hz : ∀ j, raw31317 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31317step0 = (fun i j => raw31317 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31317step0 raw31317; decide +kernel
      have hl : raw31317step0Labels = raw31317Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31317 raw31317Labels permutation434 hz
    mixedMoment B raw31317step0 raw31317step0Labels = mixedMoment B raw31317step1 raw31317step1Labels := by
      have ha : raw31317step1 = (fun i j => raw31317step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31317step1 raw31317step0; decide +kernel
      have hl : raw31317step1Labels = raw31317step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31317step0 raw31317step0Labels permutation32 permutation3
    _ = mixedMoment B node3141 node3141Labels := by rfl

def raw31318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31318Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31318step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31318step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31318 raw31318Labels = mixedMoment B node3190 node3190Labels := by
  calc
    mixedMoment B raw31318 raw31318Labels = mixedMoment B raw31318step0 raw31318step0Labels := by
      have ha : raw31318step0 = (fun i j => raw31318 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31318step0 raw31318; decide +kernel
      have hl : raw31318step0Labels = raw31318Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31318 raw31318Labels permutation158 permutation3
    _ = mixedMoment B node3190 node3190Labels := by rfl

def raw31319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw31319Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31319step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31319step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw31319step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31319 raw31319Labels = mixedMoment B node3210 node3210Labels := by
  calc
    mixedMoment B raw31319 raw31319Labels = mixedMoment B raw31319step0 raw31319step0Labels := by
      have hz : ∀ j, raw31319 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31319step0 = (fun i j => raw31319 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31319step0 raw31319; decide +kernel
      have hl : raw31319step0Labels = raw31319Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31319 raw31319Labels permutation434 hz
    mixedMoment B raw31319step0 raw31319step0Labels = mixedMoment B raw31319step1 raw31319step1Labels := by
      have ha : raw31319step1 = (fun i j => raw31319step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31319step1 raw31319step0; decide +kernel
      have hl : raw31319step1Labels = raw31319step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31319step0 raw31319step0Labels permutation34 permutation3
    _ = mixedMoment B node3210 node3210Labels := by rfl

def raw31320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw31320Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31320step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2], ![1, -1, 0]]
def raw31320step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31320step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw31320step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31320 raw31320Labels = mixedMoment B node3214 node3214Labels := by
  calc
    mixedMoment B raw31320 raw31320Labels = mixedMoment B raw31320step0 raw31320step0Labels := by
      have hz : ∀ j, raw31320 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31320step0 = (fun i j => raw31320 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31320step0 raw31320; decide +kernel
      have hl : raw31320step0Labels = raw31320Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31320 raw31320Labels permutation434 hz
    mixedMoment B raw31320step0 raw31320step0Labels = mixedMoment B raw31320step1 raw31320step1Labels := by
      have ha : raw31320step1 = (fun i j => raw31320step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31320step1 raw31320step0; decide +kernel
      have hl : raw31320step1Labels = raw31320step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31320step0 raw31320step0Labels permutation33 permutation3
    _ = mixedMoment B node3214 node3214Labels := by rfl

def raw31321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31321Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31321step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31321step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31321 raw31321Labels = mixedMoment B node1330 node1330Labels := by
  calc
    mixedMoment B raw31321 raw31321Labels = mixedMoment B raw31321step0 raw31321step0Labels := by
      have ha : raw31321step0 = (fun i j => raw31321 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31321step0 raw31321; decide +kernel
      have hl : raw31321step0Labels = raw31321Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31321 raw31321Labels permutation152 permutation3
    _ = mixedMoment B node1330 node1330Labels := by rfl

def raw31322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31322Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31322step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31322step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31322 raw31322Labels = mixedMoment B node3134 node3134Labels := by
  calc
    mixedMoment B raw31322 raw31322Labels = mixedMoment B raw31322step0 raw31322step0Labels := by
      have ha : raw31322step0 = (fun i j => raw31322 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31322step0 raw31322; decide +kernel
      have hl : raw31322step0Labels = raw31322Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31322 raw31322Labels permutation152 permutation3
    _ = mixedMoment B node3134 node3134Labels := by rfl

def raw31323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31323Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31323step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31323step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31323 raw31323Labels = mixedMoment B node3163 node3163Labels := by
  calc
    mixedMoment B raw31323 raw31323Labels = mixedMoment B raw31323step0 raw31323step0Labels := by
      have ha : raw31323step0 = (fun i j => raw31323 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31323step0 raw31323; decide +kernel
      have hl : raw31323step0Labels = raw31323Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31323 raw31323Labels permutation176 permutation3
    _ = mixedMoment B node3163 node3163Labels := by rfl

def raw31324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw31324Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31324step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw31324step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31324 raw31324Labels = mixedMoment B node3202 node3202Labels := by
  calc
    mixedMoment B raw31324 raw31324Labels = mixedMoment B raw31324step0 raw31324step0Labels := by
      have ha : raw31324step0 = (fun i j => raw31324 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31324step0 raw31324; decide +kernel
      have hl : raw31324step0Labels = raw31324Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31324 raw31324Labels permutation154 permutation3
    _ = mixedMoment B node3202 node3202Labels := by rfl

def raw31325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw31325Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31325step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw31325step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31325 raw31325Labels = mixedMoment B node3205 node3205Labels := by
  calc
    mixedMoment B raw31325 raw31325Labels = mixedMoment B raw31325step0 raw31325step0Labels := by
      have ha : raw31325step0 = (fun i j => raw31325 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31325step0 raw31325; decide +kernel
      have hl : raw31325step0Labels = raw31325Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31325 raw31325Labels permutation153 permutation3
    _ = mixedMoment B node3205 node3205Labels := by rfl

def raw31326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw31326Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![3, -1, -2], ![2, -2, 0]]
def raw31326step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31326step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw31326step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31326 raw31326Labels = mixedMoment B node1334 node1334Labels := by
  calc
    mixedMoment B raw31326 raw31326Labels = mixedMoment B raw31326step0 raw31326step0Labels := by
      have hz : ∀ j, raw31326 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31326step0 = (fun i j => raw31326 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31326step0 raw31326; decide +kernel
      have hl : raw31326step0Labels = raw31326Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31326 raw31326Labels permutation434 hz
    mixedMoment B raw31326step0 raw31326step0Labels = mixedMoment B raw31326step1 raw31326step1Labels := by
      have ha : raw31326step1 = (fun i j => raw31326step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31326step1 raw31326step0; decide +kernel
      have hl : raw31326step1Labels = raw31326step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31326step0 raw31326step0Labels permutation33 permutation3
    _ = mixedMoment B node1334 node1334Labels := by rfl

def raw31327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw31327Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![3, -1, -2], ![2, -2, 0]]
def raw31327step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31327step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![0, -1, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw31327step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31327step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw31327step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31327 raw31327Labels = mixedMoment B node2803 node2803Labels := by
  calc
    mixedMoment B raw31327 raw31327Labels = mixedMoment B raw31327step0 raw31327step0Labels := by
      have hz : ∀ j, raw31327 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31327step0 = (fun i j => raw31327 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31327step0 raw31327; decide +kernel
      have hl : raw31327step0Labels = raw31327Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31327 raw31327Labels permutation434 hz
    mixedMoment B raw31327step0 raw31327step0Labels = mixedMoment B raw31327step1 raw31327step1Labels := by
      have ha : raw31327step1 = (fun i j => raw31327step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31327step1 raw31327step0; decide +kernel
      have hl : raw31327step1Labels = raw31327step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31327step0 raw31327step0Labels permutation127 permutation3
    mixedMoment B raw31327step1 raw31327step1Labels = mixedMoment B raw31327step2 raw31327step2Labels := by
      have ha : raw31327step2 = -raw31327step1 := by apply Matrix.ext; change ∀ i j, raw31327step2 i j = -(raw31327step1 i j); unfold raw31327step2 raw31327step1; decide +kernel
      have hl : raw31327step2Labels = raw31327step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2803 node2803Labels := by rfl

def raw31328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw31328Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31328step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![3, -1, -2], ![2, -2, 0]]
def raw31328step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31328step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw31328step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31328step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw31328step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31328 raw31328Labels = mixedMoment B node2816 node2816Labels := by
  calc
    mixedMoment B raw31328 raw31328Labels = mixedMoment B raw31328step0 raw31328step0Labels := by
      have hz : ∀ j, raw31328 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31328step0 = (fun i j => raw31328 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31328step0 raw31328; decide +kernel
      have hl : raw31328step0Labels = raw31328Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31328 raw31328Labels permutation434 hz
    mixedMoment B raw31328step0 raw31328step0Labels = mixedMoment B raw31328step1 raw31328step1Labels := by
      have ha : raw31328step1 = (fun i j => raw31328step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31328step1 raw31328step0; decide +kernel
      have hl : raw31328step1Labels = raw31328step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31328step0 raw31328step0Labels permutation125 permutation3
    mixedMoment B raw31328step1 raw31328step1Labels = mixedMoment B raw31328step2 raw31328step2Labels := by
      have ha : raw31328step2 = -raw31328step1 := by apply Matrix.ext; change ∀ i j, raw31328step2 i j = -(raw31328step1 i j); unfold raw31328step2 raw31328step1; decide +kernel
      have hl : raw31328step2Labels = raw31328step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2816 node2816Labels := by rfl

def raw31329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw31329Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31329step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![2, 0, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw31329step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31329step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw31329step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31329 raw31329Labels = mixedMoment B node2800 node2800Labels := by
  calc
    mixedMoment B raw31329 raw31329Labels = mixedMoment B raw31329step0 raw31329step0Labels := by
      have ha : raw31329step0 = (fun i j => raw31329 (permutation582 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31329step0 raw31329; decide +kernel
      have hl : raw31329step0Labels = raw31329Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31329 raw31329Labels permutation582 permutation3
    mixedMoment B raw31329step0 raw31329step0Labels = mixedMoment B raw31329step1 raw31329step1Labels := by
      have ha : raw31329step1 = -raw31329step0 := by apply Matrix.ext; change ∀ i j, raw31329step1 i j = -(raw31329step0 i j); unfold raw31329step1 raw31329step0; decide +kernel
      have hl : raw31329step1Labels = raw31329step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2800 node2800Labels := by rfl

def raw31330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw31330Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![3, -1, -2], ![1, -1, 0]]
def raw31330step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31330step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw31330step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31330step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw31330step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31330 raw31330Labels = mixedMoment B node2941 node2941Labels := by
  calc
    mixedMoment B raw31330 raw31330Labels = mixedMoment B raw31330step0 raw31330step0Labels := by
      have hz : ∀ j, raw31330 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31330step0 = (fun i j => raw31330 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31330step0 raw31330; decide +kernel
      have hl : raw31330step0Labels = raw31330Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31330 raw31330Labels permutation434 hz
    mixedMoment B raw31330step0 raw31330step0Labels = mixedMoment B raw31330step1 raw31330step1Labels := by
      have ha : raw31330step1 = (fun i j => raw31330step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31330step1 raw31330step0; decide +kernel
      have hl : raw31330step1Labels = raw31330step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31330step0 raw31330step0Labels permutation127 permutation3
    mixedMoment B raw31330step1 raw31330step1Labels = mixedMoment B raw31330step2 raw31330step2Labels := by
      have ha : raw31330step2 = -raw31330step1 := by apply Matrix.ext; change ∀ i j, raw31330step2 i j = -(raw31330step1 i j); unfold raw31330step2 raw31330step1; decide +kernel
      have hl : raw31330step2Labels = raw31330step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2941 node2941Labels := by rfl

def raw31331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw31331Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw31331step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31331step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![3, 0, -3]]
def raw31331step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31331 raw31331Labels = mixedMoment B node1332 node1332Labels := by
  calc
    mixedMoment B raw31331 raw31331Labels = mixedMoment B raw31331step0 raw31331step0Labels := by
      have hz : ∀ j, raw31331 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31331step0 = (fun i j => raw31331 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31331step0 raw31331; decide +kernel
      have hl : raw31331step0Labels = raw31331Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31331 raw31331Labels permutation434 hz
    mixedMoment B raw31331step0 raw31331step0Labels = mixedMoment B raw31331step1 raw31331step1Labels := by
      have ha : raw31331step1 = (fun i j => raw31331step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31331step1 raw31331step0; decide +kernel
      have hl : raw31331step1Labels = raw31331step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31331step0 raw31331step0Labels permutation32 permutation3
    _ = mixedMoment B node1332 node1332Labels := by rfl

def raw31332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw31332Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31332step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw31332step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31332step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 0, 2], ![-3, 3, 0]]
def raw31332step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31332step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![2, 0, -2], ![3, -3, 0]]
def raw31332step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31332 raw31332Labels = mixedMoment B node1797 node1797Labels := by
  calc
    mixedMoment B raw31332 raw31332Labels = mixedMoment B raw31332step0 raw31332step0Labels := by
      have hz : ∀ j, raw31332 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31332step0 = (fun i j => raw31332 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31332step0 raw31332; decide +kernel
      have hl : raw31332step0Labels = raw31332Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31332 raw31332Labels permutation434 hz
    mixedMoment B raw31332step0 raw31332step0Labels = mixedMoment B raw31332step1 raw31332step1Labels := by
      have ha : raw31332step1 = (fun i j => raw31332step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31332step1 raw31332step0; decide +kernel
      have hl : raw31332step1Labels = raw31332step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31332step0 raw31332step0Labels permutation151 permutation3
    mixedMoment B raw31332step1 raw31332step1Labels = mixedMoment B raw31332step2 raw31332step2Labels := by
      have ha : raw31332step2 = -raw31332step1 := by apply Matrix.ext; change ∀ i j, raw31332step2 i j = -(raw31332step1 i j); unfold raw31332step2 raw31332step1; decide +kernel
      have hl : raw31332step2Labels = raw31332step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1797 node1797Labels := by rfl

def raw31333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw31333Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31333step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, 0, -2], ![3, -3, 0]]
def raw31333step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31333step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw31333step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31333step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw31333step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31333 raw31333Labels = mixedMoment B node1813 node1813Labels := by
  calc
    mixedMoment B raw31333 raw31333Labels = mixedMoment B raw31333step0 raw31333step0Labels := by
      have hz : ∀ j, raw31333 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31333step0 = (fun i j => raw31333 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31333step0 raw31333; decide +kernel
      have hl : raw31333step0Labels = raw31333Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31333 raw31333Labels permutation434 hz
    mixedMoment B raw31333step0 raw31333step0Labels = mixedMoment B raw31333step1 raw31333step1Labels := by
      have ha : raw31333step1 = (fun i j => raw31333step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31333step1 raw31333step0; decide +kernel
      have hl : raw31333step1Labels = raw31333step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31333step0 raw31333step0Labels permutation149 permutation3
    mixedMoment B raw31333step1 raw31333step1Labels = mixedMoment B raw31333step2 raw31333step2Labels := by
      have ha : raw31333step2 = -raw31333step1 := by apply Matrix.ext; change ∀ i j, raw31333step2 i j = -(raw31333step1 i j); unfold raw31333step2 raw31333step1; decide +kernel
      have hl : raw31333step2Labels = raw31333step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1813 node1813Labels := by rfl

def raw31334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw31334Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31334step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw31334step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31334step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw31334step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31334 raw31334Labels = mixedMoment B node1793 node1793Labels := by
  calc
    mixedMoment B raw31334 raw31334Labels = mixedMoment B raw31334step0 raw31334step0Labels := by
      have ha : raw31334step0 = (fun i j => raw31334 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31334step0 raw31334; decide +kernel
      have hl : raw31334step0Labels = raw31334Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31334 raw31334Labels permutation680 permutation3
    mixedMoment B raw31334step0 raw31334step0Labels = mixedMoment B raw31334step1 raw31334step1Labels := by
      have ha : raw31334step1 = -raw31334step0 := by apply Matrix.ext; change ∀ i j, raw31334step1 i j = -(raw31334step0 i j); unfold raw31334step1 raw31334step0; decide +kernel
      have hl : raw31334step1Labels = raw31334step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1793 node1793Labels := by rfl

def raw31335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw31335Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw31335step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31335step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw31335step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31335step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw31335step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31335 raw31335Labels = mixedMoment B node2092 node2092Labels := by
  calc
    mixedMoment B raw31335 raw31335Labels = mixedMoment B raw31335step0 raw31335step0Labels := by
      have hz : ∀ j, raw31335 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31335step0 = (fun i j => raw31335 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31335step0 raw31335; decide +kernel
      have hl : raw31335step0Labels = raw31335Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31335 raw31335Labels permutation434 hz
    mixedMoment B raw31335step0 raw31335step0Labels = mixedMoment B raw31335step1 raw31335step1Labels := by
      have ha : raw31335step1 = (fun i j => raw31335step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31335step1 raw31335step0; decide +kernel
      have hl : raw31335step1Labels = raw31335step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31335step0 raw31335step0Labels permutation151 permutation3
    mixedMoment B raw31335step1 raw31335step1Labels = mixedMoment B raw31335step2 raw31335step2Labels := by
      have ha : raw31335step2 = -raw31335step1 := by apply Matrix.ext; change ∀ i j, raw31335step2 i j = -(raw31335step1 i j); unfold raw31335step2 raw31335step1; decide +kernel
      have hl : raw31335step2Labels = raw31335step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2092 node2092Labels := by rfl

def raw31336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31336Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31336step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31336step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31336step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw31336step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31336step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw31336step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31336step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw31336step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31336 raw31336Labels = mixedMoment B node2677 node2677Labels := by
  calc
    mixedMoment B raw31336 raw31336Labels = mixedMoment B raw31336step0 raw31336step0Labels := by
      have hz : ∀ j, raw31336 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31336step0 = (fun i j => raw31336 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31336step0 raw31336; decide +kernel
      have hl : raw31336step0Labels = raw31336Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31336 raw31336Labels permutation434 hz
    mixedMoment B raw31336step0 raw31336step0Labels = mixedMoment B raw31336step1 raw31336step1Labels := by
      have ha : raw31336step1 = (fun i j => raw31336step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31336step1 raw31336step0; decide +kernel
      have hl : raw31336step1Labels = raw31336step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31336step0 raw31336step0Labels permutation36 permutation7
    mixedMoment B raw31336step1 raw31336step1Labels = mixedMoment B raw31336step2 raw31336step2Labels := by
      have ha : raw31336step2 = -raw31336step1 := by apply Matrix.ext; change ∀ i j, raw31336step2 i j = -(raw31336step1 i j); unfold raw31336step2 raw31336step1; decide +kernel
      have hl : raw31336step2Labels = raw31336step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31336step2 raw31336step2Labels = mixedMoment B raw31336step3 raw31336step3Labels := by
      have ha : raw31336step3 = raw31336step2 := by apply Matrix.ext; unfold raw31336step3 raw31336step2; decide +kernel
      have hl : raw31336step2Labels = labelEmbedding1 ∘ raw31336step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31336step2 raw31336step2Labels raw31336step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2677 node2677Labels := by rfl

def raw31337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31337Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31337step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31337step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw31337step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31337step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw31337step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31337step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw31337step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31337 raw31337Labels = mixedMoment B node2729 node2729Labels := by
  calc
    mixedMoment B raw31337 raw31337Labels = mixedMoment B raw31337step0 raw31337step0Labels := by
      have hz : ∀ j, raw31337 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31337step0 = (fun i j => raw31337 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31337step0 raw31337; decide +kernel
      have hl : raw31337step0Labels = raw31337Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31337 raw31337Labels permutation434 hz
    mixedMoment B raw31337step0 raw31337step0Labels = mixedMoment B raw31337step1 raw31337step1Labels := by
      have ha : raw31337step1 = (fun i j => raw31337step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31337step1 raw31337step0; decide +kernel
      have hl : raw31337step1Labels = raw31337step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31337step0 raw31337step0Labels permutation36 permutation7
    mixedMoment B raw31337step1 raw31337step1Labels = mixedMoment B raw31337step2 raw31337step2Labels := by
      have ha : raw31337step2 = -raw31337step1 := by apply Matrix.ext; change ∀ i j, raw31337step2 i j = -(raw31337step1 i j); unfold raw31337step2 raw31337step1; decide +kernel
      have hl : raw31337step2Labels = raw31337step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31337step2 raw31337step2Labels = mixedMoment B raw31337step3 raw31337step3Labels := by
      have ha : raw31337step3 = raw31337step2 := by apply Matrix.ext; unfold raw31337step3 raw31337step2; decide +kernel
      have hl : raw31337step2Labels = labelEmbedding1 ∘ raw31337step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31337step2 raw31337step2Labels raw31337step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2729 node2729Labels := by rfl

def raw31338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31338Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31338step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw31338step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31338step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw31338step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31338step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw31338step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31338 raw31338Labels = mixedMoment B node2697 node2697Labels := by
  calc
    mixedMoment B raw31338 raw31338Labels = mixedMoment B raw31338step0 raw31338step0Labels := by
      have ha : raw31338step0 = (fun i j => raw31338 (permutation162 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31338step0 raw31338; decide +kernel
      have hl : raw31338step0Labels = raw31338Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31338 raw31338Labels permutation162 permutation7
    mixedMoment B raw31338step0 raw31338step0Labels = mixedMoment B raw31338step1 raw31338step1Labels := by
      have ha : raw31338step1 = -raw31338step0 := by apply Matrix.ext; change ∀ i j, raw31338step1 i j = -(raw31338step0 i j); unfold raw31338step1 raw31338step0; decide +kernel
      have hl : raw31338step1Labels = raw31338step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31338step1 raw31338step1Labels = mixedMoment B raw31338step2 raw31338step2Labels := by
      have ha : raw31338step2 = raw31338step1 := by apply Matrix.ext; unfold raw31338step2 raw31338step1; decide +kernel
      have hl : raw31338step1Labels = labelEmbedding1 ∘ raw31338step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31338step1 raw31338step1Labels raw31338step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2697 node2697Labels := by rfl

def raw31339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw31339Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31339step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31339step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw31339step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31339step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw31339step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31339step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw31339step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31339 raw31339Labels = mixedMoment B node2731 node2731Labels := by
  calc
    mixedMoment B raw31339 raw31339Labels = mixedMoment B raw31339step0 raw31339step0Labels := by
      have hz : ∀ j, raw31339 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31339step0 = (fun i j => raw31339 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31339step0 raw31339; decide +kernel
      have hl : raw31339step0Labels = raw31339Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31339 raw31339Labels permutation434 hz
    mixedMoment B raw31339step0 raw31339step0Labels = mixedMoment B raw31339step1 raw31339step1Labels := by
      have ha : raw31339step1 = (fun i j => raw31339step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31339step1 raw31339step0; decide +kernel
      have hl : raw31339step1Labels = raw31339step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31339step0 raw31339step0Labels permutation36 permutation7
    mixedMoment B raw31339step1 raw31339step1Labels = mixedMoment B raw31339step2 raw31339step2Labels := by
      have ha : raw31339step2 = -raw31339step1 := by apply Matrix.ext; change ∀ i j, raw31339step2 i j = -(raw31339step1 i j); unfold raw31339step2 raw31339step1; decide +kernel
      have hl : raw31339step2Labels = raw31339step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31339step2 raw31339step2Labels = mixedMoment B raw31339step3 raw31339step3Labels := by
      have ha : raw31339step3 = raw31339step2 := by apply Matrix.ext; unfold raw31339step3 raw31339step2; decide +kernel
      have hl : raw31339step2Labels = labelEmbedding1 ∘ raw31339step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31339step2 raw31339step2Labels raw31339step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2731 node2731Labels := by rfl

def raw31340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw31340Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw31340step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31340step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw31340step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31340step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw31340step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31340step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw31340step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31340 raw31340Labels = mixedMoment B node2722 node2722Labels := by
  calc
    mixedMoment B raw31340 raw31340Labels = mixedMoment B raw31340step0 raw31340step0Labels := by
      have hz : ∀ j, raw31340 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31340step0 = (fun i j => raw31340 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31340step0 raw31340; decide +kernel
      have hl : raw31340step0Labels = raw31340Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31340 raw31340Labels permutation434 hz
    mixedMoment B raw31340step0 raw31340step0Labels = mixedMoment B raw31340step1 raw31340step1Labels := by
      have ha : raw31340step1 = (fun i j => raw31340step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31340step1 raw31340step0; decide +kernel
      have hl : raw31340step1Labels = raw31340step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31340step0 raw31340step0Labels permutation36 permutation7
    mixedMoment B raw31340step1 raw31340step1Labels = mixedMoment B raw31340step2 raw31340step2Labels := by
      have ha : raw31340step2 = -raw31340step1 := by apply Matrix.ext; change ∀ i j, raw31340step2 i j = -(raw31340step1 i j); unfold raw31340step2 raw31340step1; decide +kernel
      have hl : raw31340step2Labels = raw31340step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31340step2 raw31340step2Labels = mixedMoment B raw31340step3 raw31340step3Labels := by
      have ha : raw31340step3 = raw31340step2 := by apply Matrix.ext; unfold raw31340step3 raw31340step2; decide +kernel
      have hl : raw31340step2Labels = labelEmbedding1 ∘ raw31340step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31340step2 raw31340step2Labels raw31340step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2722 node2722Labels := by rfl

def raw31341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31341Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31341step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31341step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31341step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31341step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31341step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw31341step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31341step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw31341step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31341step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw31341step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31341 raw31341Labels = mixedMoment B node1738 node1738Labels := by
  calc
    mixedMoment B raw31341 raw31341Labels = mixedMoment B raw31341step0 raw31341step0Labels := by
      have hz : ∀ j, raw31341 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31341step0 = (fun i j => raw31341 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31341step0 raw31341; decide +kernel
      have hl : raw31341step0Labels = raw31341Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31341 raw31341Labels permutation434 hz
    mixedMoment B raw31341step0 raw31341step0Labels = mixedMoment B raw31341step1 raw31341step1Labels := by
      have hz : ∀ j, raw31341step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw31341step1 = (fun i j => raw31341step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw31341step1 raw31341step0; decide +kernel
      have hl : raw31341step1Labels = raw31341step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31341step0 raw31341step0Labels permutation56 hz
    mixedMoment B raw31341step1 raw31341step1Labels = mixedMoment B raw31341step2 raw31341step2Labels := by
      have ha : raw31341step2 = (fun i j => raw31341step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31341step2 raw31341step1; decide +kernel
      have hl : raw31341step2Labels = raw31341step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31341step1 raw31341step1Labels permutation12 permutation7
    mixedMoment B raw31341step2 raw31341step2Labels = mixedMoment B raw31341step3 raw31341step3Labels := by
      have ha : raw31341step3 = -raw31341step2 := by apply Matrix.ext; change ∀ i j, raw31341step3 i j = -(raw31341step2 i j); unfold raw31341step3 raw31341step2; decide +kernel
      have hl : raw31341step3Labels = raw31341step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31341step3 raw31341step3Labels = mixedMoment B raw31341step4 raw31341step4Labels := by
      have ha : raw31341step4 = raw31341step3 := by apply Matrix.ext; unfold raw31341step4 raw31341step3; decide +kernel
      have hl : raw31341step3Labels = labelEmbedding1 ∘ raw31341step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31341step3 raw31341step3Labels raw31341step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1738 node1738Labels := by rfl

def raw31342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31342Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31342step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31342step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31342step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31342step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31342step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw31342step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31342step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw31342step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31342step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw31342step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31342 raw31342Labels = mixedMoment B node2276 node2276Labels := by
  calc
    mixedMoment B raw31342 raw31342Labels = mixedMoment B raw31342step0 raw31342step0Labels := by
      have hz : ∀ j, raw31342 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31342step0 = (fun i j => raw31342 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31342step0 raw31342; decide +kernel
      have hl : raw31342step0Labels = raw31342Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31342 raw31342Labels permutation434 hz
    mixedMoment B raw31342step0 raw31342step0Labels = mixedMoment B raw31342step1 raw31342step1Labels := by
      have hz : ∀ j, raw31342step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw31342step1 = (fun i j => raw31342step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw31342step1 raw31342step0; decide +kernel
      have hl : raw31342step1Labels = raw31342step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31342step0 raw31342step0Labels permutation56 hz
    mixedMoment B raw31342step1 raw31342step1Labels = mixedMoment B raw31342step2 raw31342step2Labels := by
      have ha : raw31342step2 = (fun i j => raw31342step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31342step2 raw31342step1; decide +kernel
      have hl : raw31342step2Labels = raw31342step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31342step1 raw31342step1Labels permutation12 permutation7
    mixedMoment B raw31342step2 raw31342step2Labels = mixedMoment B raw31342step3 raw31342step3Labels := by
      have ha : raw31342step3 = -raw31342step2 := by apply Matrix.ext; change ∀ i j, raw31342step3 i j = -(raw31342step2 i j); unfold raw31342step3 raw31342step2; decide +kernel
      have hl : raw31342step3Labels = raw31342step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31342step3 raw31342step3Labels = mixedMoment B raw31342step4 raw31342step4Labels := by
      have ha : raw31342step4 = raw31342step3 := by apply Matrix.ext; unfold raw31342step4 raw31342step3; decide +kernel
      have hl : raw31342step3Labels = labelEmbedding1 ∘ raw31342step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31342step3 raw31342step3Labels raw31342step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2276 node2276Labels := by rfl

def raw31343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31343Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31343step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31343step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31343step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw31343step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31343step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw31343step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31343step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw31343step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31343 raw31343Labels = mixedMoment B node2215 node2215Labels := by
  calc
    mixedMoment B raw31343 raw31343Labels = mixedMoment B raw31343step0 raw31343step0Labels := by
      have hz : ∀ j, raw31343 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw31343step0 = (fun i j => raw31343 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw31343step0 raw31343; decide +kernel
      have hl : raw31343step0Labels = raw31343Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31343 raw31343Labels permutation265 hz
    mixedMoment B raw31343step0 raw31343step0Labels = mixedMoment B raw31343step1 raw31343step1Labels := by
      have ha : raw31343step1 = (fun i j => raw31343step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31343step1 raw31343step0; decide +kernel
      have hl : raw31343step1Labels = raw31343step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31343step0 raw31343step0Labels permutation42 permutation7
    mixedMoment B raw31343step1 raw31343step1Labels = mixedMoment B raw31343step2 raw31343step2Labels := by
      have ha : raw31343step2 = -raw31343step1 := by apply Matrix.ext; change ∀ i j, raw31343step2 i j = -(raw31343step1 i j); unfold raw31343step2 raw31343step1; decide +kernel
      have hl : raw31343step2Labels = raw31343step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31343step2 raw31343step2Labels = mixedMoment B raw31343step3 raw31343step3Labels := by
      have ha : raw31343step3 = raw31343step2 := by apply Matrix.ext; unfold raw31343step3 raw31343step2; decide +kernel
      have hl : raw31343step2Labels = labelEmbedding1 ∘ raw31343step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31343step2 raw31343step2Labels raw31343step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2215 node2215Labels := by rfl

def raw31344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw31344Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31344step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31344step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31344step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31344step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw31344step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31344step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw31344step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31344step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw31344step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31344 raw31344Labels = mixedMoment B node2278 node2278Labels := by
  calc
    mixedMoment B raw31344 raw31344Labels = mixedMoment B raw31344step0 raw31344step0Labels := by
      have hz : ∀ j, raw31344 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31344step0 = (fun i j => raw31344 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31344step0 raw31344; decide +kernel
      have hl : raw31344step0Labels = raw31344Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31344 raw31344Labels permutation434 hz
    mixedMoment B raw31344step0 raw31344step0Labels = mixedMoment B raw31344step1 raw31344step1Labels := by
      have hz : ∀ j, raw31344step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw31344step1 = (fun i j => raw31344step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw31344step1 raw31344step0; decide +kernel
      have hl : raw31344step1Labels = raw31344step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31344step0 raw31344step0Labels permutation56 hz
    mixedMoment B raw31344step1 raw31344step1Labels = mixedMoment B raw31344step2 raw31344step2Labels := by
      have ha : raw31344step2 = (fun i j => raw31344step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31344step2 raw31344step1; decide +kernel
      have hl : raw31344step2Labels = raw31344step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31344step1 raw31344step1Labels permutation12 permutation7
    mixedMoment B raw31344step2 raw31344step2Labels = mixedMoment B raw31344step3 raw31344step3Labels := by
      have ha : raw31344step3 = -raw31344step2 := by apply Matrix.ext; change ∀ i j, raw31344step3 i j = -(raw31344step2 i j); unfold raw31344step3 raw31344step2; decide +kernel
      have hl : raw31344step3Labels = raw31344step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31344step3 raw31344step3Labels = mixedMoment B raw31344step4 raw31344step4Labels := by
      have ha : raw31344step4 = raw31344step3 := by apply Matrix.ext; unfold raw31344step4 raw31344step3; decide +kernel
      have hl : raw31344step3Labels = labelEmbedding1 ∘ raw31344step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31344step3 raw31344step3Labels raw31344step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2278 node2278Labels := by rfl

def raw31345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw31345Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw31345step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31345step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![2, 0, -2], ![1, -1, 0]]
def raw31345step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31345step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw31345step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31345step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw31345step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31345step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw31345step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31345 raw31345Labels = mixedMoment B node2264 node2264Labels := by
  calc
    mixedMoment B raw31345 raw31345Labels = mixedMoment B raw31345step0 raw31345step0Labels := by
      have hz : ∀ j, raw31345 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31345step0 = (fun i j => raw31345 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31345step0 raw31345; decide +kernel
      have hl : raw31345step0Labels = raw31345Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31345 raw31345Labels permutation434 hz
    mixedMoment B raw31345step0 raw31345step0Labels = mixedMoment B raw31345step1 raw31345step1Labels := by
      have hz : ∀ j, raw31345step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw31345step1 = (fun i j => raw31345step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw31345step1 raw31345step0; decide +kernel
      have hl : raw31345step1Labels = raw31345step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31345step0 raw31345step0Labels permutation56 hz
    mixedMoment B raw31345step1 raw31345step1Labels = mixedMoment B raw31345step2 raw31345step2Labels := by
      have ha : raw31345step2 = (fun i j => raw31345step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31345step2 raw31345step1; decide +kernel
      have hl : raw31345step2Labels = raw31345step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31345step1 raw31345step1Labels permutation12 permutation7
    mixedMoment B raw31345step2 raw31345step2Labels = mixedMoment B raw31345step3 raw31345step3Labels := by
      have ha : raw31345step3 = -raw31345step2 := by apply Matrix.ext; change ∀ i j, raw31345step3 i j = -(raw31345step2 i j); unfold raw31345step3 raw31345step2; decide +kernel
      have hl : raw31345step3Labels = raw31345step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31345step3 raw31345step3Labels = mixedMoment B raw31345step4 raw31345step4Labels := by
      have ha : raw31345step4 = raw31345step3 := by apply Matrix.ext; unfold raw31345step4 raw31345step3; decide +kernel
      have hl : raw31345step3Labels = labelEmbedding1 ∘ raw31345step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31345step3 raw31345step3Labels raw31345step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2264 node2264Labels := by rfl

def raw31346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31346Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31346step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31346step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31346step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw31346step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31346step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw31346step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31346step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw31346step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31346 raw31346Labels = mixedMoment B node1681 node1681Labels := by
  calc
    mixedMoment B raw31346 raw31346Labels = mixedMoment B raw31346step0 raw31346step0Labels := by
      have hz : ∀ j, raw31346 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31346step0 = (fun i j => raw31346 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31346step0 raw31346; decide +kernel
      have hl : raw31346step0Labels = raw31346Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31346 raw31346Labels permutation434 hz
    mixedMoment B raw31346step0 raw31346step0Labels = mixedMoment B raw31346step1 raw31346step1Labels := by
      have ha : raw31346step1 = (fun i j => raw31346step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31346step1 raw31346step0; decide +kernel
      have hl : raw31346step1Labels = raw31346step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31346step0 raw31346step0Labels permutation36 permutation7
    mixedMoment B raw31346step1 raw31346step1Labels = mixedMoment B raw31346step2 raw31346step2Labels := by
      have ha : raw31346step2 = -raw31346step1 := by apply Matrix.ext; change ∀ i j, raw31346step2 i j = -(raw31346step1 i j); unfold raw31346step2 raw31346step1; decide +kernel
      have hl : raw31346step2Labels = raw31346step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31346step2 raw31346step2Labels = mixedMoment B raw31346step3 raw31346step3Labels := by
      have ha : raw31346step3 = raw31346step2 := by apply Matrix.ext; unfold raw31346step3 raw31346step2; decide +kernel
      have hl : raw31346step2Labels = labelEmbedding1 ∘ raw31346step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31346step2 raw31346step2Labels raw31346step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1681 node1681Labels := by rfl

def raw31347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31347Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31347step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31347step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31347step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw31347step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31347step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw31347step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31347step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw31347step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31347 raw31347Labels = mixedMoment B node2157 node2157Labels := by
  calc
    mixedMoment B raw31347 raw31347Labels = mixedMoment B raw31347step0 raw31347step0Labels := by
      have hz : ∀ j, raw31347 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31347step0 = (fun i j => raw31347 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31347step0 raw31347; decide +kernel
      have hl : raw31347step0Labels = raw31347Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31347 raw31347Labels permutation434 hz
    mixedMoment B raw31347step0 raw31347step0Labels = mixedMoment B raw31347step1 raw31347step1Labels := by
      have ha : raw31347step1 = (fun i j => raw31347step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31347step1 raw31347step0; decide +kernel
      have hl : raw31347step1Labels = raw31347step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31347step0 raw31347step0Labels permutation36 permutation7
    mixedMoment B raw31347step1 raw31347step1Labels = mixedMoment B raw31347step2 raw31347step2Labels := by
      have ha : raw31347step2 = -raw31347step1 := by apply Matrix.ext; change ∀ i j, raw31347step2 i j = -(raw31347step1 i j); unfold raw31347step2 raw31347step1; decide +kernel
      have hl : raw31347step2Labels = raw31347step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31347step2 raw31347step2Labels = mixedMoment B raw31347step3 raw31347step3Labels := by
      have ha : raw31347step3 = raw31347step2 := by apply Matrix.ext; unfold raw31347step3 raw31347step2; decide +kernel
      have hl : raw31347step2Labels = labelEmbedding1 ∘ raw31347step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31347step2 raw31347step2Labels raw31347step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2157 node2157Labels := by rfl

def raw31348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31348Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31348step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 0, 2]]
def raw31348step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31348step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw31348step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31348step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw31348step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31348 raw31348Labels = mixedMoment B node2177 node2177Labels := by
  calc
    mixedMoment B raw31348 raw31348Labels = mixedMoment B raw31348step0 raw31348step0Labels := by
      have ha : raw31348step0 = (fun i j => raw31348 (permutation162 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31348step0 raw31348; decide +kernel
      have hl : raw31348step0Labels = raw31348Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31348 raw31348Labels permutation162 permutation7
    mixedMoment B raw31348step0 raw31348step0Labels = mixedMoment B raw31348step1 raw31348step1Labels := by
      have ha : raw31348step1 = -raw31348step0 := by apply Matrix.ext; change ∀ i j, raw31348step1 i j = -(raw31348step0 i j); unfold raw31348step1 raw31348step0; decide +kernel
      have hl : raw31348step1Labels = raw31348step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31348step1 raw31348step1Labels = mixedMoment B raw31348step2 raw31348step2Labels := by
      have ha : raw31348step2 = raw31348step1 := by apply Matrix.ext; unfold raw31348step2 raw31348step1; decide +kernel
      have hl : raw31348step1Labels = labelEmbedding1 ∘ raw31348step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31348step1 raw31348step1Labels raw31348step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2177 node2177Labels := by rfl

def raw31349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw31349Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw31349step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31349step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw31349step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31349step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw31349step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31349step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw31349step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31349 raw31349Labels = mixedMoment B node2216 node2216Labels := by
  calc
    mixedMoment B raw31349 raw31349Labels = mixedMoment B raw31349step0 raw31349step0Labels := by
      have hz : ∀ j, raw31349 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31349step0 = (fun i j => raw31349 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31349step0 raw31349; decide +kernel
      have hl : raw31349step0Labels = raw31349Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31349 raw31349Labels permutation434 hz
    mixedMoment B raw31349step0 raw31349step0Labels = mixedMoment B raw31349step1 raw31349step1Labels := by
      have ha : raw31349step1 = (fun i j => raw31349step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31349step1 raw31349step0; decide +kernel
      have hl : raw31349step1Labels = raw31349step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31349step0 raw31349step0Labels permutation36 permutation7
    mixedMoment B raw31349step1 raw31349step1Labels = mixedMoment B raw31349step2 raw31349step2Labels := by
      have ha : raw31349step2 = -raw31349step1 := by apply Matrix.ext; change ∀ i j, raw31349step2 i j = -(raw31349step1 i j); unfold raw31349step2 raw31349step1; decide +kernel
      have hl : raw31349step2Labels = raw31349step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31349step2 raw31349step2Labels = mixedMoment B raw31349step3 raw31349step3Labels := by
      have ha : raw31349step3 = raw31349step2 := by apply Matrix.ext; unfold raw31349step3 raw31349step2; decide +kernel
      have hl : raw31349step2Labels = labelEmbedding1 ∘ raw31349step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31349step2 raw31349step2Labels raw31349step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2216 node2216Labels := by rfl

def raw31350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw31350Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2], ![1, -1, 0]]
def raw31350step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31350step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw31350step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31350step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw31350step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31350step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw31350step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31350 raw31350Labels = mixedMoment B node2205 node2205Labels := by
  calc
    mixedMoment B raw31350 raw31350Labels = mixedMoment B raw31350step0 raw31350step0Labels := by
      have hz : ∀ j, raw31350 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31350step0 = (fun i j => raw31350 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31350step0 raw31350; decide +kernel
      have hl : raw31350step0Labels = raw31350Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31350 raw31350Labels permutation434 hz
    mixedMoment B raw31350step0 raw31350step0Labels = mixedMoment B raw31350step1 raw31350step1Labels := by
      have ha : raw31350step1 = (fun i j => raw31350step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31350step1 raw31350step0; decide +kernel
      have hl : raw31350step1Labels = raw31350step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31350step0 raw31350step0Labels permutation36 permutation7
    mixedMoment B raw31350step1 raw31350step1Labels = mixedMoment B raw31350step2 raw31350step2Labels := by
      have ha : raw31350step2 = -raw31350step1 := by apply Matrix.ext; change ∀ i j, raw31350step2 i j = -(raw31350step1 i j); unfold raw31350step2 raw31350step1; decide +kernel
      have hl : raw31350step2Labels = raw31350step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31350step2 raw31350step2Labels = mixedMoment B raw31350step3 raw31350step3Labels := by
      have ha : raw31350step3 = raw31350step2 := by apply Matrix.ext; unfold raw31350step3 raw31350step2; decide +kernel
      have hl : raw31350step2Labels = labelEmbedding1 ∘ raw31350step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31350step2 raw31350step2Labels raw31350step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2205 node2205Labels := by rfl

def raw31351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31351Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31351step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw31351step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31351step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw31351step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31351step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw31351step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31351 raw31351Labels = mixedMoment B node1667 node1667Labels := by
  calc
    mixedMoment B raw31351 raw31351Labels = mixedMoment B raw31351step0 raw31351step0Labels := by
      have ha : raw31351step0 = (fun i j => raw31351 (permutation162 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31351step0 raw31351; decide +kernel
      have hl : raw31351step0Labels = raw31351Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31351 raw31351Labels permutation162 permutation7
    mixedMoment B raw31351step0 raw31351step0Labels = mixedMoment B raw31351step1 raw31351step1Labels := by
      have ha : raw31351step1 = -raw31351step0 := by apply Matrix.ext; change ∀ i j, raw31351step1 i j = -(raw31351step0 i j); unfold raw31351step1 raw31351step0; decide +kernel
      have hl : raw31351step1Labels = raw31351step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31351step1 raw31351step1Labels = mixedMoment B raw31351step2 raw31351step2Labels := by
      have ha : raw31351step2 = raw31351step1 := by apply Matrix.ext; unfold raw31351step2 raw31351step1; decide +kernel
      have hl : raw31351step1Labels = labelEmbedding1 ∘ raw31351step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31351step1 raw31351step1Labels raw31351step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1667 node1667Labels := by rfl

def raw31352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31352Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31352step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw31352step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31352step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw31352step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31352step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw31352step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31352 raw31352Labels = mixedMoment B node2144 node2144Labels := by
  calc
    mixedMoment B raw31352 raw31352Labels = mixedMoment B raw31352step0 raw31352step0Labels := by
      have ha : raw31352step0 = (fun i j => raw31352 (permutation162 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31352step0 raw31352; decide +kernel
      have hl : raw31352step0Labels = raw31352Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31352 raw31352Labels permutation162 permutation7
    mixedMoment B raw31352step0 raw31352step0Labels = mixedMoment B raw31352step1 raw31352step1Labels := by
      have ha : raw31352step1 = -raw31352step0 := by apply Matrix.ext; change ∀ i j, raw31352step1 i j = -(raw31352step0 i j); unfold raw31352step1 raw31352step0; decide +kernel
      have hl : raw31352step1Labels = raw31352step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31352step1 raw31352step1Labels = mixedMoment B raw31352step2 raw31352step2Labels := by
      have ha : raw31352step2 = raw31352step1 := by apply Matrix.ext; unfold raw31352step2 raw31352step1; decide +kernel
      have hl : raw31352step1Labels = labelEmbedding1 ∘ raw31352step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31352step1 raw31352step1Labels raw31352step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2144 node2144Labels := by rfl

def raw31353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31353Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31353step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw31353step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31353step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw31353step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31353step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw31353step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31353 raw31353Labels = mixedMoment B node2194 node2194Labels := by
  calc
    mixedMoment B raw31353 raw31353Labels = mixedMoment B raw31353step0 raw31353step0Labels := by
      have ha : raw31353step0 = (fun i j => raw31353 (permutation162 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31353step0 raw31353; decide +kernel
      have hl : raw31353step0Labels = raw31353Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31353 raw31353Labels permutation162 permutation7
    mixedMoment B raw31353step0 raw31353step0Labels = mixedMoment B raw31353step1 raw31353step1Labels := by
      have ha : raw31353step1 = -raw31353step0 := by apply Matrix.ext; change ∀ i j, raw31353step1 i j = -(raw31353step0 i j); unfold raw31353step1 raw31353step0; decide +kernel
      have hl : raw31353step1Labels = raw31353step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31353step1 raw31353step1Labels = mixedMoment B raw31353step2 raw31353step2Labels := by
      have ha : raw31353step2 = raw31353step1 := by apply Matrix.ext; unfold raw31353step2 raw31353step1; decide +kernel
      have hl : raw31353step1Labels = labelEmbedding1 ∘ raw31353step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31353step1 raw31353step1Labels raw31353step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2194 node2194Labels := by rfl

def raw31354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw31354Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31354step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw31354step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31354step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw31354step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31354step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw31354step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31354 raw31354Labels = mixedMoment B node2195 node2195Labels := by
  calc
    mixedMoment B raw31354 raw31354Labels = mixedMoment B raw31354step0 raw31354step0Labels := by
      have ha : raw31354step0 = (fun i j => raw31354 (permutation162 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31354step0 raw31354; decide +kernel
      have hl : raw31354step0Labels = raw31354Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31354 raw31354Labels permutation162 permutation7
    mixedMoment B raw31354step0 raw31354step0Labels = mixedMoment B raw31354step1 raw31354step1Labels := by
      have ha : raw31354step1 = -raw31354step0 := by apply Matrix.ext; change ∀ i j, raw31354step1 i j = -(raw31354step0 i j); unfold raw31354step1 raw31354step0; decide +kernel
      have hl : raw31354step1Labels = raw31354step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31354step1 raw31354step1Labels = mixedMoment B raw31354step2 raw31354step2Labels := by
      have ha : raw31354step2 = raw31354step1 := by apply Matrix.ext; unfold raw31354step2 raw31354step1; decide +kernel
      have hl : raw31354step1Labels = labelEmbedding1 ∘ raw31354step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31354step1 raw31354step1Labels raw31354step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2195 node2195Labels := by rfl

def raw31355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw31355Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31355step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw31355step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31355step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw31355step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31355step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw31355step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31355 raw31355Labels = mixedMoment B node2190 node2190Labels := by
  calc
    mixedMoment B raw31355 raw31355Labels = mixedMoment B raw31355step0 raw31355step0Labels := by
      have ha : raw31355step0 = (fun i j => raw31355 (permutation162 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31355step0 raw31355; decide +kernel
      have hl : raw31355step0Labels = raw31355Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31355 raw31355Labels permutation162 permutation7
    mixedMoment B raw31355step0 raw31355step0Labels = mixedMoment B raw31355step1 raw31355step1Labels := by
      have ha : raw31355step1 = -raw31355step0 := by apply Matrix.ext; change ∀ i j, raw31355step1 i j = -(raw31355step0 i j); unfold raw31355step1 raw31355step0; decide +kernel
      have hl : raw31355step1Labels = raw31355step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31355step1 raw31355step1Labels = mixedMoment B raw31355step2 raw31355step2Labels := by
      have ha : raw31355step2 = raw31355step1 := by apply Matrix.ext; unfold raw31355step2 raw31355step1; decide +kernel
      have hl : raw31355step1Labels = labelEmbedding1 ∘ raw31355step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31355step1 raw31355step1Labels raw31355step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2190 node2190Labels := by rfl

def raw31356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw31356Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31356step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![3, -1, -2], ![2, -2, 0]]
def raw31356step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31356step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw31356step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31356step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw31356step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31356step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw31356step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31356 raw31356Labels = mixedMoment B node1679 node1679Labels := by
  calc
    mixedMoment B raw31356 raw31356Labels = mixedMoment B raw31356step0 raw31356step0Labels := by
      have hz : ∀ j, raw31356 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31356step0 = (fun i j => raw31356 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31356step0 raw31356; decide +kernel
      have hl : raw31356step0Labels = raw31356Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31356 raw31356Labels permutation434 hz
    mixedMoment B raw31356step0 raw31356step0Labels = mixedMoment B raw31356step1 raw31356step1Labels := by
      have ha : raw31356step1 = (fun i j => raw31356step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31356step1 raw31356step0; decide +kernel
      have hl : raw31356step1Labels = raw31356step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31356step0 raw31356step0Labels permutation36 permutation7
    mixedMoment B raw31356step1 raw31356step1Labels = mixedMoment B raw31356step2 raw31356step2Labels := by
      have ha : raw31356step2 = -raw31356step1 := by apply Matrix.ext; change ∀ i j, raw31356step2 i j = -(raw31356step1 i j); unfold raw31356step2 raw31356step1; decide +kernel
      have hl : raw31356step2Labels = raw31356step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31356step2 raw31356step2Labels = mixedMoment B raw31356step3 raw31356step3Labels := by
      have ha : raw31356step3 = raw31356step2 := by apply Matrix.ext; unfold raw31356step3 raw31356step2; decide +kernel
      have hl : raw31356step2Labels = labelEmbedding1 ∘ raw31356step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31356step2 raw31356step2Labels raw31356step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1679 node1679Labels := by rfl

def raw31357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw31357Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31357step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 1, -1], ![3, -1, -2], ![2, -2, 0]]
def raw31357step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31357step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw31357step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31357step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw31357step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31357step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw31357step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31357 raw31357Labels = mixedMoment B node2155 node2155Labels := by
  calc
    mixedMoment B raw31357 raw31357Labels = mixedMoment B raw31357step0 raw31357step0Labels := by
      have hz : ∀ j, raw31357 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31357step0 = (fun i j => raw31357 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31357step0 raw31357; decide +kernel
      have hl : raw31357step0Labels = raw31357Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31357 raw31357Labels permutation434 hz
    mixedMoment B raw31357step0 raw31357step0Labels = mixedMoment B raw31357step1 raw31357step1Labels := by
      have ha : raw31357step1 = (fun i j => raw31357step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31357step1 raw31357step0; decide +kernel
      have hl : raw31357step1Labels = raw31357step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31357step0 raw31357step0Labels permutation36 permutation7
    mixedMoment B raw31357step1 raw31357step1Labels = mixedMoment B raw31357step2 raw31357step2Labels := by
      have ha : raw31357step2 = -raw31357step1 := by apply Matrix.ext; change ∀ i j, raw31357step2 i j = -(raw31357step1 i j); unfold raw31357step2 raw31357step1; decide +kernel
      have hl : raw31357step2Labels = raw31357step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31357step2 raw31357step2Labels = mixedMoment B raw31357step3 raw31357step3Labels := by
      have ha : raw31357step3 = raw31357step2 := by apply Matrix.ext; unfold raw31357step3 raw31357step2; decide +kernel
      have hl : raw31357step2Labels = labelEmbedding1 ∘ raw31357step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31357step2 raw31357step2Labels raw31357step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2155 node2155Labels := by rfl

def raw31358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw31358Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![3, -1, -2], ![2, -2, 0]]
def raw31358step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31358step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, -1, 3]]
def raw31358step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31358step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw31358step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31358step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw31358step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31358 raw31358Labels = mixedMoment B node2212 node2212Labels := by
  calc
    mixedMoment B raw31358 raw31358Labels = mixedMoment B raw31358step0 raw31358step0Labels := by
      have hz : ∀ j, raw31358 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31358step0 = (fun i j => raw31358 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31358step0 raw31358; decide +kernel
      have hl : raw31358step0Labels = raw31358Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31358 raw31358Labels permutation434 hz
    mixedMoment B raw31358step0 raw31358step0Labels = mixedMoment B raw31358step1 raw31358step1Labels := by
      have ha : raw31358step1 = (fun i j => raw31358step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31358step1 raw31358step0; decide +kernel
      have hl : raw31358step1Labels = raw31358step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31358step0 raw31358step0Labels permutation36 permutation7
    mixedMoment B raw31358step1 raw31358step1Labels = mixedMoment B raw31358step2 raw31358step2Labels := by
      have ha : raw31358step2 = -raw31358step1 := by apply Matrix.ext; change ∀ i j, raw31358step2 i j = -(raw31358step1 i j); unfold raw31358step2 raw31358step1; decide +kernel
      have hl : raw31358step2Labels = raw31358step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31358step2 raw31358step2Labels = mixedMoment B raw31358step3 raw31358step3Labels := by
      have ha : raw31358step3 = raw31358step2 := by apply Matrix.ext; unfold raw31358step3 raw31358step2; decide +kernel
      have hl : raw31358step2Labels = labelEmbedding1 ∘ raw31358step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31358step2 raw31358step2Labels raw31358step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2212 node2212Labels := by rfl

def raw31359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw31359Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31359step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, -1, 3]]
def raw31359step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31359step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw31359step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31359step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw31359step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31359 raw31359Labels = mixedMoment B node2176 node2176Labels := by
  calc
    mixedMoment B raw31359 raw31359Labels = mixedMoment B raw31359step0 raw31359step0Labels := by
      have ha : raw31359step0 = (fun i j => raw31359 (permutation162 i) (permutation7 j)) := by apply Matrix.ext; unfold raw31359step0 raw31359; decide +kernel
      have hl : raw31359step0Labels = raw31359Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31359 raw31359Labels permutation162 permutation7
    mixedMoment B raw31359step0 raw31359step0Labels = mixedMoment B raw31359step1 raw31359step1Labels := by
      have ha : raw31359step1 = -raw31359step0 := by apply Matrix.ext; change ∀ i j, raw31359step1 i j = -(raw31359step0 i j); unfold raw31359step1 raw31359step0; decide +kernel
      have hl : raw31359step1Labels = raw31359step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31359step1 raw31359step1Labels = mixedMoment B raw31359step2 raw31359step2Labels := by
      have ha : raw31359step2 = raw31359step1 := by apply Matrix.ext; unfold raw31359step2 raw31359step1; decide +kernel
      have hl : raw31359step1Labels = labelEmbedding1 ∘ raw31359step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31359step1 raw31359step1Labels raw31359step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2176 node2176Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
