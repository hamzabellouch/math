import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw36096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36096Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw36096step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36096step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw36096step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36096step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw36096step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36096step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw36096step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36096 raw36096Labels = mixedMoment B node2670 node2670Labels := by
  calc
    mixedMoment B raw36096 raw36096Labels = mixedMoment B raw36096step0 raw36096step0Labels := by
      have hz : ∀ j, raw36096 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36096step0 = (fun i j => raw36096 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36096step0 raw36096; decide +kernel
      have hl : raw36096step0Labels = raw36096Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36096 raw36096Labels permutation346 hz
    mixedMoment B raw36096step0 raw36096step0Labels = mixedMoment B raw36096step1 raw36096step1Labels := by
      have ha : raw36096step1 = (fun i j => raw36096step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36096step1 raw36096step0; decide +kernel
      have hl : raw36096step1Labels = raw36096step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36096step0 raw36096step0Labels permutation58 permutation7
    mixedMoment B raw36096step1 raw36096step1Labels = mixedMoment B raw36096step2 raw36096step2Labels := by
      have ha : raw36096step2 = -raw36096step1 := by apply Matrix.ext; change ∀ i j, raw36096step2 i j = -(raw36096step1 i j); unfold raw36096step2 raw36096step1; decide +kernel
      have hl : raw36096step2Labels = raw36096step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36096step2 raw36096step2Labels = mixedMoment B raw36096step3 raw36096step3Labels := by
      have ha : raw36096step3 = raw36096step2 := by apply Matrix.ext; unfold raw36096step3 raw36096step2; decide +kernel
      have hl : raw36096step2Labels = labelEmbedding1 ∘ raw36096step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36096step2 raw36096step2Labels raw36096step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2670 node2670Labels := by rfl

def raw36097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw36097Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw36097step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36097step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![3, -1, -2]]
def raw36097step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36097step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 0, 1], ![-2, -1, 3]]
def raw36097step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36097step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw36097step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36097step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw36097step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36097 raw36097Labels = mixedMoment B node2685 node2685Labels := by
  calc
    mixedMoment B raw36097 raw36097Labels = mixedMoment B raw36097step0 raw36097step0Labels := by
      have hz : ∀ j, raw36097 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36097step0 = (fun i j => raw36097 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36097step0 raw36097; decide +kernel
      have hl : raw36097step0Labels = raw36097Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36097 raw36097Labels permutation520 hz
    mixedMoment B raw36097step0 raw36097step0Labels = mixedMoment B raw36097step1 raw36097step1Labels := by
      have hz : ∀ j, raw36097step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36097step1 = (fun i j => raw36097step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36097step1 raw36097step0; decide +kernel
      have hl : raw36097step1Labels = raw36097step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36097step0 raw36097step0Labels permutation80 hz
    mixedMoment B raw36097step1 raw36097step1Labels = mixedMoment B raw36097step2 raw36097step2Labels := by
      have ha : raw36097step2 = (fun i j => raw36097step1 (permutation14 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36097step2 raw36097step1; decide +kernel
      have hl : raw36097step2Labels = raw36097step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36097step1 raw36097step1Labels permutation14 permutation7
    mixedMoment B raw36097step2 raw36097step2Labels = mixedMoment B raw36097step3 raw36097step3Labels := by
      have ha : raw36097step3 = -raw36097step2 := by apply Matrix.ext; change ∀ i j, raw36097step3 i j = -(raw36097step2 i j); unfold raw36097step3 raw36097step2; decide +kernel
      have hl : raw36097step3Labels = raw36097step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36097step3 raw36097step3Labels = mixedMoment B raw36097step4 raw36097step4Labels := by
      have ha : raw36097step4 = raw36097step3 := by apply Matrix.ext; unfold raw36097step4 raw36097step3; decide +kernel
      have hl : raw36097step3Labels = labelEmbedding1 ∘ raw36097step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36097step3 raw36097step3Labels raw36097step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2685 node2685Labels := by rfl

def raw36098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36098Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36098step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36098step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36098step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36098step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36098step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36098step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36098 raw36098Labels = mixedMoment B node5172 node5172Labels := by
  calc
    mixedMoment B raw36098 raw36098Labels = mixedMoment B raw36098step0 raw36098step0Labels := by
      have hz : ∀ j, raw36098 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36098step0 = (fun i j => raw36098 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36098step0 raw36098; decide +kernel
      have hl : raw36098step0Labels = raw36098Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36098 raw36098Labels permutation346 hz
    mixedMoment B raw36098step0 raw36098step0Labels = mixedMoment B raw36098step1 raw36098step1Labels := by
      have ha : raw36098step1 = (fun i j => raw36098step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36098step1 raw36098step0; decide +kernel
      have hl : raw36098step1Labels = raw36098step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36098step0 raw36098step0Labels permutation56 permutation3
    mixedMoment B raw36098step1 raw36098step1Labels = mixedMoment B raw36098step2 raw36098step2Labels := by
      have ha : raw36098step2 = raw36098step1 := by apply Matrix.ext; unfold raw36098step2 raw36098step1; decide +kernel
      have hl : raw36098step1Labels = labelEmbedding6 ∘ raw36098step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36098step1 raw36098step1Labels raw36098step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5172 node5172Labels := by rfl

def raw36099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36099Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36099step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw36099step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36099step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36099step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36099 raw36099Labels = mixedMoment B node5416 node5416Labels := by
  calc
    mixedMoment B raw36099 raw36099Labels = mixedMoment B raw36099step0 raw36099step0Labels := by
      have ha : raw36099step0 = (fun i j => raw36099 (permutation663 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36099step0 raw36099; decide +kernel
      have hl : raw36099step0Labels = raw36099Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36099 raw36099Labels permutation663 permutation2
    mixedMoment B raw36099step0 raw36099step0Labels = mixedMoment B raw36099step1 raw36099step1Labels := by
      have ha : raw36099step1 = -raw36099step0 := by apply Matrix.ext; change ∀ i j, raw36099step1 i j = -(raw36099step0 i j); unfold raw36099step1 raw36099step0; decide +kernel
      have hl : raw36099step1Labels = raw36099step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5416 node5416Labels := by rfl

def raw36100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw36100Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36100step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36100step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw36100step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36100step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw36100step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36100step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36100step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36100 raw36100Labels = mixedMoment B node5442 node5442Labels := by
  calc
    mixedMoment B raw36100 raw36100Labels = mixedMoment B raw36100step0 raw36100step0Labels := by
      have hz : ∀ j, raw36100 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36100step0 = (fun i j => raw36100 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36100step0 raw36100; decide +kernel
      have hl : raw36100step0Labels = raw36100Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36100 raw36100Labels permutation520 hz
    mixedMoment B raw36100step0 raw36100step0Labels = mixedMoment B raw36100step1 raw36100step1Labels := by
      have hz : ∀ j, raw36100step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36100step1 = (fun i j => raw36100step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36100step1 raw36100step0; decide +kernel
      have hl : raw36100step1Labels = raw36100step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36100step0 raw36100step0Labels permutation80 hz
    mixedMoment B raw36100step1 raw36100step1Labels = mixedMoment B raw36100step2 raw36100step2Labels := by
      have ha : raw36100step2 = (fun i j => raw36100step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36100step2 raw36100step1; decide +kernel
      have hl : raw36100step2Labels = raw36100step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36100step1 raw36100step1Labels permutation30 permutation2
    mixedMoment B raw36100step2 raw36100step2Labels = mixedMoment B raw36100step3 raw36100step3Labels := by
      have ha : raw36100step3 = -raw36100step2 := by apply Matrix.ext; change ∀ i j, raw36100step3 i j = -(raw36100step2 i j); unfold raw36100step3 raw36100step2; decide +kernel
      have hl : raw36100step3Labels = raw36100step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5442 node5442Labels := by rfl

def raw36101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36101Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36101step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36101step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36101step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36101step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36101 raw36101Labels = mixedMoment B node4947 node4947Labels := by
  calc
    mixedMoment B raw36101 raw36101Labels = mixedMoment B raw36101step0 raw36101step0Labels := by
      have ha : raw36101step0 = (fun i j => raw36101 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36101step0 raw36101; decide +kernel
      have hl : raw36101step0Labels = raw36101Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36101 raw36101Labels permutation265 permutation3
    mixedMoment B raw36101step0 raw36101step0Labels = mixedMoment B raw36101step1 raw36101step1Labels := by
      have ha : raw36101step1 = raw36101step0 := by apply Matrix.ext; unfold raw36101step1 raw36101step0; decide +kernel
      have hl : raw36101step0Labels = labelEmbedding6 ∘ raw36101step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36101step0 raw36101step0Labels raw36101step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4947 node4947Labels := by rfl

def raw36102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw36102Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36102step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36102step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw36102step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36102step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw36102step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36102 raw36102Labels = mixedMoment B node5418 node5418Labels := by
  calc
    mixedMoment B raw36102 raw36102Labels = mixedMoment B raw36102step0 raw36102step0Labels := by
      have hz : ∀ j, raw36102 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36102step0 = (fun i j => raw36102 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36102step0 raw36102; decide +kernel
      have hl : raw36102step0Labels = raw36102Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36102 raw36102Labels permutation520 hz
    mixedMoment B raw36102step0 raw36102step0Labels = mixedMoment B raw36102step1 raw36102step1Labels := by
      have ha : raw36102step1 = (fun i j => raw36102step0 (permutation144 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36102step1 raw36102step0; decide +kernel
      have hl : raw36102step1Labels = raw36102step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36102step0 raw36102step0Labels permutation144 permutation2
    mixedMoment B raw36102step1 raw36102step1Labels = mixedMoment B raw36102step2 raw36102step2Labels := by
      have ha : raw36102step2 = -raw36102step1 := by apply Matrix.ext; change ∀ i j, raw36102step2 i j = -(raw36102step1 i j); unfold raw36102step2 raw36102step1; decide +kernel
      have hl : raw36102step2Labels = raw36102step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5418 node5418Labels := by rfl

def raw36103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36103Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36103step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36103step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36103step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36103step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36103step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36103 raw36103Labels = mixedMoment B node4949 node4949Labels := by
  calc
    mixedMoment B raw36103 raw36103Labels = mixedMoment B raw36103step0 raw36103step0Labels := by
      have hz : ∀ j, raw36103 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36103step0 = (fun i j => raw36103 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36103step0 raw36103; decide +kernel
      have hl : raw36103step0Labels = raw36103Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36103 raw36103Labels permutation346 hz
    mixedMoment B raw36103step0 raw36103step0Labels = mixedMoment B raw36103step1 raw36103step1Labels := by
      have ha : raw36103step1 = (fun i j => raw36103step0 (permutation59 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36103step1 raw36103step0; decide +kernel
      have hl : raw36103step1Labels = raw36103step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36103step0 raw36103step0Labels permutation59 permutation3
    mixedMoment B raw36103step1 raw36103step1Labels = mixedMoment B raw36103step2 raw36103step2Labels := by
      have ha : raw36103step2 = raw36103step1 := by apply Matrix.ext; unfold raw36103step2 raw36103step1; decide +kernel
      have hl : raw36103step1Labels = labelEmbedding6 ∘ raw36103step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36103step1 raw36103step1Labels raw36103step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4949 node4949Labels := by rfl

def raw36104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36104Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36104step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![1, 0, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36104step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36104step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36104step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36104step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36104step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36104 raw36104Labels = mixedMoment B node5373 node5373Labels := by
  calc
    mixedMoment B raw36104 raw36104Labels = mixedMoment B raw36104step0 raw36104step0Labels := by
      have ha : raw36104step0 = (fun i j => raw36104 (permutation518 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36104step0 raw36104; decide +kernel
      have hl : raw36104step0Labels = raw36104Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36104 raw36104Labels permutation518 permutation3
    mixedMoment B raw36104step0 raw36104step0Labels = mixedMoment B raw36104step1 raw36104step1Labels := by
      have ha : raw36104step1 = -raw36104step0 := by apply Matrix.ext; change ∀ i j, raw36104step1 i j = -(raw36104step0 i j); unfold raw36104step1 raw36104step0; decide +kernel
      have hl : raw36104step1Labels = raw36104step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36104step1 raw36104step1Labels = mixedMoment B raw36104step2 raw36104step2Labels := by
      have ha : raw36104step2 = raw36104step1 := by apply Matrix.ext; unfold raw36104step2 raw36104step1; decide +kernel
      have hl : raw36104step1Labels = labelEmbedding6 ∘ raw36104step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36104step1 raw36104step1Labels raw36104step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5373 node5373Labels := by rfl

def raw36105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw36105Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw36105step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36105step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw36105step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36105step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw36105step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36105step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -1, -1], ![2, -1, -1]]
def raw36105step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36105 raw36105Labels = mixedMoment B node5390 node5390Labels := by
  calc
    mixedMoment B raw36105 raw36105Labels = mixedMoment B raw36105step0 raw36105step0Labels := by
      have hz : ∀ j, raw36105 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36105step0 = (fun i j => raw36105 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36105step0 raw36105; decide +kernel
      have hl : raw36105step0Labels = raw36105Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36105 raw36105Labels permutation520 hz
    mixedMoment B raw36105step0 raw36105step0Labels = mixedMoment B raw36105step1 raw36105step1Labels := by
      have hz : ∀ j, raw36105step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36105step1 = (fun i j => raw36105step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36105step1 raw36105step0; decide +kernel
      have hl : raw36105step1Labels = raw36105step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36105step0 raw36105step0Labels permutation80 hz
    mixedMoment B raw36105step1 raw36105step1Labels = mixedMoment B raw36105step2 raw36105step2Labels := by
      have ha : raw36105step2 = (fun i j => raw36105step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36105step2 raw36105step1; decide +kernel
      have hl : raw36105step2Labels = raw36105step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36105step1 raw36105step1Labels permutation30 permutation2
    mixedMoment B raw36105step2 raw36105step2Labels = mixedMoment B raw36105step3 raw36105step3Labels := by
      have ha : raw36105step3 = -raw36105step2 := by apply Matrix.ext; change ∀ i j, raw36105step3 i j = -(raw36105step2 i j); unfold raw36105step3 raw36105step2; decide +kernel
      have hl : raw36105step3Labels = raw36105step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5390 node5390Labels := by rfl

def raw36106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw36106Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw36106step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36106step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36106step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36106step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36106step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36106 raw36106Labels = mixedMoment B node4949 node4949Labels := by
  calc
    mixedMoment B raw36106 raw36106Labels = mixedMoment B raw36106step0 raw36106step0Labels := by
      have hz : ∀ j, raw36106 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36106step0 = (fun i j => raw36106 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36106step0 raw36106; decide +kernel
      have hl : raw36106step0Labels = raw36106Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36106 raw36106Labels permutation346 hz
    mixedMoment B raw36106step0 raw36106step0Labels = mixedMoment B raw36106step1 raw36106step1Labels := by
      have ha : raw36106step1 = (fun i j => raw36106step0 (permutation57 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36106step1 raw36106step0; decide +kernel
      have hl : raw36106step1Labels = raw36106step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36106step0 raw36106step0Labels permutation57 permutation3
    mixedMoment B raw36106step1 raw36106step1Labels = mixedMoment B raw36106step2 raw36106step2Labels := by
      have ha : raw36106step2 = raw36106step1 := by apply Matrix.ext; unfold raw36106step2 raw36106step1; decide +kernel
      have hl : raw36106step1Labels = labelEmbedding6 ∘ raw36106step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36106step1 raw36106step1Labels raw36106step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4949 node4949Labels := by rfl

def raw36107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw36107Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36107step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![1, 0, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36107step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36107step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36107step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36107step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36107step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36107 raw36107Labels = mixedMoment B node5373 node5373Labels := by
  calc
    mixedMoment B raw36107 raw36107Labels = mixedMoment B raw36107step0 raw36107step0Labels := by
      have ha : raw36107step0 = (fun i j => raw36107 (permutation588 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36107step0 raw36107; decide +kernel
      have hl : raw36107step0Labels = raw36107Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36107 raw36107Labels permutation588 permutation3
    mixedMoment B raw36107step0 raw36107step0Labels = mixedMoment B raw36107step1 raw36107step1Labels := by
      have ha : raw36107step1 = -raw36107step0 := by apply Matrix.ext; change ∀ i j, raw36107step1 i j = -(raw36107step0 i j); unfold raw36107step1 raw36107step0; decide +kernel
      have hl : raw36107step1Labels = raw36107step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36107step1 raw36107step1Labels = mixedMoment B raw36107step2 raw36107step2Labels := by
      have ha : raw36107step2 = raw36107step1 := by apply Matrix.ext; unfold raw36107step2 raw36107step1; decide +kernel
      have hl : raw36107step1Labels = labelEmbedding6 ∘ raw36107step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36107step1 raw36107step1Labels raw36107step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5373 node5373Labels := by rfl

def raw36108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw36108Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw36108step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36108step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw36108step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36108step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw36108step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36108 raw36108Labels = mixedMoment B node4948 node4948Labels := by
  calc
    mixedMoment B raw36108 raw36108Labels = mixedMoment B raw36108step0 raw36108step0Labels := by
      have hz : ∀ j, raw36108 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36108step0 = (fun i j => raw36108 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36108step0 raw36108; decide +kernel
      have hl : raw36108step0Labels = raw36108Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36108 raw36108Labels permutation346 hz
    mixedMoment B raw36108step0 raw36108step0Labels = mixedMoment B raw36108step1 raw36108step1Labels := by
      have ha : raw36108step1 = (fun i j => raw36108step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36108step1 raw36108step0; decide +kernel
      have hl : raw36108step1Labels = raw36108step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36108step0 raw36108step0Labels permutation56 permutation3
    mixedMoment B raw36108step1 raw36108step1Labels = mixedMoment B raw36108step2 raw36108step2Labels := by
      have ha : raw36108step2 = raw36108step1 := by apply Matrix.ext; unfold raw36108step2 raw36108step1; decide +kernel
      have hl : raw36108step1Labels = labelEmbedding6 ∘ raw36108step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36108step1 raw36108step1Labels raw36108step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4948 node4948Labels := by rfl

def raw36109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw36109Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36109step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw36109step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36109step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw36109step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36109 raw36109Labels = mixedMoment B node5115 node5115Labels := by
  calc
    mixedMoment B raw36109 raw36109Labels = mixedMoment B raw36109step0 raw36109step0Labels := by
      have ha : raw36109step0 = (fun i j => raw36109 (permutation663 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36109step0 raw36109; decide +kernel
      have hl : raw36109step0Labels = raw36109Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36109 raw36109Labels permutation663 permutation2
    mixedMoment B raw36109step0 raw36109step0Labels = mixedMoment B raw36109step1 raw36109step1Labels := by
      have ha : raw36109step1 = -raw36109step0 := by apply Matrix.ext; change ∀ i j, raw36109step1 i j = -(raw36109step0 i j); unfold raw36109step1 raw36109step0; decide +kernel
      have hl : raw36109step1Labels = raw36109step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5115 node5115Labels := by rfl

def raw36110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw36110Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw36110step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36110step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw36110step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36110step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw36110step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36110step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw36110step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36110 raw36110Labels = mixedMoment B node5177 node5177Labels := by
  calc
    mixedMoment B raw36110 raw36110Labels = mixedMoment B raw36110step0 raw36110step0Labels := by
      have hz : ∀ j, raw36110 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36110step0 = (fun i j => raw36110 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36110step0 raw36110; decide +kernel
      have hl : raw36110step0Labels = raw36110Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36110 raw36110Labels permutation520 hz
    mixedMoment B raw36110step0 raw36110step0Labels = mixedMoment B raw36110step1 raw36110step1Labels := by
      have hz : ∀ j, raw36110step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36110step1 = (fun i j => raw36110step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36110step1 raw36110step0; decide +kernel
      have hl : raw36110step1Labels = raw36110step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36110step0 raw36110step0Labels permutation80 hz
    mixedMoment B raw36110step1 raw36110step1Labels = mixedMoment B raw36110step2 raw36110step2Labels := by
      have ha : raw36110step2 = (fun i j => raw36110step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36110step2 raw36110step1; decide +kernel
      have hl : raw36110step2Labels = raw36110step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36110step1 raw36110step1Labels permutation30 permutation2
    mixedMoment B raw36110step2 raw36110step2Labels = mixedMoment B raw36110step3 raw36110step3Labels := by
      have ha : raw36110step3 = -raw36110step2 := by apply Matrix.ext; change ∀ i j, raw36110step3 i j = -(raw36110step2 i j); unfold raw36110step3 raw36110step2; decide +kernel
      have hl : raw36110step3Labels = raw36110step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5177 node5177Labels := by rfl

def raw36111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36111Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36111step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36111step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36111step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36111step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36111step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36111 raw36111Labels = mixedMoment B node5168 node5168Labels := by
  calc
    mixedMoment B raw36111 raw36111Labels = mixedMoment B raw36111step0 raw36111step0Labels := by
      have hz : ∀ j, raw36111 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36111step0 = (fun i j => raw36111 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36111step0 raw36111; decide +kernel
      have hl : raw36111step0Labels = raw36111Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36111 raw36111Labels permutation346 hz
    mixedMoment B raw36111step0 raw36111step0Labels = mixedMoment B raw36111step1 raw36111step1Labels := by
      have ha : raw36111step1 = (fun i j => raw36111step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36111step1 raw36111step0; decide +kernel
      have hl : raw36111step1Labels = raw36111step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36111step0 raw36111step0Labels permutation56 permutation3
    mixedMoment B raw36111step1 raw36111step1Labels = mixedMoment B raw36111step2 raw36111step2Labels := by
      have ha : raw36111step2 = raw36111step1 := by apply Matrix.ext; unfold raw36111step2 raw36111step1; decide +kernel
      have hl : raw36111step1Labels = labelEmbedding6 ∘ raw36111step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36111step1 raw36111step1Labels raw36111step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5168 node5168Labels := by rfl

def raw36112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36112Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36112step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw36112step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36112step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36112step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36112step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36112step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36112 raw36112Labels = mixedMoment B node5416 node5416Labels := by
  calc
    mixedMoment B raw36112 raw36112Labels = mixedMoment B raw36112step0 raw36112step0Labels := by
      have ha : raw36112step0 = (fun i j => raw36112 (permutation660 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36112step0 raw36112; decide +kernel
      have hl : raw36112step0Labels = raw36112Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36112 raw36112Labels permutation660 permutation3
    mixedMoment B raw36112step0 raw36112step0Labels = mixedMoment B raw36112step1 raw36112step1Labels := by
      have ha : raw36112step1 = -raw36112step0 := by apply Matrix.ext; change ∀ i j, raw36112step1 i j = -(raw36112step0 i j); unfold raw36112step1 raw36112step0; decide +kernel
      have hl : raw36112step1Labels = raw36112step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36112step1 raw36112step1Labels = mixedMoment B raw36112step2 raw36112step2Labels := by
      have ha : raw36112step2 = raw36112step1 := by apply Matrix.ext; unfold raw36112step2 raw36112step1; decide +kernel
      have hl : raw36112step1Labels = labelEmbedding6 ∘ raw36112step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36112step1 raw36112step1Labels raw36112step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5416 node5416Labels := by rfl

def raw36113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36113Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36113step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36113step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw36113step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36113step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36113step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36113step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36113step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36113 raw36113Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw36113 raw36113Labels = mixedMoment B raw36113step0 raw36113step0Labels := by
      have hz : ∀ j, raw36113 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36113step0 = (fun i j => raw36113 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36113step0 raw36113; decide +kernel
      have hl : raw36113step0Labels = raw36113Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36113 raw36113Labels permutation346 hz
    mixedMoment B raw36113step0 raw36113step0Labels = mixedMoment B raw36113step1 raw36113step1Labels := by
      have ha : raw36113step1 = (fun i j => raw36113step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36113step1 raw36113step0; decide +kernel
      have hl : raw36113step1Labels = raw36113step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36113step0 raw36113step0Labels permutation150 permutation3
    mixedMoment B raw36113step1 raw36113step1Labels = mixedMoment B raw36113step2 raw36113step2Labels := by
      have ha : raw36113step2 = -raw36113step1 := by apply Matrix.ext; change ∀ i j, raw36113step2 i j = -(raw36113step1 i j); unfold raw36113step2 raw36113step1; decide +kernel
      have hl : raw36113step2Labels = raw36113step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36113step2 raw36113step2Labels = mixedMoment B raw36113step3 raw36113step3Labels := by
      have ha : raw36113step3 = raw36113step2 := by apply Matrix.ext; unfold raw36113step3 raw36113step2; decide +kernel
      have hl : raw36113step2Labels = labelEmbedding6 ∘ raw36113step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36113step2 raw36113step2Labels raw36113step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw36114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw36114Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw36114step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36114step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw36114step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36114step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36114step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36114step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36114step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36114 raw36114Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw36114 raw36114Labels = mixedMoment B raw36114step0 raw36114step0Labels := by
      have hz : ∀ j, raw36114 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36114step0 = (fun i j => raw36114 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36114step0 raw36114; decide +kernel
      have hl : raw36114step0Labels = raw36114Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36114 raw36114Labels permutation346 hz
    mixedMoment B raw36114step0 raw36114step0Labels = mixedMoment B raw36114step1 raw36114step1Labels := by
      have ha : raw36114step1 = (fun i j => raw36114step0 (permutation144 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36114step1 raw36114step0; decide +kernel
      have hl : raw36114step1Labels = raw36114step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36114step0 raw36114step0Labels permutation144 permutation3
    mixedMoment B raw36114step1 raw36114step1Labels = mixedMoment B raw36114step2 raw36114step2Labels := by
      have ha : raw36114step2 = -raw36114step1 := by apply Matrix.ext; change ∀ i j, raw36114step2 i j = -(raw36114step1 i j); unfold raw36114step2 raw36114step1; decide +kernel
      have hl : raw36114step2Labels = raw36114step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36114step2 raw36114step2Labels = mixedMoment B raw36114step3 raw36114step3Labels := by
      have ha : raw36114step3 = raw36114step2 := by apply Matrix.ext; unfold raw36114step3 raw36114step2; decide +kernel
      have hl : raw36114step2Labels = labelEmbedding6 ∘ raw36114step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36114step2 raw36114step2Labels raw36114step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw36115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36115Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36115step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36115step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36115step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36115step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36115 raw36115Labels = mixedMoment B node4939 node4939Labels := by
  calc
    mixedMoment B raw36115 raw36115Labels = mixedMoment B raw36115step0 raw36115step0Labels := by
      have ha : raw36115step0 = (fun i j => raw36115 (permutation273 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36115step0 raw36115; decide +kernel
      have hl : raw36115step0Labels = raw36115Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36115 raw36115Labels permutation273 permutation3
    mixedMoment B raw36115step0 raw36115step0Labels = mixedMoment B raw36115step1 raw36115step1Labels := by
      have ha : raw36115step1 = raw36115step0 := by apply Matrix.ext; unfold raw36115step1 raw36115step0; decide +kernel
      have hl : raw36115step0Labels = labelEmbedding6 ∘ raw36115step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36115step0 raw36115step0Labels raw36115step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4939 node4939Labels := by rfl

def raw36116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36116Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36116step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36116step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36116step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36116step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36116step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36116step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36116 raw36116Labels = mixedMoment B node5393 node5393Labels := by
  calc
    mixedMoment B raw36116 raw36116Labels = mixedMoment B raw36116step0 raw36116step0Labels := by
      have ha : raw36116step0 = (fun i j => raw36116 (permutation645 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36116step0 raw36116; decide +kernel
      have hl : raw36116step0Labels = raw36116Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36116 raw36116Labels permutation645 permutation3
    mixedMoment B raw36116step0 raw36116step0Labels = mixedMoment B raw36116step1 raw36116step1Labels := by
      have ha : raw36116step1 = -raw36116step0 := by apply Matrix.ext; change ∀ i j, raw36116step1 i j = -(raw36116step0 i j); unfold raw36116step1 raw36116step0; decide +kernel
      have hl : raw36116step1Labels = raw36116step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36116step1 raw36116step1Labels = mixedMoment B raw36116step2 raw36116step2Labels := by
      have ha : raw36116step2 = raw36116step1 := by apply Matrix.ext; unfold raw36116step2 raw36116step1; decide +kernel
      have hl : raw36116step1Labels = labelEmbedding6 ∘ raw36116step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36116step1 raw36116step1Labels raw36116step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5393 node5393Labels := by rfl

def raw36117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw36117Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36117step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36117step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36117step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36117step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36117step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36117step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36117 raw36117Labels = mixedMoment B node5393 node5393Labels := by
  calc
    mixedMoment B raw36117 raw36117Labels = mixedMoment B raw36117step0 raw36117step0Labels := by
      have ha : raw36117step0 = (fun i j => raw36117 (permutation639 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36117step0 raw36117; decide +kernel
      have hl : raw36117step0Labels = raw36117Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36117 raw36117Labels permutation639 permutation3
    mixedMoment B raw36117step0 raw36117step0Labels = mixedMoment B raw36117step1 raw36117step1Labels := by
      have ha : raw36117step1 = -raw36117step0 := by apply Matrix.ext; change ∀ i j, raw36117step1 i j = -(raw36117step0 i j); unfold raw36117step1 raw36117step0; decide +kernel
      have hl : raw36117step1Labels = raw36117step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36117step1 raw36117step1Labels = mixedMoment B raw36117step2 raw36117step2Labels := by
      have ha : raw36117step2 = raw36117step1 := by apply Matrix.ext; unfold raw36117step2 raw36117step1; decide +kernel
      have hl : raw36117step1Labels = labelEmbedding6 ∘ raw36117step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36117step1 raw36117step1Labels raw36117step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5393 node5393Labels := by rfl

def raw36118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36118Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36118step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36118step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36118step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36118step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36118step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36118 raw36118Labels = mixedMoment B node4946 node4946Labels := by
  calc
    mixedMoment B raw36118 raw36118Labels = mixedMoment B raw36118step0 raw36118step0Labels := by
      have hz : ∀ j, raw36118 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36118step0 = (fun i j => raw36118 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36118step0 raw36118; decide +kernel
      have hl : raw36118step0Labels = raw36118Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36118 raw36118Labels permutation346 hz
    mixedMoment B raw36118step0 raw36118step0Labels = mixedMoment B raw36118step1 raw36118step1Labels := by
      have ha : raw36118step1 = (fun i j => raw36118step0 (permutation58 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36118step1 raw36118step0; decide +kernel
      have hl : raw36118step1Labels = raw36118step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36118step0 raw36118step0Labels permutation58 permutation3
    mixedMoment B raw36118step1 raw36118step1Labels = mixedMoment B raw36118step2 raw36118step2Labels := by
      have ha : raw36118step2 = raw36118step1 := by apply Matrix.ext; unfold raw36118step2 raw36118step1; decide +kernel
      have hl : raw36118step1Labels = labelEmbedding6 ∘ raw36118step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36118step1 raw36118step1Labels raw36118step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4946 node4946Labels := by rfl

def raw36119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36119Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36119step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36119step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36119step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36119step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36119step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36119step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36119 raw36119Labels = mixedMoment B node5337 node5337Labels := by
  calc
    mixedMoment B raw36119 raw36119Labels = mixedMoment B raw36119step0 raw36119step0Labels := by
      have ha : raw36119step0 = (fun i j => raw36119 (permutation663 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36119step0 raw36119; decide +kernel
      have hl : raw36119step0Labels = raw36119Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36119 raw36119Labels permutation663 permutation3
    mixedMoment B raw36119step0 raw36119step0Labels = mixedMoment B raw36119step1 raw36119step1Labels := by
      have ha : raw36119step1 = -raw36119step0 := by apply Matrix.ext; change ∀ i j, raw36119step1 i j = -(raw36119step0 i j); unfold raw36119step1 raw36119step0; decide +kernel
      have hl : raw36119step1Labels = raw36119step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36119step1 raw36119step1Labels = mixedMoment B raw36119step2 raw36119step2Labels := by
      have ha : raw36119step2 = raw36119step1 := by apply Matrix.ext; unfold raw36119step2 raw36119step1; decide +kernel
      have hl : raw36119step1Labels = labelEmbedding6 ∘ raw36119step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36119step1 raw36119step1Labels raw36119step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5337 node5337Labels := by rfl

def raw36120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw36120Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36120step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw36120step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36120step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36120step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36120step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36120step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36120step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36120step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36120 raw36120Labels = mixedMoment B node5356 node5356Labels := by
  calc
    mixedMoment B raw36120 raw36120Labels = mixedMoment B raw36120step0 raw36120step0Labels := by
      have hz : ∀ j, raw36120 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36120step0 = (fun i j => raw36120 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36120step0 raw36120; decide +kernel
      have hl : raw36120step0Labels = raw36120Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36120 raw36120Labels permutation346 hz
    mixedMoment B raw36120step0 raw36120step0Labels = mixedMoment B raw36120step1 raw36120step1Labels := by
      have ha : raw36120step1 = (fun i j => raw36120step0 (permutation144 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36120step1 raw36120step0; decide +kernel
      have hl : raw36120step1Labels = raw36120step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36120step0 raw36120step0Labels permutation144 permutation3
    mixedMoment B raw36120step1 raw36120step1Labels = mixedMoment B raw36120step2 raw36120step2Labels := by
      have ha : raw36120step2 = -raw36120step1 := by apply Matrix.ext; change ∀ i j, raw36120step2 i j = -(raw36120step1 i j); unfold raw36120step2 raw36120step1; decide +kernel
      have hl : raw36120step2Labels = raw36120step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36120step2 raw36120step2Labels = mixedMoment B raw36120step3 raw36120step3Labels := by
      have ha : raw36120step3 = raw36120step2 := by apply Matrix.ext; unfold raw36120step3 raw36120step2; decide +kernel
      have hl : raw36120step2Labels = labelEmbedding6 ∘ raw36120step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36120step2 raw36120step2Labels raw36120step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5356 node5356Labels := by rfl

def raw36121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw36121Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36121step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw36121step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36121step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36121step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36121step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36121step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36121 raw36121Labels = mixedMoment B node4946 node4946Labels := by
  calc
    mixedMoment B raw36121 raw36121Labels = mixedMoment B raw36121step0 raw36121step0Labels := by
      have hz : ∀ j, raw36121 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36121step0 = (fun i j => raw36121 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36121step0 raw36121; decide +kernel
      have hl : raw36121step0Labels = raw36121Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36121 raw36121Labels permutation346 hz
    mixedMoment B raw36121step0 raw36121step0Labels = mixedMoment B raw36121step1 raw36121step1Labels := by
      have ha : raw36121step1 = (fun i j => raw36121step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36121step1 raw36121step0; decide +kernel
      have hl : raw36121step1Labels = raw36121step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36121step0 raw36121step0Labels permutation56 permutation3
    mixedMoment B raw36121step1 raw36121step1Labels = mixedMoment B raw36121step2 raw36121step2Labels := by
      have ha : raw36121step2 = raw36121step1 := by apply Matrix.ext; unfold raw36121step2 raw36121step1; decide +kernel
      have hl : raw36121step1Labels = labelEmbedding6 ∘ raw36121step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36121step1 raw36121step1Labels raw36121step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4946 node4946Labels := by rfl

def raw36122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw36122Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36122step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36122step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36122step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36122step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36122step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36122step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36122 raw36122Labels = mixedMoment B node5337 node5337Labels := by
  calc
    mixedMoment B raw36122 raw36122Labels = mixedMoment B raw36122step0 raw36122step0Labels := by
      have ha : raw36122step0 = (fun i j => raw36122 (permutation687 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36122step0 raw36122; decide +kernel
      have hl : raw36122step0Labels = raw36122Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36122 raw36122Labels permutation687 permutation3
    mixedMoment B raw36122step0 raw36122step0Labels = mixedMoment B raw36122step1 raw36122step1Labels := by
      have ha : raw36122step1 = -raw36122step0 := by apply Matrix.ext; change ∀ i j, raw36122step1 i j = -(raw36122step0 i j); unfold raw36122step1 raw36122step0; decide +kernel
      have hl : raw36122step1Labels = raw36122step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36122step1 raw36122step1Labels = mixedMoment B raw36122step2 raw36122step2Labels := by
      have ha : raw36122step2 = raw36122step1 := by apply Matrix.ext; unfold raw36122step2 raw36122step1; decide +kernel
      have hl : raw36122step1Labels = labelEmbedding6 ∘ raw36122step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36122step1 raw36122step1Labels raw36122step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5337 node5337Labels := by rfl

def raw36123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw36123Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw36123step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36123step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36123step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36123step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36123step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36123step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36123step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36123 raw36123Labels = mixedMoment B node5356 node5356Labels := by
  calc
    mixedMoment B raw36123 raw36123Labels = mixedMoment B raw36123step0 raw36123step0Labels := by
      have hz : ∀ j, raw36123 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36123step0 = (fun i j => raw36123 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36123step0 raw36123; decide +kernel
      have hl : raw36123step0Labels = raw36123Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36123 raw36123Labels permutation346 hz
    mixedMoment B raw36123step0 raw36123step0Labels = mixedMoment B raw36123step1 raw36123step1Labels := by
      have ha : raw36123step1 = (fun i j => raw36123step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36123step1 raw36123step0; decide +kernel
      have hl : raw36123step1Labels = raw36123step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36123step0 raw36123step0Labels permutation150 permutation3
    mixedMoment B raw36123step1 raw36123step1Labels = mixedMoment B raw36123step2 raw36123step2Labels := by
      have ha : raw36123step2 = -raw36123step1 := by apply Matrix.ext; change ∀ i j, raw36123step2 i j = -(raw36123step1 i j); unfold raw36123step2 raw36123step1; decide +kernel
      have hl : raw36123step2Labels = raw36123step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36123step2 raw36123step2Labels = mixedMoment B raw36123step3 raw36123step3Labels := by
      have ha : raw36123step3 = raw36123step2 := by apply Matrix.ext; unfold raw36123step3 raw36123step2; decide +kernel
      have hl : raw36123step2Labels = labelEmbedding6 ∘ raw36123step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36123step2 raw36123step2Labels raw36123step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5356 node5356Labels := by rfl

def raw36124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw36124Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36124step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw36124step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36124step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-3, 1, 2]]
def raw36124step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36124step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw36124step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36124step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -1, -2]]
def raw36124step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36124 raw36124Labels = mixedMoment B node4769 node4769Labels := by
  calc
    mixedMoment B raw36124 raw36124Labels = mixedMoment B raw36124step0 raw36124step0Labels := by
      have hz : ∀ j, raw36124 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36124step0 = (fun i j => raw36124 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36124step0 raw36124; decide +kernel
      have hl : raw36124step0Labels = raw36124Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36124 raw36124Labels permutation346 hz
    mixedMoment B raw36124step0 raw36124step0Labels = mixedMoment B raw36124step1 raw36124step1Labels := by
      have ha : raw36124step1 = (fun i j => raw36124step0 (permutation144 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36124step1 raw36124step0; decide +kernel
      have hl : raw36124step1Labels = raw36124step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36124step0 raw36124step0Labels permutation144 permutation3
    mixedMoment B raw36124step1 raw36124step1Labels = mixedMoment B raw36124step2 raw36124step2Labels := by
      have ha : raw36124step2 = -raw36124step1 := by apply Matrix.ext; change ∀ i j, raw36124step2 i j = -(raw36124step1 i j); unfold raw36124step2 raw36124step1; decide +kernel
      have hl : raw36124step2Labels = raw36124step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36124step2 raw36124step2Labels = mixedMoment B raw36124step3 raw36124step3Labels := by
      have ha : raw36124step3 = raw36124step2 := by apply Matrix.ext; unfold raw36124step3 raw36124step2; decide +kernel
      have hl : raw36124step2Labels = labelEmbedding6 ∘ raw36124step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36124step2 raw36124step2Labels raw36124step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4769 node4769Labels := by rfl

def raw36125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw36125Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36125step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36125step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36125step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36125step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36125step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36125step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36125 raw36125Labels = mixedMoment B node4767 node4767Labels := by
  calc
    mixedMoment B raw36125 raw36125Labels = mixedMoment B raw36125step0 raw36125step0Labels := by
      have ha : raw36125step0 = (fun i j => raw36125 (permutation663 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36125step0 raw36125; decide +kernel
      have hl : raw36125step0Labels = raw36125Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36125 raw36125Labels permutation663 permutation3
    mixedMoment B raw36125step0 raw36125step0Labels = mixedMoment B raw36125step1 raw36125step1Labels := by
      have ha : raw36125step1 = -raw36125step0 := by apply Matrix.ext; change ∀ i j, raw36125step1 i j = -(raw36125step0 i j); unfold raw36125step1 raw36125step0; decide +kernel
      have hl : raw36125step1Labels = raw36125step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36125step1 raw36125step1Labels = mixedMoment B raw36125step2 raw36125step2Labels := by
      have ha : raw36125step2 = raw36125step1 := by apply Matrix.ext; unfold raw36125step2 raw36125step1; decide +kernel
      have hl : raw36125step1Labels = labelEmbedding6 ∘ raw36125step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36125step1 raw36125step1Labels raw36125step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4767 node4767Labels := by rfl

def raw36126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw36126Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw36126step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36126step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36126step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36126step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36126step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36126step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36126step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36126 raw36126Labels = mixedMoment B node4811 node4811Labels := by
  calc
    mixedMoment B raw36126 raw36126Labels = mixedMoment B raw36126step0 raw36126step0Labels := by
      have hz : ∀ j, raw36126 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36126step0 = (fun i j => raw36126 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36126step0 raw36126; decide +kernel
      have hl : raw36126step0Labels = raw36126Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36126 raw36126Labels permutation346 hz
    mixedMoment B raw36126step0 raw36126step0Labels = mixedMoment B raw36126step1 raw36126step1Labels := by
      have ha : raw36126step1 = (fun i j => raw36126step0 (permutation144 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36126step1 raw36126step0; decide +kernel
      have hl : raw36126step1Labels = raw36126step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36126step0 raw36126step0Labels permutation144 permutation3
    mixedMoment B raw36126step1 raw36126step1Labels = mixedMoment B raw36126step2 raw36126step2Labels := by
      have ha : raw36126step2 = -raw36126step1 := by apply Matrix.ext; change ∀ i j, raw36126step2 i j = -(raw36126step1 i j); unfold raw36126step2 raw36126step1; decide +kernel
      have hl : raw36126step2Labels = raw36126step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36126step2 raw36126step2Labels = mixedMoment B raw36126step3 raw36126step3Labels := by
      have ha : raw36126step3 = raw36126step2 := by apply Matrix.ext; unfold raw36126step3 raw36126step2; decide +kernel
      have hl : raw36126step2Labels = labelEmbedding6 ∘ raw36126step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36126step2 raw36126step2Labels raw36126step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4811 node4811Labels := by rfl

def raw36127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36127Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36127step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36127step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36127step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36127step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36127step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36127 raw36127Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw36127 raw36127Labels = mixedMoment B raw36127step0 raw36127step0Labels := by
      have hz : ∀ j, raw36127 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36127step0 = (fun i j => raw36127 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36127step0 raw36127; decide +kernel
      have hl : raw36127step0Labels = raw36127Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36127 raw36127Labels permutation346 hz
    mixedMoment B raw36127step0 raw36127step0Labels = mixedMoment B raw36127step1 raw36127step1Labels := by
      have ha : raw36127step1 = (fun i j => raw36127step0 (permutation58 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36127step1 raw36127step0; decide +kernel
      have hl : raw36127step1Labels = raw36127step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36127step0 raw36127step0Labels permutation58 permutation3
    mixedMoment B raw36127step1 raw36127step1Labels = mixedMoment B raw36127step2 raw36127step2Labels := by
      have ha : raw36127step2 = raw36127step1 := by apply Matrix.ext; unfold raw36127step2 raw36127step1; decide +kernel
      have hl : raw36127step1Labels = labelEmbedding6 ∘ raw36127step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36127step1 raw36127step1Labels raw36127step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5169 node5169Labels := by rfl

def raw36128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36128Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36128step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36128step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36128 raw36128Labels = mixedMoment B node5476 node5476Labels := by
  calc
    mixedMoment B raw36128 raw36128Labels = mixedMoment B raw36128step0 raw36128step0Labels := by
      have ha : raw36128step0 = (fun i j => raw36128 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36128step0 raw36128; decide +kernel
      have hl : raw36128step0Labels = raw36128Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36128 raw36128Labels permutation265 permutation2
    _ = mixedMoment B node5476 node5476Labels := by rfl

def raw36129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw36129Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw36129step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36129step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36129step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36129 raw36129Labels = mixedMoment B node5483 node5483Labels := by
  calc
    mixedMoment B raw36129 raw36129Labels = mixedMoment B raw36129step0 raw36129step0Labels := by
      have hz : ∀ j, raw36129 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36129step0 = (fun i j => raw36129 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36129step0 raw36129; decide +kernel
      have hl : raw36129step0Labels = raw36129Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36129 raw36129Labels permutation346 hz
    mixedMoment B raw36129step0 raw36129step0Labels = mixedMoment B raw36129step1 raw36129step1Labels := by
      have ha : raw36129step1 = (fun i j => raw36129step0 (permutation58 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36129step1 raw36129step0; decide +kernel
      have hl : raw36129step1Labels = raw36129step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36129step0 raw36129step0Labels permutation58 permutation2
    _ = mixedMoment B node5483 node5483Labels := by rfl

def raw36130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw36130Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw36130step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36130step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw36130step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36130 raw36130Labels = mixedMoment B node5486 node5486Labels := by
  calc
    mixedMoment B raw36130 raw36130Labels = mixedMoment B raw36130step0 raw36130step0Labels := by
      have hz : ∀ j, raw36130 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36130step0 = (fun i j => raw36130 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36130step0 raw36130; decide +kernel
      have hl : raw36130step0Labels = raw36130Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36130 raw36130Labels permutation346 hz
    mixedMoment B raw36130step0 raw36130step0Labels = mixedMoment B raw36130step1 raw36130step1Labels := by
      have ha : raw36130step1 = (fun i j => raw36130step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36130step1 raw36130step0; decide +kernel
      have hl : raw36130step1Labels = raw36130step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36130step0 raw36130step0Labels permutation56 permutation2
    _ = mixedMoment B node5486 node5486Labels := by rfl

def raw36131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36131Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36131step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36131step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36131step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36131step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36131 raw36131Labels = mixedMoment B node4941 node4941Labels := by
  calc
    mixedMoment B raw36131 raw36131Labels = mixedMoment B raw36131step0 raw36131step0Labels := by
      have ha : raw36131step0 = (fun i j => raw36131 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36131step0 raw36131; decide +kernel
      have hl : raw36131step0Labels = raw36131Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36131 raw36131Labels permutation164 permutation3
    mixedMoment B raw36131step0 raw36131step0Labels = mixedMoment B raw36131step1 raw36131step1Labels := by
      have ha : raw36131step1 = raw36131step0 := by apply Matrix.ext; unfold raw36131step1 raw36131step0; decide +kernel
      have hl : raw36131step0Labels = labelEmbedding6 ∘ raw36131step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36131step0 raw36131step0Labels raw36131step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4941 node4941Labels := by rfl

def raw36132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36132Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36132step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36132step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36132step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36132step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36132 raw36132Labels = mixedMoment B node4941 node4941Labels := by
  calc
    mixedMoment B raw36132 raw36132Labels = mixedMoment B raw36132step0 raw36132step0Labels := by
      have ha : raw36132step0 = (fun i j => raw36132 (permutation277 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36132step0 raw36132; decide +kernel
      have hl : raw36132step0Labels = raw36132Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36132 raw36132Labels permutation277 permutation3
    mixedMoment B raw36132step0 raw36132step0Labels = mixedMoment B raw36132step1 raw36132step1Labels := by
      have ha : raw36132step1 = raw36132step0 := by apply Matrix.ext; unfold raw36132step1 raw36132step0; decide +kernel
      have hl : raw36132step0Labels = labelEmbedding6 ∘ raw36132step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36132step0 raw36132step0Labels raw36132step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4941 node4941Labels := by rfl

def raw36133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw36133Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36133step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36133step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36133step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36133step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36133 raw36133Labels = mixedMoment B node5460 node5460Labels := by
  calc
    mixedMoment B raw36133 raw36133Labels = mixedMoment B raw36133step0 raw36133step0Labels := by
      have ha : raw36133step0 = (fun i j => raw36133 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36133step0 raw36133; decide +kernel
      have hl : raw36133step0Labels = raw36133Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36133 raw36133Labels permutation164 permutation3
    mixedMoment B raw36133step0 raw36133step0Labels = mixedMoment B raw36133step1 raw36133step1Labels := by
      have ha : raw36133step1 = raw36133step0 := by apply Matrix.ext; unfold raw36133step1 raw36133step0; decide +kernel
      have hl : raw36133step0Labels = labelEmbedding6 ∘ raw36133step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36133step0 raw36133step0Labels raw36133step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5460 node5460Labels := by rfl

def raw36134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw36134Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36134 raw36134Labels = mixedMoment B node5464 node5464Labels := by
  calc
    _ = mixedMoment B node5464 node5464Labels := by rfl

def raw36135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36135Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36135step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36135step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36135step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36135step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36135step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36135 raw36135Labels = mixedMoment B node4946 node4946Labels := by
  calc
    mixedMoment B raw36135 raw36135Labels = mixedMoment B raw36135step0 raw36135step0Labels := by
      have hz : ∀ j, raw36135 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36135step0 = (fun i j => raw36135 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36135step0 raw36135; decide +kernel
      have hl : raw36135step0Labels = raw36135Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36135 raw36135Labels permutation346 hz
    mixedMoment B raw36135step0 raw36135step0Labels = mixedMoment B raw36135step1 raw36135step1Labels := by
      have ha : raw36135step1 = (fun i j => raw36135step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36135step1 raw36135step0; decide +kernel
      have hl : raw36135step1Labels = raw36135step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36135step0 raw36135step0Labels permutation35 permutation3
    mixedMoment B raw36135step1 raw36135step1Labels = mixedMoment B raw36135step2 raw36135step2Labels := by
      have ha : raw36135step2 = raw36135step1 := by apply Matrix.ext; unfold raw36135step2 raw36135step1; decide +kernel
      have hl : raw36135step1Labels = labelEmbedding6 ∘ raw36135step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36135step1 raw36135step1Labels raw36135step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4946 node4946Labels := by rfl

def raw36136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36136Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36136step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36136step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36136step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36136step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36136step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36136step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36136 raw36136Labels = mixedMoment B node4946 node4946Labels := by
  calc
    mixedMoment B raw36136 raw36136Labels = mixedMoment B raw36136step0 raw36136step0Labels := by
      have hz : ∀ j, raw36136 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36136step0 = (fun i j => raw36136 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36136step0 raw36136; decide +kernel
      have hl : raw36136step0Labels = raw36136Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36136 raw36136Labels permutation346 hz
    mixedMoment B raw36136step0 raw36136step0Labels = mixedMoment B raw36136step1 raw36136step1Labels := by
      have ha : raw36136step1 = (fun i j => raw36136step0 (permutation59 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36136step1 raw36136step0; decide +kernel
      have hl : raw36136step1Labels = raw36136step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36136step0 raw36136step0Labels permutation59 permutation3
    mixedMoment B raw36136step1 raw36136step1Labels = mixedMoment B raw36136step2 raw36136step2Labels := by
      have ha : raw36136step2 = raw36136step1 := by apply Matrix.ext; unfold raw36136step2 raw36136step1; decide +kernel
      have hl : raw36136step1Labels = labelEmbedding6 ∘ raw36136step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36136step1 raw36136step1Labels raw36136step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4946 node4946Labels := by rfl

def raw36137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36137Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36137step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36137step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36137step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36137step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36137step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36137step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36137 raw36137Labels = mixedMoment B node5337 node5337Labels := by
  calc
    mixedMoment B raw36137 raw36137Labels = mixedMoment B raw36137step0 raw36137step0Labels := by
      have ha : raw36137step0 = (fun i j => raw36137 (permutation518 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36137step0 raw36137; decide +kernel
      have hl : raw36137step0Labels = raw36137Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36137 raw36137Labels permutation518 permutation3
    mixedMoment B raw36137step0 raw36137step0Labels = mixedMoment B raw36137step1 raw36137step1Labels := by
      have ha : raw36137step1 = -raw36137step0 := by apply Matrix.ext; change ∀ i j, raw36137step1 i j = -(raw36137step0 i j); unfold raw36137step1 raw36137step0; decide +kernel
      have hl : raw36137step1Labels = raw36137step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36137step1 raw36137step1Labels = mixedMoment B raw36137step2 raw36137step2Labels := by
      have ha : raw36137step2 = raw36137step1 := by apply Matrix.ext; unfold raw36137step2 raw36137step1; decide +kernel
      have hl : raw36137step1Labels = labelEmbedding6 ∘ raw36137step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36137step1 raw36137step1Labels raw36137step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5337 node5337Labels := by rfl

def raw36138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -2, 0], ![0, 1, -1], ![2, -1, -1]]
def raw36138Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -2, 0], ![0, 1, -1], ![2, -1, -1]]
def raw36138step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36138step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36138step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36138step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36138step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36138step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36138step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36138 raw36138Labels = mixedMoment B node5356 node5356Labels := by
  calc
    mixedMoment B raw36138 raw36138Labels = mixedMoment B raw36138step0 raw36138step0Labels := by
      have hz : ∀ j, raw36138 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36138step0 = (fun i j => raw36138 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36138step0 raw36138; decide +kernel
      have hl : raw36138step0Labels = raw36138Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36138 raw36138Labels permutation346 hz
    mixedMoment B raw36138step0 raw36138step0Labels = mixedMoment B raw36138step1 raw36138step1Labels := by
      have ha : raw36138step1 = (fun i j => raw36138step0 (permutation102 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36138step1 raw36138step0; decide +kernel
      have hl : raw36138step1Labels = raw36138step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36138step0 raw36138step0Labels permutation102 permutation3
    mixedMoment B raw36138step1 raw36138step1Labels = mixedMoment B raw36138step2 raw36138step2Labels := by
      have ha : raw36138step2 = -raw36138step1 := by apply Matrix.ext; change ∀ i j, raw36138step2 i j = -(raw36138step1 i j); unfold raw36138step2 raw36138step1; decide +kernel
      have hl : raw36138step2Labels = raw36138step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36138step2 raw36138step2Labels = mixedMoment B raw36138step3 raw36138step3Labels := by
      have ha : raw36138step3 = raw36138step2 := by apply Matrix.ext; unfold raw36138step3 raw36138step2; decide +kernel
      have hl : raw36138step2Labels = labelEmbedding6 ∘ raw36138step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36138step2 raw36138step2Labels raw36138step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5356 node5356Labels := by rfl

def raw36139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw36139Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36139step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw36139step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36139step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw36139step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36139step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw36139step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36139step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw36139step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36139 raw36139Labels = mixedMoment B node5418 node5418Labels := by
  calc
    mixedMoment B raw36139 raw36139Labels = mixedMoment B raw36139step0 raw36139step0Labels := by
      have hz : ∀ j, raw36139 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36139step0 = (fun i j => raw36139 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36139step0 raw36139; decide +kernel
      have hl : raw36139step0Labels = raw36139Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36139 raw36139Labels permutation346 hz
    mixedMoment B raw36139step0 raw36139step0Labels = mixedMoment B raw36139step1 raw36139step1Labels := by
      have ha : raw36139step1 = (fun i j => raw36139step0 (permutation96 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36139step1 raw36139step0; decide +kernel
      have hl : raw36139step1Labels = raw36139step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36139step0 raw36139step0Labels permutation96 permutation3
    mixedMoment B raw36139step1 raw36139step1Labels = mixedMoment B raw36139step2 raw36139step2Labels := by
      have ha : raw36139step2 = -raw36139step1 := by apply Matrix.ext; change ∀ i j, raw36139step2 i j = -(raw36139step1 i j); unfold raw36139step2 raw36139step1; decide +kernel
      have hl : raw36139step2Labels = raw36139step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36139step2 raw36139step2Labels = mixedMoment B raw36139step3 raw36139step3Labels := by
      have ha : raw36139step3 = raw36139step2 := by apply Matrix.ext; unfold raw36139step3 raw36139step2; decide +kernel
      have hl : raw36139step2Labels = labelEmbedding6 ∘ raw36139step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36139step2 raw36139step2Labels raw36139step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5418 node5418Labels := by rfl

def raw36140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw36140Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36140step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw36140step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36140step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw36140step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36140step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw36140step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36140 raw36140Labels = mixedMoment B node4943 node4943Labels := by
  calc
    mixedMoment B raw36140 raw36140Labels = mixedMoment B raw36140step0 raw36140step0Labels := by
      have hz : ∀ j, raw36140 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36140step0 = (fun i j => raw36140 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36140step0 raw36140; decide +kernel
      have hl : raw36140step0Labels = raw36140Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36140 raw36140Labels permutation346 hz
    mixedMoment B raw36140step0 raw36140step0Labels = mixedMoment B raw36140step1 raw36140step1Labels := by
      have ha : raw36140step1 = (fun i j => raw36140step0 (permutation58 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36140step1 raw36140step0; decide +kernel
      have hl : raw36140step1Labels = raw36140step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36140step0 raw36140step0Labels permutation58 permutation3
    mixedMoment B raw36140step1 raw36140step1Labels = mixedMoment B raw36140step2 raw36140step2Labels := by
      have ha : raw36140step2 = raw36140step1 := by apply Matrix.ext; unfold raw36140step2 raw36140step1; decide +kernel
      have hl : raw36140step1Labels = labelEmbedding6 ∘ raw36140step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36140step1 raw36140step1Labels raw36140step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4943 node4943Labels := by rfl

def raw36141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw36141Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36141step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36141step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36141step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36141step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36141step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36141step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36141 raw36141Labels = mixedMoment B node5039 node5039Labels := by
  calc
    mixedMoment B raw36141 raw36141Labels = mixedMoment B raw36141step0 raw36141step0Labels := by
      have ha : raw36141step0 = (fun i j => raw36141 (permutation663 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36141step0 raw36141; decide +kernel
      have hl : raw36141step0Labels = raw36141Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36141 raw36141Labels permutation663 permutation3
    mixedMoment B raw36141step0 raw36141step0Labels = mixedMoment B raw36141step1 raw36141step1Labels := by
      have ha : raw36141step1 = -raw36141step0 := by apply Matrix.ext; change ∀ i j, raw36141step1 i j = -(raw36141step0 i j); unfold raw36141step1 raw36141step0; decide +kernel
      have hl : raw36141step1Labels = raw36141step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36141step1 raw36141step1Labels = mixedMoment B raw36141step2 raw36141step2Labels := by
      have ha : raw36141step2 = raw36141step1 := by apply Matrix.ext; unfold raw36141step2 raw36141step1; decide +kernel
      have hl : raw36141step1Labels = labelEmbedding6 ∘ raw36141step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36141step1 raw36141step1Labels raw36141step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5039 node5039Labels := by rfl

def raw36142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw36142Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw36142step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36142step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36142step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36142step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36142step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36142step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36142step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36142 raw36142Labels = mixedMoment B node5081 node5081Labels := by
  calc
    mixedMoment B raw36142 raw36142Labels = mixedMoment B raw36142step0 raw36142step0Labels := by
      have hz : ∀ j, raw36142 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36142step0 = (fun i j => raw36142 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36142step0 raw36142; decide +kernel
      have hl : raw36142step0Labels = raw36142Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36142 raw36142Labels permutation346 hz
    mixedMoment B raw36142step0 raw36142step0Labels = mixedMoment B raw36142step1 raw36142step1Labels := by
      have ha : raw36142step1 = (fun i j => raw36142step0 (permutation144 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36142step1 raw36142step0; decide +kernel
      have hl : raw36142step1Labels = raw36142step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36142step0 raw36142step0Labels permutation144 permutation3
    mixedMoment B raw36142step1 raw36142step1Labels = mixedMoment B raw36142step2 raw36142step2Labels := by
      have ha : raw36142step2 = -raw36142step1 := by apply Matrix.ext; change ∀ i j, raw36142step2 i j = -(raw36142step1 i j); unfold raw36142step2 raw36142step1; decide +kernel
      have hl : raw36142step2Labels = raw36142step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36142step2 raw36142step2Labels = mixedMoment B raw36142step3 raw36142step3Labels := by
      have ha : raw36142step3 = raw36142step2 := by apply Matrix.ext; unfold raw36142step3 raw36142step2; decide +kernel
      have hl : raw36142step2Labels = labelEmbedding6 ∘ raw36142step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36142step2 raw36142step2Labels raw36142step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5081 node5081Labels := by rfl

def raw36143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw36143Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw36143step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36143step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36143step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36143step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36143step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36143 raw36143Labels = mixedMoment B node5163 node5163Labels := by
  calc
    mixedMoment B raw36143 raw36143Labels = mixedMoment B raw36143step0 raw36143step0Labels := by
      have hz : ∀ j, raw36143 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36143step0 = (fun i j => raw36143 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36143step0 raw36143; decide +kernel
      have hl : raw36143step0Labels = raw36143Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36143 raw36143Labels permutation346 hz
    mixedMoment B raw36143step0 raw36143step0Labels = mixedMoment B raw36143step1 raw36143step1Labels := by
      have ha : raw36143step1 = (fun i j => raw36143step0 (permutation58 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36143step1 raw36143step0; decide +kernel
      have hl : raw36143step1Labels = raw36143step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36143step0 raw36143step0Labels permutation58 permutation3
    mixedMoment B raw36143step1 raw36143step1Labels = mixedMoment B raw36143step2 raw36143step2Labels := by
      have ha : raw36143step2 = raw36143step1 := by apply Matrix.ext; unfold raw36143step2 raw36143step1; decide +kernel
      have hl : raw36143step1Labels = labelEmbedding6 ∘ raw36143step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36143step1 raw36143step1Labels raw36143step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5163 node5163Labels := by rfl

def raw36144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw36144Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36144step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw36144step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36144step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36144step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36144step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36144step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36144 raw36144Labels = mixedMoment B node5401 node5401Labels := by
  calc
    mixedMoment B raw36144 raw36144Labels = mixedMoment B raw36144step0 raw36144step0Labels := by
      have ha : raw36144step0 = (fun i j => raw36144 (permutation660 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36144step0 raw36144; decide +kernel
      have hl : raw36144step0Labels = raw36144Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36144 raw36144Labels permutation660 permutation3
    mixedMoment B raw36144step0 raw36144step0Labels = mixedMoment B raw36144step1 raw36144step1Labels := by
      have ha : raw36144step1 = -raw36144step0 := by apply Matrix.ext; change ∀ i j, raw36144step1 i j = -(raw36144step0 i j); unfold raw36144step1 raw36144step0; decide +kernel
      have hl : raw36144step1Labels = raw36144step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36144step1 raw36144step1Labels = mixedMoment B raw36144step2 raw36144step2Labels := by
      have ha : raw36144step2 = raw36144step1 := by apply Matrix.ext; unfold raw36144step2 raw36144step1; decide +kernel
      have hl : raw36144step1Labels = labelEmbedding6 ∘ raw36144step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36144step1 raw36144step1Labels raw36144step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5401 node5401Labels := by rfl

def raw36145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw36145Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw36145step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36145step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw36145step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36145step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw36145step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36145step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36145step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36145step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36145step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36145 raw36145Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw36145 raw36145Labels = mixedMoment B raw36145step0 raw36145step0Labels := by
      have hz : ∀ j, raw36145 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw36145step0 = (fun i j => raw36145 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw36145step0 raw36145; decide +kernel
      have hl : raw36145step0Labels = raw36145Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36145 raw36145Labels permutation434 hz
    mixedMoment B raw36145step0 raw36145step0Labels = mixedMoment B raw36145step1 raw36145step1Labels := by
      have hz : ∀ j, raw36145step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36145step1 = (fun i j => raw36145step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36145step1 raw36145step0; decide +kernel
      have hl : raw36145step1Labels = raw36145step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36145step0 raw36145step0Labels permutation80 hz
    mixedMoment B raw36145step1 raw36145step1Labels = mixedMoment B raw36145step2 raw36145step2Labels := by
      have ha : raw36145step2 = (fun i j => raw36145step1 (permutation30 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36145step2 raw36145step1; decide +kernel
      have hl : raw36145step2Labels = raw36145step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36145step1 raw36145step1Labels permutation30 permutation3
    mixedMoment B raw36145step2 raw36145step2Labels = mixedMoment B raw36145step3 raw36145step3Labels := by
      have ha : raw36145step3 = -raw36145step2 := by apply Matrix.ext; change ∀ i j, raw36145step3 i j = -(raw36145step2 i j); unfold raw36145step3 raw36145step2; decide +kernel
      have hl : raw36145step3Labels = raw36145step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36145step3 raw36145step3Labels = mixedMoment B raw36145step4 raw36145step4Labels := by
      have ha : raw36145step4 = raw36145step3 := by apply Matrix.ext; unfold raw36145step4 raw36145step3; decide +kernel
      have hl : raw36145step3Labels = labelEmbedding6 ∘ raw36145step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36145step3 raw36145step3Labels raw36145step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5451 node5451Labels := by rfl

def raw36146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw36146Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw36146step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36146step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36146step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36146step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36146step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36146 raw36146Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw36146 raw36146Labels = mixedMoment B raw36146step0 raw36146step0Labels := by
      have hz : ∀ j, raw36146 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36146step0 = (fun i j => raw36146 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36146step0 raw36146; decide +kernel
      have hl : raw36146step0Labels = raw36146Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36146 raw36146Labels permutation346 hz
    mixedMoment B raw36146step0 raw36146step0Labels = mixedMoment B raw36146step1 raw36146step1Labels := by
      have ha : raw36146step1 = (fun i j => raw36146step0 (permutation140 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36146step1 raw36146step0; decide +kernel
      have hl : raw36146step1Labels = raw36146step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36146step0 raw36146step0Labels permutation140 permutation5
    mixedMoment B raw36146step1 raw36146step1Labels = mixedMoment B raw36146step2 raw36146step2Labels := by
      have ha : raw36146step2 = raw36146step1 := by apply Matrix.ext; unfold raw36146step2 raw36146step1; decide +kernel
      have hl : raw36146step1Labels = labelEmbedding8 ∘ raw36146step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36146step1 raw36146step1Labels raw36146step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw36147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw36147Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw36147step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36147step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw36147step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36147 raw36147Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw36147 raw36147Labels = mixedMoment B raw36147step0 raw36147step0Labels := by
      have hz : ∀ j, raw36147 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36147step0 = (fun i j => raw36147 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36147step0 raw36147; decide +kernel
      have hl : raw36147step0Labels = raw36147Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36147 raw36147Labels permutation346 hz
    mixedMoment B raw36147step0 raw36147step0Labels = mixedMoment B raw36147step1 raw36147step1Labels := by
      have ha : raw36147step1 = (fun i j => raw36147step0 (permutation57 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36147step1 raw36147step0; decide +kernel
      have hl : raw36147step1Labels = raw36147step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36147step0 raw36147step0Labels permutation57 permutation2
    _ = mixedMoment B node5485 node5485Labels := by rfl

def raw36148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw36148Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36148step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36148step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36148step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36148step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36148 raw36148Labels = mixedMoment B node4936 node4936Labels := by
  calc
    mixedMoment B raw36148 raw36148Labels = mixedMoment B raw36148step0 raw36148step0Labels := by
      have ha : raw36148step0 = (fun i j => raw36148 (permutation277 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36148step0 raw36148; decide +kernel
      have hl : raw36148step0Labels = raw36148Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36148 raw36148Labels permutation277 permutation3
    mixedMoment B raw36148step0 raw36148step0Labels = mixedMoment B raw36148step1 raw36148step1Labels := by
      have ha : raw36148step1 = raw36148step0 := by apply Matrix.ext; unfold raw36148step1 raw36148step0; decide +kernel
      have hl : raw36148step0Labels = labelEmbedding6 ∘ raw36148step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36148step0 raw36148step0Labels raw36148step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4936 node4936Labels := by rfl

def raw36149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw36149Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36149step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw36149step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36149step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36149step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36149step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36149step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36149step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36149step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36149 raw36149Labels = mixedMoment B node5404 node5404Labels := by
  calc
    mixedMoment B raw36149 raw36149Labels = mixedMoment B raw36149step0 raw36149step0Labels := by
      have hz : ∀ j, raw36149 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw36149step0 = (fun i j => raw36149 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw36149step0 raw36149; decide +kernel
      have hl : raw36149step0Labels = raw36149Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36149 raw36149Labels permutation434 hz
    mixedMoment B raw36149step0 raw36149step0Labels = mixedMoment B raw36149step1 raw36149step1Labels := by
      have ha : raw36149step1 = (fun i j => raw36149step0 (permutation144 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36149step1 raw36149step0; decide +kernel
      have hl : raw36149step1Labels = raw36149step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36149step0 raw36149step0Labels permutation144 permutation3
    mixedMoment B raw36149step1 raw36149step1Labels = mixedMoment B raw36149step2 raw36149step2Labels := by
      have ha : raw36149step2 = -raw36149step1 := by apply Matrix.ext; change ∀ i j, raw36149step2 i j = -(raw36149step1 i j); unfold raw36149step2 raw36149step1; decide +kernel
      have hl : raw36149step2Labels = raw36149step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36149step2 raw36149step2Labels = mixedMoment B raw36149step3 raw36149step3Labels := by
      have ha : raw36149step3 = raw36149step2 := by apply Matrix.ext; unfold raw36149step3 raw36149step2; decide +kernel
      have hl : raw36149step2Labels = labelEmbedding6 ∘ raw36149step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36149step2 raw36149step2Labels raw36149step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5404 node5404Labels := by rfl

def raw36150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw36150Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36150step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, 0, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw36150step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36150step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw36150step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36150step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw36150step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36150 raw36150Labels = mixedMoment B node5391 node5391Labels := by
  calc
    mixedMoment B raw36150 raw36150Labels = mixedMoment B raw36150step0 raw36150step0Labels := by
      have ha : raw36150step0 = (fun i j => raw36150 (permutation639 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36150step0 raw36150; decide +kernel
      have hl : raw36150step0Labels = raw36150Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36150 raw36150Labels permutation639 permutation3
    mixedMoment B raw36150step0 raw36150step0Labels = mixedMoment B raw36150step1 raw36150step1Labels := by
      have ha : raw36150step1 = -raw36150step0 := by apply Matrix.ext; change ∀ i j, raw36150step1 i j = -(raw36150step0 i j); unfold raw36150step1 raw36150step0; decide +kernel
      have hl : raw36150step1Labels = raw36150step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36150step1 raw36150step1Labels = mixedMoment B raw36150step2 raw36150step2Labels := by
      have ha : raw36150step2 = raw36150step1 := by apply Matrix.ext; unfold raw36150step2 raw36150step1; decide +kernel
      have hl : raw36150step1Labels = labelEmbedding6 ∘ raw36150step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36150step1 raw36150step1Labels raw36150step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5391 node5391Labels := by rfl

def raw36151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw36151Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36151step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw36151step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36151step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw36151step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36151 raw36151Labels = mixedMoment B node5462 node5462Labels := by
  calc
    mixedMoment B raw36151 raw36151Labels = mixedMoment B raw36151step0 raw36151step0Labels := by
      have ha : raw36151step0 = (fun i j => raw36151 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36151step0 raw36151; decide +kernel
      have hl : raw36151step0Labels = raw36151Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36151 raw36151Labels permutation164 permutation3
    mixedMoment B raw36151step0 raw36151step0Labels = mixedMoment B raw36151step1 raw36151step1Labels := by
      have ha : raw36151step1 = raw36151step0 := by apply Matrix.ext; unfold raw36151step1 raw36151step0; decide +kernel
      have hl : raw36151step0Labels = labelEmbedding6 ∘ raw36151step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36151step0 raw36151step0Labels raw36151step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5462 node5462Labels := by rfl

def raw36152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw36152Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw36152step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36152step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw36152step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36152step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw36152step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36152 raw36152Labels = mixedMoment B node4937 node4937Labels := by
  calc
    mixedMoment B raw36152 raw36152Labels = mixedMoment B raw36152step0 raw36152step0Labels := by
      have hz : ∀ j, raw36152 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36152step0 = (fun i j => raw36152 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36152step0 raw36152; decide +kernel
      have hl : raw36152step0Labels = raw36152Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36152 raw36152Labels permutation346 hz
    mixedMoment B raw36152step0 raw36152step0Labels = mixedMoment B raw36152step1 raw36152step1Labels := by
      have ha : raw36152step1 = (fun i j => raw36152step0 (permutation58 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36152step1 raw36152step0; decide +kernel
      have hl : raw36152step1Labels = raw36152step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36152step0 raw36152step0Labels permutation58 permutation3
    mixedMoment B raw36152step1 raw36152step1Labels = mixedMoment B raw36152step2 raw36152step2Labels := by
      have ha : raw36152step2 = raw36152step1 := by apply Matrix.ext; unfold raw36152step2 raw36152step1; decide +kernel
      have hl : raw36152step1Labels = labelEmbedding6 ∘ raw36152step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36152step1 raw36152step1Labels raw36152step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4937 node4937Labels := by rfl

def raw36153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw36153Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36153step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36153step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36153step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36153step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36153step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36153step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36153 raw36153Labels = mixedMoment B node5319 node5319Labels := by
  calc
    mixedMoment B raw36153 raw36153Labels = mixedMoment B raw36153step0 raw36153step0Labels := by
      have ha : raw36153step0 = (fun i j => raw36153 (permutation518 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36153step0 raw36153; decide +kernel
      have hl : raw36153step0Labels = raw36153Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36153 raw36153Labels permutation518 permutation3
    mixedMoment B raw36153step0 raw36153step0Labels = mixedMoment B raw36153step1 raw36153step1Labels := by
      have ha : raw36153step1 = -raw36153step0 := by apply Matrix.ext; change ∀ i j, raw36153step1 i j = -(raw36153step0 i j); unfold raw36153step1 raw36153step0; decide +kernel
      have hl : raw36153step1Labels = raw36153step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36153step1 raw36153step1Labels = mixedMoment B raw36153step2 raw36153step2Labels := by
      have ha : raw36153step2 = raw36153step1 := by apply Matrix.ext; unfold raw36153step2 raw36153step1; decide +kernel
      have hl : raw36153step1Labels = labelEmbedding6 ∘ raw36153step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36153step1 raw36153step1Labels raw36153step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5319 node5319Labels := by rfl

def raw36154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -2, 0], ![0, 2, -2], ![2, -2, 0]]
def raw36154Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36154step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -2, 0], ![0, 2, -2], ![2, -2, 0]]
def raw36154step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36154step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw36154step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36154step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw36154step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36154step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw36154step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36154 raw36154Labels = mixedMoment B node5330 node5330Labels := by
  calc
    mixedMoment B raw36154 raw36154Labels = mixedMoment B raw36154step0 raw36154step0Labels := by
      have hz : ∀ j, raw36154 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36154step0 = (fun i j => raw36154 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36154step0 raw36154; decide +kernel
      have hl : raw36154step0Labels = raw36154Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36154 raw36154Labels permutation346 hz
    mixedMoment B raw36154step0 raw36154step0Labels = mixedMoment B raw36154step1 raw36154step1Labels := by
      have ha : raw36154step1 = (fun i j => raw36154step0 (permutation102 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36154step1 raw36154step0; decide +kernel
      have hl : raw36154step1Labels = raw36154step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36154step0 raw36154step0Labels permutation102 permutation3
    mixedMoment B raw36154step1 raw36154step1Labels = mixedMoment B raw36154step2 raw36154step2Labels := by
      have ha : raw36154step2 = -raw36154step1 := by apply Matrix.ext; change ∀ i j, raw36154step2 i j = -(raw36154step1 i j); unfold raw36154step2 raw36154step1; decide +kernel
      have hl : raw36154step2Labels = raw36154step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36154step2 raw36154step2Labels = mixedMoment B raw36154step3 raw36154step3Labels := by
      have ha : raw36154step3 = raw36154step2 := by apply Matrix.ext; unfold raw36154step3 raw36154step2; decide +kernel
      have hl : raw36154step2Labels = labelEmbedding6 ∘ raw36154step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36154step2 raw36154step2Labels raw36154step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5330 node5330Labels := by rfl

def raw36155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2], ![1, -1, 0]]
def raw36155Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36155step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -2, 0], ![1, 1, -2], ![1, -1, 0]]
def raw36155step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36155step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36155step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36155step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36155step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36155step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36155step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36155 raw36155Labels = mixedMoment B node5404 node5404Labels := by
  calc
    mixedMoment B raw36155 raw36155Labels = mixedMoment B raw36155step0 raw36155step0Labels := by
      have hz : ∀ j, raw36155 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36155step0 = (fun i j => raw36155 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36155step0 raw36155; decide +kernel
      have hl : raw36155step0Labels = raw36155Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36155 raw36155Labels permutation346 hz
    mixedMoment B raw36155step0 raw36155step0Labels = mixedMoment B raw36155step1 raw36155step1Labels := by
      have ha : raw36155step1 = (fun i j => raw36155step0 (permutation102 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36155step1 raw36155step0; decide +kernel
      have hl : raw36155step1Labels = raw36155step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36155step0 raw36155step0Labels permutation102 permutation3
    mixedMoment B raw36155step1 raw36155step1Labels = mixedMoment B raw36155step2 raw36155step2Labels := by
      have ha : raw36155step2 = -raw36155step1 := by apply Matrix.ext; change ∀ i j, raw36155step2 i j = -(raw36155step1 i j); unfold raw36155step2 raw36155step1; decide +kernel
      have hl : raw36155step2Labels = raw36155step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36155step2 raw36155step2Labels = mixedMoment B raw36155step3 raw36155step3Labels := by
      have ha : raw36155step3 = raw36155step2 := by apply Matrix.ext; unfold raw36155step3 raw36155step2; decide +kernel
      have hl : raw36155step2Labels = labelEmbedding6 ∘ raw36155step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36155step2 raw36155step2Labels raw36155step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5404 node5404Labels := by rfl

def raw36156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw36156Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36156step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw36156step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36156step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36156step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36156step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36156step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36156 raw36156Labels = mixedMoment B node4949 node4949Labels := by
  calc
    mixedMoment B raw36156 raw36156Labels = mixedMoment B raw36156step0 raw36156step0Labels := by
      have hz : ∀ j, raw36156 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36156step0 = (fun i j => raw36156 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36156step0 raw36156; decide +kernel
      have hl : raw36156step0Labels = raw36156Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36156 raw36156Labels permutation346 hz
    mixedMoment B raw36156step0 raw36156step0Labels = mixedMoment B raw36156step1 raw36156step1Labels := by
      have ha : raw36156step1 = (fun i j => raw36156step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36156step1 raw36156step0; decide +kernel
      have hl : raw36156step1Labels = raw36156step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36156step0 raw36156step0Labels permutation56 permutation3
    mixedMoment B raw36156step1 raw36156step1Labels = mixedMoment B raw36156step2 raw36156step2Labels := by
      have ha : raw36156step2 = raw36156step1 := by apply Matrix.ext; unfold raw36156step2 raw36156step1; decide +kernel
      have hl : raw36156step1Labels = labelEmbedding6 ∘ raw36156step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36156step1 raw36156step1Labels raw36156step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4949 node4949Labels := by rfl

def raw36157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw36157Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36157step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![1, 0, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36157step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36157step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36157step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36157step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36157step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36157 raw36157Labels = mixedMoment B node5373 node5373Labels := by
  calc
    mixedMoment B raw36157 raw36157Labels = mixedMoment B raw36157step0 raw36157step0Labels := by
      have ha : raw36157step0 = (fun i j => raw36157 (permutation687 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36157step0 raw36157; decide +kernel
      have hl : raw36157step0Labels = raw36157Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36157 raw36157Labels permutation687 permutation3
    mixedMoment B raw36157step0 raw36157step0Labels = mixedMoment B raw36157step1 raw36157step1Labels := by
      have ha : raw36157step1 = -raw36157step0 := by apply Matrix.ext; change ∀ i j, raw36157step1 i j = -(raw36157step0 i j); unfold raw36157step1 raw36157step0; decide +kernel
      have hl : raw36157step1Labels = raw36157step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36157step1 raw36157step1Labels = mixedMoment B raw36157step2 raw36157step2Labels := by
      have ha : raw36157step2 = raw36157step1 := by apply Matrix.ext; unfold raw36157step2 raw36157step1; decide +kernel
      have hl : raw36157step1Labels = labelEmbedding6 ∘ raw36157step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36157step1 raw36157step1Labels raw36157step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5373 node5373Labels := by rfl

def raw36158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw36158Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw36158step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36158step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw36158step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36158step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw36158step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36158 raw36158Labels = mixedMoment B node5418 node5418Labels := by
  calc
    mixedMoment B raw36158 raw36158Labels = mixedMoment B raw36158step0 raw36158step0Labels := by
      have hz : ∀ j, raw36158 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36158step0 = (fun i j => raw36158 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36158step0 raw36158; decide +kernel
      have hl : raw36158step0Labels = raw36158Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36158 raw36158Labels permutation346 hz
    mixedMoment B raw36158step0 raw36158step0Labels = mixedMoment B raw36158step1 raw36158step1Labels := by
      have ha : raw36158step1 = (fun i j => raw36158step0 (permutation120 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36158step1 raw36158step0; decide +kernel
      have hl : raw36158step1Labels = raw36158step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36158step0 raw36158step0Labels permutation120 permutation2
    mixedMoment B raw36158step1 raw36158step1Labels = mixedMoment B raw36158step2 raw36158step2Labels := by
      have ha : raw36158step2 = -raw36158step1 := by apply Matrix.ext; change ∀ i j, raw36158step2 i j = -(raw36158step1 i j); unfold raw36158step2 raw36158step1; decide +kernel
      have hl : raw36158step2Labels = raw36158step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5418 node5418Labels := by rfl

def raw36159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw36159Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36159step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw36159step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36159step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw36159step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36159step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw36159step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36159step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw36159step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36159 raw36159Labels = mixedMoment B node4726 node4726Labels := by
  calc
    mixedMoment B raw36159 raw36159Labels = mixedMoment B raw36159step0 raw36159step0Labels := by
      have hz : ∀ j, raw36159 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36159step0 = (fun i j => raw36159 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36159step0 raw36159; decide +kernel
      have hl : raw36159step0Labels = raw36159Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36159 raw36159Labels permutation346 hz
    mixedMoment B raw36159step0 raw36159step0Labels = mixedMoment B raw36159step1 raw36159step1Labels := by
      have ha : raw36159step1 = (fun i j => raw36159step0 (permutation144 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36159step1 raw36159step0; decide +kernel
      have hl : raw36159step1Labels = raw36159step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36159step0 raw36159step0Labels permutation144 permutation3
    mixedMoment B raw36159step1 raw36159step1Labels = mixedMoment B raw36159step2 raw36159step2Labels := by
      have ha : raw36159step2 = -raw36159step1 := by apply Matrix.ext; change ∀ i j, raw36159step2 i j = -(raw36159step1 i j); unfold raw36159step2 raw36159step1; decide +kernel
      have hl : raw36159step2Labels = raw36159step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36159step2 raw36159step2Labels = mixedMoment B raw36159step3 raw36159step3Labels := by
      have ha : raw36159step3 = raw36159step2 := by apply Matrix.ext; unfold raw36159step3 raw36159step2; decide +kernel
      have hl : raw36159step2Labels = labelEmbedding6 ∘ raw36159step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36159step2 raw36159step2Labels raw36159step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4726 node4726Labels := by rfl

def raw36160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw36160Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36160step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36160step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36160step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36160step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36160step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36160step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36160 raw36160Labels = mixedMoment B node4725 node4725Labels := by
  calc
    mixedMoment B raw36160 raw36160Labels = mixedMoment B raw36160step0 raw36160step0Labels := by
      have ha : raw36160step0 = (fun i j => raw36160 (permutation663 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36160step0 raw36160; decide +kernel
      have hl : raw36160step0Labels = raw36160Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36160 raw36160Labels permutation663 permutation3
    mixedMoment B raw36160step0 raw36160step0Labels = mixedMoment B raw36160step1 raw36160step1Labels := by
      have ha : raw36160step1 = -raw36160step0 := by apply Matrix.ext; change ∀ i j, raw36160step1 i j = -(raw36160step0 i j); unfold raw36160step1 raw36160step0; decide +kernel
      have hl : raw36160step1Labels = raw36160step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36160step1 raw36160step1Labels = mixedMoment B raw36160step2 raw36160step2Labels := by
      have ha : raw36160step2 = raw36160step1 := by apply Matrix.ext; unfold raw36160step2 raw36160step1; decide +kernel
      have hl : raw36160step1Labels = labelEmbedding6 ∘ raw36160step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36160step1 raw36160step1Labels raw36160step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4725 node4725Labels := by rfl

def raw36161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw36161Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36161step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw36161step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36161step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw36161step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36161step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw36161step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36161step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw36161step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36161 raw36161Labels = mixedMoment B node4750 node4750Labels := by
  calc
    mixedMoment B raw36161 raw36161Labels = mixedMoment B raw36161step0 raw36161step0Labels := by
      have hz : ∀ j, raw36161 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36161step0 = (fun i j => raw36161 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36161step0 raw36161; decide +kernel
      have hl : raw36161step0Labels = raw36161Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36161 raw36161Labels permutation346 hz
    mixedMoment B raw36161step0 raw36161step0Labels = mixedMoment B raw36161step1 raw36161step1Labels := by
      have ha : raw36161step1 = (fun i j => raw36161step0 (permutation144 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36161step1 raw36161step0; decide +kernel
      have hl : raw36161step1Labels = raw36161step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36161step0 raw36161step0Labels permutation144 permutation3
    mixedMoment B raw36161step1 raw36161step1Labels = mixedMoment B raw36161step2 raw36161step2Labels := by
      have ha : raw36161step2 = -raw36161step1 := by apply Matrix.ext; change ∀ i j, raw36161step2 i j = -(raw36161step1 i j); unfold raw36161step2 raw36161step1; decide +kernel
      have hl : raw36161step2Labels = raw36161step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36161step2 raw36161step2Labels = mixedMoment B raw36161step3 raw36161step3Labels := by
      have ha : raw36161step3 = raw36161step2 := by apply Matrix.ext; unfold raw36161step3 raw36161step2; decide +kernel
      have hl : raw36161step2Labels = labelEmbedding6 ∘ raw36161step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36161step2 raw36161step2Labels raw36161step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4750 node4750Labels := by rfl

def raw36162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw36162Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw36162step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36162step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw36162step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36162 raw36162Labels = mixedMoment B node2590 node2590Labels := by
  calc
    mixedMoment B raw36162 raw36162Labels = mixedMoment B raw36162step0 raw36162step0Labels := by
      have hz : ∀ j, raw36162 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36162step0 = (fun i j => raw36162 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36162step0 raw36162; decide +kernel
      have hl : raw36162step0Labels = raw36162Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36162 raw36162Labels permutation346 hz
    mixedMoment B raw36162step0 raw36162step0Labels = mixedMoment B raw36162step1 raw36162step1Labels := by
      have ha : raw36162step1 = (fun i j => raw36162step0 (permutation58 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36162step1 raw36162step0; decide +kernel
      have hl : raw36162step1Labels = raw36162step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36162step0 raw36162step0Labels permutation58 permutation3
    _ = mixedMoment B node2590 node2590Labels := by rfl

def raw36163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw36163Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36163step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw36163step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36163step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36163step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36163 raw36163Labels = mixedMoment B node3787 node3787Labels := by
  calc
    mixedMoment B raw36163 raw36163Labels = mixedMoment B raw36163step0 raw36163step0Labels := by
      have ha : raw36163step0 = (fun i j => raw36163 (permutation660 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36163step0 raw36163; decide +kernel
      have hl : raw36163step0Labels = raw36163Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36163 raw36163Labels permutation660 permutation3
    mixedMoment B raw36163step0 raw36163step0Labels = mixedMoment B raw36163step1 raw36163step1Labels := by
      have ha : raw36163step1 = -raw36163step0 := by apply Matrix.ext; change ∀ i j, raw36163step1 i j = -(raw36163step0 i j); unfold raw36163step1 raw36163step0; decide +kernel
      have hl : raw36163step1Labels = raw36163step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3787 node3787Labels := by rfl

def raw36164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw36164Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36164step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw36164step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36164step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw36164step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36164step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw36164step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36164step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36164step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36164 raw36164Labels = mixedMoment B node3888 node3888Labels := by
  calc
    mixedMoment B raw36164 raw36164Labels = mixedMoment B raw36164step0 raw36164step0Labels := by
      have hz : ∀ j, raw36164 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw36164step0 = (fun i j => raw36164 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw36164step0 raw36164; decide +kernel
      have hl : raw36164step0Labels = raw36164Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36164 raw36164Labels permutation434 hz
    mixedMoment B raw36164step0 raw36164step0Labels = mixedMoment B raw36164step1 raw36164step1Labels := by
      have hz : ∀ j, raw36164step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw36164step1 = (fun i j => raw36164step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw36164step1 raw36164step0; decide +kernel
      have hl : raw36164step1Labels = raw36164step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36164step0 raw36164step0Labels permutation80 hz
    mixedMoment B raw36164step1 raw36164step1Labels = mixedMoment B raw36164step2 raw36164step2Labels := by
      have ha : raw36164step2 = (fun i j => raw36164step1 (permutation30 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36164step2 raw36164step1; decide +kernel
      have hl : raw36164step2Labels = raw36164step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36164step1 raw36164step1Labels permutation30 permutation3
    mixedMoment B raw36164step2 raw36164step2Labels = mixedMoment B raw36164step3 raw36164step3Labels := by
      have ha : raw36164step3 = -raw36164step2 := by apply Matrix.ext; change ∀ i j, raw36164step3 i j = -(raw36164step2 i j); unfold raw36164step3 raw36164step2; decide +kernel
      have hl : raw36164step3Labels = raw36164step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3888 node3888Labels := by rfl

def raw36165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw36165Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw36165step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36165step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw36165step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36165step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw36165step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36165 raw36165Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw36165 raw36165Labels = mixedMoment B raw36165step0 raw36165step0Labels := by
      have hz : ∀ j, raw36165 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36165step0 = (fun i j => raw36165 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36165step0 raw36165; decide +kernel
      have hl : raw36165step0Labels = raw36165Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36165 raw36165Labels permutation346 hz
    mixedMoment B raw36165step0 raw36165step0Labels = mixedMoment B raw36165step1 raw36165step1Labels := by
      have ha : raw36165step1 = (fun i j => raw36165step0 (permutation144 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36165step1 raw36165step0; decide +kernel
      have hl : raw36165step1Labels = raw36165step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36165step0 raw36165step0Labels permutation144 permutation3
    mixedMoment B raw36165step1 raw36165step1Labels = mixedMoment B raw36165step2 raw36165step2Labels := by
      have ha : raw36165step2 = -raw36165step1 := by apply Matrix.ext; change ∀ i j, raw36165step2 i j = -(raw36165step1 i j); unfold raw36165step2 raw36165step1; decide +kernel
      have hl : raw36165step2Labels = raw36165step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3813 node3813Labels := by rfl

def raw36166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw36166Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36166step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw36166step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36166step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw36166step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36166 raw36166Labels = mixedMoment B node3998 node3998Labels := by
  calc
    mixedMoment B raw36166 raw36166Labels = mixedMoment B raw36166step0 raw36166step0Labels := by
      have hz : ∀ j, raw36166 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36166step0 = (fun i j => raw36166 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36166step0 raw36166; decide +kernel
      have hl : raw36166step0Labels = raw36166Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36166 raw36166Labels permutation346 hz
    mixedMoment B raw36166step0 raw36166step0Labels = mixedMoment B raw36166step1 raw36166step1Labels := by
      have ha : raw36166step1 = (fun i j => raw36166step0 (permutation58 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36166step1 raw36166step0; decide +kernel
      have hl : raw36166step1Labels = raw36166step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36166step0 raw36166step0Labels permutation58 permutation3
    _ = mixedMoment B node3998 node3998Labels := by rfl

def raw36167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw36167Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36167step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36167step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36167 raw36167Labels = mixedMoment B node2328 node2328Labels := by
  calc
    mixedMoment B raw36167 raw36167Labels = mixedMoment B raw36167step0 raw36167step0Labels := by
      have ha : raw36167step0 = (fun i j => raw36167 (permutation277 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36167step0 raw36167; decide +kernel
      have hl : raw36167step0Labels = raw36167Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36167 raw36167Labels permutation277 permutation3
    _ = mixedMoment B node2328 node2328Labels := by rfl

def raw36168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw36168Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw36168step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36168step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36168step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36168step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36168step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36168 raw36168Labels = mixedMoment B node3790 node3790Labels := by
  calc
    mixedMoment B raw36168 raw36168Labels = mixedMoment B raw36168step0 raw36168step0Labels := by
      have hz : ∀ j, raw36168 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw36168step0 = (fun i j => raw36168 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw36168step0 raw36168; decide +kernel
      have hl : raw36168step0Labels = raw36168Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36168 raw36168Labels permutation434 hz
    mixedMoment B raw36168step0 raw36168step0Labels = mixedMoment B raw36168step1 raw36168step1Labels := by
      have ha : raw36168step1 = (fun i j => raw36168step0 (permutation144 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36168step1 raw36168step0; decide +kernel
      have hl : raw36168step1Labels = raw36168step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36168step0 raw36168step0Labels permutation144 permutation3
    mixedMoment B raw36168step1 raw36168step1Labels = mixedMoment B raw36168step2 raw36168step2Labels := by
      have ha : raw36168step2 = -raw36168step1 := by apply Matrix.ext; change ∀ i j, raw36168step2 i j = -(raw36168step1 i j); unfold raw36168step2 raw36168step1; decide +kernel
      have hl : raw36168step2Labels = raw36168step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3790 node3790Labels := by rfl

def raw36169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw36169Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36169step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, 0, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw36169step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36169step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw36169step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36169 raw36169Labels = mixedMoment B node3776 node3776Labels := by
  calc
    mixedMoment B raw36169 raw36169Labels = mixedMoment B raw36169step0 raw36169step0Labels := by
      have ha : raw36169step0 = (fun i j => raw36169 (permutation639 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36169step0 raw36169; decide +kernel
      have hl : raw36169step0Labels = raw36169Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36169 raw36169Labels permutation639 permutation3
    mixedMoment B raw36169step0 raw36169step0Labels = mixedMoment B raw36169step1 raw36169step1Labels := by
      have ha : raw36169step1 = -raw36169step0 := by apply Matrix.ext; change ∀ i j, raw36169step1 i j = -(raw36169step0 i j); unfold raw36169step1 raw36169step0; decide +kernel
      have hl : raw36169step1Labels = raw36169step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3776 node3776Labels := by rfl

def raw36170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw36170Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36170step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw36170step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36170 raw36170Labels = mixedMoment B node3928 node3928Labels := by
  calc
    mixedMoment B raw36170 raw36170Labels = mixedMoment B raw36170step0 raw36170step0Labels := by
      have ha : raw36170step0 = (fun i j => raw36170 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36170step0 raw36170; decide +kernel
      have hl : raw36170step0Labels = raw36170Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36170 raw36170Labels permutation164 permutation3
    _ = mixedMoment B node3928 node3928Labels := by rfl

def raw36171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw36171Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw36171step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36171step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw36171step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36171 raw36171Labels = mixedMoment B node2329 node2329Labels := by
  calc
    mixedMoment B raw36171 raw36171Labels = mixedMoment B raw36171step0 raw36171step0Labels := by
      have hz : ∀ j, raw36171 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36171step0 = (fun i j => raw36171 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36171step0 raw36171; decide +kernel
      have hl : raw36171step0Labels = raw36171Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36171 raw36171Labels permutation346 hz
    mixedMoment B raw36171step0 raw36171step0Labels = mixedMoment B raw36171step1 raw36171step1Labels := by
      have ha : raw36171step1 = (fun i j => raw36171step0 (permutation58 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36171step1 raw36171step0; decide +kernel
      have hl : raw36171step1Labels = raw36171step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36171step0 raw36171step0Labels permutation58 permutation3
    _ = mixedMoment B node2329 node2329Labels := by rfl

def raw36172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw36172Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36172step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36172step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36172step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36172step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36172 raw36172Labels = mixedMoment B node3642 node3642Labels := by
  calc
    mixedMoment B raw36172 raw36172Labels = mixedMoment B raw36172step0 raw36172step0Labels := by
      have ha : raw36172step0 = (fun i j => raw36172 (permutation518 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36172step0 raw36172; decide +kernel
      have hl : raw36172step0Labels = raw36172Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36172 raw36172Labels permutation518 permutation3
    mixedMoment B raw36172step0 raw36172step0Labels = mixedMoment B raw36172step1 raw36172step1Labels := by
      have ha : raw36172step1 = -raw36172step0 := by apply Matrix.ext; change ∀ i j, raw36172step1 i j = -(raw36172step0 i j); unfold raw36172step1 raw36172step0; decide +kernel
      have hl : raw36172step1Labels = raw36172step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3642 node3642Labels := by rfl

def raw36173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -2, 0], ![0, 2, -2], ![2, -2, 0]]
def raw36173Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36173step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -2, 0], ![0, 2, -2], ![2, -2, 0]]
def raw36173step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36173step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw36173step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36173step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw36173step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36173 raw36173Labels = mixedMoment B node3661 node3661Labels := by
  calc
    mixedMoment B raw36173 raw36173Labels = mixedMoment B raw36173step0 raw36173step0Labels := by
      have hz : ∀ j, raw36173 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36173step0 = (fun i j => raw36173 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36173step0 raw36173; decide +kernel
      have hl : raw36173step0Labels = raw36173Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36173 raw36173Labels permutation346 hz
    mixedMoment B raw36173step0 raw36173step0Labels = mixedMoment B raw36173step1 raw36173step1Labels := by
      have ha : raw36173step1 = (fun i j => raw36173step0 (permutation102 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36173step1 raw36173step0; decide +kernel
      have hl : raw36173step1Labels = raw36173step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36173step0 raw36173step0Labels permutation102 permutation3
    mixedMoment B raw36173step1 raw36173step1Labels = mixedMoment B raw36173step2 raw36173step2Labels := by
      have ha : raw36173step2 = -raw36173step1 := by apply Matrix.ext; change ∀ i j, raw36173step2 i j = -(raw36173step1 i j); unfold raw36173step2 raw36173step1; decide +kernel
      have hl : raw36173step2Labels = raw36173step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3661 node3661Labels := by rfl

def raw36174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2], ![1, -1, 0]]
def raw36174Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36174step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -2, 0], ![1, 1, -2], ![1, -1, 0]]
def raw36174step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36174step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36174step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36174step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36174step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36174 raw36174Labels = mixedMoment B node3790 node3790Labels := by
  calc
    mixedMoment B raw36174 raw36174Labels = mixedMoment B raw36174step0 raw36174step0Labels := by
      have hz : ∀ j, raw36174 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36174step0 = (fun i j => raw36174 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36174step0 raw36174; decide +kernel
      have hl : raw36174step0Labels = raw36174Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36174 raw36174Labels permutation346 hz
    mixedMoment B raw36174step0 raw36174step0Labels = mixedMoment B raw36174step1 raw36174step1Labels := by
      have ha : raw36174step1 = (fun i j => raw36174step0 (permutation102 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36174step1 raw36174step0; decide +kernel
      have hl : raw36174step1Labels = raw36174step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36174step0 raw36174step0Labels permutation102 permutation3
    mixedMoment B raw36174step1 raw36174step1Labels = mixedMoment B raw36174step2 raw36174step2Labels := by
      have ha : raw36174step2 = -raw36174step1 := by apply Matrix.ext; change ∀ i j, raw36174step2 i j = -(raw36174step1 i j); unfold raw36174step2 raw36174step1; decide +kernel
      have hl : raw36174step2Labels = raw36174step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3790 node3790Labels := by rfl

def raw36175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw36175Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw36175step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36175step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36175step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36175 raw36175Labels = mixedMoment B node2341 node2341Labels := by
  calc
    mixedMoment B raw36175 raw36175Labels = mixedMoment B raw36175step0 raw36175step0Labels := by
      have hz : ∀ j, raw36175 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36175step0 = (fun i j => raw36175 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36175step0 raw36175; decide +kernel
      have hl : raw36175step0Labels = raw36175Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36175 raw36175Labels permutation346 hz
    mixedMoment B raw36175step0 raw36175step0Labels = mixedMoment B raw36175step1 raw36175step1Labels := by
      have ha : raw36175step1 = (fun i j => raw36175step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36175step1 raw36175step0; decide +kernel
      have hl : raw36175step1Labels = raw36175step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36175step0 raw36175step0Labels permutation56 permutation3
    _ = mixedMoment B node2341 node2341Labels := by rfl

def raw36176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw36176Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36176step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![1, 0, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36176step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36176step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36176step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36176 raw36176Labels = mixedMoment B node3709 node3709Labels := by
  calc
    mixedMoment B raw36176 raw36176Labels = mixedMoment B raw36176step0 raw36176step0Labels := by
      have ha : raw36176step0 = (fun i j => raw36176 (permutation687 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36176step0 raw36176; decide +kernel
      have hl : raw36176step0Labels = raw36176Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36176 raw36176Labels permutation687 permutation3
    mixedMoment B raw36176step0 raw36176step0Labels = mixedMoment B raw36176step1 raw36176step1Labels := by
      have ha : raw36176step1 = -raw36176step0 := by apply Matrix.ext; change ∀ i j, raw36176step1 i j = -(raw36176step0 i j); unfold raw36176step1 raw36176step0; decide +kernel
      have hl : raw36176step1Labels = raw36176step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3709 node3709Labels := by rfl

def raw36177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw36177Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw36177step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36177step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36177step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36177 raw36177Labels = mixedMoment B node3933 node3933Labels := by
  calc
    mixedMoment B raw36177 raw36177Labels = mixedMoment B raw36177step0 raw36177step0Labels := by
      have hz : ∀ j, raw36177 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36177step0 = (fun i j => raw36177 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36177step0 raw36177; decide +kernel
      have hl : raw36177step0Labels = raw36177Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36177 raw36177Labels permutation346 hz
    mixedMoment B raw36177step0 raw36177step0Labels = mixedMoment B raw36177step1 raw36177step1Labels := by
      have ha : raw36177step1 = (fun i j => raw36177step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36177step1 raw36177step0; decide +kernel
      have hl : raw36177step1Labels = raw36177step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36177step0 raw36177step0Labels permutation33 permutation3
    _ = mixedMoment B node3933 node3933Labels := by rfl

def raw36178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw36178Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw36178step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36178step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-3, 1, 2]]
def raw36178step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36178step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -1, -2]]
def raw36178step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36178 raw36178Labels = mixedMoment B node1880 node1880Labels := by
  calc
    mixedMoment B raw36178 raw36178Labels = mixedMoment B raw36178step0 raw36178step0Labels := by
      have hz : ∀ j, raw36178 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36178step0 = (fun i j => raw36178 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36178step0 raw36178; decide +kernel
      have hl : raw36178step0Labels = raw36178Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36178 raw36178Labels permutation346 hz
    mixedMoment B raw36178step0 raw36178step0Labels = mixedMoment B raw36178step1 raw36178step1Labels := by
      have ha : raw36178step1 = (fun i j => raw36178step0 (permutation144 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36178step1 raw36178step0; decide +kernel
      have hl : raw36178step1Labels = raw36178step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36178step0 raw36178step0Labels permutation144 permutation3
    mixedMoment B raw36178step1 raw36178step1Labels = mixedMoment B raw36178step2 raw36178step2Labels := by
      have ha : raw36178step2 = -raw36178step1 := by apply Matrix.ext; change ∀ i j, raw36178step2 i j = -(raw36178step1 i j); unfold raw36178step2 raw36178step1; decide +kernel
      have hl : raw36178step2Labels = raw36178step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1880 node1880Labels := by rfl

def raw36179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw36179Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36179step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36179step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36179step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36179step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36179 raw36179Labels = mixedMoment B node1879 node1879Labels := by
  calc
    mixedMoment B raw36179 raw36179Labels = mixedMoment B raw36179step0 raw36179step0Labels := by
      have ha : raw36179step0 = (fun i j => raw36179 (permutation663 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36179step0 raw36179; decide +kernel
      have hl : raw36179step0Labels = raw36179Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36179 raw36179Labels permutation663 permutation3
    mixedMoment B raw36179step0 raw36179step0Labels = mixedMoment B raw36179step1 raw36179step1Labels := by
      have ha : raw36179step1 = -raw36179step0 := by apply Matrix.ext; change ∀ i j, raw36179step1 i j = -(raw36179step0 i j); unfold raw36179step1 raw36179step0; decide +kernel
      have hl : raw36179step1Labels = raw36179step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1879 node1879Labels := by rfl

def raw36180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw36180Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw36180step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw36180step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw36180step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw36180step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw36180step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36180 raw36180Labels = mixedMoment B node1929 node1929Labels := by
  calc
    mixedMoment B raw36180 raw36180Labels = mixedMoment B raw36180step0 raw36180step0Labels := by
      have hz : ∀ j, raw36180 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36180step0 = (fun i j => raw36180 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36180step0 raw36180; decide +kernel
      have hl : raw36180step0Labels = raw36180Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36180 raw36180Labels permutation346 hz
    mixedMoment B raw36180step0 raw36180step0Labels = mixedMoment B raw36180step1 raw36180step1Labels := by
      have ha : raw36180step1 = (fun i j => raw36180step0 (permutation144 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36180step1 raw36180step0; decide +kernel
      have hl : raw36180step1Labels = raw36180step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36180step0 raw36180step0Labels permutation144 permutation3
    mixedMoment B raw36180step1 raw36180step1Labels = mixedMoment B raw36180step2 raw36180step2Labels := by
      have ha : raw36180step2 = -raw36180step1 := by apply Matrix.ext; change ∀ i j, raw36180step2 i j = -(raw36180step1 i j); unfold raw36180step2 raw36180step1; decide +kernel
      have hl : raw36180step2Labels = raw36180step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1929 node1929Labels := by rfl

def raw36181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36181Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36181step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36181step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw36181step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36181step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw36181step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36181 raw36181Labels = mixedMoment B node5170 node5170Labels := by
  calc
    mixedMoment B raw36181 raw36181Labels = mixedMoment B raw36181step0 raw36181step0Labels := by
      have hz : ∀ j, raw36181 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36181step0 = (fun i j => raw36181 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36181step0 raw36181; decide +kernel
      have hl : raw36181step0Labels = raw36181Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36181 raw36181Labels permutation346 hz
    mixedMoment B raw36181step0 raw36181step0Labels = mixedMoment B raw36181step1 raw36181step1Labels := by
      have ha : raw36181step1 = (fun i j => raw36181step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36181step1 raw36181step0; decide +kernel
      have hl : raw36181step1Labels = raw36181step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36181step0 raw36181step0Labels permutation56 permutation3
    mixedMoment B raw36181step1 raw36181step1Labels = mixedMoment B raw36181step2 raw36181step2Labels := by
      have ha : raw36181step2 = raw36181step1 := by apply Matrix.ext; unfold raw36181step2 raw36181step1; decide +kernel
      have hl : raw36181step1Labels = labelEmbedding6 ∘ raw36181step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36181step1 raw36181step1Labels raw36181step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5170 node5170Labels := by rfl

def raw36182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36182Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36182step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw36182step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36182step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36182step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36182 raw36182Labels = mixedMoment B node5401 node5401Labels := by
  calc
    mixedMoment B raw36182 raw36182Labels = mixedMoment B raw36182step0 raw36182step0Labels := by
      have ha : raw36182step0 = (fun i j => raw36182 (permutation663 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36182step0 raw36182; decide +kernel
      have hl : raw36182step0Labels = raw36182Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36182 raw36182Labels permutation663 permutation2
    mixedMoment B raw36182step0 raw36182step0Labels = mixedMoment B raw36182step1 raw36182step1Labels := by
      have ha : raw36182step1 = -raw36182step0 := by apply Matrix.ext; change ∀ i j, raw36182step1 i j = -(raw36182step0 i j); unfold raw36182step1 raw36182step0; decide +kernel
      have hl : raw36182step1Labels = raw36182step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5401 node5401Labels := by rfl

def raw36183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36183Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36183step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36183step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw36183step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36183step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw36183step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36183 raw36183Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw36183 raw36183Labels = mixedMoment B raw36183step0 raw36183step0Labels := by
      have hz : ∀ j, raw36183 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36183step0 = (fun i j => raw36183 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36183step0 raw36183; decide +kernel
      have hl : raw36183step0Labels = raw36183Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36183 raw36183Labels permutation346 hz
    mixedMoment B raw36183step0 raw36183step0Labels = mixedMoment B raw36183step1 raw36183step1Labels := by
      have ha : raw36183step1 = (fun i j => raw36183step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36183step1 raw36183step0; decide +kernel
      have hl : raw36183step1Labels = raw36183step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36183step0 raw36183step0Labels permutation144 permutation7
    mixedMoment B raw36183step1 raw36183step1Labels = mixedMoment B raw36183step2 raw36183step2Labels := by
      have ha : raw36183step2 = raw36183step1 := by apply Matrix.ext; unfold raw36183step2 raw36183step1; decide +kernel
      have hl : raw36183step1Labels = labelEmbedding10 ∘ raw36183step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36183step1 raw36183step1Labels raw36183step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw36184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw36184Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw36184step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36184step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw36184step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36184step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36184step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36184 raw36184Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw36184 raw36184Labels = mixedMoment B raw36184step0 raw36184step0Labels := by
      have hz : ∀ j, raw36184 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36184step0 = (fun i j => raw36184 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36184step0 raw36184; decide +kernel
      have hl : raw36184step0Labels = raw36184Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36184 raw36184Labels permutation346 hz
    mixedMoment B raw36184step0 raw36184step0Labels = mixedMoment B raw36184step1 raw36184step1Labels := by
      have ha : raw36184step1 = (fun i j => raw36184step0 (permutation144 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36184step1 raw36184step0; decide +kernel
      have hl : raw36184step1Labels = raw36184step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36184step0 raw36184step0Labels permutation144 permutation2
    mixedMoment B raw36184step1 raw36184step1Labels = mixedMoment B raw36184step2 raw36184step2Labels := by
      have ha : raw36184step2 = -raw36184step1 := by apply Matrix.ext; change ∀ i j, raw36184step2 i j = -(raw36184step1 i j); unfold raw36184step2 raw36184step1; decide +kernel
      have hl : raw36184step2Labels = raw36184step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5410 node5410Labels := by rfl

def raw36185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw36185Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw36185step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36185step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw36185step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36185 raw36185Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw36185 raw36185Labels = mixedMoment B raw36185step0 raw36185step0Labels := by
      have hz : ∀ j, raw36185 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36185step0 = (fun i j => raw36185 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36185step0 raw36185; decide +kernel
      have hl : raw36185step0Labels = raw36185Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36185 raw36185Labels permutation346 hz
    mixedMoment B raw36185step0 raw36185step0Labels = mixedMoment B raw36185step1 raw36185step1Labels := by
      have ha : raw36185step1 = (fun i j => raw36185step0 (permutation58 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36185step1 raw36185step0; decide +kernel
      have hl : raw36185step1Labels = raw36185step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36185step0 raw36185step0Labels permutation58 permutation2
    _ = mixedMoment B node5484 node5484Labels := by rfl

def raw36186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36186Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36186step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36186step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw36186step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36186step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw36186step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36186 raw36186Labels = mixedMoment B node5170 node5170Labels := by
  calc
    mixedMoment B raw36186 raw36186Labels = mixedMoment B raw36186step0 raw36186step0Labels := by
      have hz : ∀ j, raw36186 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36186step0 = (fun i j => raw36186 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36186step0 raw36186; decide +kernel
      have hl : raw36186step0Labels = raw36186Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36186 raw36186Labels permutation346 hz
    mixedMoment B raw36186step0 raw36186step0Labels = mixedMoment B raw36186step1 raw36186step1Labels := by
      have ha : raw36186step1 = (fun i j => raw36186step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36186step1 raw36186step0; decide +kernel
      have hl : raw36186step1Labels = raw36186step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36186step0 raw36186step0Labels permutation32 permutation3
    mixedMoment B raw36186step1 raw36186step1Labels = mixedMoment B raw36186step2 raw36186step2Labels := by
      have ha : raw36186step2 = raw36186step1 := by apply Matrix.ext; unfold raw36186step2 raw36186step1; decide +kernel
      have hl : raw36186step1Labels = labelEmbedding6 ∘ raw36186step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36186step1 raw36186step1Labels raw36186step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5170 node5170Labels := by rfl

def raw36187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36187Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36187step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36187step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36187step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36187step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36187 raw36187Labels = mixedMoment B node4942 node4942Labels := by
  calc
    mixedMoment B raw36187 raw36187Labels = mixedMoment B raw36187step0 raw36187step0Labels := by
      have ha : raw36187step0 = (fun i j => raw36187 (permutation271 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36187step0 raw36187; decide +kernel
      have hl : raw36187step0Labels = raw36187Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36187 raw36187Labels permutation271 permutation3
    mixedMoment B raw36187step0 raw36187step0Labels = mixedMoment B raw36187step1 raw36187step1Labels := by
      have ha : raw36187step1 = raw36187step0 := by apply Matrix.ext; unfold raw36187step1 raw36187step0; decide +kernel
      have hl : raw36187step0Labels = labelEmbedding6 ∘ raw36187step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36187step0 raw36187step0Labels raw36187step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4942 node4942Labels := by rfl

def raw36188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36188Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36188step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36188step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36188step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw36188step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36188 raw36188Labels = mixedMoment B node5419 node5419Labels := by
  calc
    mixedMoment B raw36188 raw36188Labels = mixedMoment B raw36188step0 raw36188step0Labels := by
      have ha : raw36188step0 = (fun i j => raw36188 (permutation645 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36188step0 raw36188; decide +kernel
      have hl : raw36188step0Labels = raw36188Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36188 raw36188Labels permutation645 permutation2
    mixedMoment B raw36188step0 raw36188step0Labels = mixedMoment B raw36188step1 raw36188step1Labels := by
      have ha : raw36188step1 = -raw36188step0 := by apply Matrix.ext; change ∀ i j, raw36188step1 i j = -(raw36188step0 i j); unfold raw36188step1 raw36188step0; decide +kernel
      have hl : raw36188step1Labels = raw36188step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5419 node5419Labels := by rfl

def raw36189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw36189Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36189step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36189step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36189step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36189step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36189 raw36189Labels = mixedMoment B node5393 node5393Labels := by
  calc
    mixedMoment B raw36189 raw36189Labels = mixedMoment B raw36189step0 raw36189step0Labels := by
      have ha : raw36189step0 = (fun i j => raw36189 (permutation657 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36189step0 raw36189; decide +kernel
      have hl : raw36189step0Labels = raw36189Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36189 raw36189Labels permutation657 permutation2
    mixedMoment B raw36189step0 raw36189step0Labels = mixedMoment B raw36189step1 raw36189step1Labels := by
      have ha : raw36189step1 = -raw36189step0 := by apply Matrix.ext; change ∀ i j, raw36189step1 i j = -(raw36189step0 i j); unfold raw36189step1 raw36189step0; decide +kernel
      have hl : raw36189step1Labels = raw36189step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5393 node5393Labels := by rfl

def raw36190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw36190Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36190step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36190step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36190 raw36190Labels = mixedMoment B node5461 node5461Labels := by
  calc
    mixedMoment B raw36190 raw36190Labels = mixedMoment B raw36190step0 raw36190step0Labels := by
      have ha : raw36190step0 = (fun i j => raw36190 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36190step0 raw36190; decide +kernel
      have hl : raw36190step0Labels = raw36190Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36190 raw36190Labels permutation164 permutation2
    _ = mixedMoment B node5461 node5461Labels := by rfl

def raw36191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36191Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36191step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36191step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36191step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36191step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36191step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36191 raw36191Labels = mixedMoment B node4951 node4951Labels := by
  calc
    mixedMoment B raw36191 raw36191Labels = mixedMoment B raw36191step0 raw36191step0Labels := by
      have hz : ∀ j, raw36191 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36191step0 = (fun i j => raw36191 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36191step0 raw36191; decide +kernel
      have hl : raw36191step0Labels = raw36191Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36191 raw36191Labels permutation346 hz
    mixedMoment B raw36191step0 raw36191step0Labels = mixedMoment B raw36191step1 raw36191step1Labels := by
      have ha : raw36191step1 = (fun i j => raw36191step0 (permutation59 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36191step1 raw36191step0; decide +kernel
      have hl : raw36191step1Labels = raw36191step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36191step0 raw36191step0Labels permutation59 permutation3
    mixedMoment B raw36191step1 raw36191step1Labels = mixedMoment B raw36191step2 raw36191step2Labels := by
      have ha : raw36191step2 = raw36191step1 := by apply Matrix.ext; unfold raw36191step2 raw36191step1; decide +kernel
      have hl : raw36191step1Labels = labelEmbedding6 ∘ raw36191step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36191step1 raw36191step1Labels raw36191step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4951 node4951Labels := by rfl

def raw36192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36192Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36192step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw36192step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36192step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw36192step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36192 raw36192Labels = mixedMoment B node5340 node5340Labels := by
  calc
    mixedMoment B raw36192 raw36192Labels = mixedMoment B raw36192step0 raw36192step0Labels := by
      have ha : raw36192step0 = (fun i j => raw36192 (permutation663 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36192step0 raw36192; decide +kernel
      have hl : raw36192step0Labels = raw36192Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36192 raw36192Labels permutation663 permutation2
    mixedMoment B raw36192step0 raw36192step0Labels = mixedMoment B raw36192step1 raw36192step1Labels := by
      have ha : raw36192step1 = -raw36192step0 := by apply Matrix.ext; change ∀ i j, raw36192step1 i j = -(raw36192step0 i j); unfold raw36192step1 raw36192step0; decide +kernel
      have hl : raw36192step1Labels = raw36192step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5340 node5340Labels := by rfl

def raw36193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw36193Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw36193step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36193step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36193step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36193step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36193step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36193 raw36193Labels = mixedMoment B node5356 node5356Labels := by
  calc
    mixedMoment B raw36193 raw36193Labels = mixedMoment B raw36193step0 raw36193step0Labels := by
      have hz : ∀ j, raw36193 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36193step0 = (fun i j => raw36193 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36193step0 raw36193; decide +kernel
      have hl : raw36193step0Labels = raw36193Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36193 raw36193Labels permutation346 hz
    mixedMoment B raw36193step0 raw36193step0Labels = mixedMoment B raw36193step1 raw36193step1Labels := by
      have ha : raw36193step1 = (fun i j => raw36193step0 (permutation144 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36193step1 raw36193step0; decide +kernel
      have hl : raw36193step1Labels = raw36193step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36193step0 raw36193step0Labels permutation144 permutation2
    mixedMoment B raw36193step1 raw36193step1Labels = mixedMoment B raw36193step2 raw36193step2Labels := by
      have ha : raw36193step2 = -raw36193step1 := by apply Matrix.ext; change ∀ i j, raw36193step2 i j = -(raw36193step1 i j); unfold raw36193step2 raw36193step1; decide +kernel
      have hl : raw36193step2Labels = raw36193step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5356 node5356Labels := by rfl

def raw36194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw36194Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36194step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw36194step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36194step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw36194step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36194 raw36194Labels = mixedMoment B node5463 node5463Labels := by
  calc
    mixedMoment B raw36194 raw36194Labels = mixedMoment B raw36194step0 raw36194step0Labels := by
      have hz : ∀ j, raw36194 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36194step0 = (fun i j => raw36194 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36194step0 raw36194; decide +kernel
      have hl : raw36194step0Labels = raw36194Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36194 raw36194Labels permutation346 hz
    mixedMoment B raw36194step0 raw36194step0Labels = mixedMoment B raw36194step1 raw36194step1Labels := by
      have ha : raw36194step1 = (fun i j => raw36194step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36194step1 raw36194step0; decide +kernel
      have hl : raw36194step1Labels = raw36194step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36194step0 raw36194step0Labels permutation35 permutation2
    _ = mixedMoment B node5463 node5463Labels := by rfl

def raw36195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw36195Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw36195step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36195step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw36195step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36195step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw36195step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36195 raw36195Labels = mixedMoment B node4945 node4945Labels := by
  calc
    mixedMoment B raw36195 raw36195Labels = mixedMoment B raw36195step0 raw36195step0Labels := by
      have hz : ∀ j, raw36195 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36195step0 = (fun i j => raw36195 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36195step0 raw36195; decide +kernel
      have hl : raw36195step0Labels = raw36195Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36195 raw36195Labels permutation346 hz
    mixedMoment B raw36195step0 raw36195step0Labels = mixedMoment B raw36195step1 raw36195step1Labels := by
      have ha : raw36195step1 = (fun i j => raw36195step0 (permutation57 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36195step1 raw36195step0; decide +kernel
      have hl : raw36195step1Labels = raw36195step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36195step0 raw36195step0Labels permutation57 permutation3
    mixedMoment B raw36195step1 raw36195step1Labels = mixedMoment B raw36195step2 raw36195step2Labels := by
      have ha : raw36195step2 = raw36195step1 := by apply Matrix.ext; unfold raw36195step2 raw36195step1; decide +kernel
      have hl : raw36195step1Labels = labelEmbedding6 ∘ raw36195step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36195step1 raw36195step1Labels raw36195step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4945 node4945Labels := by rfl

def raw36196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw36196Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36196step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw36196step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36196step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw36196step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36196 raw36196Labels = mixedMoment B node5217 node5217Labels := by
  calc
    mixedMoment B raw36196 raw36196Labels = mixedMoment B raw36196step0 raw36196step0Labels := by
      have ha : raw36196step0 = (fun i j => raw36196 (permutation588 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36196step0 raw36196; decide +kernel
      have hl : raw36196step0Labels = raw36196Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36196 raw36196Labels permutation588 permutation5
    mixedMoment B raw36196step0 raw36196step0Labels = mixedMoment B raw36196step1 raw36196step1Labels := by
      have ha : raw36196step1 = raw36196step0 := by apply Matrix.ext; unfold raw36196step1 raw36196step0; decide +kernel
      have hl : raw36196step0Labels = labelEmbedding8 ∘ raw36196step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36196step0 raw36196step0Labels raw36196step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5217 node5217Labels := by rfl

def raw36197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw36197Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36197step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw36197step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36197step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36197step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36197step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36197step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36197 raw36197Labels = mixedMoment B node5236 node5236Labels := by
  calc
    mixedMoment B raw36197 raw36197Labels = mixedMoment B raw36197step0 raw36197step0Labels := by
      have hz : ∀ j, raw36197 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36197step0 = (fun i j => raw36197 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36197step0 raw36197; decide +kernel
      have hl : raw36197step0Labels = raw36197Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36197 raw36197Labels permutation346 hz
    mixedMoment B raw36197step0 raw36197step0Labels = mixedMoment B raw36197step1 raw36197step1Labels := by
      have ha : raw36197step1 = (fun i j => raw36197step0 (permutation126 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36197step1 raw36197step0; decide +kernel
      have hl : raw36197step1Labels = raw36197step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36197step0 raw36197step0Labels permutation126 permutation5
    mixedMoment B raw36197step1 raw36197step1Labels = mixedMoment B raw36197step2 raw36197step2Labels := by
      have ha : raw36197step2 = raw36197step1 := by apply Matrix.ext; unfold raw36197step2 raw36197step1; decide +kernel
      have hl : raw36197step1Labels = labelEmbedding8 ∘ raw36197step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36197step1 raw36197step1Labels raw36197step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5236 node5236Labels := by rfl

def raw36198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw36198Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw36198step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36198step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36198step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw36198step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36198step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36198 raw36198Labels = mixedMoment B node5269 node5269Labels := by
  calc
    mixedMoment B raw36198 raw36198Labels = mixedMoment B raw36198step0 raw36198step0Labels := by
      have hz : ∀ j, raw36198 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36198step0 = (fun i j => raw36198 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36198step0 raw36198; decide +kernel
      have hl : raw36198step0Labels = raw36198Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36198 raw36198Labels permutation346 hz
    mixedMoment B raw36198step0 raw36198step0Labels = mixedMoment B raw36198step1 raw36198step1Labels := by
      have ha : raw36198step1 = (fun i j => raw36198step0 (permutation120 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36198step1 raw36198step0; decide +kernel
      have hl : raw36198step1Labels = raw36198step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36198step0 raw36198step0Labels permutation120 permutation5
    mixedMoment B raw36198step1 raw36198step1Labels = mixedMoment B raw36198step2 raw36198step2Labels := by
      have ha : raw36198step2 = raw36198step1 := by apply Matrix.ext; unfold raw36198step2 raw36198step1; decide +kernel
      have hl : raw36198step1Labels = labelEmbedding8 ∘ raw36198step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36198step1 raw36198step1Labels raw36198step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5269 node5269Labels := by rfl

def raw36199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw36199Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36199step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw36199step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36199step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw36199step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36199step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw36199step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36199 raw36199Labels = mixedMoment B node4944 node4944Labels := by
  calc
    mixedMoment B raw36199 raw36199Labels = mixedMoment B raw36199step0 raw36199step0Labels := by
      have hz : ∀ j, raw36199 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36199step0 = (fun i j => raw36199 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36199step0 raw36199; decide +kernel
      have hl : raw36199step0Labels = raw36199Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36199 raw36199Labels permutation346 hz
    mixedMoment B raw36199step0 raw36199step0Labels = mixedMoment B raw36199step1 raw36199step1Labels := by
      have ha : raw36199step1 = (fun i j => raw36199step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36199step1 raw36199step0; decide +kernel
      have hl : raw36199step1Labels = raw36199step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36199step0 raw36199step0Labels permutation56 permutation3
    mixedMoment B raw36199step1 raw36199step1Labels = mixedMoment B raw36199step2 raw36199step2Labels := by
      have ha : raw36199step2 = raw36199step1 := by apply Matrix.ext; unfold raw36199step2 raw36199step1; decide +kernel
      have hl : raw36199step1Labels = labelEmbedding6 ∘ raw36199step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36199step1 raw36199step1Labels raw36199step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4944 node4944Labels := by rfl

def raw36200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw36200Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36200step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw36200step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36200step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw36200step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36200 raw36200Labels = mixedMoment B node5043 node5043Labels := by
  calc
    mixedMoment B raw36200 raw36200Labels = mixedMoment B raw36200step0 raw36200step0Labels := by
      have ha : raw36200step0 = (fun i j => raw36200 (permutation663 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36200step0 raw36200; decide +kernel
      have hl : raw36200step0Labels = raw36200Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36200 raw36200Labels permutation663 permutation2
    mixedMoment B raw36200step0 raw36200step0Labels = mixedMoment B raw36200step1 raw36200step1Labels := by
      have ha : raw36200step1 = -raw36200step0 := by apply Matrix.ext; change ∀ i j, raw36200step1 i j = -(raw36200step0 i j); unfold raw36200step1 raw36200step0; decide +kernel
      have hl : raw36200step1Labels = raw36200step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5043 node5043Labels := by rfl

def raw36201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw36201Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw36201step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36201step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36201step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36201step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw36201step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36201 raw36201Labels = mixedMoment B node5189 node5189Labels := by
  calc
    mixedMoment B raw36201 raw36201Labels = mixedMoment B raw36201step0 raw36201step0Labels := by
      have hz : ∀ j, raw36201 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36201step0 = (fun i j => raw36201 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36201step0 raw36201; decide +kernel
      have hl : raw36201step0Labels = raw36201Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36201 raw36201Labels permutation346 hz
    mixedMoment B raw36201step0 raw36201step0Labels = mixedMoment B raw36201step1 raw36201step1Labels := by
      have ha : raw36201step1 = (fun i j => raw36201step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36201step1 raw36201step0; decide +kernel
      have hl : raw36201step1Labels = raw36201step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36201step0 raw36201step0Labels permutation150 permutation2
    mixedMoment B raw36201step1 raw36201step1Labels = mixedMoment B raw36201step2 raw36201step2Labels := by
      have ha : raw36201step2 = -raw36201step1 := by apply Matrix.ext; change ∀ i j, raw36201step2 i j = -(raw36201step1 i j); unfold raw36201step2 raw36201step1; decide +kernel
      have hl : raw36201step2Labels = raw36201step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5189 node5189Labels := by rfl

def raw36202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw36202Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36202step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw36202step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36202step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36202step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36202step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36202step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36202 raw36202Labels = mixedMoment B node5081 node5081Labels := by
  calc
    mixedMoment B raw36202 raw36202Labels = mixedMoment B raw36202step0 raw36202step0Labels := by
      have hz : ∀ j, raw36202 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36202step0 = (fun i j => raw36202 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36202step0 raw36202; decide +kernel
      have hl : raw36202step0Labels = raw36202Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36202 raw36202Labels permutation346 hz
    mixedMoment B raw36202step0 raw36202step0Labels = mixedMoment B raw36202step1 raw36202step1Labels := by
      have ha : raw36202step1 = (fun i j => raw36202step0 (permutation144 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36202step1 raw36202step0; decide +kernel
      have hl : raw36202step1Labels = raw36202step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36202step0 raw36202step0Labels permutation144 permutation2
    mixedMoment B raw36202step1 raw36202step1Labels = mixedMoment B raw36202step2 raw36202step2Labels := by
      have ha : raw36202step2 = -raw36202step1 := by apply Matrix.ext; change ∀ i j, raw36202step2 i j = -(raw36202step1 i j); unfold raw36202step2 raw36202step1; decide +kernel
      have hl : raw36202step2Labels = raw36202step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5081 node5081Labels := by rfl

def raw36203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36203Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36203step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36203step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-2, 1, 1]]
def raw36203step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36203step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw36203step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36203step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw36203step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36203 raw36203Labels = mixedMoment B node3606 node3606Labels := by
  calc
    mixedMoment B raw36203 raw36203Labels = mixedMoment B raw36203step0 raw36203step0Labels := by
      have hz : ∀ j, raw36203 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36203step0 = (fun i j => raw36203 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36203step0 raw36203; decide +kernel
      have hl : raw36203step0Labels = raw36203Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36203 raw36203Labels permutation346 hz
    mixedMoment B raw36203step0 raw36203step0Labels = mixedMoment B raw36203step1 raw36203step1Labels := by
      have ha : raw36203step1 = (fun i j => raw36203step0 (permutation57 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36203step1 raw36203step0; decide +kernel
      have hl : raw36203step1Labels = raw36203step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36203step0 raw36203step0Labels permutation57 permutation5
    mixedMoment B raw36203step1 raw36203step1Labels = mixedMoment B raw36203step2 raw36203step2Labels := by
      have ha : raw36203step2 = -raw36203step1 := by apply Matrix.ext; change ∀ i j, raw36203step2 i j = -(raw36203step1 i j); unfold raw36203step2 raw36203step1; decide +kernel
      have hl : raw36203step2Labels = raw36203step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36203step2 raw36203step2Labels = mixedMoment B raw36203step3 raw36203step3Labels := by
      have ha : raw36203step3 = raw36203step2 := by apply Matrix.ext; unfold raw36203step3 raw36203step2; decide +kernel
      have hl : raw36203step2Labels = labelEmbedding1 ∘ raw36203step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36203step2 raw36203step2Labels raw36203step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3606 node3606Labels := by rfl

def raw36204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36204Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36204step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw36204step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36204step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw36204step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36204 raw36204Labels = mixedMoment B node3804 node3804Labels := by
  calc
    mixedMoment B raw36204 raw36204Labels = mixedMoment B raw36204step0 raw36204step0Labels := by
      have ha : raw36204step0 = (fun i j => raw36204 (permutation657 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36204step0 raw36204; decide +kernel
      have hl : raw36204step0Labels = raw36204Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36204 raw36204Labels permutation657 permutation7
    mixedMoment B raw36204step0 raw36204step0Labels = mixedMoment B raw36204step1 raw36204step1Labels := by
      have ha : raw36204step1 = raw36204step0 := by apply Matrix.ext; unfold raw36204step1 raw36204step0; decide +kernel
      have hl : raw36204step0Labels = labelEmbedding1 ∘ raw36204step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36204step0 raw36204step0Labels raw36204step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3804 node3804Labels := by rfl

def raw36205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36205Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36205step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36205step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw36205step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36205step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw36205step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36205 raw36205Labels = mixedMoment B node3857 node3857Labels := by
  calc
    mixedMoment B raw36205 raw36205Labels = mixedMoment B raw36205step0 raw36205step0Labels := by
      have hz : ∀ j, raw36205 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36205step0 = (fun i j => raw36205 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36205step0 raw36205; decide +kernel
      have hl : raw36205step0Labels = raw36205Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36205 raw36205Labels permutation346 hz
    mixedMoment B raw36205step0 raw36205step0Labels = mixedMoment B raw36205step1 raw36205step1Labels := by
      have ha : raw36205step1 = (fun i j => raw36205step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36205step1 raw36205step0; decide +kernel
      have hl : raw36205step1Labels = raw36205step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36205step0 raw36205step0Labels permutation144 permutation7
    mixedMoment B raw36205step1 raw36205step1Labels = mixedMoment B raw36205step2 raw36205step2Labels := by
      have ha : raw36205step2 = raw36205step1 := by apply Matrix.ext; unfold raw36205step2 raw36205step1; decide +kernel
      have hl : raw36205step1Labels = labelEmbedding1 ∘ raw36205step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36205step1 raw36205step1Labels raw36205step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3857 node3857Labels := by rfl

def raw36206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw36206Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36206step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw36206step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36206step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36206step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36206step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36206step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36206 raw36206Labels = mixedMoment B node3816 node3816Labels := by
  calc
    mixedMoment B raw36206 raw36206Labels = mixedMoment B raw36206step0 raw36206step0Labels := by
      have hz : ∀ j, raw36206 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36206step0 = (fun i j => raw36206 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36206step0 raw36206; decide +kernel
      have hl : raw36206step0Labels = raw36206Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36206 raw36206Labels permutation346 hz
    mixedMoment B raw36206step0 raw36206step0Labels = mixedMoment B raw36206step1 raw36206step1Labels := by
      have ha : raw36206step1 = (fun i j => raw36206step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36206step1 raw36206step0; decide +kernel
      have hl : raw36206step1Labels = raw36206step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36206step0 raw36206step0Labels permutation144 permutation7
    mixedMoment B raw36206step1 raw36206step1Labels = mixedMoment B raw36206step2 raw36206step2Labels := by
      have ha : raw36206step2 = raw36206step1 := by apply Matrix.ext; unfold raw36206step2 raw36206step1; decide +kernel
      have hl : raw36206step1Labels = labelEmbedding1 ∘ raw36206step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36206step1 raw36206step1Labels raw36206step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3816 node3816Labels := by rfl

def raw36207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw36207Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36207step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw36207step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36207step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw36207step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36207step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw36207step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36207 raw36207Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw36207 raw36207Labels = mixedMoment B raw36207step0 raw36207step0Labels := by
      have hz : ∀ j, raw36207 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36207step0 = (fun i j => raw36207 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36207step0 raw36207; decide +kernel
      have hl : raw36207step0Labels = raw36207Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36207 raw36207Labels permutation346 hz
    mixedMoment B raw36207step0 raw36207step0Labels = mixedMoment B raw36207step1 raw36207step1Labels := by
      have ha : raw36207step1 = (fun i j => raw36207step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36207step1 raw36207step0; decide +kernel
      have hl : raw36207step1Labels = raw36207step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36207step0 raw36207step0Labels permutation144 permutation7
    mixedMoment B raw36207step1 raw36207step1Labels = mixedMoment B raw36207step2 raw36207step2Labels := by
      have ha : raw36207step2 = raw36207step1 := by apply Matrix.ext; unfold raw36207step2 raw36207step1; decide +kernel
      have hl : raw36207step1Labels = labelEmbedding1 ∘ raw36207step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36207step1 raw36207step1Labels raw36207step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3983 node3983Labels := by rfl

def raw36208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36208Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36208step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36208step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-2, 1, 1]]
def raw36208step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36208step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw36208step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36208step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw36208step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36208 raw36208Labels = mixedMoment B node3606 node3606Labels := by
  calc
    mixedMoment B raw36208 raw36208Labels = mixedMoment B raw36208step0 raw36208step0Labels := by
      have hz : ∀ j, raw36208 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36208step0 = (fun i j => raw36208 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36208step0 raw36208; decide +kernel
      have hl : raw36208step0Labels = raw36208Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36208 raw36208Labels permutation346 hz
    mixedMoment B raw36208step0 raw36208step0Labels = mixedMoment B raw36208step1 raw36208step1Labels := by
      have ha : raw36208step1 = (fun i j => raw36208step0 (permutation33 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36208step1 raw36208step0; decide +kernel
      have hl : raw36208step1Labels = raw36208step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36208step0 raw36208step0Labels permutation33 permutation5
    mixedMoment B raw36208step1 raw36208step1Labels = mixedMoment B raw36208step2 raw36208step2Labels := by
      have ha : raw36208step2 = -raw36208step1 := by apply Matrix.ext; change ∀ i j, raw36208step2 i j = -(raw36208step1 i j); unfold raw36208step2 raw36208step1; decide +kernel
      have hl : raw36208step2Labels = raw36208step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36208step2 raw36208step2Labels = mixedMoment B raw36208step3 raw36208step3Labels := by
      have ha : raw36208step3 = raw36208step2 := by apply Matrix.ext; unfold raw36208step3 raw36208step2; decide +kernel
      have hl : raw36208step2Labels = labelEmbedding1 ∘ raw36208step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36208step2 raw36208step2Labels raw36208step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3606 node3606Labels := by rfl

def raw36209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36209Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36209step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw36209step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36209step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw36209step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36209step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw36209step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36209 raw36209Labels = mixedMoment B node3407 node3407Labels := by
  calc
    mixedMoment B raw36209 raw36209Labels = mixedMoment B raw36209step0 raw36209step0Labels := by
      have ha : raw36209step0 = (fun i j => raw36209 (permutation275 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36209step0 raw36209; decide +kernel
      have hl : raw36209step0Labels = raw36209Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36209 raw36209Labels permutation275 permutation5
    mixedMoment B raw36209step0 raw36209step0Labels = mixedMoment B raw36209step1 raw36209step1Labels := by
      have ha : raw36209step1 = -raw36209step0 := by apply Matrix.ext; change ∀ i j, raw36209step1 i j = -(raw36209step0 i j); unfold raw36209step1 raw36209step0; decide +kernel
      have hl : raw36209step1Labels = raw36209step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36209step1 raw36209step1Labels = mixedMoment B raw36209step2 raw36209step2Labels := by
      have ha : raw36209step2 = raw36209step1 := by apply Matrix.ext; unfold raw36209step2 raw36209step1; decide +kernel
      have hl : raw36209step1Labels = labelEmbedding1 ∘ raw36209step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36209step1 raw36209step1Labels raw36209step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3407 node3407Labels := by rfl

def raw36210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36210Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36210step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36210step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36210step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36210step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36210 raw36210Labels = mixedMoment B node3842 node3842Labels := by
  calc
    mixedMoment B raw36210 raw36210Labels = mixedMoment B raw36210step0 raw36210step0Labels := by
      have ha : raw36210step0 = (fun i j => raw36210 (permutation657 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36210step0 raw36210; decide +kernel
      have hl : raw36210step0Labels = raw36210Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36210 raw36210Labels permutation657 permutation7
    mixedMoment B raw36210step0 raw36210step0Labels = mixedMoment B raw36210step1 raw36210step1Labels := by
      have ha : raw36210step1 = raw36210step0 := by apply Matrix.ext; unfold raw36210step1 raw36210step0; decide +kernel
      have hl : raw36210step0Labels = labelEmbedding1 ∘ raw36210step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36210step0 raw36210step0Labels raw36210step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3842 node3842Labels := by rfl

def raw36211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw36211Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36211step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36211step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36211step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36211step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36211 raw36211Labels = mixedMoment B node3797 node3797Labels := by
  calc
    mixedMoment B raw36211 raw36211Labels = mixedMoment B raw36211step0 raw36211step0Labels := by
      have ha : raw36211step0 = (fun i j => raw36211 (permutation657 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36211step0 raw36211; decide +kernel
      have hl : raw36211step0Labels = raw36211Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36211 raw36211Labels permutation657 permutation7
    mixedMoment B raw36211step0 raw36211step0Labels = mixedMoment B raw36211step1 raw36211step1Labels := by
      have ha : raw36211step1 = raw36211step0 := by apply Matrix.ext; unfold raw36211step1 raw36211step0; decide +kernel
      have hl : raw36211step0Labels = labelEmbedding1 ∘ raw36211step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36211step0 raw36211step0Labels raw36211step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3797 node3797Labels := by rfl

def raw36212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw36212Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36212step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36212step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36212step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36212step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36212 raw36212Labels = mixedMoment B node3973 node3973Labels := by
  calc
    mixedMoment B raw36212 raw36212Labels = mixedMoment B raw36212step0 raw36212step0Labels := by
      have ha : raw36212step0 = (fun i j => raw36212 (permutation545 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36212step0 raw36212; decide +kernel
      have hl : raw36212step0Labels = raw36212Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36212 raw36212Labels permutation545 permutation5
    mixedMoment B raw36212step0 raw36212step0Labels = mixedMoment B raw36212step1 raw36212step1Labels := by
      have ha : raw36212step1 = raw36212step0 := by apply Matrix.ext; unfold raw36212step1 raw36212step0; decide +kernel
      have hl : raw36212step0Labels = labelEmbedding1 ∘ raw36212step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36212step0 raw36212step0Labels raw36212step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3973 node3973Labels := by rfl

def raw36213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36213Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36213step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36213step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw36213step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36213step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw36213step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36213step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw36213step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36213 raw36213Labels = mixedMoment B node3418 node3418Labels := by
  calc
    mixedMoment B raw36213 raw36213Labels = mixedMoment B raw36213step0 raw36213step0Labels := by
      have hz : ∀ j, raw36213 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36213step0 = (fun i j => raw36213 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36213step0 raw36213; decide +kernel
      have hl : raw36213step0Labels = raw36213Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36213 raw36213Labels permutation346 hz
    mixedMoment B raw36213step0 raw36213step0Labels = mixedMoment B raw36213step1 raw36213step1Labels := by
      have ha : raw36213step1 = (fun i j => raw36213step0 (permutation60 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36213step1 raw36213step0; decide +kernel
      have hl : raw36213step1Labels = raw36213step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36213step0 raw36213step0Labels permutation60 permutation5
    mixedMoment B raw36213step1 raw36213step1Labels = mixedMoment B raw36213step2 raw36213step2Labels := by
      have ha : raw36213step2 = -raw36213step1 := by apply Matrix.ext; change ∀ i j, raw36213step2 i j = -(raw36213step1 i j); unfold raw36213step2 raw36213step1; decide +kernel
      have hl : raw36213step2Labels = raw36213step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36213step2 raw36213step2Labels = mixedMoment B raw36213step3 raw36213step3Labels := by
      have ha : raw36213step3 = raw36213step2 := by apply Matrix.ext; unfold raw36213step3 raw36213step2; decide +kernel
      have hl : raw36213step2Labels = labelEmbedding1 ∘ raw36213step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36213step2 raw36213step2Labels raw36213step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3418 node3418Labels := by rfl

def raw36214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw36214Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36214step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36214step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36214step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36214step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36214 raw36214Labels = mixedMoment B node3763 node3763Labels := by
  calc
    mixedMoment B raw36214 raw36214Labels = mixedMoment B raw36214step0 raw36214step0Labels := by
      have ha : raw36214step0 = (fun i j => raw36214 (permutation657 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36214step0 raw36214; decide +kernel
      have hl : raw36214step0Labels = raw36214Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36214 raw36214Labels permutation657 permutation7
    mixedMoment B raw36214step0 raw36214step0Labels = mixedMoment B raw36214step1 raw36214step1Labels := by
      have ha : raw36214step1 = raw36214step0 := by apply Matrix.ext; unfold raw36214step1 raw36214step0; decide +kernel
      have hl : raw36214step0Labels = labelEmbedding1 ∘ raw36214step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36214step0 raw36214step0Labels raw36214step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3763 node3763Labels := by rfl

def raw36215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw36215Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36215step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw36215step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36215step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36215step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36215step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36215step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36215 raw36215Labels = mixedMoment B node3773 node3773Labels := by
  calc
    mixedMoment B raw36215 raw36215Labels = mixedMoment B raw36215step0 raw36215step0Labels := by
      have hz : ∀ j, raw36215 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36215step0 = (fun i j => raw36215 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36215step0 raw36215; decide +kernel
      have hl : raw36215step0Labels = raw36215Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36215 raw36215Labels permutation346 hz
    mixedMoment B raw36215step0 raw36215step0Labels = mixedMoment B raw36215step1 raw36215step1Labels := by
      have ha : raw36215step1 = (fun i j => raw36215step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36215step1 raw36215step0; decide +kernel
      have hl : raw36215step1Labels = raw36215step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36215step0 raw36215step0Labels permutation144 permutation7
    mixedMoment B raw36215step1 raw36215step1Labels = mixedMoment B raw36215step2 raw36215step2Labels := by
      have ha : raw36215step2 = raw36215step1 := by apply Matrix.ext; unfold raw36215step2 raw36215step1; decide +kernel
      have hl : raw36215step1Labels = labelEmbedding1 ∘ raw36215step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36215step1 raw36215step1Labels raw36215step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3773 node3773Labels := by rfl

def raw36216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw36216Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw36216step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36216step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36216step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36216step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36216step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36216 raw36216Labels = mixedMoment B node3960 node3960Labels := by
  calc
    mixedMoment B raw36216 raw36216Labels = mixedMoment B raw36216step0 raw36216step0Labels := by
      have hz : ∀ j, raw36216 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36216step0 = (fun i j => raw36216 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36216step0 raw36216; decide +kernel
      have hl : raw36216step0Labels = raw36216Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36216 raw36216Labels permutation346 hz
    mixedMoment B raw36216step0 raw36216step0Labels = mixedMoment B raw36216step1 raw36216step1Labels := by
      have ha : raw36216step1 = (fun i j => raw36216step0 (permutation120 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36216step1 raw36216step0; decide +kernel
      have hl : raw36216step1Labels = raw36216step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36216step0 raw36216step0Labels permutation120 permutation5
    mixedMoment B raw36216step1 raw36216step1Labels = mixedMoment B raw36216step2 raw36216step2Labels := by
      have ha : raw36216step2 = raw36216step1 := by apply Matrix.ext; unfold raw36216step2 raw36216step1; decide +kernel
      have hl : raw36216step1Labels = labelEmbedding1 ∘ raw36216step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36216step1 raw36216step1Labels raw36216step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3960 node3960Labels := by rfl

def raw36217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw36217Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw36217step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36217step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw36217step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36217step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw36217step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36217 raw36217Labels = mixedMoment B node2658 node2658Labels := by
  calc
    mixedMoment B raw36217 raw36217Labels = mixedMoment B raw36217step0 raw36217step0Labels := by
      have hz : ∀ j, raw36217 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36217step0 = (fun i j => raw36217 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36217step0 raw36217; decide +kernel
      have hl : raw36217step0Labels = raw36217Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36217 raw36217Labels permutation346 hz
    mixedMoment B raw36217step0 raw36217step0Labels = mixedMoment B raw36217step1 raw36217step1Labels := by
      have ha : raw36217step1 = (fun i j => raw36217step0 (permutation126 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36217step1 raw36217step0; decide +kernel
      have hl : raw36217step1Labels = raw36217step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36217step0 raw36217step0Labels permutation126 permutation5
    mixedMoment B raw36217step1 raw36217step1Labels = mixedMoment B raw36217step2 raw36217step2Labels := by
      have ha : raw36217step2 = raw36217step1 := by apply Matrix.ext; unfold raw36217step2 raw36217step1; decide +kernel
      have hl : raw36217step1Labels = labelEmbedding1 ∘ raw36217step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36217step1 raw36217step1Labels raw36217step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2658 node2658Labels := by rfl

def raw36218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw36218Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36218step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw36218step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36218step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw36218step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36218 raw36218Labels = mixedMoment B node2656 node2656Labels := by
  calc
    mixedMoment B raw36218 raw36218Labels = mixedMoment B raw36218step0 raw36218step0Labels := by
      have ha : raw36218step0 = (fun i j => raw36218 (permutation588 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36218step0 raw36218; decide +kernel
      have hl : raw36218step0Labels = raw36218Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36218 raw36218Labels permutation588 permutation5
    mixedMoment B raw36218step0 raw36218step0Labels = mixedMoment B raw36218step1 raw36218step1Labels := by
      have ha : raw36218step1 = raw36218step0 := by apply Matrix.ext; unfold raw36218step1 raw36218step0; decide +kernel
      have hl : raw36218step0Labels = labelEmbedding1 ∘ raw36218step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36218step0 raw36218step0Labels raw36218step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2656 node2656Labels := by rfl

def raw36219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw36219Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36219step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw36219step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36219step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36219step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36219step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36219step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36219 raw36219Labels = mixedMoment B node2682 node2682Labels := by
  calc
    mixedMoment B raw36219 raw36219Labels = mixedMoment B raw36219step0 raw36219step0Labels := by
      have hz : ∀ j, raw36219 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36219step0 = (fun i j => raw36219 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36219step0 raw36219; decide +kernel
      have hl : raw36219step0Labels = raw36219Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36219 raw36219Labels permutation346 hz
    mixedMoment B raw36219step0 raw36219step0Labels = mixedMoment B raw36219step1 raw36219step1Labels := by
      have ha : raw36219step1 = (fun i j => raw36219step0 (permutation126 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36219step1 raw36219step0; decide +kernel
      have hl : raw36219step1Labels = raw36219step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36219step0 raw36219step0Labels permutation126 permutation5
    mixedMoment B raw36219step1 raw36219step1Labels = mixedMoment B raw36219step2 raw36219step2Labels := by
      have ha : raw36219step2 = raw36219step1 := by apply Matrix.ext; unfold raw36219step2 raw36219step1; decide +kernel
      have hl : raw36219step1Labels = labelEmbedding1 ∘ raw36219step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36219step1 raw36219step1Labels raw36219step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2682 node2682Labels := by rfl

def raw36220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw36220Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36220step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw36220step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36220step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36220step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36220step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36220step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36220 raw36220Labels = mixedMoment B node2736 node2736Labels := by
  calc
    mixedMoment B raw36220 raw36220Labels = mixedMoment B raw36220step0 raw36220step0Labels := by
      have hz : ∀ j, raw36220 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36220step0 = (fun i j => raw36220 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36220step0 raw36220; decide +kernel
      have hl : raw36220step0Labels = raw36220Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36220 raw36220Labels permutation346 hz
    mixedMoment B raw36220step0 raw36220step0Labels = mixedMoment B raw36220step1 raw36220step1Labels := by
      have ha : raw36220step1 = (fun i j => raw36220step0 (permutation120 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36220step1 raw36220step0; decide +kernel
      have hl : raw36220step1Labels = raw36220step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36220step0 raw36220step0Labels permutation120 permutation5
    mixedMoment B raw36220step1 raw36220step1Labels = mixedMoment B raw36220step2 raw36220step2Labels := by
      have ha : raw36220step2 = raw36220step1 := by apply Matrix.ext; unfold raw36220step2 raw36220step1; decide +kernel
      have hl : raw36220step1Labels = labelEmbedding1 ∘ raw36220step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36220step1 raw36220step1Labels raw36220step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2736 node2736Labels := by rfl

def raw36221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw36221Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36221step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw36221step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36221step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw36221step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36221step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw36221step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36221step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw36221step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36221 raw36221Labels = mixedMoment B node3413 node3413Labels := by
  calc
    mixedMoment B raw36221 raw36221Labels = mixedMoment B raw36221step0 raw36221step0Labels := by
      have hz : ∀ j, raw36221 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36221step0 = (fun i j => raw36221 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36221step0 raw36221; decide +kernel
      have hl : raw36221step0Labels = raw36221Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36221 raw36221Labels permutation346 hz
    mixedMoment B raw36221step0 raw36221step0Labels = mixedMoment B raw36221step1 raw36221step1Labels := by
      have ha : raw36221step1 = (fun i j => raw36221step0 (permutation57 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36221step1 raw36221step0; decide +kernel
      have hl : raw36221step1Labels = raw36221step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36221step0 raw36221step0Labels permutation57 permutation5
    mixedMoment B raw36221step1 raw36221step1Labels = mixedMoment B raw36221step2 raw36221step2Labels := by
      have ha : raw36221step2 = -raw36221step1 := by apply Matrix.ext; change ∀ i j, raw36221step2 i j = -(raw36221step1 i j); unfold raw36221step2 raw36221step1; decide +kernel
      have hl : raw36221step2Labels = raw36221step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36221step2 raw36221step2Labels = mixedMoment B raw36221step3 raw36221step3Labels := by
      have ha : raw36221step3 = raw36221step2 := by apply Matrix.ext; unfold raw36221step3 raw36221step2; decide +kernel
      have hl : raw36221step2Labels = labelEmbedding1 ∘ raw36221step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36221step2 raw36221step2Labels raw36221step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3413 node3413Labels := by rfl

def raw36222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw36222Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36222step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36222step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36222step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36222step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36222 raw36222Labels = mixedMoment B node3465 node3465Labels := by
  calc
    mixedMoment B raw36222 raw36222Labels = mixedMoment B raw36222step0 raw36222step0Labels := by
      have ha : raw36222step0 = (fun i j => raw36222 (permutation657 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36222step0 raw36222; decide +kernel
      have hl : raw36222step0Labels = raw36222Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36222 raw36222Labels permutation657 permutation7
    mixedMoment B raw36222step0 raw36222step0Labels = mixedMoment B raw36222step1 raw36222step1Labels := by
      have ha : raw36222step1 = raw36222step0 := by apply Matrix.ext; unfold raw36222step1 raw36222step0; decide +kernel
      have hl : raw36222step0Labels = labelEmbedding1 ∘ raw36222step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36222step0 raw36222step0Labels raw36222step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3465 node3465Labels := by rfl

def raw36223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw36223Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw36223step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36223step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36223step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36223step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36223step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36223 raw36223Labels = mixedMoment B node3542 node3542Labels := by
  calc
    mixedMoment B raw36223 raw36223Labels = mixedMoment B raw36223step0 raw36223step0Labels := by
      have hz : ∀ j, raw36223 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36223step0 = (fun i j => raw36223 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36223step0 raw36223; decide +kernel
      have hl : raw36223step0Labels = raw36223Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36223 raw36223Labels permutation346 hz
    mixedMoment B raw36223step0 raw36223step0Labels = mixedMoment B raw36223step1 raw36223step1Labels := by
      have ha : raw36223step1 = (fun i j => raw36223step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36223step1 raw36223step0; decide +kernel
      have hl : raw36223step1Labels = raw36223step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36223step0 raw36223step0Labels permutation144 permutation7
    mixedMoment B raw36223step1 raw36223step1Labels = mixedMoment B raw36223step2 raw36223step2Labels := by
      have ha : raw36223step2 = raw36223step1 := by apply Matrix.ext; unfold raw36223step2 raw36223step1; decide +kernel
      have hl : raw36223step1Labels = labelEmbedding1 ∘ raw36223step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36223step1 raw36223step1Labels raw36223step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3542 node3542Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
