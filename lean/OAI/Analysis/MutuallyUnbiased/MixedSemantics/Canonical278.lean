import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
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

def raw35584 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw35584Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35584step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw35584step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35584step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw35584step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35584 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35584 raw35584Labels = mixedMoment B node5381 node5381Labels := by
  calc
    mixedMoment B raw35584 raw35584Labels = mixedMoment B raw35584step0 raw35584step0Labels := by
      have ha : raw35584step0 = (fun i j => raw35584 (permutation267 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35584step0 raw35584; decide +kernel
      have hl : raw35584step0Labels = raw35584Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35584 raw35584Labels permutation267 permutation7
    mixedMoment B raw35584step0 raw35584step0Labels = mixedMoment B raw35584step1 raw35584step1Labels := by
      have ha : raw35584step1 = raw35584step0 := by apply Matrix.ext; unfold raw35584step1 raw35584step0; decide +kernel
      have hl : raw35584step0Labels = labelEmbedding10 ∘ raw35584step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35584step0 raw35584step0Labels raw35584step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5381 node5381Labels := by rfl

def raw35585 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw35585Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35585step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw35585step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35585step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw35585step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35585 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35585 raw35585Labels = mixedMoment B node5381 node5381Labels := by
  calc
    mixedMoment B raw35585 raw35585Labels = mixedMoment B raw35585step0 raw35585step0Labels := by
      have ha : raw35585step0 = (fun i j => raw35585 (permutation265 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35585step0 raw35585; decide +kernel
      have hl : raw35585step0Labels = raw35585Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35585 raw35585Labels permutation265 permutation7
    mixedMoment B raw35585step0 raw35585step0Labels = mixedMoment B raw35585step1 raw35585step1Labels := by
      have ha : raw35585step1 = raw35585step0 := by apply Matrix.ext; unfold raw35585step1 raw35585step0; decide +kernel
      have hl : raw35585step0Labels = labelEmbedding10 ∘ raw35585step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35585step0 raw35585step0Labels raw35585step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5381 node5381Labels := by rfl

def raw35586 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35586Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35586step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35586step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35586step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35586step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35586 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35586 raw35586Labels = mixedMoment B node5380 node5380Labels := by
  calc
    mixedMoment B raw35586 raw35586Labels = mixedMoment B raw35586step0 raw35586step0Labels := by
      have ha : raw35586step0 = (fun i j => raw35586 (permutation265 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35586step0 raw35586; decide +kernel
      have hl : raw35586step0Labels = raw35586Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35586 raw35586Labels permutation265 permutation7
    mixedMoment B raw35586step0 raw35586step0Labels = mixedMoment B raw35586step1 raw35586step1Labels := by
      have ha : raw35586step1 = raw35586step0 := by apply Matrix.ext; unfold raw35586step1 raw35586step0; decide +kernel
      have hl : raw35586step0Labels = labelEmbedding10 ∘ raw35586step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35586step0 raw35586step0Labels raw35586step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5380 node5380Labels := by rfl

def raw35587 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw35587Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35587step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw35587step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35587step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw35587step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35587step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35587step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35587step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35587step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35587 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35587 raw35587Labels = mixedMoment B node5228 node5228Labels := by
  calc
    mixedMoment B raw35587 raw35587Labels = mixedMoment B raw35587step0 raw35587step0Labels := by
      have hz : ∀ j, raw35587 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35587step0 = (fun i j => raw35587 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35587step0 raw35587; decide +kernel
      have hl : raw35587step0Labels = raw35587Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35587 raw35587Labels permutation346 hz
    mixedMoment B raw35587step0 raw35587step0Labels = mixedMoment B raw35587step1 raw35587step1Labels := by
      have ha : raw35587step1 = (fun i j => raw35587step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw35587step1 raw35587step0; decide +kernel
      have hl : raw35587step1Labels = raw35587step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35587step0 raw35587step0Labels permutation34 permutation4
    mixedMoment B raw35587step1 raw35587step1Labels = mixedMoment B raw35587step2 raw35587step2Labels := by
      have ha : raw35587step2 = -raw35587step1 := by apply Matrix.ext; change ∀ i j, raw35587step2 i j = -(raw35587step1 i j); unfold raw35587step2 raw35587step1; decide +kernel
      have hl : raw35587step2Labels = raw35587step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35587step2 raw35587step2Labels = mixedMoment B raw35587step3 raw35587step3Labels := by
      have ha : raw35587step3 = raw35587step2 := by apply Matrix.ext; unfold raw35587step3 raw35587step2; decide +kernel
      have hl : raw35587step2Labels = labelEmbedding7 ∘ raw35587step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35587step2 raw35587step2Labels raw35587step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5228 node5228Labels := by rfl

def raw35588 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw35588Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35588step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw35588step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35588step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35588step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35588step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35588step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35588 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35588 raw35588Labels = mixedMoment B node5367 node5367Labels := by
  calc
    mixedMoment B raw35588 raw35588Labels = mixedMoment B raw35588step0 raw35588step0Labels := by
      have hz : ∀ j, raw35588 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35588step0 = (fun i j => raw35588 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35588step0 raw35588; decide +kernel
      have hl : raw35588step0Labels = raw35588Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35588 raw35588Labels permutation346 hz
    mixedMoment B raw35588step0 raw35588step0Labels = mixedMoment B raw35588step1 raw35588step1Labels := by
      have ha : raw35588step1 = (fun i j => raw35588step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35588step1 raw35588step0; decide +kernel
      have hl : raw35588step1Labels = raw35588step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35588step0 raw35588step0Labels permutation34 permutation6
    mixedMoment B raw35588step1 raw35588step1Labels = mixedMoment B raw35588step2 raw35588step2Labels := by
      have ha : raw35588step2 = raw35588step1 := by apply Matrix.ext; unfold raw35588step2 raw35588step1; decide +kernel
      have hl : raw35588step1Labels = labelEmbedding9 ∘ raw35588step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35588step1 raw35588step1Labels raw35588step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5367 node5367Labels := by rfl

def raw35589 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw35589Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35589step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35589step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35589step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35589step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35589 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35589 raw35589Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw35589 raw35589Labels = mixedMoment B raw35589step0 raw35589step0Labels := by
      have ha : raw35589step0 = (fun i j => raw35589 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35589step0 raw35589; decide +kernel
      have hl : raw35589step0Labels = raw35589Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35589 raw35589Labels permutation154 permutation6
    mixedMoment B raw35589step0 raw35589step0Labels = mixedMoment B raw35589step1 raw35589step1Labels := by
      have ha : raw35589step1 = raw35589step0 := by apply Matrix.ext; unfold raw35589step1 raw35589step0; decide +kernel
      have hl : raw35589step0Labels = labelEmbedding9 ∘ raw35589step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35589step0 raw35589step0Labels raw35589step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

def raw35590 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw35590Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35590step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw35590step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35590step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35590step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35590step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35590step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35590 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35590 raw35590Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw35590 raw35590Labels = mixedMoment B raw35590step0 raw35590step0Labels := by
      have hz : ∀ j, raw35590 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35590step0 = (fun i j => raw35590 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35590step0 raw35590; decide +kernel
      have hl : raw35590step0Labels = raw35590Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35590 raw35590Labels permutation346 hz
    mixedMoment B raw35590step0 raw35590step0Labels = mixedMoment B raw35590step1 raw35590step1Labels := by
      have ha : raw35590step1 = (fun i j => raw35590step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35590step1 raw35590step0; decide +kernel
      have hl : raw35590step1Labels = raw35590step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35590step0 raw35590step0Labels permutation34 permutation6
    mixedMoment B raw35590step1 raw35590step1Labels = mixedMoment B raw35590step2 raw35590step2Labels := by
      have ha : raw35590step2 = raw35590step1 := by apply Matrix.ext; unfold raw35590step2 raw35590step1; decide +kernel
      have hl : raw35590step1Labels = labelEmbedding9 ∘ raw35590step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35590step1 raw35590step1Labels raw35590step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5384 node5384Labels := by rfl

def raw35591 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35591Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35591step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35591step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35591step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35591step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35591step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35591step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35591 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35591 raw35591Labels = mixedMoment B node5388 node5388Labels := by
  calc
    mixedMoment B raw35591 raw35591Labels = mixedMoment B raw35591step0 raw35591step0Labels := by
      have hz : ∀ j, raw35591 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35591step0 = (fun i j => raw35591 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35591step0 raw35591; decide +kernel
      have hl : raw35591step0Labels = raw35591Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35591 raw35591Labels permutation346 hz
    mixedMoment B raw35591step0 raw35591step0Labels = mixedMoment B raw35591step1 raw35591step1Labels := by
      have ha : raw35591step1 = (fun i j => raw35591step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35591step1 raw35591step0; decide +kernel
      have hl : raw35591step1Labels = raw35591step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35591step0 raw35591step0Labels permutation34 permutation6
    mixedMoment B raw35591step1 raw35591step1Labels = mixedMoment B raw35591step2 raw35591step2Labels := by
      have ha : raw35591step2 = raw35591step1 := by apply Matrix.ext; unfold raw35591step2 raw35591step1; decide +kernel
      have hl : raw35591step1Labels = labelEmbedding9 ∘ raw35591step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35591step1 raw35591step1Labels raw35591step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5388 node5388Labels := by rfl

def raw35592 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw35592Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35592step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw35592step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35592step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw35592step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35592step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35592step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35592step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35592step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35592 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35592 raw35592Labels = mixedMoment B node5228 node5228Labels := by
  calc
    mixedMoment B raw35592 raw35592Labels = mixedMoment B raw35592step0 raw35592step0Labels := by
      have hz : ∀ j, raw35592 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35592step0 = (fun i j => raw35592 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35592step0 raw35592; decide +kernel
      have hl : raw35592step0Labels = raw35592Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35592 raw35592Labels permutation346 hz
    mixedMoment B raw35592step0 raw35592step0Labels = mixedMoment B raw35592step1 raw35592step1Labels := by
      have ha : raw35592step1 = (fun i j => raw35592step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw35592step1 raw35592step0; decide +kernel
      have hl : raw35592step1Labels = raw35592step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35592step0 raw35592step0Labels permutation32 permutation4
    mixedMoment B raw35592step1 raw35592step1Labels = mixedMoment B raw35592step2 raw35592step2Labels := by
      have ha : raw35592step2 = -raw35592step1 := by apply Matrix.ext; change ∀ i j, raw35592step2 i j = -(raw35592step1 i j); unfold raw35592step2 raw35592step1; decide +kernel
      have hl : raw35592step2Labels = raw35592step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35592step2 raw35592step2Labels = mixedMoment B raw35592step3 raw35592step3Labels := by
      have ha : raw35592step3 = raw35592step2 := by apply Matrix.ext; unfold raw35592step3 raw35592step2; decide +kernel
      have hl : raw35592step2Labels = labelEmbedding7 ∘ raw35592step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35592step2 raw35592step2Labels raw35592step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5228 node5228Labels := by rfl

def raw35593 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw35593Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35593step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw35593step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35593step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35593step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35593step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35593step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35593 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35593 raw35593Labels = mixedMoment B node5367 node5367Labels := by
  calc
    mixedMoment B raw35593 raw35593Labels = mixedMoment B raw35593step0 raw35593step0Labels := by
      have hz : ∀ j, raw35593 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35593step0 = (fun i j => raw35593 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35593step0 raw35593; decide +kernel
      have hl : raw35593step0Labels = raw35593Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35593 raw35593Labels permutation346 hz
    mixedMoment B raw35593step0 raw35593step0Labels = mixedMoment B raw35593step1 raw35593step1Labels := by
      have ha : raw35593step1 = (fun i j => raw35593step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35593step1 raw35593step0; decide +kernel
      have hl : raw35593step1Labels = raw35593step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35593step0 raw35593step0Labels permutation32 permutation6
    mixedMoment B raw35593step1 raw35593step1Labels = mixedMoment B raw35593step2 raw35593step2Labels := by
      have ha : raw35593step2 = raw35593step1 := by apply Matrix.ext; unfold raw35593step2 raw35593step1; decide +kernel
      have hl : raw35593step1Labels = labelEmbedding9 ∘ raw35593step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35593step1 raw35593step1Labels raw35593step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5367 node5367Labels := by rfl

def raw35594 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw35594Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35594step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35594step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35594step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35594step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35594 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35594 raw35594Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw35594 raw35594Labels = mixedMoment B raw35594step0 raw35594step0Labels := by
      have ha : raw35594step0 = (fun i j => raw35594 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35594step0 raw35594; decide +kernel
      have hl : raw35594step0Labels = raw35594Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35594 raw35594Labels permutation152 permutation6
    mixedMoment B raw35594step0 raw35594step0Labels = mixedMoment B raw35594step1 raw35594step1Labels := by
      have ha : raw35594step1 = raw35594step0 := by apply Matrix.ext; unfold raw35594step1 raw35594step0; decide +kernel
      have hl : raw35594step0Labels = labelEmbedding9 ∘ raw35594step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35594step0 raw35594step0Labels raw35594step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

def raw35595 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw35595Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35595step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-2, 1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw35595step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35595step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35595step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35595step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35595step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35595 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35595 raw35595Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw35595 raw35595Labels = mixedMoment B raw35595step0 raw35595step0Labels := by
      have hz : ∀ j, raw35595 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35595step0 = (fun i j => raw35595 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35595step0 raw35595; decide +kernel
      have hl : raw35595step0Labels = raw35595Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35595 raw35595Labels permutation346 hz
    mixedMoment B raw35595step0 raw35595step0Labels = mixedMoment B raw35595step1 raw35595step1Labels := by
      have ha : raw35595step1 = (fun i j => raw35595step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35595step1 raw35595step0; decide +kernel
      have hl : raw35595step1Labels = raw35595step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35595step0 raw35595step0Labels permutation32 permutation6
    mixedMoment B raw35595step1 raw35595step1Labels = mixedMoment B raw35595step2 raw35595step2Labels := by
      have ha : raw35595step2 = raw35595step1 := by apply Matrix.ext; unfold raw35595step2 raw35595step1; decide +kernel
      have hl : raw35595step1Labels = labelEmbedding9 ∘ raw35595step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35595step1 raw35595step1Labels raw35595step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5384 node5384Labels := by rfl

def raw35596 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw35596Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35596step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw35596step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35596step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35596step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35596step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35596step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35596 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35596 raw35596Labels = mixedMoment B node5388 node5388Labels := by
  calc
    mixedMoment B raw35596 raw35596Labels = mixedMoment B raw35596step0 raw35596step0Labels := by
      have hz : ∀ j, raw35596 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35596step0 = (fun i j => raw35596 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35596step0 raw35596; decide +kernel
      have hl : raw35596step0Labels = raw35596Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35596 raw35596Labels permutation346 hz
    mixedMoment B raw35596step0 raw35596step0Labels = mixedMoment B raw35596step1 raw35596step1Labels := by
      have ha : raw35596step1 = (fun i j => raw35596step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35596step1 raw35596step0; decide +kernel
      have hl : raw35596step1Labels = raw35596step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35596step0 raw35596step0Labels permutation32 permutation6
    mixedMoment B raw35596step1 raw35596step1Labels = mixedMoment B raw35596step2 raw35596step2Labels := by
      have ha : raw35596step2 = raw35596step1 := by apply Matrix.ext; unfold raw35596step2 raw35596step1; decide +kernel
      have hl : raw35596step1Labels = labelEmbedding9 ∘ raw35596step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35596step1 raw35596step1Labels raw35596step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5388 node5388Labels := by rfl

def raw35597 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw35597Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35597step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw35597step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35597step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw35597step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35597step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw35597step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35597step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw35597step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35597 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35597 raw35597Labels = mixedMoment B node5222 node5222Labels := by
  calc
    mixedMoment B raw35597 raw35597Labels = mixedMoment B raw35597step0 raw35597step0Labels := by
      have hz : ∀ j, raw35597 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35597step0 = (fun i j => raw35597 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35597step0 raw35597; decide +kernel
      have hl : raw35597step0Labels = raw35597Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35597 raw35597Labels permutation346 hz
    mixedMoment B raw35597step0 raw35597step0Labels = mixedMoment B raw35597step1 raw35597step1Labels := by
      have ha : raw35597step1 = (fun i j => raw35597step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw35597step1 raw35597step0; decide +kernel
      have hl : raw35597step1Labels = raw35597step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35597step0 raw35597step0Labels permutation32 permutation4
    mixedMoment B raw35597step1 raw35597step1Labels = mixedMoment B raw35597step2 raw35597step2Labels := by
      have ha : raw35597step2 = -raw35597step1 := by apply Matrix.ext; change ∀ i j, raw35597step2 i j = -(raw35597step1 i j); unfold raw35597step2 raw35597step1; decide +kernel
      have hl : raw35597step2Labels = raw35597step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35597step2 raw35597step2Labels = mixedMoment B raw35597step3 raw35597step3Labels := by
      have ha : raw35597step3 = raw35597step2 := by apply Matrix.ext; unfold raw35597step3 raw35597step2; decide +kernel
      have hl : raw35597step2Labels = labelEmbedding7 ∘ raw35597step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35597step2 raw35597step2Labels raw35597step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5222 node5222Labels := by rfl

def raw35598 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw35598Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35598step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw35598step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35598step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35598step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35598step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw35598step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35598 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35598 raw35598Labels = mixedMoment B node5248 node5248Labels := by
  calc
    mixedMoment B raw35598 raw35598Labels = mixedMoment B raw35598step0 raw35598step0Labels := by
      have hz : ∀ j, raw35598 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35598step0 = (fun i j => raw35598 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35598step0 raw35598; decide +kernel
      have hl : raw35598step0Labels = raw35598Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35598 raw35598Labels permutation346 hz
    mixedMoment B raw35598step0 raw35598step0Labels = mixedMoment B raw35598step1 raw35598step1Labels := by
      have ha : raw35598step1 = (fun i j => raw35598step0 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw35598step1 raw35598step0; decide +kernel
      have hl : raw35598step1Labels = raw35598step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35598step0 raw35598step0Labels permutation145 permutation4
    mixedMoment B raw35598step1 raw35598step1Labels = mixedMoment B raw35598step2 raw35598step2Labels := by
      have ha : raw35598step2 = raw35598step1 := by apply Matrix.ext; unfold raw35598step2 raw35598step1; decide +kernel
      have hl : raw35598step1Labels = labelEmbedding7 ∘ raw35598step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35598step1 raw35598step1Labels raw35598step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5248 node5248Labels := by rfl

def raw35599 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw35599Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35599step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35599step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35599step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35599step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35599 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35599 raw35599Labels = mixedMoment B node5243 node5243Labels := by
  calc
    mixedMoment B raw35599 raw35599Labels = mixedMoment B raw35599step0 raw35599step0Labels := by
      have ha : raw35599step0 = (fun i j => raw35599 (permutation662 i) (permutation4 j)) := by apply Matrix.ext; unfold raw35599step0 raw35599; decide +kernel
      have hl : raw35599step0Labels = raw35599Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35599 raw35599Labels permutation662 permutation4
    mixedMoment B raw35599step0 raw35599step0Labels = mixedMoment B raw35599step1 raw35599step1Labels := by
      have ha : raw35599step1 = raw35599step0 := by apply Matrix.ext; unfold raw35599step1 raw35599step0; decide +kernel
      have hl : raw35599step0Labels = labelEmbedding7 ∘ raw35599step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35599step0 raw35599step0Labels raw35599step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5243 node5243Labels := by rfl

def raw35600 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw35600Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35600step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-2, 1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw35600step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35600step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw35600step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35600step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw35600step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35600 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35600 raw35600Labels = mixedMoment B node5264 node5264Labels := by
  calc
    mixedMoment B raw35600 raw35600Labels = mixedMoment B raw35600step0 raw35600step0Labels := by
      have hz : ∀ j, raw35600 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35600step0 = (fun i j => raw35600 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35600step0 raw35600; decide +kernel
      have hl : raw35600step0Labels = raw35600Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35600 raw35600Labels permutation346 hz
    mixedMoment B raw35600step0 raw35600step0Labels = mixedMoment B raw35600step1 raw35600step1Labels := by
      have ha : raw35600step1 = (fun i j => raw35600step0 (permutation149 i) (permutation4 j)) := by apply Matrix.ext; unfold raw35600step1 raw35600step0; decide +kernel
      have hl : raw35600step1Labels = raw35600step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35600step0 raw35600step0Labels permutation149 permutation4
    mixedMoment B raw35600step1 raw35600step1Labels = mixedMoment B raw35600step2 raw35600step2Labels := by
      have ha : raw35600step2 = raw35600step1 := by apply Matrix.ext; unfold raw35600step2 raw35600step1; decide +kernel
      have hl : raw35600step1Labels = labelEmbedding7 ∘ raw35600step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35600step1 raw35600step1Labels raw35600step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5264 node5264Labels := by rfl

def raw35601 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw35601Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35601step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw35601step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35601step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw35601step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35601step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw35601step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35601 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35601 raw35601Labels = mixedMoment B node5264 node5264Labels := by
  calc
    mixedMoment B raw35601 raw35601Labels = mixedMoment B raw35601step0 raw35601step0Labels := by
      have hz : ∀ j, raw35601 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35601step0 = (fun i j => raw35601 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35601step0 raw35601; decide +kernel
      have hl : raw35601step0Labels = raw35601Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35601 raw35601Labels permutation346 hz
    mixedMoment B raw35601step0 raw35601step0Labels = mixedMoment B raw35601step1 raw35601step1Labels := by
      have ha : raw35601step1 = (fun i j => raw35601step0 (permutation143 i) (permutation4 j)) := by apply Matrix.ext; unfold raw35601step1 raw35601step0; decide +kernel
      have hl : raw35601step1Labels = raw35601step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35601step0 raw35601step0Labels permutation143 permutation4
    mixedMoment B raw35601step1 raw35601step1Labels = mixedMoment B raw35601step2 raw35601step2Labels := by
      have ha : raw35601step2 = raw35601step1 := by apply Matrix.ext; unfold raw35601step2 raw35601step1; decide +kernel
      have hl : raw35601step1Labels = labelEmbedding7 ∘ raw35601step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35601step1 raw35601step1Labels raw35601step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5264 node5264Labels := by rfl

def raw35602 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35602Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35602step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35602step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35602step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35602step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35602step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35602step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35602 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35602 raw35602Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw35602 raw35602Labels = mixedMoment B raw35602step0 raw35602step0Labels := by
      have hz : ∀ j, raw35602 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35602step0 = (fun i j => raw35602 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35602step0 raw35602; decide +kernel
      have hl : raw35602step0Labels = raw35602Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35602 raw35602Labels permutation346 hz
    mixedMoment B raw35602step0 raw35602step0Labels = mixedMoment B raw35602step1 raw35602step1Labels := by
      have ha : raw35602step1 = (fun i j => raw35602step0 (permutation58 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35602step1 raw35602step0; decide +kernel
      have hl : raw35602step1Labels = raw35602step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35602step0 raw35602step0Labels permutation58 permutation3
    mixedMoment B raw35602step1 raw35602step1Labels = mixedMoment B raw35602step2 raw35602step2Labels := by
      have ha : raw35602step2 = raw35602step1 := by apply Matrix.ext; unfold raw35602step2 raw35602step1; decide +kernel
      have hl : raw35602step1Labels = labelEmbedding6 ∘ raw35602step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35602step1 raw35602step1Labels raw35602step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4866 node4866Labels := by rfl

def raw35603 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35603Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35603step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35603step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35603step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35603step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35603 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35603 raw35603Labels = mixedMoment B node5401 node5401Labels := by
  calc
    mixedMoment B raw35603 raw35603Labels = mixedMoment B raw35603step0 raw35603step0Labels := by
      have ha : raw35603step0 = (fun i j => raw35603 (permutation291 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35603step0 raw35603; decide +kernel
      have hl : raw35603step0Labels = raw35603Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35603 raw35603Labels permutation291 permutation3
    mixedMoment B raw35603step0 raw35603step0Labels = mixedMoment B raw35603step1 raw35603step1Labels := by
      have ha : raw35603step1 = raw35603step0 := by apply Matrix.ext; unfold raw35603step1 raw35603step0; decide +kernel
      have hl : raw35603step0Labels = labelEmbedding6 ∘ raw35603step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35603step0 raw35603step0Labels raw35603step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5401 node5401Labels := by rfl

def raw35604 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw35604Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35604step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw35604step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35604step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35604step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35604step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw35604step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35604step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw35604step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35604 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35604 raw35604Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw35604 raw35604Labels = mixedMoment B raw35604step0 raw35604step0Labels := by
      have hz : ∀ j, raw35604 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35604step0 = (fun i j => raw35604 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35604step0 raw35604; decide +kernel
      have hl : raw35604step0Labels = raw35604Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35604 raw35604Labels permutation346 hz
    mixedMoment B raw35604step0 raw35604step0Labels = mixedMoment B raw35604step1 raw35604step1Labels := by
      have ha : raw35604step1 = (fun i j => raw35604step0 (permutation68 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35604step1 raw35604step0; decide +kernel
      have hl : raw35604step1Labels = raw35604step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35604step0 raw35604step0Labels permutation68 permutation5
    mixedMoment B raw35604step1 raw35604step1Labels = mixedMoment B raw35604step2 raw35604step2Labels := by
      have ha : raw35604step2 = -raw35604step1 := by apply Matrix.ext; change ∀ i j, raw35604step2 i j = -(raw35604step1 i j); unfold raw35604step2 raw35604step1; decide +kernel
      have hl : raw35604step2Labels = raw35604step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35604step2 raw35604step2Labels = mixedMoment B raw35604step3 raw35604step3Labels := by
      have ha : raw35604step3 = raw35604step2 := by apply Matrix.ext; unfold raw35604step3 raw35604step2; decide +kernel
      have hl : raw35604step2Labels = labelEmbedding8 ∘ raw35604step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35604step2 raw35604step2Labels raw35604step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw35605 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw35605Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35605step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw35605step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35605step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw35605step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35605step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw35605step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35605 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35605 raw35605Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw35605 raw35605Labels = mixedMoment B raw35605step0 raw35605step0Labels := by
      have hz : ∀ j, raw35605 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35605step0 = (fun i j => raw35605 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35605step0 raw35605; decide +kernel
      have hl : raw35605step0Labels = raw35605Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35605 raw35605Labels permutation346 hz
    mixedMoment B raw35605step0 raw35605step0Labels = mixedMoment B raw35605step1 raw35605step1Labels := by
      have ha : raw35605step1 = (fun i j => raw35605step0 (permutation59 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35605step1 raw35605step0; decide +kernel
      have hl : raw35605step1Labels = raw35605step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35605step0 raw35605step0Labels permutation59 permutation3
    mixedMoment B raw35605step1 raw35605step1Labels = mixedMoment B raw35605step2 raw35605step2Labels := by
      have ha : raw35605step2 = raw35605step1 := by apply Matrix.ext; unfold raw35605step2 raw35605step1; decide +kernel
      have hl : raw35605step1Labels = labelEmbedding6 ∘ raw35605step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35605step1 raw35605step1Labels raw35605step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw35606 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35606Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35606step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35606step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35606step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35606step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35606 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35606 raw35606Labels = mixedMoment B node4679 node4679Labels := by
  calc
    mixedMoment B raw35606 raw35606Labels = mixedMoment B raw35606step0 raw35606step0Labels := by
      have ha : raw35606step0 = (fun i j => raw35606 (permutation277 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35606step0 raw35606; decide +kernel
      have hl : raw35606step0Labels = raw35606Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35606 raw35606Labels permutation277 permutation3
    mixedMoment B raw35606step0 raw35606step0Labels = mixedMoment B raw35606step1 raw35606step1Labels := by
      have ha : raw35606step1 = raw35606step0 := by apply Matrix.ext; unfold raw35606step1 raw35606step0; decide +kernel
      have hl : raw35606step0Labels = labelEmbedding6 ∘ raw35606step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35606step0 raw35606step0Labels raw35606step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4679 node4679Labels := by rfl

def raw35607 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![2, -1, -1]]
def raw35607Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35607step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35607step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35607step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35607step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35607 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35607 raw35607Labels = mixedMoment B node5380 node5380Labels := by
  calc
    mixedMoment B raw35607 raw35607Labels = mixedMoment B raw35607step0 raw35607step0Labels := by
      have ha : raw35607step0 = (fun i j => raw35607 (permutation277 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35607step0 raw35607; decide +kernel
      have hl : raw35607step0Labels = raw35607Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35607 raw35607Labels permutation277 permutation3
    mixedMoment B raw35607step0 raw35607step0Labels = mixedMoment B raw35607step1 raw35607step1Labels := by
      have ha : raw35607step1 = raw35607step0 := by apply Matrix.ext; unfold raw35607step1 raw35607step0; decide +kernel
      have hl : raw35607step0Labels = labelEmbedding6 ∘ raw35607step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35607step0 raw35607step0Labels raw35607step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5380 node5380Labels := by rfl

def raw35608 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35608Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35608step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35608step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35608step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw35608step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35608step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw35608step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35608 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35608 raw35608Labels = mixedMoment B node4684 node4684Labels := by
  calc
    mixedMoment B raw35608 raw35608Labels = mixedMoment B raw35608step0 raw35608step0Labels := by
      have hz : ∀ j, raw35608 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35608step0 = (fun i j => raw35608 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35608step0 raw35608; decide +kernel
      have hl : raw35608step0Labels = raw35608Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35608 raw35608Labels permutation346 hz
    mixedMoment B raw35608step0 raw35608step0Labels = mixedMoment B raw35608step1 raw35608step1Labels := by
      have ha : raw35608step1 = (fun i j => raw35608step0 (permutation59 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35608step1 raw35608step0; decide +kernel
      have hl : raw35608step1Labels = raw35608step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35608step0 raw35608step0Labels permutation59 permutation3
    mixedMoment B raw35608step1 raw35608step1Labels = mixedMoment B raw35608step2 raw35608step2Labels := by
      have ha : raw35608step2 = raw35608step1 := by apply Matrix.ext; unfold raw35608step2 raw35608step1; decide +kernel
      have hl : raw35608step1Labels = labelEmbedding6 ∘ raw35608step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35608step1 raw35608step1Labels raw35608step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4684 node4684Labels := by rfl

def raw35609 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35609Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35609step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35609step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35609step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35609step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35609step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35609step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35609 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35609 raw35609Labels = mixedMoment B node5336 node5336Labels := by
  calc
    mixedMoment B raw35609 raw35609Labels = mixedMoment B raw35609step0 raw35609step0Labels := by
      have ha : raw35609step0 = (fun i j => raw35609 (permutation518 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35609step0 raw35609; decide +kernel
      have hl : raw35609step0Labels = raw35609Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35609 raw35609Labels permutation518 permutation3
    mixedMoment B raw35609step0 raw35609step0Labels = mixedMoment B raw35609step1 raw35609step1Labels := by
      have ha : raw35609step1 = -raw35609step0 := by apply Matrix.ext; change ∀ i j, raw35609step1 i j = -(raw35609step0 i j); unfold raw35609step1 raw35609step0; decide +kernel
      have hl : raw35609step1Labels = raw35609step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35609step1 raw35609step1Labels = mixedMoment B raw35609step2 raw35609step2Labels := by
      have ha : raw35609step2 = raw35609step1 := by apply Matrix.ext; unfold raw35609step2 raw35609step1; decide +kernel
      have hl : raw35609step1Labels = labelEmbedding6 ∘ raw35609step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35609step1 raw35609step1Labels raw35609step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5336 node5336Labels := by rfl

def raw35610 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![0, 1, -1], ![2, -1, -1]]
def raw35610Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35610step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![0, 1, -1], ![2, -1, -1]]
def raw35610step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35610step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35610step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35610step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35610step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35610step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35610step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35610 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35610 raw35610Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw35610 raw35610Labels = mixedMoment B raw35610step0 raw35610step0Labels := by
      have hz : ∀ j, raw35610 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35610step0 = (fun i j => raw35610 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35610step0 raw35610; decide +kernel
      have hl : raw35610step0Labels = raw35610Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35610 raw35610Labels permutation346 hz
    mixedMoment B raw35610step0 raw35610step0Labels = mixedMoment B raw35610step1 raw35610step1Labels := by
      have ha : raw35610step1 = (fun i j => raw35610step0 (permutation102 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35610step1 raw35610step0; decide +kernel
      have hl : raw35610step1Labels = raw35610step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35610step0 raw35610step0Labels permutation102 permutation3
    mixedMoment B raw35610step1 raw35610step1Labels = mixedMoment B raw35610step2 raw35610step2Labels := by
      have ha : raw35610step2 = -raw35610step1 := by apply Matrix.ext; change ∀ i j, raw35610step2 i j = -(raw35610step1 i j); unfold raw35610step2 raw35610step1; decide +kernel
      have hl : raw35610step2Labels = raw35610step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35610step2 raw35610step2Labels = mixedMoment B raw35610step3 raw35610step3Labels := by
      have ha : raw35610step3 = raw35610step2 := by apply Matrix.ext; unfold raw35610step3 raw35610step2; decide +kernel
      have hl : raw35610step2Labels = labelEmbedding6 ∘ raw35610step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35610step2 raw35610step2Labels raw35610step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

def raw35611 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw35611Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35611step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw35611step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35611step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw35611step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35611step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw35611step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35611 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35611 raw35611Labels = mixedMoment B node5387 node5387Labels := by
  calc
    mixedMoment B raw35611 raw35611Labels = mixedMoment B raw35611step0 raw35611step0Labels := by
      have hz : ∀ j, raw35611 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35611step0 = (fun i j => raw35611 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35611step0 raw35611; decide +kernel
      have hl : raw35611step0Labels = raw35611Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35611 raw35611Labels permutation346 hz
    mixedMoment B raw35611step0 raw35611step0Labels = mixedMoment B raw35611step1 raw35611step1Labels := by
      have ha : raw35611step1 = (fun i j => raw35611step0 (permutation59 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35611step1 raw35611step0; decide +kernel
      have hl : raw35611step1Labels = raw35611step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35611step0 raw35611step0Labels permutation59 permutation3
    mixedMoment B raw35611step1 raw35611step1Labels = mixedMoment B raw35611step2 raw35611step2Labels := by
      have ha : raw35611step2 = raw35611step1 := by apply Matrix.ext; unfold raw35611step2 raw35611step1; decide +kernel
      have hl : raw35611step1Labels = labelEmbedding6 ∘ raw35611step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35611step1 raw35611step1Labels raw35611step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5387 node5387Labels := by rfl

def raw35612 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw35612Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35612step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw35612step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35612step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw35612step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35612step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw35612step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35612 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35612 raw35612Labels = mixedMoment B node4681 node4681Labels := by
  calc
    mixedMoment B raw35612 raw35612Labels = mixedMoment B raw35612step0 raw35612step0Labels := by
      have hz : ∀ j, raw35612 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35612step0 = (fun i j => raw35612 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35612step0 raw35612; decide +kernel
      have hl : raw35612step0Labels = raw35612Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35612 raw35612Labels permutation346 hz
    mixedMoment B raw35612step0 raw35612step0Labels = mixedMoment B raw35612step1 raw35612step1Labels := by
      have ha : raw35612step1 = (fun i j => raw35612step0 (permutation58 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35612step1 raw35612step0; decide +kernel
      have hl : raw35612step1Labels = raw35612step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35612step0 raw35612step0Labels permutation58 permutation3
    mixedMoment B raw35612step1 raw35612step1Labels = mixedMoment B raw35612step2 raw35612step2Labels := by
      have ha : raw35612step2 = raw35612step1 := by apply Matrix.ext; unfold raw35612step2 raw35612step1; decide +kernel
      have hl : raw35612step1Labels = labelEmbedding6 ∘ raw35612step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35612step1 raw35612step1Labels raw35612step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4681 node4681Labels := by rfl

def raw35613 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw35613Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35613step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35613step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35613step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35613step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35613step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35613step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35613 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35613 raw35613Labels = mixedMoment B node5038 node5038Labels := by
  calc
    mixedMoment B raw35613 raw35613Labels = mixedMoment B raw35613step0 raw35613step0Labels := by
      have ha : raw35613step0 = (fun i j => raw35613 (permutation663 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35613step0 raw35613; decide +kernel
      have hl : raw35613step0Labels = raw35613Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35613 raw35613Labels permutation663 permutation3
    mixedMoment B raw35613step0 raw35613step0Labels = mixedMoment B raw35613step1 raw35613step1Labels := by
      have ha : raw35613step1 = -raw35613step0 := by apply Matrix.ext; change ∀ i j, raw35613step1 i j = -(raw35613step0 i j); unfold raw35613step1 raw35613step0; decide +kernel
      have hl : raw35613step1Labels = raw35613step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35613step1 raw35613step1Labels = mixedMoment B raw35613step2 raw35613step2Labels := by
      have ha : raw35613step2 = raw35613step1 := by apply Matrix.ext; unfold raw35613step2 raw35613step1; decide +kernel
      have hl : raw35613step1Labels = labelEmbedding6 ∘ raw35613step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35613step1 raw35613step1Labels raw35613step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5038 node5038Labels := by rfl

def raw35614 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw35614Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35614step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 1, -1], ![3, -2, -1]]
def raw35614step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35614step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35614step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35614step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35614step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35614step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35614step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35614 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35614 raw35614Labels = mixedMoment B node5080 node5080Labels := by
  calc
    mixedMoment B raw35614 raw35614Labels = mixedMoment B raw35614step0 raw35614step0Labels := by
      have hz : ∀ j, raw35614 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35614step0 = (fun i j => raw35614 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35614step0 raw35614; decide +kernel
      have hl : raw35614step0Labels = raw35614Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35614 raw35614Labels permutation346 hz
    mixedMoment B raw35614step0 raw35614step0Labels = mixedMoment B raw35614step1 raw35614step1Labels := by
      have ha : raw35614step1 = (fun i j => raw35614step0 (permutation144 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35614step1 raw35614step0; decide +kernel
      have hl : raw35614step1Labels = raw35614step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35614step0 raw35614step0Labels permutation144 permutation3
    mixedMoment B raw35614step1 raw35614step1Labels = mixedMoment B raw35614step2 raw35614step2Labels := by
      have ha : raw35614step2 = -raw35614step1 := by apply Matrix.ext; change ∀ i j, raw35614step2 i j = -(raw35614step1 i j); unfold raw35614step2 raw35614step1; decide +kernel
      have hl : raw35614step2Labels = raw35614step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35614step2 raw35614step2Labels = mixedMoment B raw35614step3 raw35614step3Labels := by
      have ha : raw35614step3 = raw35614step2 := by apply Matrix.ext; unfold raw35614step3 raw35614step2; decide +kernel
      have hl : raw35614step2Labels = labelEmbedding6 ∘ raw35614step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35614step2 raw35614step2Labels raw35614step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5080 node5080Labels := by rfl

def raw35615 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw35615Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35615step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw35615step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35615step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35615step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35615step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35615step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35615 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35615 raw35615Labels = mixedMoment B node5465 node5465Labels := by
  calc
    mixedMoment B raw35615 raw35615Labels = mixedMoment B raw35615step0 raw35615step0Labels := by
      have hz : ∀ j, raw35615 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35615step0 = (fun i j => raw35615 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35615step0 raw35615; decide +kernel
      have hl : raw35615step0Labels = raw35615Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35615 raw35615Labels permutation346 hz
    mixedMoment B raw35615step0 raw35615step0Labels = mixedMoment B raw35615step1 raw35615step1Labels := by
      have ha : raw35615step1 = (fun i j => raw35615step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35615step1 raw35615step0; decide +kernel
      have hl : raw35615step1Labels = raw35615step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35615step0 raw35615step0Labels permutation32 permutation6
    mixedMoment B raw35615step1 raw35615step1Labels = mixedMoment B raw35615step2 raw35615step2Labels := by
      have ha : raw35615step2 = raw35615step1 := by apply Matrix.ext; unfold raw35615step2 raw35615step1; decide +kernel
      have hl : raw35615step1Labels = labelEmbedding9 ∘ raw35615step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35615step1 raw35615step1Labels raw35615step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5465 node5465Labels := by rfl

def raw35616 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw35616Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35616step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35616step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35616step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35616step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35616 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35616 raw35616Labels = mixedMoment B node5352 node5352Labels := by
  calc
    mixedMoment B raw35616 raw35616Labels = mixedMoment B raw35616step0 raw35616step0Labels := by
      have ha : raw35616step0 = (fun i j => raw35616 (permutation267 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35616step0 raw35616; decide +kernel
      have hl : raw35616step0Labels = raw35616Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35616 raw35616Labels permutation267 permutation7
    mixedMoment B raw35616step0 raw35616step0Labels = mixedMoment B raw35616step1 raw35616step1Labels := by
      have ha : raw35616step1 = raw35616step0 := by apply Matrix.ext; unfold raw35616step1 raw35616step0; decide +kernel
      have hl : raw35616step0Labels = labelEmbedding10 ∘ raw35616step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35616step0 raw35616step0Labels raw35616step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5352 node5352Labels := by rfl

def raw35617 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw35617Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35617step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-2, 1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw35617step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35617step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35617step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35617step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35617step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35617 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35617 raw35617Labels = mixedMoment B node5368 node5368Labels := by
  calc
    mixedMoment B raw35617 raw35617Labels = mixedMoment B raw35617step0 raw35617step0Labels := by
      have hz : ∀ j, raw35617 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35617step0 = (fun i j => raw35617 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35617step0 raw35617; decide +kernel
      have hl : raw35617step0Labels = raw35617Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35617 raw35617Labels permutation346 hz
    mixedMoment B raw35617step0 raw35617step0Labels = mixedMoment B raw35617step1 raw35617step1Labels := by
      have ha : raw35617step1 = (fun i j => raw35617step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35617step1 raw35617step0; decide +kernel
      have hl : raw35617step1Labels = raw35617step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35617step0 raw35617step0Labels permutation58 permutation7
    mixedMoment B raw35617step1 raw35617step1Labels = mixedMoment B raw35617step2 raw35617step2Labels := by
      have ha : raw35617step2 = raw35617step1 := by apply Matrix.ext; unfold raw35617step2 raw35617step1; decide +kernel
      have hl : raw35617step1Labels = labelEmbedding10 ∘ raw35617step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35617step1 raw35617step1Labels raw35617step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5368 node5368Labels := by rfl

def raw35618 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw35618Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35618step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw35618step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35618step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35618step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35618step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35618step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35618 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35618 raw35618Labels = mixedMoment B node5367 node5367Labels := by
  calc
    mixedMoment B raw35618 raw35618Labels = mixedMoment B raw35618step0 raw35618step0Labels := by
      have hz : ∀ j, raw35618 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35618step0 = (fun i j => raw35618 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35618step0 raw35618; decide +kernel
      have hl : raw35618step0Labels = raw35618Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35618 raw35618Labels permutation346 hz
    mixedMoment B raw35618step0 raw35618step0Labels = mixedMoment B raw35618step1 raw35618step1Labels := by
      have ha : raw35618step1 = (fun i j => raw35618step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35618step1 raw35618step0; decide +kernel
      have hl : raw35618step1Labels = raw35618step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35618step0 raw35618step0Labels permutation58 permutation7
    mixedMoment B raw35618step1 raw35618step1Labels = mixedMoment B raw35618step2 raw35618step2Labels := by
      have ha : raw35618step2 = raw35618step1 := by apply Matrix.ext; unfold raw35618step2 raw35618step1; decide +kernel
      have hl : raw35618step1Labels = labelEmbedding10 ∘ raw35618step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35618step1 raw35618step1Labels raw35618step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5367 node5367Labels := by rfl

def raw35619 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -1, -2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw35619Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35619step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -1, -2], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw35619step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35619step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2]]
def raw35619step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35619step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw35619step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35619 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35619 raw35619Labels = mixedMoment B node5288 node5288Labels := by
  calc
    mixedMoment B raw35619 raw35619Labels = mixedMoment B raw35619step0 raw35619step0Labels := by
      have hz : ∀ j, raw35619 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35619step0 = (fun i j => raw35619 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35619step0 raw35619; decide +kernel
      have hl : raw35619step0Labels = raw35619Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35619 raw35619Labels permutation346 hz
    mixedMoment B raw35619step0 raw35619step0Labels = mixedMoment B raw35619step1 raw35619step1Labels := by
      have ha : raw35619step1 = (fun i j => raw35619step0 (permutation68 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35619step1 raw35619step0; decide +kernel
      have hl : raw35619step1Labels = raw35619step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35619step0 raw35619step0Labels permutation68 permutation2
    mixedMoment B raw35619step1 raw35619step1Labels = mixedMoment B raw35619step2 raw35619step2Labels := by
      have ha : raw35619step2 = -raw35619step1 := by apply Matrix.ext; change ∀ i j, raw35619step2 i j = -(raw35619step1 i j); unfold raw35619step2 raw35619step1; decide +kernel
      have hl : raw35619step2Labels = raw35619step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5288 node5288Labels := by rfl

def raw35620 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw35620Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35620step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw35620step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35620step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35620step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35620 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35620 raw35620Labels = mixedMoment B node5226 node5226Labels := by
  calc
    mixedMoment B raw35620 raw35620Labels = mixedMoment B raw35620step0 raw35620step0Labels := by
      have ha : raw35620step0 = (fun i j => raw35620 (permutation277 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35620step0 raw35620; decide +kernel
      have hl : raw35620step0Labels = raw35620Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35620 raw35620Labels permutation277 permutation2
    mixedMoment B raw35620step0 raw35620step0Labels = mixedMoment B raw35620step1 raw35620step1Labels := by
      have ha : raw35620step1 = -raw35620step0 := by apply Matrix.ext; change ∀ i j, raw35620step1 i j = -(raw35620step0 i j); unfold raw35620step1 raw35620step0; decide +kernel
      have hl : raw35620step1Labels = raw35620step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5226 node5226Labels := by rfl

def raw35621 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw35621Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35621step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![-2, 1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw35621step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35621step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw35621step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35621step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw35621step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35621 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35621 raw35621Labels = mixedMoment B node5229 node5229Labels := by
  calc
    mixedMoment B raw35621 raw35621Labels = mixedMoment B raw35621step0 raw35621step0Labels := by
      have hz : ∀ j, raw35621 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35621step0 = (fun i j => raw35621 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35621step0 raw35621; decide +kernel
      have hl : raw35621step0Labels = raw35621Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35621 raw35621Labels permutation346 hz
    mixedMoment B raw35621step0 raw35621step0Labels = mixedMoment B raw35621step1 raw35621step1Labels := by
      have ha : raw35621step1 = (fun i j => raw35621step0 (permutation59 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35621step1 raw35621step0; decide +kernel
      have hl : raw35621step1Labels = raw35621step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35621step0 raw35621step0Labels permutation59 permutation2
    mixedMoment B raw35621step1 raw35621step1Labels = mixedMoment B raw35621step2 raw35621step2Labels := by
      have ha : raw35621step2 = -raw35621step1 := by apply Matrix.ext; change ∀ i j, raw35621step2 i j = -(raw35621step1 i j); unfold raw35621step2 raw35621step1; decide +kernel
      have hl : raw35621step2Labels = raw35621step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5229 node5229Labels := by rfl

def raw35622 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw35622Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35622step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -1, -2], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw35622step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35622step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw35622step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35622step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35622step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35622 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35622 raw35622Labels = mixedMoment B node5228 node5228Labels := by
  calc
    mixedMoment B raw35622 raw35622Labels = mixedMoment B raw35622step0 raw35622step0Labels := by
      have hz : ∀ j, raw35622 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35622step0 = (fun i j => raw35622 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35622step0 raw35622; decide +kernel
      have hl : raw35622step0Labels = raw35622Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35622 raw35622Labels permutation346 hz
    mixedMoment B raw35622step0 raw35622step0Labels = mixedMoment B raw35622step1 raw35622step1Labels := by
      have ha : raw35622step1 = (fun i j => raw35622step0 (permutation58 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35622step1 raw35622step0; decide +kernel
      have hl : raw35622step1Labels = raw35622step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35622step0 raw35622step0Labels permutation58 permutation2
    mixedMoment B raw35622step1 raw35622step1Labels = mixedMoment B raw35622step2 raw35622step2Labels := by
      have ha : raw35622step2 = -raw35622step1 := by apply Matrix.ext; change ∀ i j, raw35622step2 i j = -(raw35622step1 i j); unfold raw35622step2 raw35622step1; decide +kernel
      have hl : raw35622step2Labels = raw35622step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5228 node5228Labels := by rfl

def raw35623 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw35623Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35623step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw35623step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35623step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35623step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35623step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35623step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35623 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35623 raw35623Labels = mixedMoment B node5226 node5226Labels := by
  calc
    mixedMoment B raw35623 raw35623Labels = mixedMoment B raw35623step0 raw35623step0Labels := by
      have ha : raw35623step0 = (fun i j => raw35623 (permutation158 i) (permutation4 j)) := by apply Matrix.ext; unfold raw35623step0 raw35623; decide +kernel
      have hl : raw35623step0Labels = raw35623Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35623 raw35623Labels permutation158 permutation4
    mixedMoment B raw35623step0 raw35623step0Labels = mixedMoment B raw35623step1 raw35623step1Labels := by
      have ha : raw35623step1 = -raw35623step0 := by apply Matrix.ext; change ∀ i j, raw35623step1 i j = -(raw35623step0 i j); unfold raw35623step1 raw35623step0; decide +kernel
      have hl : raw35623step1Labels = raw35623step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35623step1 raw35623step1Labels = mixedMoment B raw35623step2 raw35623step2Labels := by
      have ha : raw35623step2 = raw35623step1 := by apply Matrix.ext; unfold raw35623step2 raw35623step1; decide +kernel
      have hl : raw35623step1Labels = labelEmbedding7 ∘ raw35623step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35623step1 raw35623step1Labels raw35623step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5226 node5226Labels := by rfl

def raw35624 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw35624Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35624step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35624step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35624step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw35624step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35624 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35624 raw35624Labels = mixedMoment B node5352 node5352Labels := by
  calc
    mixedMoment B raw35624 raw35624Labels = mixedMoment B raw35624step0 raw35624step0Labels := by
      have ha : raw35624step0 = (fun i j => raw35624 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35624step0 raw35624; decide +kernel
      have hl : raw35624step0Labels = raw35624Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35624 raw35624Labels permutation152 permutation6
    mixedMoment B raw35624step0 raw35624step0Labels = mixedMoment B raw35624step1 raw35624step1Labels := by
      have ha : raw35624step1 = raw35624step0 := by apply Matrix.ext; unfold raw35624step1 raw35624step0; decide +kernel
      have hl : raw35624step0Labels = labelEmbedding9 ∘ raw35624step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35624step0 raw35624step0Labels raw35624step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5352 node5352Labels := by rfl

def raw35625 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw35625Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35625step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35625step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35625step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35625step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35625 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35625 raw35625Labels = mixedMoment B node5379 node5379Labels := by
  calc
    mixedMoment B raw35625 raw35625Labels = mixedMoment B raw35625step0 raw35625step0Labels := by
      have ha : raw35625step0 = (fun i j => raw35625 (permutation267 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35625step0 raw35625; decide +kernel
      have hl : raw35625step0Labels = raw35625Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35625 raw35625Labels permutation267 permutation7
    mixedMoment B raw35625step0 raw35625step0Labels = mixedMoment B raw35625step1 raw35625step1Labels := by
      have ha : raw35625step1 = raw35625step0 := by apply Matrix.ext; unfold raw35625step1 raw35625step0; decide +kernel
      have hl : raw35625step0Labels = labelEmbedding10 ∘ raw35625step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35625step0 raw35625step0Labels raw35625step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5379 node5379Labels := by rfl

def raw35626 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw35626Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35626step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35626step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35626step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35626step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35626 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35626 raw35626Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw35626 raw35626Labels = mixedMoment B raw35626step0 raw35626step0Labels := by
      have ha : raw35626step0 = (fun i j => raw35626 (permutation267 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35626step0 raw35626; decide +kernel
      have hl : raw35626step0Labels = raw35626Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35626 raw35626Labels permutation267 permutation7
    mixedMoment B raw35626step0 raw35626step0Labels = mixedMoment B raw35626step1 raw35626step1Labels := by
      have ha : raw35626step1 = raw35626step0 := by apply Matrix.ext; unfold raw35626step1 raw35626step0; decide +kernel
      have hl : raw35626step0Labels = labelEmbedding10 ∘ raw35626step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35626step0 raw35626step0Labels raw35626step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

def raw35627 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw35627Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35627step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw35627step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35627step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw35627step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35627step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35627step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35627step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw35627step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35627 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35627 raw35627Labels = mixedMoment B node5237 node5237Labels := by
  calc
    mixedMoment B raw35627 raw35627Labels = mixedMoment B raw35627step0 raw35627step0Labels := by
      have hz : ∀ j, raw35627 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35627step0 = (fun i j => raw35627 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35627step0 raw35627; decide +kernel
      have hl : raw35627step0Labels = raw35627Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35627 raw35627Labels permutation346 hz
    mixedMoment B raw35627step0 raw35627step0Labels = mixedMoment B raw35627step1 raw35627step1Labels := by
      have ha : raw35627step1 = (fun i j => raw35627step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw35627step1 raw35627step0; decide +kernel
      have hl : raw35627step1Labels = raw35627step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35627step0 raw35627step0Labels permutation32 permutation4
    mixedMoment B raw35627step1 raw35627step1Labels = mixedMoment B raw35627step2 raw35627step2Labels := by
      have ha : raw35627step2 = -raw35627step1 := by apply Matrix.ext; change ∀ i j, raw35627step2 i j = -(raw35627step1 i j); unfold raw35627step2 raw35627step1; decide +kernel
      have hl : raw35627step2Labels = raw35627step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35627step2 raw35627step2Labels = mixedMoment B raw35627step3 raw35627step3Labels := by
      have ha : raw35627step3 = raw35627step2 := by apply Matrix.ext; unfold raw35627step3 raw35627step2; decide +kernel
      have hl : raw35627step2Labels = labelEmbedding7 ∘ raw35627step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35627step2 raw35627step2Labels raw35627step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5237 node5237Labels := by rfl

def raw35628 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw35628Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35628step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw35628step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35628step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35628step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35628step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35628step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35628 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35628 raw35628Labels = mixedMoment B node5369 node5369Labels := by
  calc
    mixedMoment B raw35628 raw35628Labels = mixedMoment B raw35628step0 raw35628step0Labels := by
      have hz : ∀ j, raw35628 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35628step0 = (fun i j => raw35628 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35628step0 raw35628; decide +kernel
      have hl : raw35628step0Labels = raw35628Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35628 raw35628Labels permutation346 hz
    mixedMoment B raw35628step0 raw35628step0Labels = mixedMoment B raw35628step1 raw35628step1Labels := by
      have ha : raw35628step1 = (fun i j => raw35628step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35628step1 raw35628step0; decide +kernel
      have hl : raw35628step1Labels = raw35628step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35628step0 raw35628step0Labels permutation32 permutation6
    mixedMoment B raw35628step1 raw35628step1Labels = mixedMoment B raw35628step2 raw35628step2Labels := by
      have ha : raw35628step2 = raw35628step1 := by apply Matrix.ext; unfold raw35628step2 raw35628step1; decide +kernel
      have hl : raw35628step1Labels = labelEmbedding9 ∘ raw35628step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35628step1 raw35628step1Labels raw35628step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5369 node5369Labels := by rfl

def raw35629 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw35629Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35629step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35629step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35629step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw35629step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35629 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35629 raw35629Labels = mixedMoment B node5380 node5380Labels := by
  calc
    mixedMoment B raw35629 raw35629Labels = mixedMoment B raw35629step0 raw35629step0Labels := by
      have ha : raw35629step0 = (fun i j => raw35629 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35629step0 raw35629; decide +kernel
      have hl : raw35629step0Labels = raw35629Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35629 raw35629Labels permutation152 permutation6
    mixedMoment B raw35629step0 raw35629step0Labels = mixedMoment B raw35629step1 raw35629step1Labels := by
      have ha : raw35629step1 = raw35629step0 := by apply Matrix.ext; unfold raw35629step1 raw35629step0; decide +kernel
      have hl : raw35629step0Labels = labelEmbedding9 ∘ raw35629step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35629step0 raw35629step0Labels raw35629step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5380 node5380Labels := by rfl

def raw35630 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw35630Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35630step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw35630step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35630step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw35630step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35630step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw35630step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35630 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35630 raw35630Labels = mixedMoment B node5387 node5387Labels := by
  calc
    mixedMoment B raw35630 raw35630Labels = mixedMoment B raw35630step0 raw35630step0Labels := by
      have hz : ∀ j, raw35630 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35630step0 = (fun i j => raw35630 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35630step0 raw35630; decide +kernel
      have hl : raw35630step0Labels = raw35630Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35630 raw35630Labels permutation346 hz
    mixedMoment B raw35630step0 raw35630step0Labels = mixedMoment B raw35630step1 raw35630step1Labels := by
      have ha : raw35630step1 = (fun i j => raw35630step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35630step1 raw35630step0; decide +kernel
      have hl : raw35630step1Labels = raw35630step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35630step0 raw35630step0Labels permutation56 permutation7
    mixedMoment B raw35630step1 raw35630step1Labels = mixedMoment B raw35630step2 raw35630step2Labels := by
      have ha : raw35630step2 = raw35630step1 := by apply Matrix.ext; unfold raw35630step2 raw35630step1; decide +kernel
      have hl : raw35630step1Labels = labelEmbedding10 ∘ raw35630step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35630step1 raw35630step1Labels raw35630step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5387 node5387Labels := by rfl

def raw35631 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw35631Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35631step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, 0, -2], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw35631step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35631step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw35631step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35631step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw35631step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw35631step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw35631step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35631 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35631 raw35631Labels = mixedMoment B node5229 node5229Labels := by
  calc
    mixedMoment B raw35631 raw35631Labels = mixedMoment B raw35631step0 raw35631step0Labels := by
      have hz : ∀ j, raw35631 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35631step0 = (fun i j => raw35631 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35631step0 raw35631; decide +kernel
      have hl : raw35631step0Labels = raw35631Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35631 raw35631Labels permutation346 hz
    mixedMoment B raw35631step0 raw35631step0Labels = mixedMoment B raw35631step1 raw35631step1Labels := by
      have ha : raw35631step1 = (fun i j => raw35631step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw35631step1 raw35631step0; decide +kernel
      have hl : raw35631step1Labels = raw35631step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35631step0 raw35631step0Labels permutation33 permutation4
    mixedMoment B raw35631step1 raw35631step1Labels = mixedMoment B raw35631step2 raw35631step2Labels := by
      have ha : raw35631step2 = -raw35631step1 := by apply Matrix.ext; change ∀ i j, raw35631step2 i j = -(raw35631step1 i j); unfold raw35631step2 raw35631step1; decide +kernel
      have hl : raw35631step2Labels = raw35631step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35631step2 raw35631step2Labels = mixedMoment B raw35631step3 raw35631step3Labels := by
      have ha : raw35631step3 = raw35631step2 := by apply Matrix.ext; unfold raw35631step3 raw35631step2; decide +kernel
      have hl : raw35631step2Labels = labelEmbedding7 ∘ raw35631step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35631step2 raw35631step2Labels raw35631step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5229 node5229Labels := by rfl

def raw35632 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw35632Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35632step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw35632step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35632step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35632step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35632step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35632step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35632 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35632 raw35632Labels = mixedMoment B node5368 node5368Labels := by
  calc
    mixedMoment B raw35632 raw35632Labels = mixedMoment B raw35632step0 raw35632step0Labels := by
      have hz : ∀ j, raw35632 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35632step0 = (fun i j => raw35632 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35632step0 raw35632; decide +kernel
      have hl : raw35632step0Labels = raw35632Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35632 raw35632Labels permutation346 hz
    mixedMoment B raw35632step0 raw35632step0Labels = mixedMoment B raw35632step1 raw35632step1Labels := by
      have ha : raw35632step1 = (fun i j => raw35632step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35632step1 raw35632step0; decide +kernel
      have hl : raw35632step1Labels = raw35632step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35632step0 raw35632step0Labels permutation32 permutation6
    mixedMoment B raw35632step1 raw35632step1Labels = mixedMoment B raw35632step2 raw35632step2Labels := by
      have ha : raw35632step2 = raw35632step1 := by apply Matrix.ext; unfold raw35632step2 raw35632step1; decide +kernel
      have hl : raw35632step1Labels = labelEmbedding9 ∘ raw35632step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35632step1 raw35632step1Labels raw35632step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5368 node5368Labels := by rfl

def raw35633 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw35633Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35633step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35633step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35633step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw35633step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35633 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35633 raw35633Labels = mixedMoment B node5379 node5379Labels := by
  calc
    mixedMoment B raw35633 raw35633Labels = mixedMoment B raw35633step0 raw35633step0Labels := by
      have ha : raw35633step0 = (fun i j => raw35633 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35633step0 raw35633; decide +kernel
      have hl : raw35633step0Labels = raw35633Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35633 raw35633Labels permutation152 permutation6
    mixedMoment B raw35633step0 raw35633step0Labels = mixedMoment B raw35633step1 raw35633step1Labels := by
      have ha : raw35633step1 = raw35633step0 := by apply Matrix.ext; unfold raw35633step1 raw35633step0; decide +kernel
      have hl : raw35633step0Labels = labelEmbedding9 ∘ raw35633step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35633step0 raw35633step0Labels raw35633step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5379 node5379Labels := by rfl

def raw35634 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![-2, 1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw35634Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35634step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-2, 1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw35634step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35634step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw35634step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35634step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw35634step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35634 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35634 raw35634Labels = mixedMoment B node5385 node5385Labels := by
  calc
    mixedMoment B raw35634 raw35634Labels = mixedMoment B raw35634step0 raw35634step0Labels := by
      have hz : ∀ j, raw35634 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35634step0 = (fun i j => raw35634 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35634step0 raw35634; decide +kernel
      have hl : raw35634step0Labels = raw35634Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35634 raw35634Labels permutation346 hz
    mixedMoment B raw35634step0 raw35634step0Labels = mixedMoment B raw35634step1 raw35634step1Labels := by
      have ha : raw35634step1 = (fun i j => raw35634step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35634step1 raw35634step0; decide +kernel
      have hl : raw35634step1Labels = raw35634step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35634step0 raw35634step0Labels permutation32 permutation6
    mixedMoment B raw35634step1 raw35634step1Labels = mixedMoment B raw35634step2 raw35634step2Labels := by
      have ha : raw35634step2 = raw35634step1 := by apply Matrix.ext; unfold raw35634step2 raw35634step1; decide +kernel
      have hl : raw35634step1Labels = labelEmbedding9 ∘ raw35634step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35634step1 raw35634step1Labels raw35634step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5385 node5385Labels := by rfl

def raw35635 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw35635Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35635step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw35635step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35635step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35635step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw35635step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35635step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35635 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35635 raw35635Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw35635 raw35635Labels = mixedMoment B raw35635step0 raw35635step0Labels := by
      have hz : ∀ j, raw35635 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35635step0 = (fun i j => raw35635 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35635step0 raw35635; decide +kernel
      have hl : raw35635step0Labels = raw35635Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35635 raw35635Labels permutation346 hz
    mixedMoment B raw35635step0 raw35635step0Labels = mixedMoment B raw35635step1 raw35635step1Labels := by
      have ha : raw35635step1 = (fun i j => raw35635step0 (permutation58 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35635step1 raw35635step0; decide +kernel
      have hl : raw35635step1Labels = raw35635step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35635step0 raw35635step0Labels permutation58 permutation7
    mixedMoment B raw35635step1 raw35635step1Labels = mixedMoment B raw35635step2 raw35635step2Labels := by
      have ha : raw35635step2 = raw35635step1 := by apply Matrix.ext; unfold raw35635step2 raw35635step1; decide +kernel
      have hl : raw35635step1Labels = labelEmbedding10 ∘ raw35635step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35635step1 raw35635step1Labels raw35635step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5384 node5384Labels := by rfl

def raw35636 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw35636Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35636step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, 0, -2], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw35636step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35636step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw35636step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw35636step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw35636step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35636 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35636 raw35636Labels = mixedMoment B node5387 node5387Labels := by
  calc
    mixedMoment B raw35636 raw35636Labels = mixedMoment B raw35636step0 raw35636step0Labels := by
      have hz : ∀ j, raw35636 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35636step0 = (fun i j => raw35636 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35636step0 raw35636; decide +kernel
      have hl : raw35636step0Labels = raw35636Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35636 raw35636Labels permutation346 hz
    mixedMoment B raw35636step0 raw35636step0Labels = mixedMoment B raw35636step1 raw35636step1Labels := by
      have ha : raw35636step1 = (fun i j => raw35636step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw35636step1 raw35636step0; decide +kernel
      have hl : raw35636step1Labels = raw35636step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35636step0 raw35636step0Labels permutation32 permutation6
    mixedMoment B raw35636step1 raw35636step1Labels = mixedMoment B raw35636step2 raw35636step2Labels := by
      have ha : raw35636step2 = raw35636step1 := by apply Matrix.ext; unfold raw35636step2 raw35636step1; decide +kernel
      have hl : raw35636step1Labels = labelEmbedding9 ∘ raw35636step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35636step1 raw35636step1Labels raw35636step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5387 node5387Labels := by rfl

def raw35637 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw35637Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35637step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw35637step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35637step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35637step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35637step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35637step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35637 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35637 raw35637Labels = mixedMoment B node4860 node4860Labels := by
  calc
    mixedMoment B raw35637 raw35637Labels = mixedMoment B raw35637step0 raw35637step0Labels := by
      have hz : ∀ j, raw35637 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35637step0 = (fun i j => raw35637 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35637step0 raw35637; decide +kernel
      have hl : raw35637step0Labels = raw35637Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35637 raw35637Labels permutation346 hz
    mixedMoment B raw35637step0 raw35637step0Labels = mixedMoment B raw35637step1 raw35637step1Labels := by
      have ha : raw35637step1 = (fun i j => raw35637step0 (permutation58 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35637step1 raw35637step0; decide +kernel
      have hl : raw35637step1Labels = raw35637step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35637step0 raw35637step0Labels permutation58 permutation3
    mixedMoment B raw35637step1 raw35637step1Labels = mixedMoment B raw35637step2 raw35637step2Labels := by
      have ha : raw35637step2 = raw35637step1 := by apply Matrix.ext; unfold raw35637step2 raw35637step1; decide +kernel
      have hl : raw35637step1Labels = labelEmbedding6 ∘ raw35637step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35637step1 raw35637step1Labels raw35637step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4860 node4860Labels := by rfl

def raw35638 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw35638Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35638step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35638step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35638step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35638step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35638 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35638 raw35638Labels = mixedMoment B node5398 node5398Labels := by
  calc
    mixedMoment B raw35638 raw35638Labels = mixedMoment B raw35638step0 raw35638step0Labels := by
      have ha : raw35638step0 = (fun i j => raw35638 (permutation291 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35638step0 raw35638; decide +kernel
      have hl : raw35638step0Labels = raw35638Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35638 raw35638Labels permutation291 permutation3
    mixedMoment B raw35638step0 raw35638step0Labels = mixedMoment B raw35638step1 raw35638step1Labels := by
      have ha : raw35638step1 = raw35638step0 := by apply Matrix.ext; unfold raw35638step1 raw35638step0; decide +kernel
      have hl : raw35638step0Labels = labelEmbedding6 ∘ raw35638step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35638step0 raw35638step0Labels raw35638step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5398 node5398Labels := by rfl

def raw35639 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw35639Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35639step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw35639step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35639step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw35639step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35639step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35639step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35639step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35639step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35639 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35639 raw35639Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw35639 raw35639Labels = mixedMoment B raw35639step0 raw35639step0Labels := by
      have hz : ∀ j, raw35639 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35639step0 = (fun i j => raw35639 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35639step0 raw35639; decide +kernel
      have hl : raw35639step0Labels = raw35639Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35639 raw35639Labels permutation346 hz
    mixedMoment B raw35639step0 raw35639step0Labels = mixedMoment B raw35639step1 raw35639step1Labels := by
      have ha : raw35639step1 = (fun i j => raw35639step0 (permutation68 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35639step1 raw35639step0; decide +kernel
      have hl : raw35639step1Labels = raw35639step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35639step0 raw35639step0Labels permutation68 permutation5
    mixedMoment B raw35639step1 raw35639step1Labels = mixedMoment B raw35639step2 raw35639step2Labels := by
      have ha : raw35639step2 = -raw35639step1 := by apply Matrix.ext; change ∀ i j, raw35639step2 i j = -(raw35639step1 i j); unfold raw35639step2 raw35639step1; decide +kernel
      have hl : raw35639step2Labels = raw35639step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35639step2 raw35639step2Labels = mixedMoment B raw35639step3 raw35639step3Labels := by
      have ha : raw35639step3 = raw35639step2 := by apply Matrix.ext; unfold raw35639step3 raw35639step2; decide +kernel
      have hl : raw35639step2Labels = labelEmbedding8 ∘ raw35639step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35639step2 raw35639step2Labels raw35639step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5384 node5384Labels := by rfl

def raw35640 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw35640Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35640step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw35640step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35640step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw35640step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35640step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw35640step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35640 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35640 raw35640Labels = mixedMoment B node5448 node5448Labels := by
  calc
    mixedMoment B raw35640 raw35640Labels = mixedMoment B raw35640step0 raw35640step0Labels := by
      have hz : ∀ j, raw35640 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35640step0 = (fun i j => raw35640 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35640step0 raw35640; decide +kernel
      have hl : raw35640step0Labels = raw35640Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35640 raw35640Labels permutation346 hz
    mixedMoment B raw35640step0 raw35640step0Labels = mixedMoment B raw35640step1 raw35640step1Labels := by
      have ha : raw35640step1 = (fun i j => raw35640step0 (permutation58 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35640step1 raw35640step0; decide +kernel
      have hl : raw35640step1Labels = raw35640step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35640step0 raw35640step0Labels permutation58 permutation3
    mixedMoment B raw35640step1 raw35640step1Labels = mixedMoment B raw35640step2 raw35640step2Labels := by
      have ha : raw35640step2 = raw35640step1 := by apply Matrix.ext; unfold raw35640step2 raw35640step1; decide +kernel
      have hl : raw35640step1Labels = labelEmbedding6 ∘ raw35640step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35640step1 raw35640step1Labels raw35640step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5448 node5448Labels := by rfl

def raw35641 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw35641Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35641step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35641step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35641step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35641step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35641 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35641 raw35641Labels = mixedMoment B node4672 node4672Labels := by
  calc
    mixedMoment B raw35641 raw35641Labels = mixedMoment B raw35641step0 raw35641step0Labels := by
      have ha : raw35641step0 = (fun i j => raw35641 (permutation277 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35641step0 raw35641; decide +kernel
      have hl : raw35641step0Labels = raw35641Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35641 raw35641Labels permutation277 permutation3
    mixedMoment B raw35641step0 raw35641step0Labels = mixedMoment B raw35641step1 raw35641step1Labels := by
      have ha : raw35641step1 = raw35641step0 := by apply Matrix.ext; unfold raw35641step1 raw35641step0; decide +kernel
      have hl : raw35641step0Labels = labelEmbedding6 ∘ raw35641step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35641step0 raw35641step0Labels raw35641step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4672 node4672Labels := by rfl

def raw35642 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw35642Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35642step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35642step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35642step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35642step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35642 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35642 raw35642Labels = mixedMoment B node5374 node5374Labels := by
  calc
    mixedMoment B raw35642 raw35642Labels = mixedMoment B raw35642step0 raw35642step0Labels := by
      have ha : raw35642step0 = (fun i j => raw35642 (permutation277 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35642step0 raw35642; decide +kernel
      have hl : raw35642step0Labels = raw35642Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35642 raw35642Labels permutation277 permutation3
    mixedMoment B raw35642step0 raw35642step0Labels = mixedMoment B raw35642step1 raw35642step1Labels := by
      have ha : raw35642step1 = raw35642step0 := by apply Matrix.ext; unfold raw35642step1 raw35642step0; decide +kernel
      have hl : raw35642step0Labels = labelEmbedding6 ∘ raw35642step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35642step0 raw35642step0Labels raw35642step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5374 node5374Labels := by rfl

def raw35643 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw35643Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35643step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35643step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35643step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35643step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35643 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35643 raw35643Labels = mixedMoment B node5383 node5383Labels := by
  calc
    mixedMoment B raw35643 raw35643Labels = mixedMoment B raw35643step0 raw35643step0Labels := by
      have ha : raw35643step0 = (fun i j => raw35643 (permutation277 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35643step0 raw35643; decide +kernel
      have hl : raw35643step0Labels = raw35643Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35643 raw35643Labels permutation277 permutation3
    mixedMoment B raw35643step0 raw35643step0Labels = mixedMoment B raw35643step1 raw35643step1Labels := by
      have ha : raw35643step1 = raw35643step0 := by apply Matrix.ext; unfold raw35643step1 raw35643step0; decide +kernel
      have hl : raw35643step0Labels = labelEmbedding6 ∘ raw35643step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35643step0 raw35643step0Labels raw35643step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5383 node5383Labels := by rfl

def raw35644 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw35644Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35644step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw35644step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35644step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw35644step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35644step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw35644step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35644 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35644 raw35644Labels = mixedMoment B node4674 node4674Labels := by
  calc
    mixedMoment B raw35644 raw35644Labels = mixedMoment B raw35644step0 raw35644step0Labels := by
      have hz : ∀ j, raw35644 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35644step0 = (fun i j => raw35644 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35644step0 raw35644; decide +kernel
      have hl : raw35644step0Labels = raw35644Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35644 raw35644Labels permutation346 hz
    mixedMoment B raw35644step0 raw35644step0Labels = mixedMoment B raw35644step1 raw35644step1Labels := by
      have ha : raw35644step1 = (fun i j => raw35644step0 (permutation58 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35644step1 raw35644step0; decide +kernel
      have hl : raw35644step1Labels = raw35644step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35644step0 raw35644step0Labels permutation58 permutation3
    mixedMoment B raw35644step1 raw35644step1Labels = mixedMoment B raw35644step2 raw35644step2Labels := by
      have ha : raw35644step2 = raw35644step1 := by apply Matrix.ext; unfold raw35644step2 raw35644step1; decide +kernel
      have hl : raw35644step1Labels = labelEmbedding6 ∘ raw35644step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35644step1 raw35644step1Labels raw35644step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4674 node4674Labels := by rfl

def raw35645 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw35645Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35645step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35645step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35645step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35645step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35645step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35645step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35645 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35645 raw35645Labels = mixedMoment B node5318 node5318Labels := by
  calc
    mixedMoment B raw35645 raw35645Labels = mixedMoment B raw35645step0 raw35645step0Labels := by
      have ha : raw35645step0 = (fun i j => raw35645 (permutation518 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35645step0 raw35645; decide +kernel
      have hl : raw35645step0Labels = raw35645Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35645 raw35645Labels permutation518 permutation3
    mixedMoment B raw35645step0 raw35645step0Labels = mixedMoment B raw35645step1 raw35645step1Labels := by
      have ha : raw35645step1 = -raw35645step0 := by apply Matrix.ext; change ∀ i j, raw35645step1 i j = -(raw35645step0 i j); unfold raw35645step1 raw35645step0; decide +kernel
      have hl : raw35645step1Labels = raw35645step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35645step1 raw35645step1Labels = mixedMoment B raw35645step2 raw35645step2Labels := by
      have ha : raw35645step2 = raw35645step1 := by apply Matrix.ext; unfold raw35645step2 raw35645step1; decide +kernel
      have hl : raw35645step1Labels = labelEmbedding6 ∘ raw35645step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35645step1 raw35645step1Labels raw35645step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5318 node5318Labels := by rfl

def raw35646 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![0, 2, -2], ![2, -2, 0]]
def raw35646Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35646step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![0, 2, -2], ![2, -2, 0]]
def raw35646step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35646step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw35646step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35646step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw35646step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35646step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw35646step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35646 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35646 raw35646Labels = mixedMoment B node5329 node5329Labels := by
  calc
    mixedMoment B raw35646 raw35646Labels = mixedMoment B raw35646step0 raw35646step0Labels := by
      have hz : ∀ j, raw35646 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35646step0 = (fun i j => raw35646 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35646step0 raw35646; decide +kernel
      have hl : raw35646step0Labels = raw35646Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35646 raw35646Labels permutation346 hz
    mixedMoment B raw35646step0 raw35646step0Labels = mixedMoment B raw35646step1 raw35646step1Labels := by
      have ha : raw35646step1 = (fun i j => raw35646step0 (permutation102 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35646step1 raw35646step0; decide +kernel
      have hl : raw35646step1Labels = raw35646step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35646step0 raw35646step0Labels permutation102 permutation3
    mixedMoment B raw35646step1 raw35646step1Labels = mixedMoment B raw35646step2 raw35646step2Labels := by
      have ha : raw35646step2 = -raw35646step1 := by apply Matrix.ext; change ∀ i j, raw35646step2 i j = -(raw35646step1 i j); unfold raw35646step2 raw35646step1; decide +kernel
      have hl : raw35646step2Labels = raw35646step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35646step2 raw35646step2Labels = mixedMoment B raw35646step3 raw35646step3Labels := by
      have ha : raw35646step3 = raw35646step2 := by apply Matrix.ext; unfold raw35646step3 raw35646step2; decide +kernel
      have hl : raw35646step2Labels = labelEmbedding6 ∘ raw35646step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35646step2 raw35646step2Labels raw35646step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5329 node5329Labels := by rfl

def raw35647 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2], ![1, -1, 0]]
def raw35647Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35647step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![1, 1, -2], ![1, -1, 0]]
def raw35647step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35647step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35647step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35647step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35647step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35647 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35647 raw35647Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw35647 raw35647Labels = mixedMoment B raw35647step0 raw35647step0Labels := by
      have hz : ∀ j, raw35647 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35647step0 = (fun i j => raw35647 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35647step0 raw35647; decide +kernel
      have hl : raw35647step0Labels = raw35647Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35647 raw35647Labels permutation346 hz
    mixedMoment B raw35647step0 raw35647step0Labels = mixedMoment B raw35647step1 raw35647step1Labels := by
      have ha : raw35647step1 = (fun i j => raw35647step0 (permutation59 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35647step1 raw35647step0; decide +kernel
      have hl : raw35647step1Labels = raw35647step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35647step0 raw35647step0Labels permutation59 permutation3
    mixedMoment B raw35647step1 raw35647step1Labels = mixedMoment B raw35647step2 raw35647step2Labels := by
      have ha : raw35647step2 = raw35647step1 := by apply Matrix.ext; unfold raw35647step2 raw35647step1; decide +kernel
      have hl : raw35647step1Labels = labelEmbedding6 ∘ raw35647step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35647step1 raw35647step1Labels raw35647step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5384 node5384Labels := by rfl

def raw35648 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw35648Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35648step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw35648step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35648step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35648step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35648step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35648step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35648 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35648 raw35648Labels = mixedMoment B node4688 node4688Labels := by
  calc
    mixedMoment B raw35648 raw35648Labels = mixedMoment B raw35648step0 raw35648step0Labels := by
      have hz : ∀ j, raw35648 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35648step0 = (fun i j => raw35648 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35648step0 raw35648; decide +kernel
      have hl : raw35648step0Labels = raw35648Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35648 raw35648Labels permutation346 hz
    mixedMoment B raw35648step0 raw35648step0Labels = mixedMoment B raw35648step1 raw35648step1Labels := by
      have ha : raw35648step1 = (fun i j => raw35648step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35648step1 raw35648step0; decide +kernel
      have hl : raw35648step1Labels = raw35648step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35648step0 raw35648step0Labels permutation56 permutation3
    mixedMoment B raw35648step1 raw35648step1Labels = mixedMoment B raw35648step2 raw35648step2Labels := by
      have ha : raw35648step2 = raw35648step1 := by apply Matrix.ext; unfold raw35648step2 raw35648step1; decide +kernel
      have hl : raw35648step1Labels = labelEmbedding6 ∘ raw35648step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35648step1 raw35648step1Labels raw35648step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4688 node4688Labels := by rfl

def raw35649 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw35649Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35649step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35649step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35649step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35649step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35649 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35649 raw35649Labels = mixedMoment B node5372 node5372Labels := by
  calc
    mixedMoment B raw35649 raw35649Labels = mixedMoment B raw35649step0 raw35649step0Labels := by
      have ha : raw35649step0 = (fun i j => raw35649 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35649step0 raw35649; decide +kernel
      have hl : raw35649step0Labels = raw35649Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35649 raw35649Labels permutation265 permutation3
    mixedMoment B raw35649step0 raw35649step0Labels = mixedMoment B raw35649step1 raw35649step1Labels := by
      have ha : raw35649step1 = raw35649step0 := by apply Matrix.ext; unfold raw35649step1 raw35649step0; decide +kernel
      have hl : raw35649step0Labels = labelEmbedding6 ∘ raw35649step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35649step0 raw35649step0Labels raw35649step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5372 node5372Labels := by rfl

def raw35650 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw35650Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35650step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw35650step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35650step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw35650step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35650 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35650 raw35650Labels = mixedMoment B node5387 node5387Labels := by
  calc
    mixedMoment B raw35650 raw35650Labels = mixedMoment B raw35650step0 raw35650step0Labels := by
      have hz : ∀ j, raw35650 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35650step0 = (fun i j => raw35650 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35650step0 raw35650; decide +kernel
      have hl : raw35650step0Labels = raw35650Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35650 raw35650Labels permutation346 hz
    mixedMoment B raw35650step0 raw35650step0Labels = mixedMoment B raw35650step1 raw35650step1Labels := by
      have ha : raw35650step1 = (fun i j => raw35650step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35650step1 raw35650step0; decide +kernel
      have hl : raw35650step1Labels = raw35650step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35650step0 raw35650step0Labels permutation33 permutation2
    _ = mixedMoment B node5387 node5387Labels := by rfl

def raw35651 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw35651Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35651step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw35651step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35651step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw35651step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35651step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw35651step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35651 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35651 raw35651Labels = mixedMoment B node4673 node4673Labels := by
  calc
    mixedMoment B raw35651 raw35651Labels = mixedMoment B raw35651step0 raw35651step0Labels := by
      have hz : ∀ j, raw35651 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35651step0 = (fun i j => raw35651 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35651step0 raw35651; decide +kernel
      have hl : raw35651step0Labels = raw35651Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35651 raw35651Labels permutation346 hz
    mixedMoment B raw35651step0 raw35651step0Labels = mixedMoment B raw35651step1 raw35651step1Labels := by
      have ha : raw35651step1 = (fun i j => raw35651step0 (permutation58 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35651step1 raw35651step0; decide +kernel
      have hl : raw35651step1Labels = raw35651step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35651step0 raw35651step0Labels permutation58 permutation3
    mixedMoment B raw35651step1 raw35651step1Labels = mixedMoment B raw35651step2 raw35651step2Labels := by
      have ha : raw35651step2 = raw35651step1 := by apply Matrix.ext; unfold raw35651step2 raw35651step1; decide +kernel
      have hl : raw35651step1Labels = labelEmbedding6 ∘ raw35651step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35651step1 raw35651step1Labels raw35651step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4673 node4673Labels := by rfl

def raw35652 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw35652Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35652step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35652step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35652step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35652step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35652step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35652step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35652 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35652 raw35652Labels = mixedMoment B node4724 node4724Labels := by
  calc
    mixedMoment B raw35652 raw35652Labels = mixedMoment B raw35652step0 raw35652step0Labels := by
      have ha : raw35652step0 = (fun i j => raw35652 (permutation663 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35652step0 raw35652; decide +kernel
      have hl : raw35652step0Labels = raw35652Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35652 raw35652Labels permutation663 permutation3
    mixedMoment B raw35652step0 raw35652step0Labels = mixedMoment B raw35652step1 raw35652step1Labels := by
      have ha : raw35652step1 = -raw35652step0 := by apply Matrix.ext; change ∀ i j, raw35652step1 i j = -(raw35652step0 i j); unfold raw35652step1 raw35652step0; decide +kernel
      have hl : raw35652step1Labels = raw35652step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35652step1 raw35652step1Labels = mixedMoment B raw35652step2 raw35652step2Labels := by
      have ha : raw35652step2 = raw35652step1 := by apply Matrix.ext; unfold raw35652step2 raw35652step1; decide +kernel
      have hl : raw35652step1Labels = labelEmbedding6 ∘ raw35652step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35652step1 raw35652step1Labels raw35652step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4724 node4724Labels := by rfl

def raw35653 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw35653Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35653step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw35653step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35653step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw35653step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35653step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw35653step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35653step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw35653step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35653 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35653 raw35653Labels = mixedMoment B node4749 node4749Labels := by
  calc
    mixedMoment B raw35653 raw35653Labels = mixedMoment B raw35653step0 raw35653step0Labels := by
      have hz : ∀ j, raw35653 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35653step0 = (fun i j => raw35653 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35653step0 raw35653; decide +kernel
      have hl : raw35653step0Labels = raw35653Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35653 raw35653Labels permutation346 hz
    mixedMoment B raw35653step0 raw35653step0Labels = mixedMoment B raw35653step1 raw35653step1Labels := by
      have ha : raw35653step1 = (fun i j => raw35653step0 (permutation144 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35653step1 raw35653step0; decide +kernel
      have hl : raw35653step1Labels = raw35653step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35653step0 raw35653step0Labels permutation144 permutation3
    mixedMoment B raw35653step1 raw35653step1Labels = mixedMoment B raw35653step2 raw35653step2Labels := by
      have ha : raw35653step2 = -raw35653step1 := by apply Matrix.ext; change ∀ i j, raw35653step2 i j = -(raw35653step1 i j); unfold raw35653step2 raw35653step1; decide +kernel
      have hl : raw35653step2Labels = raw35653step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35653step2 raw35653step2Labels = mixedMoment B raw35653step3 raw35653step3Labels := by
      have ha : raw35653step3 = raw35653step2 := by apply Matrix.ext; unfold raw35653step3 raw35653step2; decide +kernel
      have hl : raw35653step2Labels = labelEmbedding6 ∘ raw35653step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35653step2 raw35653step2Labels raw35653step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4749 node4749Labels := by rfl

def raw35654 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw35654Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35654step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw35654step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35654step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35654step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35654 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35654 raw35654Labels = mixedMoment B node2101 node2101Labels := by
  calc
    mixedMoment B raw35654 raw35654Labels = mixedMoment B raw35654step0 raw35654step0Labels := by
      have hz : ∀ j, raw35654 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35654step0 = (fun i j => raw35654 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35654step0 raw35654; decide +kernel
      have hl : raw35654step0Labels = raw35654Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35654 raw35654Labels permutation346 hz
    mixedMoment B raw35654step0 raw35654step0Labels = mixedMoment B raw35654step1 raw35654step1Labels := by
      have ha : raw35654step1 = (fun i j => raw35654step0 (permutation58 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35654step1 raw35654step0; decide +kernel
      have hl : raw35654step1Labels = raw35654step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35654step0 raw35654step0Labels permutation58 permutation3
    _ = mixedMoment B node2101 node2101Labels := by rfl

def raw35655 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw35655Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35655step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35655step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35655 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35655 raw35655Labels = mixedMoment B node3784 node3784Labels := by
  calc
    mixedMoment B raw35655 raw35655Labels = mixedMoment B raw35655step0 raw35655step0Labels := by
      have ha : raw35655step0 = (fun i j => raw35655 (permutation291 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35655step0 raw35655; decide +kernel
      have hl : raw35655step0Labels = raw35655Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35655 raw35655Labels permutation291 permutation3
    _ = mixedMoment B node3784 node3784Labels := by rfl

def raw35656 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw35656Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35656step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw35656step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35656step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw35656step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35656step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw35656step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35656 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35656 raw35656Labels = mixedMoment B node3811 node3811Labels := by
  calc
    mixedMoment B raw35656 raw35656Labels = mixedMoment B raw35656step0 raw35656step0Labels := by
      have hz : ∀ j, raw35656 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35656step0 = (fun i j => raw35656 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35656step0 raw35656; decide +kernel
      have hl : raw35656step0Labels = raw35656Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35656 raw35656Labels permutation346 hz
    mixedMoment B raw35656step0 raw35656step0Labels = mixedMoment B raw35656step1 raw35656step1Labels := by
      have ha : raw35656step1 = (fun i j => raw35656step0 (permutation144 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35656step1 raw35656step0; decide +kernel
      have hl : raw35656step1Labels = raw35656step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35656step0 raw35656step0Labels permutation144 permutation3
    mixedMoment B raw35656step1 raw35656step1Labels = mixedMoment B raw35656step2 raw35656step2Labels := by
      have ha : raw35656step2 = -raw35656step1 := by apply Matrix.ext; change ∀ i j, raw35656step2 i j = -(raw35656step1 i j); unfold raw35656step2 raw35656step1; decide +kernel
      have hl : raw35656step2Labels = raw35656step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3811 node3811Labels := by rfl

def raw35657 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw35657Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35657step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw35657step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35657step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw35657step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35657 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35657 raw35657Labels = mixedMoment B node3885 node3885Labels := by
  calc
    mixedMoment B raw35657 raw35657Labels = mixedMoment B raw35657step0 raw35657step0Labels := by
      have hz : ∀ j, raw35657 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35657step0 = (fun i j => raw35657 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35657step0 raw35657; decide +kernel
      have hl : raw35657step0Labels = raw35657Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35657 raw35657Labels permutation346 hz
    mixedMoment B raw35657step0 raw35657step0Labels = mixedMoment B raw35657step1 raw35657step1Labels := by
      have ha : raw35657step1 = (fun i j => raw35657step0 (permutation58 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35657step1 raw35657step0; decide +kernel
      have hl : raw35657step1Labels = raw35657step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35657step0 raw35657step0Labels permutation58 permutation3
    _ = mixedMoment B node3885 node3885Labels := by rfl

def raw35658 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw35658Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35658step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35658step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35658 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35658 raw35658Labels = mixedMoment B node1798 node1798Labels := by
  calc
    mixedMoment B raw35658 raw35658Labels = mixedMoment B raw35658step0 raw35658step0Labels := by
      have ha : raw35658step0 = (fun i j => raw35658 (permutation277 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35658step0 raw35658; decide +kernel
      have hl : raw35658step0Labels = raw35658Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35658 raw35658Labels permutation277 permutation3
    _ = mixedMoment B node1798 node1798Labels := by rfl

def raw35659 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw35659Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35659step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw35659step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35659 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35659 raw35659Labels = mixedMoment B node3713 node3713Labels := by
  calc
    mixedMoment B raw35659 raw35659Labels = mixedMoment B raw35659step0 raw35659step0Labels := by
      have ha : raw35659step0 = (fun i j => raw35659 (permutation277 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35659step0 raw35659; decide +kernel
      have hl : raw35659step0Labels = raw35659Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35659 raw35659Labels permutation277 permutation3
    _ = mixedMoment B node3713 node3713Labels := by rfl

def raw35660 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw35660Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35660step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw35660step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35660 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35660 raw35660Labels = mixedMoment B node3731 node3731Labels := by
  calc
    mixedMoment B raw35660 raw35660Labels = mixedMoment B raw35660step0 raw35660step0Labels := by
      have ha : raw35660step0 = (fun i j => raw35660 (permutation277 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35660step0 raw35660; decide +kernel
      have hl : raw35660step0Labels = raw35660Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35660 raw35660Labels permutation277 permutation3
    _ = mixedMoment B node3731 node3731Labels := by rfl

def raw35661 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw35661Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35661step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw35661step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35661step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw35661step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35661 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35661 raw35661Labels = mixedMoment B node1800 node1800Labels := by
  calc
    mixedMoment B raw35661 raw35661Labels = mixedMoment B raw35661step0 raw35661step0Labels := by
      have hz : ∀ j, raw35661 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35661step0 = (fun i j => raw35661 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35661step0 raw35661; decide +kernel
      have hl : raw35661step0Labels = raw35661Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35661 raw35661Labels permutation346 hz
    mixedMoment B raw35661step0 raw35661step0Labels = mixedMoment B raw35661step1 raw35661step1Labels := by
      have ha : raw35661step1 = (fun i j => raw35661step0 (permutation58 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35661step1 raw35661step0; decide +kernel
      have hl : raw35661step1Labels = raw35661step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35661step0 raw35661step0Labels permutation58 permutation3
    _ = mixedMoment B node1800 node1800Labels := by rfl

def raw35662 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw35662Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35662step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35662step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35662step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35662step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35662 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35662 raw35662Labels = mixedMoment B node3641 node3641Labels := by
  calc
    mixedMoment B raw35662 raw35662Labels = mixedMoment B raw35662step0 raw35662step0Labels := by
      have ha : raw35662step0 = (fun i j => raw35662 (permutation518 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35662step0 raw35662; decide +kernel
      have hl : raw35662step0Labels = raw35662Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35662 raw35662Labels permutation518 permutation3
    mixedMoment B raw35662step0 raw35662step0Labels = mixedMoment B raw35662step1 raw35662step1Labels := by
      have ha : raw35662step1 = -raw35662step0 := by apply Matrix.ext; change ∀ i j, raw35662step1 i j = -(raw35662step0 i j); unfold raw35662step1 raw35662step0; decide +kernel
      have hl : raw35662step1Labels = raw35662step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3641 node3641Labels := by rfl

def raw35663 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![0, 2, -2], ![2, -2, 0]]
def raw35663Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35663step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![0, 2, -2], ![2, -2, 0]]
def raw35663step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35663step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw35663step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35663step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw35663step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35663 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35663 raw35663Labels = mixedMoment B node3660 node3660Labels := by
  calc
    mixedMoment B raw35663 raw35663Labels = mixedMoment B raw35663step0 raw35663step0Labels := by
      have hz : ∀ j, raw35663 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35663step0 = (fun i j => raw35663 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35663step0 raw35663; decide +kernel
      have hl : raw35663step0Labels = raw35663Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35663 raw35663Labels permutation346 hz
    mixedMoment B raw35663step0 raw35663step0Labels = mixedMoment B raw35663step1 raw35663step1Labels := by
      have ha : raw35663step1 = (fun i j => raw35663step0 (permutation102 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35663step1 raw35663step0; decide +kernel
      have hl : raw35663step1Labels = raw35663step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35663step0 raw35663step0Labels permutation102 permutation3
    mixedMoment B raw35663step1 raw35663step1Labels = mixedMoment B raw35663step2 raw35663step2Labels := by
      have ha : raw35663step2 = -raw35663step1 := by apply Matrix.ext; change ∀ i j, raw35663step2 i j = -(raw35663step1 i j); unfold raw35663step2 raw35663step1; decide +kernel
      have hl : raw35663step2Labels = raw35663step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3660 node3660Labels := by rfl

def raw35664 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2], ![1, -1, 0]]
def raw35664Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35664step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![1, 1, -2], ![1, -1, 0]]
def raw35664step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35664step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35664step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35664 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35664 raw35664Labels = mixedMoment B node3732 node3732Labels := by
  calc
    mixedMoment B raw35664 raw35664Labels = mixedMoment B raw35664step0 raw35664step0Labels := by
      have hz : ∀ j, raw35664 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35664step0 = (fun i j => raw35664 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35664step0 raw35664; decide +kernel
      have hl : raw35664step0Labels = raw35664Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35664 raw35664Labels permutation346 hz
    mixedMoment B raw35664step0 raw35664step0Labels = mixedMoment B raw35664step1 raw35664step1Labels := by
      have ha : raw35664step1 = (fun i j => raw35664step0 (permutation59 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35664step1 raw35664step0; decide +kernel
      have hl : raw35664step1Labels = raw35664step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35664step0 raw35664step0Labels permutation59 permutation3
    _ = mixedMoment B node3732 node3732Labels := by rfl

def raw35665 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw35665Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35665step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw35665step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35665step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35665step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35665 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35665 raw35665Labels = mixedMoment B node1814 node1814Labels := by
  calc
    mixedMoment B raw35665 raw35665Labels = mixedMoment B raw35665step0 raw35665step0Labels := by
      have hz : ∀ j, raw35665 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35665step0 = (fun i j => raw35665 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35665step0 raw35665; decide +kernel
      have hl : raw35665step0Labels = raw35665Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35665 raw35665Labels permutation346 hz
    mixedMoment B raw35665step0 raw35665step0Labels = mixedMoment B raw35665step1 raw35665step1Labels := by
      have ha : raw35665step1 = (fun i j => raw35665step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35665step1 raw35665step0; decide +kernel
      have hl : raw35665step1Labels = raw35665step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35665step0 raw35665step0Labels permutation56 permutation3
    _ = mixedMoment B node1814 node1814Labels := by rfl

def raw35666 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw35666Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35666step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35666step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35666 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35666 raw35666Labels = mixedMoment B node3708 node3708Labels := by
  calc
    mixedMoment B raw35666 raw35666Labels = mixedMoment B raw35666step0 raw35666step0Labels := by
      have ha : raw35666step0 = (fun i j => raw35666 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35666step0 raw35666; decide +kernel
      have hl : raw35666step0Labels = raw35666Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35666 raw35666Labels permutation265 permutation3
    _ = mixedMoment B node3708 node3708Labels := by rfl

def raw35667 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw35667Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35667step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw35667step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35667step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw35667step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35667 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35667 raw35667Labels = mixedMoment B node3739 node3739Labels := by
  calc
    mixedMoment B raw35667 raw35667Labels = mixedMoment B raw35667step0 raw35667step0Labels := by
      have hz : ∀ j, raw35667 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35667step0 = (fun i j => raw35667 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35667step0 raw35667; decide +kernel
      have hl : raw35667step0Labels = raw35667Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35667 raw35667Labels permutation346 hz
    mixedMoment B raw35667step0 raw35667step0Labels = mixedMoment B raw35667step1 raw35667step1Labels := by
      have ha : raw35667step1 = (fun i j => raw35667step0 (permutation57 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35667step1 raw35667step0; decide +kernel
      have hl : raw35667step1Labels = raw35667step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35667step0 raw35667step0Labels permutation57 permutation3
    _ = mixedMoment B node3739 node3739Labels := by rfl

def raw35668 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw35668Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35668step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw35668step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35668step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw35668step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35668 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35668 raw35668Labels = mixedMoment B node1799 node1799Labels := by
  calc
    mixedMoment B raw35668 raw35668Labels = mixedMoment B raw35668step0 raw35668step0Labels := by
      have hz : ∀ j, raw35668 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35668step0 = (fun i j => raw35668 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35668step0 raw35668; decide +kernel
      have hl : raw35668step0Labels = raw35668Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35668 raw35668Labels permutation346 hz
    mixedMoment B raw35668step0 raw35668step0Labels = mixedMoment B raw35668step1 raw35668step1Labels := by
      have ha : raw35668step1 = (fun i j => raw35668step0 (permutation58 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35668step1 raw35668step0; decide +kernel
      have hl : raw35668step1Labels = raw35668step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35668step0 raw35668step0Labels permutation58 permutation3
    _ = mixedMoment B node1799 node1799Labels := by rfl

def raw35669 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw35669Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35669step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35669step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35669step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35669step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35669 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35669 raw35669Labels = mixedMoment B node1878 node1878Labels := by
  calc
    mixedMoment B raw35669 raw35669Labels = mixedMoment B raw35669step0 raw35669step0Labels := by
      have ha : raw35669step0 = (fun i j => raw35669 (permutation663 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35669step0 raw35669; decide +kernel
      have hl : raw35669step0Labels = raw35669Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35669 raw35669Labels permutation663 permutation3
    mixedMoment B raw35669step0 raw35669step0Labels = mixedMoment B raw35669step1 raw35669step1Labels := by
      have ha : raw35669step1 = -raw35669step0 := by apply Matrix.ext; change ∀ i j, raw35669step1 i j = -(raw35669step0 i j); unfold raw35669step1 raw35669step0; decide +kernel
      have hl : raw35669step1Labels = raw35669step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1878 node1878Labels := by rfl

def raw35670 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw35670Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35670step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 2, -2], ![3, -3, 0]]
def raw35670step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw35670step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw35670step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw35670step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw35670step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35670 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35670 raw35670Labels = mixedMoment B node1928 node1928Labels := by
  calc
    mixedMoment B raw35670 raw35670Labels = mixedMoment B raw35670step0 raw35670step0Labels := by
      have hz : ∀ j, raw35670 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35670step0 = (fun i j => raw35670 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35670step0 raw35670; decide +kernel
      have hl : raw35670step0Labels = raw35670Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35670 raw35670Labels permutation346 hz
    mixedMoment B raw35670step0 raw35670step0Labels = mixedMoment B raw35670step1 raw35670step1Labels := by
      have ha : raw35670step1 = (fun i j => raw35670step0 (permutation144 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35670step1 raw35670step0; decide +kernel
      have hl : raw35670step1Labels = raw35670step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35670step0 raw35670step0Labels permutation144 permutation3
    mixedMoment B raw35670step1 raw35670step1Labels = mixedMoment B raw35670step2 raw35670step2Labels := by
      have ha : raw35670step2 = -raw35670step1 := by apply Matrix.ext; change ∀ i j, raw35670step2 i j = -(raw35670step1 i j); unfold raw35670step2 raw35670step1; decide +kernel
      have hl : raw35670step2Labels = raw35670step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1928 node1928Labels := by rfl

def raw35671 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35671Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35671step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 1, 2], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35671step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35671step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35671step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35671 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35671 raw35671Labels = mixedMoment B node5163 node5163Labels := by
  calc
    mixedMoment B raw35671 raw35671Labels = mixedMoment B raw35671step0 raw35671step0Labels := by
      have hz : ∀ j, raw35671 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35671step0 = (fun i j => raw35671 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35671step0 raw35671; decide +kernel
      have hl : raw35671step0Labels = raw35671Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35671 raw35671Labels permutation346 hz
    mixedMoment B raw35671step0 raw35671step0Labels = mixedMoment B raw35671step1 raw35671step1Labels := by
      have ha : raw35671step1 = (fun i j => raw35671step0 (permutation58 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35671step1 raw35671step0; decide +kernel
      have hl : raw35671step1Labels = raw35671step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35671step0 raw35671step0Labels permutation58 permutation2
    _ = mixedMoment B node5163 node5163Labels := by rfl

def raw35672 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35672Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35672step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw35672step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35672step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw35672step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35672 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35672 raw35672Labels = mixedMoment B node5400 node5400Labels := by
  calc
    mixedMoment B raw35672 raw35672Labels = mixedMoment B raw35672step0 raw35672step0Labels := by
      have ha : raw35672step0 = (fun i j => raw35672 (permutation660 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35672step0 raw35672; decide +kernel
      have hl : raw35672step0Labels = raw35672Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35672 raw35672Labels permutation660 permutation2
    mixedMoment B raw35672step0 raw35672step0Labels = mixedMoment B raw35672step1 raw35672step1Labels := by
      have ha : raw35672step1 = -raw35672step0 := by apply Matrix.ext; change ∀ i j, raw35672step1 i j = -(raw35672step0 i j); unfold raw35672step1 raw35672step0; decide +kernel
      have hl : raw35672step1Labels = raw35672step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5400 node5400Labels := by rfl

def raw35673 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35673Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35673step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35673step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35673step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35673step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35673 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35673 raw35673Labels = mixedMoment B node5432 node5432Labels := by
  calc
    mixedMoment B raw35673 raw35673Labels = mixedMoment B raw35673step0 raw35673step0Labels := by
      have hz : ∀ j, raw35673 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35673step0 = (fun i j => raw35673 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35673step0 raw35673; decide +kernel
      have hl : raw35673step0Labels = raw35673Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35673 raw35673Labels permutation346 hz
    mixedMoment B raw35673step0 raw35673step0Labels = mixedMoment B raw35673step1 raw35673step1Labels := by
      have ha : raw35673step1 = (fun i j => raw35673step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35673step1 raw35673step0; decide +kernel
      have hl : raw35673step1Labels = raw35673step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35673step0 raw35673step0Labels permutation56 permutation2
    _ = mixedMoment B node5432 node5432Labels := by rfl

def raw35674 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw35674Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35674step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw35674step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35674step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw35674step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35674step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35674step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35674 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35674 raw35674Labels = mixedMoment B node5409 node5409Labels := by
  calc
    mixedMoment B raw35674 raw35674Labels = mixedMoment B raw35674step0 raw35674step0Labels := by
      have hz : ∀ j, raw35674 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35674step0 = (fun i j => raw35674 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35674step0 raw35674; decide +kernel
      have hl : raw35674step0Labels = raw35674Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35674 raw35674Labels permutation346 hz
    mixedMoment B raw35674step0 raw35674step0Labels = mixedMoment B raw35674step1 raw35674step1Labels := by
      have ha : raw35674step1 = (fun i j => raw35674step0 (permutation144 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35674step1 raw35674step0; decide +kernel
      have hl : raw35674step1Labels = raw35674step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35674step0 raw35674step0Labels permutation144 permutation2
    mixedMoment B raw35674step1 raw35674step1Labels = mixedMoment B raw35674step2 raw35674step2Labels := by
      have ha : raw35674step2 = -raw35674step1 := by apply Matrix.ext; change ∀ i j, raw35674step2 i j = -(raw35674step1 i j); unfold raw35674step2 raw35674step1; decide +kernel
      have hl : raw35674step2Labels = raw35674step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5409 node5409Labels := by rfl

def raw35675 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw35675Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35675step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw35675step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35675step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw35675step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35675 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35675 raw35675Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw35675 raw35675Labels = mixedMoment B raw35675step0 raw35675step0Labels := by
      have hz : ∀ j, raw35675 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35675step0 = (fun i j => raw35675 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35675step0 raw35675; decide +kernel
      have hl : raw35675step0Labels = raw35675Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35675 raw35675Labels permutation346 hz
    mixedMoment B raw35675step0 raw35675step0Labels = mixedMoment B raw35675step1 raw35675step1Labels := by
      have ha : raw35675step1 = (fun i j => raw35675step0 (permutation58 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35675step1 raw35675step0; decide +kernel
      have hl : raw35675step1Labels = raw35675step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35675step0 raw35675step0Labels permutation58 permutation2
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw35676 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35676Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35676step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35676step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35676step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw35676step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35676step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw35676step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35676 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35676 raw35676Labels = mixedMoment B node4867 node4867Labels := by
  calc
    mixedMoment B raw35676 raw35676Labels = mixedMoment B raw35676step0 raw35676step0Labels := by
      have hz : ∀ j, raw35676 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35676step0 = (fun i j => raw35676 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35676step0 raw35676; decide +kernel
      have hl : raw35676step0Labels = raw35676Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35676 raw35676Labels permutation346 hz
    mixedMoment B raw35676step0 raw35676step0Labels = mixedMoment B raw35676step1 raw35676step1Labels := by
      have ha : raw35676step1 = (fun i j => raw35676step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35676step1 raw35676step0; decide +kernel
      have hl : raw35676step1Labels = raw35676step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35676step0 raw35676step0Labels permutation32 permutation3
    mixedMoment B raw35676step1 raw35676step1Labels = mixedMoment B raw35676step2 raw35676step2Labels := by
      have ha : raw35676step2 = raw35676step1 := by apply Matrix.ext; unfold raw35676step2 raw35676step1; decide +kernel
      have hl : raw35676step1Labels = labelEmbedding6 ∘ raw35676step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35676step1 raw35676step1Labels raw35676step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4867 node4867Labels := by rfl

def raw35677 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35677Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35677step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw35677step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35677step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw35677step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35677 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35677 raw35677Labels = mixedMoment B node5402 node5402Labels := by
  calc
    mixedMoment B raw35677 raw35677Labels = mixedMoment B raw35677step0 raw35677step0Labels := by
      have ha : raw35677step0 = (fun i j => raw35677 (permutation664 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35677step0 raw35677; decide +kernel
      have hl : raw35677step0Labels = raw35677Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35677 raw35677Labels permutation664 permutation2
    mixedMoment B raw35677step0 raw35677step0Labels = mixedMoment B raw35677step1 raw35677step1Labels := by
      have ha : raw35677step1 = -raw35677step0 := by apply Matrix.ext; change ∀ i j, raw35677step1 i j = -(raw35677step0 i j); unfold raw35677step1 raw35677step0; decide +kernel
      have hl : raw35677step1Labels = raw35677step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5402 node5402Labels := by rfl

def raw35678 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35678Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35678step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35678step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35678step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw35678step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35678step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw35678step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35678step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw35678step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35678 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35678 raw35678Labels = mixedMoment B node5436 node5436Labels := by
  calc
    mixedMoment B raw35678 raw35678Labels = mixedMoment B raw35678step0 raw35678step0Labels := by
      have hz : ∀ j, raw35678 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35678step0 = (fun i j => raw35678 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35678step0 raw35678; decide +kernel
      have hl : raw35678step0Labels = raw35678Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35678 raw35678Labels permutation346 hz
    mixedMoment B raw35678step0 raw35678step0Labels = mixedMoment B raw35678step1 raw35678step1Labels := by
      have ha : raw35678step1 = (fun i j => raw35678step0 (permutation42 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35678step1 raw35678step0; decide +kernel
      have hl : raw35678step1Labels = raw35678step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35678step0 raw35678step0Labels permutation42 permutation5
    mixedMoment B raw35678step1 raw35678step1Labels = mixedMoment B raw35678step2 raw35678step2Labels := by
      have ha : raw35678step2 = -raw35678step1 := by apply Matrix.ext; change ∀ i j, raw35678step2 i j = -(raw35678step1 i j); unfold raw35678step2 raw35678step1; decide +kernel
      have hl : raw35678step2Labels = raw35678step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35678step2 raw35678step2Labels = mixedMoment B raw35678step3 raw35678step3Labels := by
      have ha : raw35678step3 = raw35678step2 := by apply Matrix.ext; unfold raw35678step3 raw35678step2; decide +kernel
      have hl : raw35678step2Labels = labelEmbedding8 ∘ raw35678step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35678step2 raw35678step2Labels raw35678step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5436 node5436Labels := by rfl

def raw35679 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw35679Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35679step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw35679step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35679step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw35679step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35679step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw35679step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35679 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35679 raw35679Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw35679 raw35679Labels = mixedMoment B raw35679step0 raw35679step0Labels := by
      have hz : ∀ j, raw35679 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35679step0 = (fun i j => raw35679 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35679step0 raw35679; decide +kernel
      have hl : raw35679step0Labels = raw35679Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35679 raw35679Labels permutation346 hz
    mixedMoment B raw35679step0 raw35679step0Labels = mixedMoment B raw35679step1 raw35679step1Labels := by
      have ha : raw35679step1 = (fun i j => raw35679step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35679step1 raw35679step0; decide +kernel
      have hl : raw35679step1Labels = raw35679step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35679step0 raw35679step0Labels permutation145 permutation2
    mixedMoment B raw35679step1 raw35679step1Labels = mixedMoment B raw35679step2 raw35679step2Labels := by
      have ha : raw35679step2 = -raw35679step1 := by apply Matrix.ext; change ∀ i j, raw35679step2 i j = -(raw35679step1 i j); unfold raw35679step2 raw35679step1; decide +kernel
      have hl : raw35679step2Labels = raw35679step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw35680 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw35680Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35680step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw35680step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35680step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw35680step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35680step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw35680step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35680step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw35680step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35680 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35680 raw35680Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw35680 raw35680Labels = mixedMoment B raw35680step0 raw35680step0Labels := by
      have hz : ∀ j, raw35680 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35680step0 = (fun i j => raw35680 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35680step0 raw35680; decide +kernel
      have hl : raw35680step0Labels = raw35680Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35680 raw35680Labels permutation346 hz
    mixedMoment B raw35680step0 raw35680step0Labels = mixedMoment B raw35680step1 raw35680step1Labels := by
      have ha : raw35680step1 = (fun i j => raw35680step0 (permutation52 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35680step1 raw35680step0; decide +kernel
      have hl : raw35680step1Labels = raw35680step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35680step0 raw35680step0Labels permutation52 permutation5
    mixedMoment B raw35680step1 raw35680step1Labels = mixedMoment B raw35680step2 raw35680step2Labels := by
      have ha : raw35680step2 = -raw35680step1 := by apply Matrix.ext; change ∀ i j, raw35680step2 i j = -(raw35680step1 i j); unfold raw35680step2 raw35680step1; decide +kernel
      have hl : raw35680step2Labels = raw35680step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35680step2 raw35680step2Labels = mixedMoment B raw35680step3 raw35680step3Labels := by
      have ha : raw35680step3 = raw35680step2 := by apply Matrix.ext; unfold raw35680step3 raw35680step2; decide +kernel
      have hl : raw35680step2Labels = labelEmbedding8 ∘ raw35680step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35680step2 raw35680step2Labels raw35680step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

def raw35681 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35681Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35681step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw35681step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35681step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw35681step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35681 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35681 raw35681Labels = mixedMoment B node4680 node4680Labels := by
  calc
    mixedMoment B raw35681 raw35681Labels = mixedMoment B raw35681step0 raw35681step0Labels := by
      have ha : raw35681step0 = (fun i j => raw35681 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35681step0 raw35681; decide +kernel
      have hl : raw35681step0Labels = raw35681Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35681 raw35681Labels permutation158 permutation3
    mixedMoment B raw35681step0 raw35681step0Labels = mixedMoment B raw35681step1 raw35681step1Labels := by
      have ha : raw35681step1 = raw35681step0 := by apply Matrix.ext; unfold raw35681step1 raw35681step0; decide +kernel
      have hl : raw35681step0Labels = labelEmbedding6 ∘ raw35681step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35681step0 raw35681step0Labels raw35681step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4680 node4680Labels := by rfl

def raw35682 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35682Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35682step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35682step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35682 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35682 raw35682Labels = mixedMoment B node4963 node4963Labels := by
  calc
    mixedMoment B raw35682 raw35682Labels = mixedMoment B raw35682step0 raw35682step0Labels := by
      have ha : raw35682step0 = (fun i j => raw35682 (permutation277 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35682step0 raw35682; decide +kernel
      have hl : raw35682step0Labels = raw35682Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35682 raw35682Labels permutation277 permutation2
    _ = mixedMoment B node4963 node4963Labels := by rfl

def raw35683 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35683Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35683step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw35683step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35683step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw35683step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35683 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35683 raw35683Labels = mixedMoment B node5381 node5381Labels := by
  calc
    mixedMoment B raw35683 raw35683Labels = mixedMoment B raw35683step0 raw35683step0Labels := by
      have ha : raw35683step0 = (fun i j => raw35683 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35683step0 raw35683; decide +kernel
      have hl : raw35683step0Labels = raw35683Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35683 raw35683Labels permutation158 permutation3
    mixedMoment B raw35683step0 raw35683step0Labels = mixedMoment B raw35683step1 raw35683step1Labels := by
      have ha : raw35683step1 = raw35683step0 := by apply Matrix.ext; unfold raw35683step1 raw35683step0; decide +kernel
      have hl : raw35683step0Labels = labelEmbedding6 ∘ raw35683step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35683step0 raw35683step0Labels raw35683step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5381 node5381Labels := by rfl

def raw35684 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw35684Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35684step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw35684step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35684 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35684 raw35684Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw35684 raw35684Labels = mixedMoment B raw35684step0 raw35684step0Labels := by
      have ha : raw35684step0 = (fun i j => raw35684 (permutation277 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35684step0 raw35684; decide +kernel
      have hl : raw35684step0Labels = raw35684Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35684 raw35684Labels permutation277 permutation2
    _ = mixedMoment B node5378 node5378Labels := by rfl

def raw35685 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw35685Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35685step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw35685step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35685 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35685 raw35685Labels = mixedMoment B node5382 node5382Labels := by
  calc
    mixedMoment B raw35685 raw35685Labels = mixedMoment B raw35685step0 raw35685step0Labels := by
      have ha : raw35685step0 = (fun i j => raw35685 (permutation277 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35685step0 raw35685; decide +kernel
      have hl : raw35685step0Labels = raw35685Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35685 raw35685Labels permutation277 permutation2
    _ = mixedMoment B node5382 node5382Labels := by rfl

def raw35686 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35686Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35686step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35686step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35686step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw35686step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35686step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw35686step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35686 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35686 raw35686Labels = mixedMoment B node4690 node4690Labels := by
  calc
    mixedMoment B raw35686 raw35686Labels = mixedMoment B raw35686step0 raw35686step0Labels := by
      have hz : ∀ j, raw35686 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35686step0 = (fun i j => raw35686 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35686step0 raw35686; decide +kernel
      have hl : raw35686step0Labels = raw35686Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35686 raw35686Labels permutation346 hz
    mixedMoment B raw35686step0 raw35686step0Labels = mixedMoment B raw35686step1 raw35686step1Labels := by
      have ha : raw35686step1 = (fun i j => raw35686step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35686step1 raw35686step0; decide +kernel
      have hl : raw35686step1Labels = raw35686step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35686step0 raw35686step0Labels permutation35 permutation3
    mixedMoment B raw35686step1 raw35686step1Labels = mixedMoment B raw35686step2 raw35686step2Labels := by
      have ha : raw35686step2 = raw35686step1 := by apply Matrix.ext; unfold raw35686step2 raw35686step1; decide +kernel
      have hl : raw35686step1Labels = labelEmbedding6 ∘ raw35686step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35686step1 raw35686step1Labels raw35686step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4690 node4690Labels := by rfl

def raw35687 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35687Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35687step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35687step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35687step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw35687step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35687 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35687 raw35687Labels = mixedMoment B node4966 node4966Labels := by
  calc
    mixedMoment B raw35687 raw35687Labels = mixedMoment B raw35687step0 raw35687step0Labels := by
      have hz : ∀ j, raw35687 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35687step0 = (fun i j => raw35687 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35687step0 raw35687; decide +kernel
      have hl : raw35687step0Labels = raw35687Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35687 raw35687Labels permutation346 hz
    mixedMoment B raw35687step0 raw35687step0Labels = mixedMoment B raw35687step1 raw35687step1Labels := by
      have ha : raw35687step1 = (fun i j => raw35687step0 (permutation58 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35687step1 raw35687step0; decide +kernel
      have hl : raw35687step1Labels = raw35687step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35687step0 raw35687step0Labels permutation58 permutation2
    _ = mixedMoment B node4966 node4966Labels := by rfl

def raw35688 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 1, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35688Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35688step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -2, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw35688step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35688step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw35688step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35688 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35688 raw35688Labels = mixedMoment B node5339 node5339Labels := by
  calc
    mixedMoment B raw35688 raw35688Labels = mixedMoment B raw35688step0 raw35688step0Labels := by
      have ha : raw35688step0 = (fun i j => raw35688 (permutation663 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35688step0 raw35688; decide +kernel
      have hl : raw35688step0Labels = raw35688Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35688 raw35688Labels permutation663 permutation2
    mixedMoment B raw35688step0 raw35688step0Labels = mixedMoment B raw35688step1 raw35688step1Labels := by
      have ha : raw35688step1 = -raw35688step0 := by apply Matrix.ext; change ∀ i j, raw35688step1 i j = -(raw35688step0 i j); unfold raw35688step1 raw35688step0; decide +kernel
      have hl : raw35688step1Labels = raw35688step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5339 node5339Labels := by rfl

def raw35689 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw35689Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35689step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw35689step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35689step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35689step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35689step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35689step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35689 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35689 raw35689Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw35689 raw35689Labels = mixedMoment B raw35689step0 raw35689step0Labels := by
      have hz : ∀ j, raw35689 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35689step0 = (fun i j => raw35689 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35689step0 raw35689; decide +kernel
      have hl : raw35689step0Labels = raw35689Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35689 raw35689Labels permutation346 hz
    mixedMoment B raw35689step0 raw35689step0Labels = mixedMoment B raw35689step1 raw35689step1Labels := by
      have ha : raw35689step1 = (fun i j => raw35689step0 (permutation144 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35689step1 raw35689step0; decide +kernel
      have hl : raw35689step1Labels = raw35689step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35689step0 raw35689step0Labels permutation144 permutation2
    mixedMoment B raw35689step1 raw35689step1Labels = mixedMoment B raw35689step2 raw35689step2Labels := by
      have ha : raw35689step2 = -raw35689step1 := by apply Matrix.ext; change ∀ i j, raw35689step2 i j = -(raw35689step1 i j); unfold raw35689step2 raw35689step1; decide +kernel
      have hl : raw35689step2Labels = raw35689step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5355 node5355Labels := by rfl

def raw35690 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw35690Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35690step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw35690step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35690step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw35690step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35690 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35690 raw35690Labels = mixedMoment B node5385 node5385Labels := by
  calc
    mixedMoment B raw35690 raw35690Labels = mixedMoment B raw35690step0 raw35690step0Labels := by
      have hz : ∀ j, raw35690 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35690step0 = (fun i j => raw35690 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35690step0 raw35690; decide +kernel
      have hl : raw35690step0Labels = raw35690Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35690 raw35690Labels permutation346 hz
    mixedMoment B raw35690step0 raw35690step0Labels = mixedMoment B raw35690step1 raw35690step1Labels := by
      have ha : raw35690step1 = (fun i j => raw35690step0 (permutation59 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35690step1 raw35690step0; decide +kernel
      have hl : raw35690step1Labels = raw35690step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35690step0 raw35690step0Labels permutation59 permutation2
    _ = mixedMoment B node5385 node5385Labels := by rfl

def raw35691 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35691Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35691step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35691step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35691step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw35691step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35691step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw35691step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35691 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35691 raw35691Labels = mixedMoment B node4683 node4683Labels := by
  calc
    mixedMoment B raw35691 raw35691Labels = mixedMoment B raw35691step0 raw35691step0Labels := by
      have hz : ∀ j, raw35691 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35691step0 = (fun i j => raw35691 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35691step0 raw35691; decide +kernel
      have hl : raw35691step0Labels = raw35691Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35691 raw35691Labels permutation346 hz
    mixedMoment B raw35691step0 raw35691step0Labels = mixedMoment B raw35691step1 raw35691step1Labels := by
      have ha : raw35691step1 = (fun i j => raw35691step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35691step1 raw35691step0; decide +kernel
      have hl : raw35691step1Labels = raw35691step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35691step0 raw35691step0Labels permutation33 permutation3
    mixedMoment B raw35691step1 raw35691step1Labels = mixedMoment B raw35691step2 raw35691step2Labels := by
      have ha : raw35691step2 = raw35691step1 := by apply Matrix.ext; unfold raw35691step2 raw35691step1; decide +kernel
      have hl : raw35691step1Labels = labelEmbedding6 ∘ raw35691step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35691step1 raw35691step1Labels raw35691step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4683 node4683Labels := by rfl

def raw35692 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35692Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35692step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35692step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35692step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35692step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35692 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35692 raw35692Labels = mixedMoment B node4976 node4976Labels := by
  calc
    mixedMoment B raw35692 raw35692Labels = mixedMoment B raw35692step0 raw35692step0Labels := by
      have hz : ∀ j, raw35692 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35692step0 = (fun i j => raw35692 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35692step0 raw35692; decide +kernel
      have hl : raw35692step0Labels = raw35692Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35692 raw35692Labels permutation346 hz
    mixedMoment B raw35692step0 raw35692step0Labels = mixedMoment B raw35692step1 raw35692step1Labels := by
      have ha : raw35692step1 = (fun i j => raw35692step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35692step1 raw35692step0; decide +kernel
      have hl : raw35692step1Labels = raw35692step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35692step0 raw35692step0Labels permutation56 permutation2
    _ = mixedMoment B node4976 node4976Labels := by rfl

def raw35693 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35693Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35693step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw35693step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35693step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, 0, -2]]
def raw35693step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35693 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35693 raw35693Labels = mixedMoment B node5216 node5216Labels := by
  calc
    mixedMoment B raw35693 raw35693Labels = mixedMoment B raw35693step0 raw35693step0Labels := by
      have ha : raw35693step0 = (fun i j => raw35693 (permutation587 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35693step0 raw35693; decide +kernel
      have hl : raw35693step0Labels = raw35693Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35693 raw35693Labels permutation587 permutation5
    mixedMoment B raw35693step0 raw35693step0Labels = mixedMoment B raw35693step1 raw35693step1Labels := by
      have ha : raw35693step1 = raw35693step0 := by apply Matrix.ext; unfold raw35693step1 raw35693step0; decide +kernel
      have hl : raw35693step0Labels = labelEmbedding8 ∘ raw35693step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35693step0 raw35693step0Labels raw35693step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5216 node5216Labels := by rfl

def raw35694 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35694Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35694step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw35694step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35694step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35694step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35694step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw35694step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35694 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35694 raw35694Labels = mixedMoment B node5232 node5232Labels := by
  calc
    mixedMoment B raw35694 raw35694Labels = mixedMoment B raw35694step0 raw35694step0Labels := by
      have hz : ∀ j, raw35694 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35694step0 = (fun i j => raw35694 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35694step0 raw35694; decide +kernel
      have hl : raw35694step0Labels = raw35694Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35694 raw35694Labels permutation346 hz
    mixedMoment B raw35694step0 raw35694step0Labels = mixedMoment B raw35694step1 raw35694step1Labels := by
      have ha : raw35694step1 = (fun i j => raw35694step0 (permutation125 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35694step1 raw35694step0; decide +kernel
      have hl : raw35694step1Labels = raw35694step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35694step0 raw35694step0Labels permutation125 permutation5
    mixedMoment B raw35694step1 raw35694step1Labels = mixedMoment B raw35694step2 raw35694step2Labels := by
      have ha : raw35694step2 = raw35694step1 := by apply Matrix.ext; unfold raw35694step2 raw35694step1; decide +kernel
      have hl : raw35694step1Labels = labelEmbedding8 ∘ raw35694step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35694step1 raw35694step1Labels raw35694step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5232 node5232Labels := by rfl

def raw35695 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw35695Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35695step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw35695step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35695step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw35695step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw35695step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw35695step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35695 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35695 raw35695Labels = mixedMoment B node5264 node5264Labels := by
  calc
    mixedMoment B raw35695 raw35695Labels = mixedMoment B raw35695step0 raw35695step0Labels := by
      have hz : ∀ j, raw35695 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35695step0 = (fun i j => raw35695 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35695step0 raw35695; decide +kernel
      have hl : raw35695step0Labels = raw35695Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35695 raw35695Labels permutation346 hz
    mixedMoment B raw35695step0 raw35695step0Labels = mixedMoment B raw35695step1 raw35695step1Labels := by
      have ha : raw35695step1 = (fun i j => raw35695step0 (permutation119 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35695step1 raw35695step0; decide +kernel
      have hl : raw35695step1Labels = raw35695step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35695step0 raw35695step0Labels permutation119 permutation5
    mixedMoment B raw35695step1 raw35695step1Labels = mixedMoment B raw35695step2 raw35695step2Labels := by
      have ha : raw35695step2 = raw35695step1 := by apply Matrix.ext; unfold raw35695step2 raw35695step1; decide +kernel
      have hl : raw35695step1Labels = labelEmbedding8 ∘ raw35695step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35695step1 raw35695step1Labels raw35695step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5264 node5264Labels := by rfl

def raw35696 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw35696Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35696step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw35696step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35696step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw35696step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw35696step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw35696step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35696 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35696 raw35696Labels = mixedMoment B node4682 node4682Labels := by
  calc
    mixedMoment B raw35696 raw35696Labels = mixedMoment B raw35696step0 raw35696step0Labels := by
      have hz : ∀ j, raw35696 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35696step0 = (fun i j => raw35696 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35696step0 raw35696; decide +kernel
      have hl : raw35696step0Labels = raw35696Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35696 raw35696Labels permutation346 hz
    mixedMoment B raw35696step0 raw35696step0Labels = mixedMoment B raw35696step1 raw35696step1Labels := by
      have ha : raw35696step1 = (fun i j => raw35696step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw35696step1 raw35696step0; decide +kernel
      have hl : raw35696step1Labels = raw35696step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35696step0 raw35696step0Labels permutation32 permutation3
    mixedMoment B raw35696step1 raw35696step1Labels = mixedMoment B raw35696step2 raw35696step2Labels := by
      have ha : raw35696step2 = raw35696step1 := by apply Matrix.ext; unfold raw35696step2 raw35696step1; decide +kernel
      have hl : raw35696step1Labels = labelEmbedding6 ∘ raw35696step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35696step1 raw35696step1Labels raw35696step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4682 node4682Labels := by rfl

def raw35697 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw35697Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35697step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw35697step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35697step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw35697step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35697 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35697 raw35697Labels = mixedMoment B node4965 node4965Labels := by
  calc
    mixedMoment B raw35697 raw35697Labels = mixedMoment B raw35697step0 raw35697step0Labels := by
      have hz : ∀ j, raw35697 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35697step0 = (fun i j => raw35697 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35697step0 raw35697; decide +kernel
      have hl : raw35697step0Labels = raw35697Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35697 raw35697Labels permutation346 hz
    mixedMoment B raw35697step0 raw35697step0Labels = mixedMoment B raw35697step1 raw35697step1Labels := by
      have ha : raw35697step1 = (fun i j => raw35697step0 (permutation58 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35697step1 raw35697step0; decide +kernel
      have hl : raw35697step1Labels = raw35697step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35697step0 raw35697step0Labels permutation58 permutation2
    _ = mixedMoment B node4965 node4965Labels := by rfl

def raw35698 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw35698Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35698step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 0, 2]]
def raw35698step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35698step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw35698step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35698 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35698 raw35698Labels = mixedMoment B node5042 node5042Labels := by
  calc
    mixedMoment B raw35698 raw35698Labels = mixedMoment B raw35698step0 raw35698step0Labels := by
      have ha : raw35698step0 = (fun i j => raw35698 (permutation663 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35698step0 raw35698; decide +kernel
      have hl : raw35698step0Labels = raw35698Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35698 raw35698Labels permutation663 permutation2
    mixedMoment B raw35698step0 raw35698step0Labels = mixedMoment B raw35698step1 raw35698step1Labels := by
      have ha : raw35698step1 = -raw35698step0 := by apply Matrix.ext; change ∀ i j, raw35698step1 i j = -(raw35698step0 i j); unfold raw35698step1 raw35698step0; decide +kernel
      have hl : raw35698step1Labels = raw35698step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5042 node5042Labels := by rfl

def raw35699 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw35699Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35699step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw35699step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35699step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35699step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35699step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw35699step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35699 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35699 raw35699Labels = mixedMoment B node5188 node5188Labels := by
  calc
    mixedMoment B raw35699 raw35699Labels = mixedMoment B raw35699step0 raw35699step0Labels := by
      have hz : ∀ j, raw35699 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35699step0 = (fun i j => raw35699 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35699step0 raw35699; decide +kernel
      have hl : raw35699step0Labels = raw35699Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35699 raw35699Labels permutation346 hz
    mixedMoment B raw35699step0 raw35699step0Labels = mixedMoment B raw35699step1 raw35699step1Labels := by
      have ha : raw35699step1 = (fun i j => raw35699step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35699step1 raw35699step0; decide +kernel
      have hl : raw35699step1Labels = raw35699step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35699step0 raw35699step0Labels permutation150 permutation2
    mixedMoment B raw35699step1 raw35699step1Labels = mixedMoment B raw35699step2 raw35699step2Labels := by
      have ha : raw35699step2 = -raw35699step1 := by apply Matrix.ext; change ∀ i j, raw35699step2 i j = -(raw35699step1 i j); unfold raw35699step2 raw35699step1; decide +kernel
      have hl : raw35699step2Labels = raw35699step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5188 node5188Labels := by rfl

def raw35700 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw35700Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35700step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw35700step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35700step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw35700step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw35700step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw35700step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical35700 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35700 raw35700Labels = mixedMoment B node5080 node5080Labels := by
  calc
    mixedMoment B raw35700 raw35700Labels = mixedMoment B raw35700step0 raw35700step0Labels := by
      have hz : ∀ j, raw35700 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35700step0 = (fun i j => raw35700 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35700step0 raw35700; decide +kernel
      have hl : raw35700step0Labels = raw35700Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35700 raw35700Labels permutation346 hz
    mixedMoment B raw35700step0 raw35700step0Labels = mixedMoment B raw35700step1 raw35700step1Labels := by
      have ha : raw35700step1 = (fun i j => raw35700step0 (permutation144 i) (permutation2 j)) := by apply Matrix.ext; unfold raw35700step1 raw35700step0; decide +kernel
      have hl : raw35700step1Labels = raw35700step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35700step0 raw35700step0Labels permutation144 permutation2
    mixedMoment B raw35700step1 raw35700step1Labels = mixedMoment B raw35700step2 raw35700step2Labels := by
      have ha : raw35700step2 = -raw35700step1 := by apply Matrix.ext; change ∀ i j, raw35700step2 i j = -(raw35700step1 i j); unfold raw35700step2 raw35700step1; decide +kernel
      have hl : raw35700step2Labels = raw35700step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5080 node5080Labels := by rfl

def raw35701 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35701Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35701step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 1, 2], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35701step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35701step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw35701step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35701step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35701step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35701step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw35701step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35701 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35701 raw35701Labels = mixedMoment B node3564 node3564Labels := by
  calc
    mixedMoment B raw35701 raw35701Labels = mixedMoment B raw35701step0 raw35701step0Labels := by
      have hz : ∀ j, raw35701 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35701step0 = (fun i j => raw35701 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35701step0 raw35701; decide +kernel
      have hl : raw35701step0Labels = raw35701Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35701 raw35701Labels permutation346 hz
    mixedMoment B raw35701step0 raw35701step0Labels = mixedMoment B raw35701step1 raw35701step1Labels := by
      have ha : raw35701step1 = (fun i j => raw35701step0 (permutation68 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35701step1 raw35701step0; decide +kernel
      have hl : raw35701step1Labels = raw35701step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35701step0 raw35701step0Labels permutation68 permutation7
    mixedMoment B raw35701step1 raw35701step1Labels = mixedMoment B raw35701step2 raw35701step2Labels := by
      have ha : raw35701step2 = -raw35701step1 := by apply Matrix.ext; change ∀ i j, raw35701step2 i j = -(raw35701step1 i j); unfold raw35701step2 raw35701step1; decide +kernel
      have hl : raw35701step2Labels = raw35701step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35701step2 raw35701step2Labels = mixedMoment B raw35701step3 raw35701step3Labels := by
      have ha : raw35701step3 = raw35701step2 := by apply Matrix.ext; unfold raw35701step3 raw35701step2; decide +kernel
      have hl : raw35701step2Labels = labelEmbedding1 ∘ raw35701step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35701step2 raw35701step2Labels raw35701step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3564 node3564Labels := by rfl

def raw35702 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35702Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35702step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35702step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35702step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35702step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35702 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35702 raw35702Labels = mixedMoment B node3799 node3799Labels := by
  calc
    mixedMoment B raw35702 raw35702Labels = mixedMoment B raw35702step0 raw35702step0Labels := by
      have ha : raw35702step0 = (fun i j => raw35702 (permutation649 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35702step0 raw35702; decide +kernel
      have hl : raw35702step0Labels = raw35702Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35702 raw35702Labels permutation649 permutation7
    mixedMoment B raw35702step0 raw35702step0Labels = mixedMoment B raw35702step1 raw35702step1Labels := by
      have ha : raw35702step1 = raw35702step0 := by apply Matrix.ext; unfold raw35702step1 raw35702step0; decide +kernel
      have hl : raw35702step0Labels = labelEmbedding1 ∘ raw35702step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35702step0 raw35702step0Labels raw35702step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3799 node3799Labels := by rfl

def raw35703 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35703Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35703step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35703step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35703step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35703step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35703step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35703step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35703 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35703 raw35703Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw35703 raw35703Labels = mixedMoment B raw35703step0 raw35703step0Labels := by
      have hz : ∀ j, raw35703 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35703step0 = (fun i j => raw35703 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35703step0 raw35703; decide +kernel
      have hl : raw35703step0Labels = raw35703Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35703 raw35703Labels permutation346 hz
    mixedMoment B raw35703step0 raw35703step0Labels = mixedMoment B raw35703step1 raw35703step1Labels := by
      have ha : raw35703step1 = (fun i j => raw35703step0 (permutation141 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35703step1 raw35703step0; decide +kernel
      have hl : raw35703step1Labels = raw35703step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35703step0 raw35703step0Labels permutation141 permutation7
    mixedMoment B raw35703step1 raw35703step1Labels = mixedMoment B raw35703step2 raw35703step2Labels := by
      have ha : raw35703step2 = raw35703step1 := by apply Matrix.ext; unfold raw35703step2 raw35703step1; decide +kernel
      have hl : raw35703step1Labels = labelEmbedding1 ∘ raw35703step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35703step1 raw35703step1Labels raw35703step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3850 node3850Labels := by rfl

def raw35704 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw35704Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35704step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw35704step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35704step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35704step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35704step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw35704step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35704 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35704 raw35704Labels = mixedMoment B node3807 node3807Labels := by
  calc
    mixedMoment B raw35704 raw35704Labels = mixedMoment B raw35704step0 raw35704step0Labels := by
      have hz : ∀ j, raw35704 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35704step0 = (fun i j => raw35704 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35704step0 raw35704; decide +kernel
      have hl : raw35704step0Labels = raw35704Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35704 raw35704Labels permutation346 hz
    mixedMoment B raw35704step0 raw35704step0Labels = mixedMoment B raw35704step1 raw35704step1Labels := by
      have ha : raw35704step1 = (fun i j => raw35704step0 (permutation141 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35704step1 raw35704step0; decide +kernel
      have hl : raw35704step1Labels = raw35704step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35704step0 raw35704step0Labels permutation141 permutation7
    mixedMoment B raw35704step1 raw35704step1Labels = mixedMoment B raw35704step2 raw35704step2Labels := by
      have ha : raw35704step2 = raw35704step1 := by apply Matrix.ext; unfold raw35704step2 raw35704step1; decide +kernel
      have hl : raw35704step1Labels = labelEmbedding1 ∘ raw35704step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35704step1 raw35704step1Labels raw35704step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3807 node3807Labels := by rfl

def raw35705 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw35705Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35705step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw35705step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35705step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw35705step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35705step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw35705step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35705step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw35705step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35705 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35705 raw35705Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw35705 raw35705Labels = mixedMoment B raw35705step0 raw35705step0Labels := by
      have hz : ∀ j, raw35705 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35705step0 = (fun i j => raw35705 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35705step0 raw35705; decide +kernel
      have hl : raw35705step0Labels = raw35705Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35705 raw35705Labels permutation346 hz
    mixedMoment B raw35705step0 raw35705step0Labels = mixedMoment B raw35705step1 raw35705step1Labels := by
      have ha : raw35705step1 = (fun i j => raw35705step0 (permutation68 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35705step1 raw35705step0; decide +kernel
      have hl : raw35705step1Labels = raw35705step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35705step0 raw35705step0Labels permutation68 permutation7
    mixedMoment B raw35705step1 raw35705step1Labels = mixedMoment B raw35705step2 raw35705step2Labels := by
      have ha : raw35705step2 = -raw35705step1 := by apply Matrix.ext; change ∀ i j, raw35705step2 i j = -(raw35705step1 i j); unfold raw35705step2 raw35705step1; decide +kernel
      have hl : raw35705step2Labels = raw35705step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35705step2 raw35705step2Labels = mixedMoment B raw35705step3 raw35705step3Labels := by
      have ha : raw35705step3 = raw35705step2 := by apply Matrix.ext; unfold raw35705step3 raw35705step2; decide +kernel
      have hl : raw35705step2Labels = labelEmbedding1 ∘ raw35705step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35705step2 raw35705step2Labels raw35705step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3876 node3876Labels := by rfl

def raw35706 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35706Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35706step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35706step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35706step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw35706step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35706step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw35706step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35706step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw35706step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35706 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35706 raw35706Labels = mixedMoment B node2251 node2251Labels := by
  calc
    mixedMoment B raw35706 raw35706Labels = mixedMoment B raw35706step0 raw35706step0Labels := by
      have hz : ∀ j, raw35706 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35706step0 = (fun i j => raw35706 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35706step0 raw35706; decide +kernel
      have hl : raw35706step0Labels = raw35706Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35706 raw35706Labels permutation346 hz
    mixedMoment B raw35706step0 raw35706step0Labels = mixedMoment B raw35706step1 raw35706step1Labels := by
      have ha : raw35706step1 = (fun i j => raw35706step0 (permutation42 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35706step1 raw35706step0; decide +kernel
      have hl : raw35706step1Labels = raw35706step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35706step0 raw35706step0Labels permutation42 permutation5
    mixedMoment B raw35706step1 raw35706step1Labels = mixedMoment B raw35706step2 raw35706step2Labels := by
      have ha : raw35706step2 = -raw35706step1 := by apply Matrix.ext; change ∀ i j, raw35706step2 i j = -(raw35706step1 i j); unfold raw35706step2 raw35706step1; decide +kernel
      have hl : raw35706step2Labels = raw35706step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35706step2 raw35706step2Labels = mixedMoment B raw35706step3 raw35706step3Labels := by
      have ha : raw35706step3 = raw35706step2 := by apply Matrix.ext; unfold raw35706step3 raw35706step2; decide +kernel
      have hl : raw35706step2Labels = labelEmbedding1 ∘ raw35706step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35706step2 raw35706step2Labels raw35706step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2251 node2251Labels := by rfl

def raw35707 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35707Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35707step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw35707step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35707step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw35707step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35707step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw35707step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35707 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35707 raw35707Labels = mixedMoment B node3802 node3802Labels := by
  calc
    mixedMoment B raw35707 raw35707Labels = mixedMoment B raw35707step0 raw35707step0Labels := by
      have ha : raw35707step0 = (fun i j => raw35707 (permutation186 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35707step0 raw35707; decide +kernel
      have hl : raw35707step0Labels = raw35707Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35707 raw35707Labels permutation186 permutation5
    mixedMoment B raw35707step0 raw35707step0Labels = mixedMoment B raw35707step1 raw35707step1Labels := by
      have ha : raw35707step1 = -raw35707step0 := by apply Matrix.ext; change ∀ i j, raw35707step1 i j = -(raw35707step0 i j); unfold raw35707step1 raw35707step0; decide +kernel
      have hl : raw35707step1Labels = raw35707step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35707step1 raw35707step1Labels = mixedMoment B raw35707step2 raw35707step2Labels := by
      have ha : raw35707step2 = raw35707step1 := by apply Matrix.ext; unfold raw35707step2 raw35707step1; decide +kernel
      have hl : raw35707step1Labels = labelEmbedding1 ∘ raw35707step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35707step1 raw35707step1Labels raw35707step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3802 node3802Labels := by rfl

def raw35708 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35708Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35708step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35708step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35708step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw35708step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35708step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw35708step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35708step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw35708step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35708 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35708 raw35708Labels = mixedMoment B node3854 node3854Labels := by
  calc
    mixedMoment B raw35708 raw35708Labels = mixedMoment B raw35708step0 raw35708step0Labels := by
      have hz : ∀ j, raw35708 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35708step0 = (fun i j => raw35708 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35708step0 raw35708; decide +kernel
      have hl : raw35708step0Labels = raw35708Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35708 raw35708Labels permutation346 hz
    mixedMoment B raw35708step0 raw35708step0Labels = mixedMoment B raw35708step1 raw35708step1Labels := by
      have ha : raw35708step1 = (fun i j => raw35708step0 (permutation42 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35708step1 raw35708step0; decide +kernel
      have hl : raw35708step1Labels = raw35708step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35708step0 raw35708step0Labels permutation42 permutation5
    mixedMoment B raw35708step1 raw35708step1Labels = mixedMoment B raw35708step2 raw35708step2Labels := by
      have ha : raw35708step2 = -raw35708step1 := by apply Matrix.ext; change ∀ i j, raw35708step2 i j = -(raw35708step1 i j); unfold raw35708step2 raw35708step1; decide +kernel
      have hl : raw35708step2Labels = raw35708step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35708step2 raw35708step2Labels = mixedMoment B raw35708step3 raw35708step3Labels := by
      have ha : raw35708step3 = raw35708step2 := by apply Matrix.ext; unfold raw35708step3 raw35708step2; decide +kernel
      have hl : raw35708step2Labels = labelEmbedding1 ∘ raw35708step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35708step2 raw35708step2Labels raw35708step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3854 node3854Labels := by rfl

def raw35709 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw35709Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35709step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw35709step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35709step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw35709step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35709step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw35709step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35709 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35709 raw35709Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw35709 raw35709Labels = mixedMoment B raw35709step0 raw35709step0Labels := by
      have hz : ∀ j, raw35709 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35709step0 = (fun i j => raw35709 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35709step0 raw35709; decide +kernel
      have hl : raw35709step0Labels = raw35709Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35709 raw35709Labels permutation346 hz
    mixedMoment B raw35709step0 raw35709step0Labels = mixedMoment B raw35709step1 raw35709step1Labels := by
      have ha : raw35709step1 = (fun i j => raw35709step0 (permutation141 i) (permutation7 j)) := by apply Matrix.ext; unfold raw35709step1 raw35709step0; decide +kernel
      have hl : raw35709step1Labels = raw35709step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35709step0 raw35709step0Labels permutation141 permutation7
    mixedMoment B raw35709step1 raw35709step1Labels = mixedMoment B raw35709step2 raw35709step2Labels := by
      have ha : raw35709step2 = raw35709step1 := by apply Matrix.ext; unfold raw35709step2 raw35709step1; decide +kernel
      have hl : raw35709step1Labels = labelEmbedding1 ∘ raw35709step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35709step1 raw35709step1Labels raw35709step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3813 node3813Labels := by rfl

def raw35710 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw35710Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35710step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw35710step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35710step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw35710step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35710step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw35710step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35710step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw35710step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35710 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35710 raw35710Labels = mixedMoment B node3881 node3881Labels := by
  calc
    mixedMoment B raw35710 raw35710Labels = mixedMoment B raw35710step0 raw35710step0Labels := by
      have hz : ∀ j, raw35710 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw35710step0 = (fun i j => raw35710 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw35710step0 raw35710; decide +kernel
      have hl : raw35710step0Labels = raw35710Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw35710 raw35710Labels permutation346 hz
    mixedMoment B raw35710step0 raw35710step0Labels = mixedMoment B raw35710step1 raw35710step1Labels := by
      have ha : raw35710step1 = (fun i j => raw35710step0 (permutation52 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35710step1 raw35710step0; decide +kernel
      have hl : raw35710step1Labels = raw35710step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35710step0 raw35710step0Labels permutation52 permutation5
    mixedMoment B raw35710step1 raw35710step1Labels = mixedMoment B raw35710step2 raw35710step2Labels := by
      have ha : raw35710step2 = -raw35710step1 := by apply Matrix.ext; change ∀ i j, raw35710step2 i j = -(raw35710step1 i j); unfold raw35710step2 raw35710step1; decide +kernel
      have hl : raw35710step2Labels = raw35710step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35710step2 raw35710step2Labels = mixedMoment B raw35710step3 raw35710step3Labels := by
      have ha : raw35710step3 = raw35710step2 := by apply Matrix.ext; unfold raw35710step3 raw35710step2; decide +kernel
      have hl : raw35710step2Labels = labelEmbedding1 ∘ raw35710step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35710step2 raw35710step2Labels raw35710step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3881 node3881Labels := by rfl

def raw35711 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw35711Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw35711step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw35711step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35711step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw35711step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw35711step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw35711step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical35711 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw35711 raw35711Labels = mixedMoment B node2145 node2145Labels := by
  calc
    mixedMoment B raw35711 raw35711Labels = mixedMoment B raw35711step0 raw35711step0Labels := by
      have ha : raw35711step0 = (fun i j => raw35711 (permutation162 i) (permutation5 j)) := by apply Matrix.ext; unfold raw35711step0 raw35711; decide +kernel
      have hl : raw35711step0Labels = raw35711Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw35711 raw35711Labels permutation162 permutation5
    mixedMoment B raw35711step0 raw35711step0Labels = mixedMoment B raw35711step1 raw35711step1Labels := by
      have ha : raw35711step1 = -raw35711step0 := by apply Matrix.ext; change ∀ i j, raw35711step1 i j = -(raw35711step0 i j); unfold raw35711step1 raw35711step0; decide +kernel
      have hl : raw35711step1Labels = raw35711step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw35711step1 raw35711step1Labels = mixedMoment B raw35711step2 raw35711step2Labels := by
      have ha : raw35711step2 = raw35711step1 := by apply Matrix.ext; unfold raw35711step2 raw35711step1; decide +kernel
      have hl : raw35711step1Labels = labelEmbedding1 ∘ raw35711step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw35711step1 raw35711step1Labels raw35711step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2145 node2145Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
