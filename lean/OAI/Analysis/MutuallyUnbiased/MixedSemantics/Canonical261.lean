import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw33408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw33408Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33408 raw33408Labels = mixedMoment B node4928 node4928Labels := by
  calc
    _ = mixedMoment B node4928 node4928Labels := by rfl

def raw33409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw33409Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33409 raw33409Labels = mixedMoment B node5029 node5029Labels := by
  calc
    _ = mixedMoment B node5029 node5029Labels := by rfl

def raw33410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw33410Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33410 raw33410Labels = mixedMoment B node5050 node5050Labels := by
  calc
    _ = mixedMoment B node5050 node5050Labels := by rfl

def raw33411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 1, -2]]
def raw33411Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33411step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw33411step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33411 raw33411Labels = mixedMoment B node5059 node5059Labels := by
  calc
    mixedMoment B raw33411 raw33411Labels = mixedMoment B raw33411step0 raw33411step0Labels := by
      have ha : raw33411step0 = (fun i j => raw33411 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33411step0 raw33411; decide +kernel
      have hl : raw33411step0Labels = raw33411Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33411 raw33411Labels permutation153 permutation2
    _ = mixedMoment B node5059 node5059Labels := by rfl

def raw33412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw33412Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33412 raw33412Labels = mixedMoment B node4523 node4523Labels := by
  calc
    _ = mixedMoment B node4523 node4523Labels := by rfl

def raw33413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw33413Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33413 raw33413Labels = mixedMoment B node4927 node4927Labels := by
  calc
    _ = mixedMoment B node4927 node4927Labels := by rfl

def raw33414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw33414Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33414 raw33414Labels = mixedMoment B node5026 node5026Labels := by
  calc
    _ = mixedMoment B node5026 node5026Labels := by rfl

def raw33415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw33415Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33415 raw33415Labels = mixedMoment B node5047 node5047Labels := by
  calc
    _ = mixedMoment B node5047 node5047Labels := by rfl

def raw33416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![3, -1, -2]]
def raw33416Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33416step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw33416step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33416 raw33416Labels = mixedMoment B node5047 node5047Labels := by
  calc
    mixedMoment B raw33416 raw33416Labels = mixedMoment B raw33416step0 raw33416step0Labels := by
      have ha : raw33416step0 = (fun i j => raw33416 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33416step0 raw33416; decide +kernel
      have hl : raw33416step0Labels = raw33416Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33416 raw33416Labels permutation154 permutation2
    _ = mixedMoment B node5047 node5047Labels := by rfl

def raw33417 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33417Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33417step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw33417step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33417step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw33417step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33417 raw33417Labels = mixedMoment B node5192 node5192Labels := by
  calc
    mixedMoment B raw33417 raw33417Labels = mixedMoment B raw33417step0 raw33417step0Labels := by
      have ha : raw33417step0 = (fun i j => raw33417 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33417step0 raw33417; decide +kernel
      have hl : raw33417step0Labels = raw33417Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33417 raw33417Labels permutation152 permutation7
    mixedMoment B raw33417step0 raw33417step0Labels = mixedMoment B raw33417step1 raw33417step1Labels := by
      have ha : raw33417step1 = raw33417step0 := by apply Matrix.ext; unfold raw33417step1 raw33417step0; decide +kernel
      have hl : raw33417step0Labels = labelEmbedding10 ∘ raw33417step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33417step0 raw33417step0Labels raw33417step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5192 node5192Labels := by rfl

def raw33418 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33418Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33418step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw33418step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33418step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw33418step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33418 raw33418Labels = mixedMoment B node5155 node5155Labels := by
  calc
    mixedMoment B raw33418 raw33418Labels = mixedMoment B raw33418step0 raw33418step0Labels := by
      have ha : raw33418step0 = (fun i j => raw33418 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33418step0 raw33418; decide +kernel
      have hl : raw33418step0Labels = raw33418Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33418 raw33418Labels permutation152 permutation7
    mixedMoment B raw33418step0 raw33418step0Labels = mixedMoment B raw33418step1 raw33418step1Labels := by
      have ha : raw33418step1 = raw33418step0 := by apply Matrix.ext; unfold raw33418step1 raw33418step0; decide +kernel
      have hl : raw33418step0Labels = labelEmbedding10 ∘ raw33418step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33418step0 raw33418step0Labels raw33418step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5155 node5155Labels := by rfl

def raw33419 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33419Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33419step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw33419step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33419step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw33419step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33419 raw33419Labels = mixedMoment B node5149 node5149Labels := by
  calc
    mixedMoment B raw33419 raw33419Labels = mixedMoment B raw33419step0 raw33419step0Labels := by
      have ha : raw33419step0 = (fun i j => raw33419 (permutation154 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33419step0 raw33419; decide +kernel
      have hl : raw33419step0Labels = raw33419Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33419 raw33419Labels permutation154 permutation7
    mixedMoment B raw33419step0 raw33419step0Labels = mixedMoment B raw33419step1 raw33419step1Labels := by
      have ha : raw33419step1 = raw33419step0 := by apply Matrix.ext; unfold raw33419step1 raw33419step0; decide +kernel
      have hl : raw33419step0Labels = labelEmbedding10 ∘ raw33419step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33419step0 raw33419step0Labels raw33419step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5149 node5149Labels := by rfl

def raw33420 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33420Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33420step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33420step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw33420step1Labels : Fin 2 → Fin 3 := ![1, 2]

def raw33420step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw33420step2Labels : Fin 2 → Fin 3 := ![1, 2]

def raw33420step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw33420step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical33420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33420 raw33420Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw33420 raw33420Labels = mixedMoment B raw33420step0 raw33420step0Labels := by
      have hz : ∀ j, raw33420 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33420step0 = (fun i j => raw33420 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33420step0 raw33420; decide +kernel
      have hl : raw33420step0Labels = raw33420Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33420 raw33420Labels permutation346 hz
    mixedMoment B raw33420step0 raw33420step0Labels = mixedMoment B raw33420step1 raw33420step1Labels := by
      have hz : ∀ i, raw33420step0 i (permutation2 0) = 0 := by decide +kernel
      have ha : raw33420step1 = (fun i j => raw33420step0 i (permutation2 j.succ)) := by apply Matrix.ext; unfold raw33420step1 raw33420step0; decide +kernel
      have hl : raw33420step1Labels = (fun j => raw33420step0Labels (permutation2 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw33420step0 raw33420step0Labels permutation2 hz
    mixedMoment B raw33420step1 raw33420step1Labels = mixedMoment B raw33420step2 raw33420step2Labels := by
      have ha : raw33420step2 = -raw33420step1 := by apply Matrix.ext; change ∀ i j, raw33420step2 i j = -(raw33420step1 i j); unfold raw33420step2 raw33420step1; decide +kernel
      have hl : raw33420step2Labels = raw33420step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33420step2 raw33420step2Labels = mixedMoment B raw33420step3 raw33420step3Labels := by
      have ha : raw33420step3 = raw33420step2 := by apply Matrix.ext; unfold raw33420step3 raw33420step2; decide +kernel
      have hl : raw33420step2Labels = labelEmbedding3 ∘ raw33420step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33420step2 raw33420step2Labels raw33420step3Labels labelEmbedding3 hl
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw33421 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33421Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33421step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33421step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33421step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw33421step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33421step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw33421step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33421 raw33421Labels = mixedMoment B node5017 node5017Labels := by
  calc
    mixedMoment B raw33421 raw33421Labels = mixedMoment B raw33421step0 raw33421step0Labels := by
      have hz : ∀ j, raw33421 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33421step0 = (fun i j => raw33421 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33421step0 raw33421; decide +kernel
      have hl : raw33421step0Labels = raw33421Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33421 raw33421Labels permutation346 hz
    mixedMoment B raw33421step0 raw33421step0Labels = mixedMoment B raw33421step1 raw33421step1Labels := by
      have ha : raw33421step1 = (fun i j => raw33421step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33421step1 raw33421step0; decide +kernel
      have hl : raw33421step1Labels = raw33421step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33421step0 raw33421step0Labels permutation32 permutation6
    mixedMoment B raw33421step1 raw33421step1Labels = mixedMoment B raw33421step2 raw33421step2Labels := by
      have ha : raw33421step2 = raw33421step1 := by apply Matrix.ext; unfold raw33421step2 raw33421step1; decide +kernel
      have hl : raw33421step1Labels = labelEmbedding9 ∘ raw33421step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33421step1 raw33421step1Labels raw33421step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5017 node5017Labels := by rfl

def raw33422 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33422Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33422step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw33422step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33422step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw33422step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33422step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw33422step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33422 raw33422Labels = mixedMoment B node4715 node4715Labels := by
  calc
    mixedMoment B raw33422 raw33422Labels = mixedMoment B raw33422step0 raw33422step0Labels := by
      have ha : raw33422step0 = (fun i j => raw33422 (permutation154 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33422step0 raw33422; decide +kernel
      have hl : raw33422step0Labels = raw33422Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33422 raw33422Labels permutation154 permutation4
    mixedMoment B raw33422step0 raw33422step0Labels = mixedMoment B raw33422step1 raw33422step1Labels := by
      have ha : raw33422step1 = -raw33422step0 := by apply Matrix.ext; change ∀ i j, raw33422step1 i j = -(raw33422step0 i j); unfold raw33422step1 raw33422step0; decide +kernel
      have hl : raw33422step1Labels = raw33422step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33422step1 raw33422step1Labels = mixedMoment B raw33422step2 raw33422step2Labels := by
      have ha : raw33422step2 = raw33422step1 := by apply Matrix.ext; unfold raw33422step2 raw33422step1; decide +kernel
      have hl : raw33422step1Labels = labelEmbedding7 ∘ raw33422step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33422step1 raw33422step1Labels raw33422step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4715 node4715Labels := by rfl

def raw33423 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33423Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33423step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw33423step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33423step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw33423step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33423 raw33423Labels = mixedMoment B node4990 node4990Labels := by
  calc
    mixedMoment B raw33423 raw33423Labels = mixedMoment B raw33423step0 raw33423step0Labels := by
      have ha : raw33423step0 = (fun i j => raw33423 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33423step0 raw33423; decide +kernel
      have hl : raw33423step0Labels = raw33423Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33423 raw33423Labels permutation154 permutation6
    mixedMoment B raw33423step0 raw33423step0Labels = mixedMoment B raw33423step1 raw33423step1Labels := by
      have ha : raw33423step1 = raw33423step0 := by apply Matrix.ext; unfold raw33423step1 raw33423step0; decide +kernel
      have hl : raw33423step0Labels = labelEmbedding9 ∘ raw33423step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33423step0 raw33423step0Labels raw33423step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4990 node4990Labels := by rfl

def raw33424 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33424Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33424step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw33424step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33424step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw33424step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33424 raw33424Labels = mixedMoment B node5046 node5046Labels := by
  calc
    mixedMoment B raw33424 raw33424Labels = mixedMoment B raw33424step0 raw33424step0Labels := by
      have ha : raw33424step0 = (fun i j => raw33424 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33424step0 raw33424; decide +kernel
      have hl : raw33424step0Labels = raw33424Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33424 raw33424Labels permutation154 permutation6
    mixedMoment B raw33424step0 raw33424step0Labels = mixedMoment B raw33424step1 raw33424step1Labels := by
      have ha : raw33424step1 = raw33424step0 := by apply Matrix.ext; unfold raw33424step1 raw33424step0; decide +kernel
      have hl : raw33424step0Labels = labelEmbedding9 ∘ raw33424step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33424step0 raw33424step0Labels raw33424step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5046 node5046Labels := by rfl

def raw33425 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![0, -2, 2]]
def raw33425Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33425step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw33425step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33425step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw33425step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33425step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw33425step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33425 raw33425Labels = mixedMoment B node4715 node4715Labels := by
  calc
    mixedMoment B raw33425 raw33425Labels = mixedMoment B raw33425step0 raw33425step0Labels := by
      have ha : raw33425step0 = (fun i j => raw33425 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33425step0 raw33425; decide +kernel
      have hl : raw33425step0Labels = raw33425Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33425 raw33425Labels permutation152 permutation4
    mixedMoment B raw33425step0 raw33425step0Labels = mixedMoment B raw33425step1 raw33425step1Labels := by
      have ha : raw33425step1 = -raw33425step0 := by apply Matrix.ext; change ∀ i j, raw33425step1 i j = -(raw33425step0 i j); unfold raw33425step1 raw33425step0; decide +kernel
      have hl : raw33425step1Labels = raw33425step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33425step1 raw33425step1Labels = mixedMoment B raw33425step2 raw33425step2Labels := by
      have ha : raw33425step2 = raw33425step1 := by apply Matrix.ext; unfold raw33425step2 raw33425step1; decide +kernel
      have hl : raw33425step1Labels = labelEmbedding7 ∘ raw33425step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33425step1 raw33425step1Labels raw33425step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4715 node4715Labels := by rfl

def raw33426 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![0, -2, 2]]
def raw33426Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33426step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw33426step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33426step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw33426step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33426 raw33426Labels = mixedMoment B node4990 node4990Labels := by
  calc
    mixedMoment B raw33426 raw33426Labels = mixedMoment B raw33426step0 raw33426step0Labels := by
      have ha : raw33426step0 = (fun i j => raw33426 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33426step0 raw33426; decide +kernel
      have hl : raw33426step0Labels = raw33426Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33426 raw33426Labels permutation152 permutation6
    mixedMoment B raw33426step0 raw33426step0Labels = mixedMoment B raw33426step1 raw33426step1Labels := by
      have ha : raw33426step1 = raw33426step0 := by apply Matrix.ext; unfold raw33426step1 raw33426step0; decide +kernel
      have hl : raw33426step0Labels = labelEmbedding9 ∘ raw33426step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33426step0 raw33426step0Labels raw33426step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4990 node4990Labels := by rfl

def raw33427 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1], ![0, -2, 2]]
def raw33427Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33427step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw33427step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33427step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![2, 0, -2]]
def raw33427step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33427 raw33427Labels = mixedMoment B node5046 node5046Labels := by
  calc
    mixedMoment B raw33427 raw33427Labels = mixedMoment B raw33427step0 raw33427step0Labels := by
      have ha : raw33427step0 = (fun i j => raw33427 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33427step0 raw33427; decide +kernel
      have hl : raw33427step0Labels = raw33427Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33427 raw33427Labels permutation152 permutation6
    mixedMoment B raw33427step0 raw33427step0Labels = mixedMoment B raw33427step1 raw33427step1Labels := by
      have ha : raw33427step1 = raw33427step0 := by apply Matrix.ext; unfold raw33427step1 raw33427step0; decide +kernel
      have hl : raw33427step0Labels = labelEmbedding9 ∘ raw33427step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33427step0 raw33427step0Labels raw33427step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5046 node5046Labels := by rfl

def raw33428 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -2, 2]]
def raw33428Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33428step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw33428step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33428step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw33428step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33428 raw33428Labels = mixedMoment B node5056 node5056Labels := by
  calc
    mixedMoment B raw33428 raw33428Labels = mixedMoment B raw33428step0 raw33428step0Labels := by
      have ha : raw33428step0 = (fun i j => raw33428 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33428step0 raw33428; decide +kernel
      have hl : raw33428step0Labels = raw33428Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33428 raw33428Labels permutation152 permutation6
    mixedMoment B raw33428step0 raw33428step0Labels = mixedMoment B raw33428step1 raw33428step1Labels := by
      have ha : raw33428step1 = raw33428step0 := by apply Matrix.ext; unfold raw33428step1 raw33428step0; decide +kernel
      have hl : raw33428step0Labels = labelEmbedding9 ∘ raw33428step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33428step0 raw33428step0Labels raw33428step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5056 node5056Labels := by rfl

def raw33429 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -3, 2]]
def raw33429Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33429step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw33429step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33429step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw33429step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33429step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw33429step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33429 raw33429Labels = mixedMoment B node4712 node4712Labels := by
  calc
    mixedMoment B raw33429 raw33429Labels = mixedMoment B raw33429step0 raw33429step0Labels := by
      have ha : raw33429step0 = (fun i j => raw33429 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33429step0 raw33429; decide +kernel
      have hl : raw33429step0Labels = raw33429Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33429 raw33429Labels permutation152 permutation4
    mixedMoment B raw33429step0 raw33429step0Labels = mixedMoment B raw33429step1 raw33429step1Labels := by
      have ha : raw33429step1 = -raw33429step0 := by apply Matrix.ext; change ∀ i j, raw33429step1 i j = -(raw33429step0 i j); unfold raw33429step1 raw33429step0; decide +kernel
      have hl : raw33429step1Labels = raw33429step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33429step1 raw33429step1Labels = mixedMoment B raw33429step2 raw33429step2Labels := by
      have ha : raw33429step2 = raw33429step1 := by apply Matrix.ext; unfold raw33429step2 raw33429step1; decide +kernel
      have hl : raw33429step1Labels = labelEmbedding7 ∘ raw33429step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33429step1 raw33429step1Labels raw33429step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4712 node4712Labels := by rfl

def raw33430 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -3, 2]]
def raw33430Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33430step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw33430step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33430step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw33430step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33430 raw33430Labels = mixedMoment B node4989 node4989Labels := by
  calc
    mixedMoment B raw33430 raw33430Labels = mixedMoment B raw33430step0 raw33430step0Labels := by
      have ha : raw33430step0 = (fun i j => raw33430 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33430step0 raw33430; decide +kernel
      have hl : raw33430step0Labels = raw33430Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33430 raw33430Labels permutation152 permutation6
    mixedMoment B raw33430step0 raw33430step0Labels = mixedMoment B raw33430step1 raw33430step1Labels := by
      have ha : raw33430step1 = raw33430step0 := by apply Matrix.ext; unfold raw33430step1 raw33430step0; decide +kernel
      have hl : raw33430step0Labels = labelEmbedding9 ∘ raw33430step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33430step0 raw33430step0Labels raw33430step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4989 node4989Labels := by rfl

def raw33431 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, -3, 2]]
def raw33431Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33431step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw33431step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33431step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw33431step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33431 raw33431Labels = mixedMoment B node5028 node5028Labels := by
  calc
    mixedMoment B raw33431 raw33431Labels = mixedMoment B raw33431step0 raw33431step0Labels := by
      have ha : raw33431step0 = (fun i j => raw33431 (permutation662 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33431step0 raw33431; decide +kernel
      have hl : raw33431step0Labels = raw33431Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33431 raw33431Labels permutation662 permutation4
    mixedMoment B raw33431step0 raw33431step0Labels = mixedMoment B raw33431step1 raw33431step1Labels := by
      have ha : raw33431step1 = raw33431step0 := by apply Matrix.ext; unfold raw33431step1 raw33431step0; decide +kernel
      have hl : raw33431step0Labels = labelEmbedding7 ∘ raw33431step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33431step0 raw33431step0Labels raw33431step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5028 node5028Labels := by rfl

def raw33432 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -3, 2]]
def raw33432Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33432step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw33432step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33432step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw33432step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33432 raw33432Labels = mixedMoment B node5055 node5055Labels := by
  calc
    mixedMoment B raw33432 raw33432Labels = mixedMoment B raw33432step0 raw33432step0Labels := by
      have ha : raw33432step0 = (fun i j => raw33432 (permutation688 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33432step0 raw33432; decide +kernel
      have hl : raw33432step0Labels = raw33432Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33432 raw33432Labels permutation688 permutation4
    mixedMoment B raw33432step0 raw33432step0Labels = mixedMoment B raw33432step1 raw33432step1Labels := by
      have ha : raw33432step1 = raw33432step0 := by apply Matrix.ext; unfold raw33432step1 raw33432step0; decide +kernel
      have hl : raw33432step0Labels = labelEmbedding7 ∘ raw33432step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33432step0 raw33432step0Labels raw33432step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5055 node5055Labels := by rfl

def raw33433 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw33433Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33433step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33433step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33433step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33433step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33433 raw33433Labels = mixedMoment B node3352 node3352Labels := by
  calc
    mixedMoment B raw33433 raw33433Labels = mixedMoment B raw33433step0 raw33433step0Labels := by
      have ha : raw33433step0 = (fun i j => raw33433 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33433step0 raw33433; decide +kernel
      have hl : raw33433step0Labels = raw33433Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33433 raw33433Labels permutation152 permutation4
    mixedMoment B raw33433step0 raw33433step0Labels = mixedMoment B raw33433step1 raw33433step1Labels := by
      have ha : raw33433step1 = -raw33433step0 := by apply Matrix.ext; change ∀ i j, raw33433step1 i j = -(raw33433step0 i j); unfold raw33433step1 raw33433step0; decide +kernel
      have hl : raw33433step1Labels = raw33433step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3352 node3352Labels := by rfl

def raw33434 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw33434Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33434step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33434step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33434step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33434step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33434 raw33434Labels = mixedMoment B node1943 node1943Labels := by
  calc
    mixedMoment B raw33434 raw33434Labels = mixedMoment B raw33434step0 raw33434step0Labels := by
      have ha : raw33434step0 = (fun i j => raw33434 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33434step0 raw33434; decide +kernel
      have hl : raw33434step0Labels = raw33434Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33434 raw33434Labels permutation152 permutation4
    mixedMoment B raw33434step0 raw33434step0Labels = mixedMoment B raw33434step1 raw33434step1Labels := by
      have ha : raw33434step1 = -raw33434step0 := by apply Matrix.ext; change ∀ i j, raw33434step1 i j = -(raw33434step0 i j); unfold raw33434step1 raw33434step0; decide +kernel
      have hl : raw33434step1Labels = raw33434step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1943 node1943Labels := by rfl

def raw33435 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![2, -2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw33435Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33435step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw33435step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33435step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw33435step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33435 raw33435Labels = mixedMoment B node1776 node1776Labels := by
  calc
    mixedMoment B raw33435 raw33435Labels = mixedMoment B raw33435step0 raw33435step0Labels := by
      have ha : raw33435step0 = (fun i j => raw33435 (permutation161 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33435step0 raw33435; decide +kernel
      have hl : raw33435step0Labels = raw33435Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33435 raw33435Labels permutation161 permutation4
    mixedMoment B raw33435step0 raw33435step0Labels = mixedMoment B raw33435step1 raw33435step1Labels := by
      have ha : raw33435step1 = -raw33435step0 := by apply Matrix.ext; change ∀ i j, raw33435step1 i j = -(raw33435step0 i j); unfold raw33435step1 raw33435step0; decide +kernel
      have hl : raw33435step1Labels = raw33435step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1776 node1776Labels := by rfl

def raw33436 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw33436Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33436step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw33436step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33436step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw33436step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33436 raw33436Labels = mixedMoment B node1771 node1771Labels := by
  calc
    mixedMoment B raw33436 raw33436Labels = mixedMoment B raw33436step0 raw33436step0Labels := by
      have ha : raw33436step0 = (fun i j => raw33436 (permutation155 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33436step0 raw33436; decide +kernel
      have hl : raw33436step0Labels = raw33436Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33436 raw33436Labels permutation155 permutation4
    mixedMoment B raw33436step0 raw33436step0Labels = mixedMoment B raw33436step1 raw33436step1Labels := by
      have ha : raw33436step1 = -raw33436step0 := by apply Matrix.ext; change ∀ i j, raw33436step1 i j = -(raw33436step0 i j); unfold raw33436step1 raw33436step0; decide +kernel
      have hl : raw33436step1Labels = raw33436step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1771 node1771Labels := by rfl

def raw33437 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw33437Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33437step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw33437step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33437step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw33437step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33437 raw33437Labels = mixedMoment B node1771 node1771Labels := by
  calc
    mixedMoment B raw33437 raw33437Labels = mixedMoment B raw33437step0 raw33437step0Labels := by
      have ha : raw33437step0 = (fun i j => raw33437 (permutation153 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33437step0 raw33437; decide +kernel
      have hl : raw33437step0Labels = raw33437Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33437 raw33437Labels permutation153 permutation4
    mixedMoment B raw33437step0 raw33437step0Labels = mixedMoment B raw33437step1 raw33437step1Labels := by
      have ha : raw33437step1 = -raw33437step0 := by apply Matrix.ext; change ∀ i j, raw33437step1 i j = -(raw33437step0 i j); unfold raw33437step1 raw33437step0; decide +kernel
      have hl : raw33437step1Labels = raw33437step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1771 node1771Labels := by rfl

def raw33438 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33438Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33438step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw33438step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33438step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw33438step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33438 raw33438Labels = mixedMoment B node1770 node1770Labels := by
  calc
    mixedMoment B raw33438 raw33438Labels = mixedMoment B raw33438step0 raw33438step0Labels := by
      have ha : raw33438step0 = (fun i j => raw33438 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33438step0 raw33438; decide +kernel
      have hl : raw33438step0Labels = raw33438Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33438 raw33438Labels permutation152 permutation4
    mixedMoment B raw33438step0 raw33438step0Labels = mixedMoment B raw33438step1 raw33438step1Labels := by
      have ha : raw33438step1 = -raw33438step0 := by apply Matrix.ext; change ∀ i j, raw33438step1 i j = -(raw33438step0 i j); unfold raw33438step1 raw33438step0; decide +kernel
      have hl : raw33438step1Labels = raw33438step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1770 node1770Labels := by rfl

def raw33439 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33439Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33439step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![2, 1, -3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw33439step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33439step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, -1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw33439step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33439 raw33439Labels = mixedMoment B node2791 node2791Labels := by
  calc
    mixedMoment B raw33439 raw33439Labels = mixedMoment B raw33439step0 raw33439step0Labels := by
      have ha : raw33439step0 = (fun i j => raw33439 (permutation265 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33439step0 raw33439; decide +kernel
      have hl : raw33439step0Labels = raw33439Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33439 raw33439Labels permutation265 permutation4
    mixedMoment B raw33439step0 raw33439step0Labels = mixedMoment B raw33439step1 raw33439step1Labels := by
      have ha : raw33439step1 = -raw33439step0 := by apply Matrix.ext; change ∀ i j, raw33439step1 i j = -(raw33439step0 i j); unfold raw33439step1 raw33439step0; decide +kernel
      have hl : raw33439step1Labels = raw33439step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2791 node2791Labels := by rfl

def raw33440 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33440Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33440step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33440step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw33440step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33440step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw33440step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33440 raw33440Labels = mixedMoment B node3356 node3356Labels := by
  calc
    mixedMoment B raw33440 raw33440Labels = mixedMoment B raw33440step0 raw33440step0Labels := by
      have hz : ∀ j, raw33440 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33440step0 = (fun i j => raw33440 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33440step0 raw33440; decide +kernel
      have hl : raw33440step0Labels = raw33440Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33440 raw33440Labels permutation346 hz
    mixedMoment B raw33440step0 raw33440step0Labels = mixedMoment B raw33440step1 raw33440step1Labels := by
      have ha : raw33440step1 = (fun i j => raw33440step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33440step1 raw33440step0; decide +kernel
      have hl : raw33440step1Labels = raw33440step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33440step0 raw33440step0Labels permutation32 permutation4
    mixedMoment B raw33440step1 raw33440step1Labels = mixedMoment B raw33440step2 raw33440step2Labels := by
      have ha : raw33440step2 = -raw33440step1 := by apply Matrix.ext; change ∀ i j, raw33440step2 i j = -(raw33440step1 i j); unfold raw33440step2 raw33440step1; decide +kernel
      have hl : raw33440step2Labels = raw33440step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3356 node3356Labels := by rfl

def raw33441 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33441Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33441step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw33441step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33441step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33441step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33441 raw33441Labels = mixedMoment B node3340 node3340Labels := by
  calc
    mixedMoment B raw33441 raw33441Labels = mixedMoment B raw33441step0 raw33441step0Labels := by
      have ha : raw33441step0 = (fun i j => raw33441 (permutation158 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33441step0 raw33441; decide +kernel
      have hl : raw33441step0Labels = raw33441Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33441 raw33441Labels permutation158 permutation4
    mixedMoment B raw33441step0 raw33441step0Labels = mixedMoment B raw33441step1 raw33441step1Labels := by
      have ha : raw33441step1 = -raw33441step0 := by apply Matrix.ext; change ∀ i j, raw33441step1 i j = -(raw33441step0 i j); unfold raw33441step1 raw33441step0; decide +kernel
      have hl : raw33441step1Labels = raw33441step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3340 node3340Labels := by rfl

def raw33442 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33442Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33442step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw33442step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33442step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33442step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33442 raw33442Labels = mixedMoment B node3340 node3340Labels := by
  calc
    mixedMoment B raw33442 raw33442Labels = mixedMoment B raw33442step0 raw33442step0Labels := by
      have ha : raw33442step0 = (fun i j => raw33442 (permutation164 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33442step0 raw33442; decide +kernel
      have hl : raw33442step0Labels = raw33442Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33442 raw33442Labels permutation164 permutation4
    mixedMoment B raw33442step0 raw33442step0Labels = mixedMoment B raw33442step1 raw33442step1Labels := by
      have ha : raw33442step1 = -raw33442step0 := by apply Matrix.ext; change ∀ i j, raw33442step1 i j = -(raw33442step0 i j); unfold raw33442step1 raw33442step0; decide +kernel
      have hl : raw33442step1Labels = raw33442step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3340 node3340Labels := by rfl

def raw33443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33443Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33443step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33443step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33443 raw33443Labels = mixedMoment B node3650 node3650Labels := by
  calc
    mixedMoment B raw33443 raw33443Labels = mixedMoment B raw33443step0 raw33443step0Labels := by
      have ha : raw33443step0 = (fun i j => raw33443 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33443step0 raw33443; decide +kernel
      have hl : raw33443step0Labels = raw33443Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33443 raw33443Labels permutation154 permutation2
    _ = mixedMoment B node3650 node3650Labels := by rfl

def raw33444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33444Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33444step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33444step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33444 raw33444Labels = mixedMoment B node2382 node2382Labels := by
  calc
    mixedMoment B raw33444 raw33444Labels = mixedMoment B raw33444step0 raw33444step0Labels := by
      have ha : raw33444step0 = (fun i j => raw33444 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33444step0 raw33444; decide +kernel
      have hl : raw33444step0Labels = raw33444Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33444 raw33444Labels permutation154 permutation2
    _ = mixedMoment B node2382 node2382Labels := by rfl

def raw33445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33445Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33445step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw33445step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33445 raw33445Labels = mixedMoment B node2304 node2304Labels := by
  calc
    mixedMoment B raw33445 raw33445Labels = mixedMoment B raw33445step0 raw33445step0Labels := by
      have ha : raw33445step0 = (fun i j => raw33445 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33445step0 raw33445; decide +kernel
      have hl : raw33445step0Labels = raw33445Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33445 raw33445Labels permutation164 permutation2
    _ = mixedMoment B node2304 node2304Labels := by rfl

def raw33446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw33446Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33446step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33446step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33446 raw33446Labels = mixedMoment B node2296 node2296Labels := by
  calc
    mixedMoment B raw33446 raw33446Labels = mixedMoment B raw33446step0 raw33446step0Labels := by
      have ha : raw33446step0 = (fun i j => raw33446 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33446step0 raw33446; decide +kernel
      have hl : raw33446step0Labels = raw33446Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33446 raw33446Labels permutation154 permutation2
    _ = mixedMoment B node2296 node2296Labels := by rfl

def raw33447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33447Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33447 raw33447Labels = mixedMoment B node2298 node2298Labels := by
  calc
    _ = mixedMoment B node2298 node2298Labels := by rfl

def raw33448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw33448Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33448step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33448step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33448 raw33448Labels = mixedMoment B node2295 node2295Labels := by
  calc
    mixedMoment B raw33448 raw33448Labels = mixedMoment B raw33448step0 raw33448step0Labels := by
      have ha : raw33448step0 = (fun i j => raw33448 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33448step0 raw33448; decide +kernel
      have hl : raw33448step0Labels = raw33448Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33448 raw33448Labels permutation154 permutation2
    _ = mixedMoment B node2295 node2295Labels := by rfl

def raw33449 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![0, 0], ![2, -2]]
def raw33449Labels : Fin 2 → Fin 2 := ![0, 1]

def raw33449step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw33449step0Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical33449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33449 raw33449Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw33449 raw33449Labels = mixedMoment B raw33449step0 raw33449step0Labels := by
      have hz : ∀ j, raw33449 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33449step0 = (fun i j => raw33449 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33449step0 raw33449; decide +kernel
      have hl : raw33449step0Labels = raw33449Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33449 raw33449Labels permutation520 hz
    _ = mixedMoment B node4088 node4088Labels := by rfl

def raw33450 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw33450Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw33450step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33450step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw33450step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33450step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw33450step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33450 raw33450Labels = mixedMoment B node3357 node3357Labels := by
  calc
    mixedMoment B raw33450 raw33450Labels = mixedMoment B raw33450step0 raw33450step0Labels := by
      have hz : ∀ j, raw33450 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33450step0 = (fun i j => raw33450 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33450step0 raw33450; decide +kernel
      have hl : raw33450step0Labels = raw33450Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33450 raw33450Labels permutation346 hz
    mixedMoment B raw33450step0 raw33450step0Labels = mixedMoment B raw33450step1 raw33450step1Labels := by
      have ha : raw33450step1 = (fun i j => raw33450step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33450step1 raw33450step0; decide +kernel
      have hl : raw33450step1Labels = raw33450step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33450step0 raw33450step0Labels permutation35 permutation4
    mixedMoment B raw33450step1 raw33450step1Labels = mixedMoment B raw33450step2 raw33450step2Labels := by
      have ha : raw33450step2 = -raw33450step1 := by apply Matrix.ext; change ∀ i j, raw33450step2 i j = -(raw33450step1 i j); unfold raw33450step2 raw33450step1; decide +kernel
      have hl : raw33450step2Labels = raw33450step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3357 node3357Labels := by rfl

def raw33451 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![0, 0, 0], ![2, -3, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw33451Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33451step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![2, -3, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw33451step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33451step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw33451step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33451step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw33451step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33451 raw33451Labels = mixedMoment B node1778 node1778Labels := by
  calc
    mixedMoment B raw33451 raw33451Labels = mixedMoment B raw33451step0 raw33451step0Labels := by
      have hz : ∀ j, raw33451 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33451step0 = (fun i j => raw33451 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33451step0 raw33451; decide +kernel
      have hl : raw33451step0Labels = raw33451Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33451 raw33451Labels permutation346 hz
    mixedMoment B raw33451step0 raw33451step0Labels = mixedMoment B raw33451step1 raw33451step1Labels := by
      have ha : raw33451step1 = (fun i j => raw33451step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33451step1 raw33451step0; decide +kernel
      have hl : raw33451step1Labels = raw33451step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33451step0 raw33451step0Labels permutation35 permutation4
    mixedMoment B raw33451step1 raw33451step1Labels = mixedMoment B raw33451step2 raw33451step2Labels := by
      have ha : raw33451step2 = -raw33451step1 := by apply Matrix.ext; change ∀ i j, raw33451step2 i j = -(raw33451step1 i j); unfold raw33451step2 raw33451step1; decide +kernel
      have hl : raw33451step2Labels = raw33451step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1778 node1778Labels := by rfl

def raw33452 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw33452Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33452step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![1, -2, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw33452step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33452step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, -1, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw33452step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33452step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw33452step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33452 raw33452Labels = mixedMoment B node1782 node1782Labels := by
  calc
    mixedMoment B raw33452 raw33452Labels = mixedMoment B raw33452step0 raw33452step0Labels := by
      have hz : ∀ j, raw33452 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33452step0 = (fun i j => raw33452 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33452step0 raw33452; decide +kernel
      have hl : raw33452step0Labels = raw33452Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33452 raw33452Labels permutation346 hz
    mixedMoment B raw33452step0 raw33452step0Labels = mixedMoment B raw33452step1 raw33452step1Labels := by
      have ha : raw33452step1 = (fun i j => raw33452step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33452step1 raw33452step0; decide +kernel
      have hl : raw33452step1Labels = raw33452step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33452step0 raw33452step0Labels permutation36 permutation4
    mixedMoment B raw33452step1 raw33452step1Labels = mixedMoment B raw33452step2 raw33452step2Labels := by
      have ha : raw33452step2 = -raw33452step1 := by apply Matrix.ext; change ∀ i j, raw33452step2 i j = -(raw33452step1 i j); unfold raw33452step2 raw33452step1; decide +kernel
      have hl : raw33452step2Labels = raw33452step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1782 node1782Labels := by rfl

def raw33453 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33453Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![1, -2, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33453step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33453step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw33453step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33453step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw33453step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33453 raw33453Labels = mixedMoment B node1780 node1780Labels := by
  calc
    mixedMoment B raw33453 raw33453Labels = mixedMoment B raw33453step0 raw33453step0Labels := by
      have hz : ∀ j, raw33453 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33453step0 = (fun i j => raw33453 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33453step0 raw33453; decide +kernel
      have hl : raw33453step0Labels = raw33453Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33453 raw33453Labels permutation346 hz
    mixedMoment B raw33453step0 raw33453step0Labels = mixedMoment B raw33453step1 raw33453step1Labels := by
      have ha : raw33453step1 = (fun i j => raw33453step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33453step1 raw33453step0; decide +kernel
      have hl : raw33453step1Labels = raw33453step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33453step0 raw33453step0Labels permutation34 permutation4
    mixedMoment B raw33453step1 raw33453step1Labels = mixedMoment B raw33453step2 raw33453step2Labels := by
      have ha : raw33453step2 = -raw33453step1 := by apply Matrix.ext; change ∀ i j, raw33453step2 i j = -(raw33453step1 i j); unfold raw33453step2 raw33453step1; decide +kernel
      have hl : raw33453step2Labels = raw33453step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1780 node1780Labels := by rfl

def raw33454 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33454Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33454step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 3, -1], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33454step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33454step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 2, 0]]
def raw33454step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33454step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw33454step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33454step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw33454step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33454 raw33454Labels = mixedMoment B node5213 node5213Labels := by
  calc
    mixedMoment B raw33454 raw33454Labels = mixedMoment B raw33454step0 raw33454step0Labels := by
      have hz : ∀ j, raw33454 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33454step0 = (fun i j => raw33454 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33454step0 raw33454; decide +kernel
      have hl : raw33454step0Labels = raw33454Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33454 raw33454Labels permutation346 hz
    mixedMoment B raw33454step0 raw33454step0Labels = mixedMoment B raw33454step1 raw33454step1Labels := by
      have ha : raw33454step1 = (fun i j => raw33454step0 (permutation56 i) (permutation5 j)) := by apply Matrix.ext; unfold raw33454step1 raw33454step0; decide +kernel
      have hl : raw33454step1Labels = raw33454step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33454step0 raw33454step0Labels permutation56 permutation5
    mixedMoment B raw33454step1 raw33454step1Labels = mixedMoment B raw33454step2 raw33454step2Labels := by
      have ha : raw33454step2 = -raw33454step1 := by apply Matrix.ext; change ∀ i j, raw33454step2 i j = -(raw33454step1 i j); unfold raw33454step2 raw33454step1; decide +kernel
      have hl : raw33454step2Labels = raw33454step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33454step2 raw33454step2Labels = mixedMoment B raw33454step3 raw33454step3Labels := by
      have ha : raw33454step3 = raw33454step2 := by apply Matrix.ext; unfold raw33454step3 raw33454step2; decide +kernel
      have hl : raw33454step2Labels = labelEmbedding8 ∘ raw33454step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33454step2 raw33454step2Labels raw33454step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5213 node5213Labels := by rfl

def raw33455 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33455Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33455step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33455step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33455step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw33455step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33455step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw33455step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33455 raw33455Labels = mixedMoment B node5204 node5204Labels := by
  calc
    mixedMoment B raw33455 raw33455Labels = mixedMoment B raw33455step0 raw33455step0Labels := by
      have hz : ∀ j, raw33455 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33455step0 = (fun i j => raw33455 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33455step0 raw33455; decide +kernel
      have hl : raw33455step0Labels = raw33455Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33455 raw33455Labels permutation346 hz
    mixedMoment B raw33455step0 raw33455step0Labels = mixedMoment B raw33455step1 raw33455step1Labels := by
      have ha : raw33455step1 = (fun i j => raw33455step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33455step1 raw33455step0; decide +kernel
      have hl : raw33455step1Labels = raw33455step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33455step0 raw33455step0Labels permutation34 permutation7
    mixedMoment B raw33455step1 raw33455step1Labels = mixedMoment B raw33455step2 raw33455step2Labels := by
      have ha : raw33455step2 = raw33455step1 := by apply Matrix.ext; unfold raw33455step2 raw33455step1; decide +kernel
      have hl : raw33455step1Labels = labelEmbedding10 ∘ raw33455step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33455step1 raw33455step1Labels raw33455step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5204 node5204Labels := by rfl

def raw33456 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33456Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33456step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33456step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw33456step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33456step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw33456step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33456 raw33456Labels = mixedMoment B node5204 node5204Labels := by
  calc
    mixedMoment B raw33456 raw33456Labels = mixedMoment B raw33456step0 raw33456step0Labels := by
      have hz : ∀ j, raw33456 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33456step0 = (fun i j => raw33456 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33456step0 raw33456; decide +kernel
      have hl : raw33456step0Labels = raw33456Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33456 raw33456Labels permutation346 hz
    mixedMoment B raw33456step0 raw33456step0Labels = mixedMoment B raw33456step1 raw33456step1Labels := by
      have ha : raw33456step1 = (fun i j => raw33456step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33456step1 raw33456step0; decide +kernel
      have hl : raw33456step1Labels = raw33456step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33456step0 raw33456step0Labels permutation32 permutation7
    mixedMoment B raw33456step1 raw33456step1Labels = mixedMoment B raw33456step2 raw33456step2Labels := by
      have ha : raw33456step2 = raw33456step1 := by apply Matrix.ext; unfold raw33456step2 raw33456step1; decide +kernel
      have hl : raw33456step1Labels = labelEmbedding10 ∘ raw33456step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33456step1 raw33456step1Labels raw33456step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5204 node5204Labels := by rfl

def raw33457 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw33457Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33457step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw33457step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33457step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw33457step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33457step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw33457step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33457 raw33457Labels = mixedMoment B node5203 node5203Labels := by
  calc
    mixedMoment B raw33457 raw33457Labels = mixedMoment B raw33457step0 raw33457step0Labels := by
      have hz : ∀ j, raw33457 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33457step0 = (fun i j => raw33457 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33457step0 raw33457; decide +kernel
      have hl : raw33457step0Labels = raw33457Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33457 raw33457Labels permutation346 hz
    mixedMoment B raw33457step0 raw33457step0Labels = mixedMoment B raw33457step1 raw33457step1Labels := by
      have ha : raw33457step1 = (fun i j => raw33457step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33457step1 raw33457step0; decide +kernel
      have hl : raw33457step1Labels = raw33457step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33457step0 raw33457step0Labels permutation32 permutation7
    mixedMoment B raw33457step1 raw33457step1Labels = mixedMoment B raw33457step2 raw33457step2Labels := by
      have ha : raw33457step2 = raw33457step1 := by apply Matrix.ext; unfold raw33457step2 raw33457step1; decide +kernel
      have hl : raw33457step1Labels = labelEmbedding10 ∘ raw33457step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33457step1 raw33457step1Labels raw33457step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5203 node5203Labels := by rfl

def raw33458 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33458Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33458step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw33458step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33458step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw33458step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33458step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw33458step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33458 raw33458Labels = mixedMoment B node4641 node4641Labels := by
  calc
    mixedMoment B raw33458 raw33458Labels = mixedMoment B raw33458step0 raw33458step0Labels := by
      have ha : raw33458step0 = (fun i j => raw33458 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33458step0 raw33458; decide +kernel
      have hl : raw33458step0Labels = raw33458Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33458 raw33458Labels permutation152 permutation4
    mixedMoment B raw33458step0 raw33458step0Labels = mixedMoment B raw33458step1 raw33458step1Labels := by
      have ha : raw33458step1 = -raw33458step0 := by apply Matrix.ext; change ∀ i j, raw33458step1 i j = -(raw33458step0 i j); unfold raw33458step1 raw33458step0; decide +kernel
      have hl : raw33458step1Labels = raw33458step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33458step1 raw33458step1Labels = mixedMoment B raw33458step2 raw33458step2Labels := by
      have ha : raw33458step2 = raw33458step1 := by apply Matrix.ext; unfold raw33458step2 raw33458step1; decide +kernel
      have hl : raw33458step1Labels = labelEmbedding7 ∘ raw33458step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33458step1 raw33458step1Labels raw33458step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4641 node4641Labels := by rfl

def raw33459 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33459Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33459step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -3, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw33459step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33459step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw33459step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33459step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw33459step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33459 raw33459Labels = mixedMoment B node4981 node4981Labels := by
  calc
    mixedMoment B raw33459 raw33459Labels = mixedMoment B raw33459step0 raw33459step0Labels := by
      have ha : raw33459step0 = (fun i j => raw33459 (permutation273 i) (permutation5 j)) := by apply Matrix.ext; unfold raw33459step0 raw33459; decide +kernel
      have hl : raw33459step0Labels = raw33459Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33459 raw33459Labels permutation273 permutation5
    mixedMoment B raw33459step0 raw33459step0Labels = mixedMoment B raw33459step1 raw33459step1Labels := by
      have ha : raw33459step1 = -raw33459step0 := by apply Matrix.ext; change ∀ i j, raw33459step1 i j = -(raw33459step0 i j); unfold raw33459step1 raw33459step0; decide +kernel
      have hl : raw33459step1Labels = raw33459step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33459step1 raw33459step1Labels = mixedMoment B raw33459step2 raw33459step2Labels := by
      have ha : raw33459step2 = raw33459step1 := by apply Matrix.ext; unfold raw33459step2 raw33459step1; decide +kernel
      have hl : raw33459step1Labels = labelEmbedding8 ∘ raw33459step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33459step1 raw33459step1Labels raw33459step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4981 node4981Labels := by rfl

def raw33460 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33460Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33460step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![1, -2, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33460step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33460step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw33460step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33460step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw33460step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33460step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw33460step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33460 raw33460Labels = mixedMoment B node4652 node4652Labels := by
  calc
    mixedMoment B raw33460 raw33460Labels = mixedMoment B raw33460step0 raw33460step0Labels := by
      have hz : ∀ j, raw33460 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33460step0 = (fun i j => raw33460 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33460step0 raw33460; decide +kernel
      have hl : raw33460step0Labels = raw33460Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33460 raw33460Labels permutation346 hz
    mixedMoment B raw33460step0 raw33460step0Labels = mixedMoment B raw33460step1 raw33460step1Labels := by
      have ha : raw33460step1 = (fun i j => raw33460step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33460step1 raw33460step0; decide +kernel
      have hl : raw33460step1Labels = raw33460step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33460step0 raw33460step0Labels permutation34 permutation4
    mixedMoment B raw33460step1 raw33460step1Labels = mixedMoment B raw33460step2 raw33460step2Labels := by
      have ha : raw33460step2 = -raw33460step1 := by apply Matrix.ext; change ∀ i j, raw33460step2 i j = -(raw33460step1 i j); unfold raw33460step2 raw33460step1; decide +kernel
      have hl : raw33460step2Labels = raw33460step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33460step2 raw33460step2Labels = mixedMoment B raw33460step3 raw33460step3Labels := by
      have ha : raw33460step3 = raw33460step2 := by apply Matrix.ext; unfold raw33460step3 raw33460step2; decide +kernel
      have hl : raw33460step2Labels = labelEmbedding7 ∘ raw33460step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33460step2 raw33460step2Labels raw33460step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4652 node4652Labels := by rfl

def raw33461 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33461Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33461step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![1, -2, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33461step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33461step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -3, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 1, 1]]
def raw33461step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33461step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw33461step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33461step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw33461step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33461 raw33461Labels = mixedMoment B node4983 node4983Labels := by
  calc
    mixedMoment B raw33461 raw33461Labels = mixedMoment B raw33461step0 raw33461step0Labels := by
      have hz : ∀ j, raw33461 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33461step0 = (fun i j => raw33461 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33461step0 raw33461; decide +kernel
      have hl : raw33461step0Labels = raw33461Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33461 raw33461Labels permutation346 hz
    mixedMoment B raw33461step0 raw33461step0Labels = mixedMoment B raw33461step1 raw33461step1Labels := by
      have ha : raw33461step1 = (fun i j => raw33461step0 (permutation59 i) (permutation5 j)) := by apply Matrix.ext; unfold raw33461step1 raw33461step0; decide +kernel
      have hl : raw33461step1Labels = raw33461step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33461step0 raw33461step0Labels permutation59 permutation5
    mixedMoment B raw33461step1 raw33461step1Labels = mixedMoment B raw33461step2 raw33461step2Labels := by
      have ha : raw33461step2 = -raw33461step1 := by apply Matrix.ext; change ∀ i j, raw33461step2 i j = -(raw33461step1 i j); unfold raw33461step2 raw33461step1; decide +kernel
      have hl : raw33461step2Labels = raw33461step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33461step2 raw33461step2Labels = mixedMoment B raw33461step3 raw33461step3Labels := by
      have ha : raw33461step3 = raw33461step2 := by apply Matrix.ext; unfold raw33461step3 raw33461step2; decide +kernel
      have hl : raw33461step2Labels = labelEmbedding8 ∘ raw33461step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33461step2 raw33461step2Labels raw33461step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4983 node4983Labels := by rfl

def raw33462 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33462Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33462step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -2, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw33462step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33462step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw33462step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33462step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw33462step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33462 raw33462Labels = mixedMoment B node5015 node5015Labels := by
  calc
    mixedMoment B raw33462 raw33462Labels = mixedMoment B raw33462step0 raw33462step0Labels := by
      have hz : ∀ j, raw33462 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33462step0 = (fun i j => raw33462 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33462step0 raw33462; decide +kernel
      have hl : raw33462step0Labels = raw33462Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33462 raw33462Labels permutation346 hz
    mixedMoment B raw33462step0 raw33462step0Labels = mixedMoment B raw33462step1 raw33462step1Labels := by
      have ha : raw33462step1 = (fun i j => raw33462step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33462step1 raw33462step0; decide +kernel
      have hl : raw33462step1Labels = raw33462step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33462step0 raw33462step0Labels permutation34 permutation6
    mixedMoment B raw33462step1 raw33462step1Labels = mixedMoment B raw33462step2 raw33462step2Labels := by
      have ha : raw33462step2 = raw33462step1 := by apply Matrix.ext; unfold raw33462step2 raw33462step1; decide +kernel
      have hl : raw33462step1Labels = labelEmbedding9 ∘ raw33462step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33462step1 raw33462step1Labels raw33462step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5015 node5015Labels := by rfl

def raw33463 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw33463Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33463step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw33463step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33463step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw33463step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33463step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw33463step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33463 raw33463Labels = mixedMoment B node5018 node5018Labels := by
  calc
    mixedMoment B raw33463 raw33463Labels = mixedMoment B raw33463step0 raw33463step0Labels := by
      have hz : ∀ j, raw33463 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33463step0 = (fun i j => raw33463 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33463step0 raw33463; decide +kernel
      have hl : raw33463step0Labels = raw33463Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33463 raw33463Labels permutation346 hz
    mixedMoment B raw33463step0 raw33463step0Labels = mixedMoment B raw33463step1 raw33463step1Labels := by
      have ha : raw33463step1 = (fun i j => raw33463step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33463step1 raw33463step0; decide +kernel
      have hl : raw33463step1Labels = raw33463step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33463step0 raw33463step0Labels permutation34 permutation6
    mixedMoment B raw33463step1 raw33463step1Labels = mixedMoment B raw33463step2 raw33463step2Labels := by
      have ha : raw33463step2 = raw33463step1 := by apply Matrix.ext; unfold raw33463step2 raw33463step1; decide +kernel
      have hl : raw33463step1Labels = labelEmbedding9 ∘ raw33463step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33463step1 raw33463step1Labels raw33463step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5018 node5018Labels := by rfl

def raw33464 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![0, -2, 2]]
def raw33464Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33464step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![0, -2, 2]]
def raw33464step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33464step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 0, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw33464step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33464step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw33464step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33464step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw33464step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33464 raw33464Labels = mixedMoment B node4652 node4652Labels := by
  calc
    mixedMoment B raw33464 raw33464Labels = mixedMoment B raw33464step0 raw33464step0Labels := by
      have hz : ∀ j, raw33464 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33464step0 = (fun i j => raw33464 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33464step0 raw33464; decide +kernel
      have hl : raw33464step0Labels = raw33464Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33464 raw33464Labels permutation346 hz
    mixedMoment B raw33464step0 raw33464step0Labels = mixedMoment B raw33464step1 raw33464step1Labels := by
      have ha : raw33464step1 = (fun i j => raw33464step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33464step1 raw33464step0; decide +kernel
      have hl : raw33464step1Labels = raw33464step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33464step0 raw33464step0Labels permutation32 permutation4
    mixedMoment B raw33464step1 raw33464step1Labels = mixedMoment B raw33464step2 raw33464step2Labels := by
      have ha : raw33464step2 = -raw33464step1 := by apply Matrix.ext; change ∀ i j, raw33464step2 i j = -(raw33464step1 i j); unfold raw33464step2 raw33464step1; decide +kernel
      have hl : raw33464step2Labels = raw33464step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33464step2 raw33464step2Labels = mixedMoment B raw33464step3 raw33464step3Labels := by
      have ha : raw33464step3 = raw33464step2 := by apply Matrix.ext; unfold raw33464step3 raw33464step2; decide +kernel
      have hl : raw33464step2Labels = labelEmbedding7 ∘ raw33464step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33464step2 raw33464step2Labels raw33464step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4652 node4652Labels := by rfl

def raw33465 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![0, -2, 2]]
def raw33465Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33465step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![0, -1, 1], ![1, -2, 1], ![0, -2, 2]]
def raw33465step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33465step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -3, 1], ![-1, 1, 0], ![-2, 2, 0], ![-2, 1, 1]]
def raw33465step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33465step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw33465step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33465step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw33465step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33465 raw33465Labels = mixedMoment B node4983 node4983Labels := by
  calc
    mixedMoment B raw33465 raw33465Labels = mixedMoment B raw33465step0 raw33465step0Labels := by
      have hz : ∀ j, raw33465 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33465step0 = (fun i j => raw33465 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33465step0 raw33465; decide +kernel
      have hl : raw33465step0Labels = raw33465Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33465 raw33465Labels permutation346 hz
    mixedMoment B raw33465step0 raw33465step0Labels = mixedMoment B raw33465step1 raw33465step1Labels := by
      have ha : raw33465step1 = (fun i j => raw33465step0 (permutation57 i) (permutation5 j)) := by apply Matrix.ext; unfold raw33465step1 raw33465step0; decide +kernel
      have hl : raw33465step1Labels = raw33465step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33465step0 raw33465step0Labels permutation57 permutation5
    mixedMoment B raw33465step1 raw33465step1Labels = mixedMoment B raw33465step2 raw33465step2Labels := by
      have ha : raw33465step2 = -raw33465step1 := by apply Matrix.ext; change ∀ i j, raw33465step2 i j = -(raw33465step1 i j); unfold raw33465step2 raw33465step1; decide +kernel
      have hl : raw33465step2Labels = raw33465step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33465step2 raw33465step2Labels = mixedMoment B raw33465step3 raw33465step3Labels := by
      have ha : raw33465step3 = raw33465step2 := by apply Matrix.ext; unfold raw33465step3 raw33465step2; decide +kernel
      have hl : raw33465step2Labels = labelEmbedding8 ∘ raw33465step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33465step2 raw33465step2Labels raw33465step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4983 node4983Labels := by rfl

def raw33466 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![0, -2, 2]]
def raw33466Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33466step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![-1, 0, 1], ![1, -2, 1], ![0, -2, 2]]
def raw33466step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33466step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw33466step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33466step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw33466step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33466 raw33466Labels = mixedMoment B node5015 node5015Labels := by
  calc
    mixedMoment B raw33466 raw33466Labels = mixedMoment B raw33466step0 raw33466step0Labels := by
      have hz : ∀ j, raw33466 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33466step0 = (fun i j => raw33466 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33466step0 raw33466; decide +kernel
      have hl : raw33466step0Labels = raw33466Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33466 raw33466Labels permutation346 hz
    mixedMoment B raw33466step0 raw33466step0Labels = mixedMoment B raw33466step1 raw33466step1Labels := by
      have ha : raw33466step1 = (fun i j => raw33466step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33466step1 raw33466step0; decide +kernel
      have hl : raw33466step1Labels = raw33466step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33466step0 raw33466step0Labels permutation32 permutation6
    mixedMoment B raw33466step1 raw33466step1Labels = mixedMoment B raw33466step2 raw33466step2Labels := by
      have ha : raw33466step2 = raw33466step1 := by apply Matrix.ext; unfold raw33466step2 raw33466step1; decide +kernel
      have hl : raw33466step1Labels = labelEmbedding9 ∘ raw33466step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33466step1 raw33466step1Labels raw33466step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5015 node5015Labels := by rfl

def raw33467 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw33467Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33467step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw33467step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33467step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw33467step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33467step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw33467step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33467 raw33467Labels = mixedMoment B node5018 node5018Labels := by
  calc
    mixedMoment B raw33467 raw33467Labels = mixedMoment B raw33467step0 raw33467step0Labels := by
      have hz : ∀ j, raw33467 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33467step0 = (fun i j => raw33467 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33467step0 raw33467; decide +kernel
      have hl : raw33467step0Labels = raw33467Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33467 raw33467Labels permutation346 hz
    mixedMoment B raw33467step0 raw33467step0Labels = mixedMoment B raw33467step1 raw33467step1Labels := by
      have ha : raw33467step1 = (fun i j => raw33467step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33467step1 raw33467step0; decide +kernel
      have hl : raw33467step1Labels = raw33467step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33467step0 raw33467step0Labels permutation32 permutation6
    mixedMoment B raw33467step1 raw33467step1Labels = mixedMoment B raw33467step2 raw33467step2Labels := by
      have ha : raw33467step2 = raw33467step1 := by apply Matrix.ext; unfold raw33467step2 raw33467step1; decide +kernel
      have hl : raw33467step1Labels = labelEmbedding9 ∘ raw33467step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33467step1 raw33467step1Labels raw33467step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5018 node5018Labels := by rfl

def raw33468 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -3, 2]]
def raw33468Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, -3, 2]]
def raw33468step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33468step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw33468step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33468step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw33468step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw33468step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw33468step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33468 raw33468Labels = mixedMoment B node4649 node4649Labels := by
  calc
    mixedMoment B raw33468 raw33468Labels = mixedMoment B raw33468step0 raw33468step0Labels := by
      have hz : ∀ j, raw33468 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33468step0 = (fun i j => raw33468 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33468step0 raw33468; decide +kernel
      have hl : raw33468step0Labels = raw33468Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33468 raw33468Labels permutation346 hz
    mixedMoment B raw33468step0 raw33468step0Labels = mixedMoment B raw33468step1 raw33468step1Labels := by
      have ha : raw33468step1 = (fun i j => raw33468step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33468step1 raw33468step0; decide +kernel
      have hl : raw33468step1Labels = raw33468step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33468step0 raw33468step0Labels permutation32 permutation4
    mixedMoment B raw33468step1 raw33468step1Labels = mixedMoment B raw33468step2 raw33468step2Labels := by
      have ha : raw33468step2 = -raw33468step1 := by apply Matrix.ext; change ∀ i j, raw33468step2 i j = -(raw33468step1 i j); unfold raw33468step2 raw33468step1; decide +kernel
      have hl : raw33468step2Labels = raw33468step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33468step2 raw33468step2Labels = mixedMoment B raw33468step3 raw33468step3Labels := by
      have ha : raw33468step3 = raw33468step2 := by apply Matrix.ext; unfold raw33468step3 raw33468step2; decide +kernel
      have hl : raw33468step2Labels = labelEmbedding7 ∘ raw33468step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33468step2 raw33468step2Labels raw33468step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4649 node4649Labels := by rfl

def raw33469 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -3, 2]]
def raw33469Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33469step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![0, -1, 1], ![0, -1, 1], ![1, -3, 2]]
def raw33469step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33469step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -3, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 2, 1]]
def raw33469step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33469step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw33469step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33469step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw33469step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33469 raw33469Labels = mixedMoment B node4982 node4982Labels := by
  calc
    mixedMoment B raw33469 raw33469Labels = mixedMoment B raw33469step0 raw33469step0Labels := by
      have hz : ∀ j, raw33469 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33469step0 = (fun i j => raw33469 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33469step0 raw33469; decide +kernel
      have hl : raw33469step0Labels = raw33469Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33469 raw33469Labels permutation346 hz
    mixedMoment B raw33469step0 raw33469step0Labels = mixedMoment B raw33469step1 raw33469step1Labels := by
      have ha : raw33469step1 = (fun i j => raw33469step0 (permutation56 i) (permutation5 j)) := by apply Matrix.ext; unfold raw33469step1 raw33469step0; decide +kernel
      have hl : raw33469step1Labels = raw33469step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33469step0 raw33469step0Labels permutation56 permutation5
    mixedMoment B raw33469step1 raw33469step1Labels = mixedMoment B raw33469step2 raw33469step2Labels := by
      have ha : raw33469step2 = -raw33469step1 := by apply Matrix.ext; change ∀ i j, raw33469step2 i j = -(raw33469step1 i j); unfold raw33469step2 raw33469step1; decide +kernel
      have hl : raw33469step2Labels = raw33469step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33469step2 raw33469step2Labels = mixedMoment B raw33469step3 raw33469step3Labels := by
      have ha : raw33469step3 = raw33469step2 := by apply Matrix.ext; unfold raw33469step3 raw33469step2; decide +kernel
      have hl : raw33469step2Labels = labelEmbedding8 ∘ raw33469step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33469step2 raw33469step2Labels raw33469step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4982 node4982Labels := by rfl

def raw33470 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -3, 2]]
def raw33470Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![-1, 0, 1], ![0, -1, 1], ![1, -3, 2]]
def raw33470step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33470step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw33470step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33470step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw33470step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33470 raw33470Labels = mixedMoment B node5014 node5014Labels := by
  calc
    mixedMoment B raw33470 raw33470Labels = mixedMoment B raw33470step0 raw33470step0Labels := by
      have hz : ∀ j, raw33470 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33470step0 = (fun i j => raw33470 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33470step0 raw33470; decide +kernel
      have hl : raw33470step0Labels = raw33470Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33470 raw33470Labels permutation346 hz
    mixedMoment B raw33470step0 raw33470step0Labels = mixedMoment B raw33470step1 raw33470step1Labels := by
      have ha : raw33470step1 = (fun i j => raw33470step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33470step1 raw33470step0; decide +kernel
      have hl : raw33470step1Labels = raw33470step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33470step0 raw33470step0Labels permutation32 permutation6
    mixedMoment B raw33470step1 raw33470step1Labels = mixedMoment B raw33470step2 raw33470step2Labels := by
      have ha : raw33470step2 = raw33470step1 := by apply Matrix.ext; unfold raw33470step2 raw33470step1; decide +kernel
      have hl : raw33470step1Labels = labelEmbedding9 ∘ raw33470step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33470step1 raw33470step1Labels raw33470step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5014 node5014Labels := by rfl

def raw33471 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw33471Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33471step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw33471step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33471step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw33471step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33471step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw33471step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33471 raw33471Labels = mixedMoment B node5014 node5014Labels := by
  calc
    mixedMoment B raw33471 raw33471Labels = mixedMoment B raw33471step0 raw33471step0Labels := by
      have hz : ∀ j, raw33471 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33471step0 = (fun i j => raw33471 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33471step0 raw33471; decide +kernel
      have hl : raw33471step0Labels = raw33471Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33471 raw33471Labels permutation346 hz
    mixedMoment B raw33471step0 raw33471step0Labels = mixedMoment B raw33471step1 raw33471step1Labels := by
      have ha : raw33471step1 = (fun i j => raw33471step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33471step1 raw33471step0; decide +kernel
      have hl : raw33471step1Labels = raw33471step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33471step0 raw33471step0Labels permutation34 permutation6
    mixedMoment B raw33471step1 raw33471step1Labels = mixedMoment B raw33471step2 raw33471step2Labels := by
      have ha : raw33471step2 = raw33471step1 := by apply Matrix.ext; unfold raw33471step2 raw33471step1; decide +kernel
      have hl : raw33471step1Labels = labelEmbedding9 ∘ raw33471step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33471step1 raw33471step1Labels raw33471step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5014 node5014Labels := by rfl

def raw33472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33472Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33472step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33472step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33472step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![-2, 0, 2]]
def raw33472step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33472step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw33472step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33472step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw33472step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33472 raw33472Labels = mixedMoment B node5279 node5279Labels := by
  calc
    mixedMoment B raw33472 raw33472Labels = mixedMoment B raw33472step0 raw33472step0Labels := by
      have hz : ∀ j, raw33472 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33472step0 = (fun i j => raw33472 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33472step0 raw33472; decide +kernel
      have hl : raw33472step0Labels = raw33472Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33472 raw33472Labels permutation346 hz
    mixedMoment B raw33472step0 raw33472step0Labels = mixedMoment B raw33472step1 raw33472step1Labels := by
      have ha : raw33472step1 = (fun i j => raw33472step0 (permutation64 i) (permutation5 j)) := by apply Matrix.ext; unfold raw33472step1 raw33472step0; decide +kernel
      have hl : raw33472step1Labels = raw33472step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33472step0 raw33472step0Labels permutation64 permutation5
    mixedMoment B raw33472step1 raw33472step1Labels = mixedMoment B raw33472step2 raw33472step2Labels := by
      have ha : raw33472step2 = -raw33472step1 := by apply Matrix.ext; change ∀ i j, raw33472step2 i j = -(raw33472step1 i j); unfold raw33472step2 raw33472step1; decide +kernel
      have hl : raw33472step2Labels = raw33472step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33472step2 raw33472step2Labels = mixedMoment B raw33472step3 raw33472step3Labels := by
      have ha : raw33472step3 = raw33472step2 := by apply Matrix.ext; unfold raw33472step3 raw33472step2; decide +kernel
      have hl : raw33472step2Labels = labelEmbedding8 ∘ raw33472step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33472step2 raw33472step2Labels raw33472step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5279 node5279Labels := by rfl

def raw33473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33473Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33473step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw33473step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33473step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33473step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33473step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33473step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33473 raw33473Labels = mixedMoment B node5263 node5263Labels := by
  calc
    mixedMoment B raw33473 raw33473Labels = mixedMoment B raw33473step0 raw33473step0Labels := by
      have ha : raw33473step0 = (fun i j => raw33473 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33473step0 raw33473; decide +kernel
      have hl : raw33473step0Labels = raw33473Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33473 raw33473Labels permutation194 permutation7
    mixedMoment B raw33473step0 raw33473step0Labels = mixedMoment B raw33473step1 raw33473step1Labels := by
      have ha : raw33473step1 = -raw33473step0 := by apply Matrix.ext; change ∀ i j, raw33473step1 i j = -(raw33473step0 i j); unfold raw33473step1 raw33473step0; decide +kernel
      have hl : raw33473step1Labels = raw33473step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33473step1 raw33473step1Labels = mixedMoment B raw33473step2 raw33473step2Labels := by
      have ha : raw33473step2 = raw33473step1 := by apply Matrix.ext; unfold raw33473step2 raw33473step1; decide +kernel
      have hl : raw33473step1Labels = labelEmbedding10 ∘ raw33473step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33473step1 raw33473step1Labels raw33473step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5263 node5263Labels := by rfl

def raw33474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33474Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33474step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33474step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33474step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw33474step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33474step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw33474step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33474step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw33474step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33474 raw33474Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw33474 raw33474Labels = mixedMoment B raw33474step0 raw33474step0Labels := by
      have hz : ∀ j, raw33474 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33474step0 = (fun i j => raw33474 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33474step0 raw33474; decide +kernel
      have hl : raw33474step0Labels = raw33474Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33474 raw33474Labels permutation346 hz
    mixedMoment B raw33474step0 raw33474step0Labels = mixedMoment B raw33474step1 raw33474step1Labels := by
      have ha : raw33474step1 = (fun i j => raw33474step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33474step1 raw33474step0; decide +kernel
      have hl : raw33474step1Labels = raw33474step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33474step0 raw33474step0Labels permutation50 permutation7
    mixedMoment B raw33474step1 raw33474step1Labels = mixedMoment B raw33474step2 raw33474step2Labels := by
      have ha : raw33474step2 = -raw33474step1 := by apply Matrix.ext; change ∀ i j, raw33474step2 i j = -(raw33474step1 i j); unfold raw33474step2 raw33474step1; decide +kernel
      have hl : raw33474step2Labels = raw33474step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33474step2 raw33474step2Labels = mixedMoment B raw33474step3 raw33474step3Labels := by
      have ha : raw33474step3 = raw33474step2 := by apply Matrix.ext; unfold raw33474step3 raw33474step2; decide +kernel
      have hl : raw33474step2Labels = labelEmbedding10 ∘ raw33474step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33474step2 raw33474step2Labels raw33474step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw33475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33475Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33475step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33475step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33475step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw33475step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33475step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw33475step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33475step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw33475step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33475 raw33475Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw33475 raw33475Labels = mixedMoment B raw33475step0 raw33475step0Labels := by
      have hz : ∀ j, raw33475 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33475step0 = (fun i j => raw33475 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33475step0 raw33475; decide +kernel
      have hl : raw33475step0Labels = raw33475Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33475 raw33475Labels permutation346 hz
    mixedMoment B raw33475step0 raw33475step0Labels = mixedMoment B raw33475step1 raw33475step1Labels := by
      have ha : raw33475step1 = (fun i j => raw33475step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33475step1 raw33475step0; decide +kernel
      have hl : raw33475step1Labels = raw33475step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33475step0 raw33475step0Labels permutation51 permutation7
    mixedMoment B raw33475step1 raw33475step1Labels = mixedMoment B raw33475step2 raw33475step2Labels := by
      have ha : raw33475step2 = -raw33475step1 := by apply Matrix.ext; change ∀ i j, raw33475step2 i j = -(raw33475step1 i j); unfold raw33475step2 raw33475step1; decide +kernel
      have hl : raw33475step2Labels = raw33475step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33475step2 raw33475step2Labels = mixedMoment B raw33475step3 raw33475step3Labels := by
      have ha : raw33475step3 = raw33475step2 := by apply Matrix.ext; unfold raw33475step3 raw33475step2; decide +kernel
      have hl : raw33475step2Labels = labelEmbedding10 ∘ raw33475step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33475step2 raw33475step2Labels raw33475step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw33476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33476Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33476 raw33476Labels = mixedMoment B node4698 node4698Labels := by
  calc
    _ = mixedMoment B node4698 node4698Labels := by rfl

def raw33477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33477Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33477step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw33477step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33477 raw33477Labels = mixedMoment B node4852 node4852Labels := by
  calc
    mixedMoment B raw33477 raw33477Labels = mixedMoment B raw33477step0 raw33477step0Labels := by
      have ha : raw33477step0 = (fun i j => raw33477 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33477step0 raw33477; decide +kernel
      have hl : raw33477step0Labels = raw33477Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33477 raw33477Labels permutation158 permutation2
    _ = mixedMoment B node4852 node4852Labels := by rfl

def raw33478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33478Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33478step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw33478step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33478 raw33478Labels = mixedMoment B node4852 node4852Labels := by
  calc
    mixedMoment B raw33478 raw33478Labels = mixedMoment B raw33478step0 raw33478step0Labels := by
      have ha : raw33478step0 = (fun i j => raw33478 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33478step0 raw33478; decide +kernel
      have hl : raw33478step0Labels = raw33478Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33478 raw33478Labels permutation164 permutation2
    _ = mixedMoment B node4852 node4852Labels := by rfl

def raw33479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33479Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33479step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33479step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33479step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33479step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33479 raw33479Labels = mixedMoment B node4703 node4703Labels := by
  calc
    mixedMoment B raw33479 raw33479Labels = mixedMoment B raw33479step0 raw33479step0Labels := by
      have hz : ∀ j, raw33479 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33479step0 = (fun i j => raw33479 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33479step0 raw33479; decide +kernel
      have hl : raw33479step0Labels = raw33479Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33479 raw33479Labels permutation346 hz
    mixedMoment B raw33479step0 raw33479step0Labels = mixedMoment B raw33479step1 raw33479step1Labels := by
      have ha : raw33479step1 = (fun i j => raw33479step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33479step1 raw33479step0; decide +kernel
      have hl : raw33479step1Labels = raw33479step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33479step0 raw33479step0Labels permutation35 permutation2
    _ = mixedMoment B node4703 node4703Labels := by rfl

def raw33480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33480Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33480step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33480step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33480 raw33480Labels = mixedMoment B node4775 node4775Labels := by
  calc
    mixedMoment B raw33480 raw33480Labels = mixedMoment B raw33480step0 raw33480step0Labels := by
      have ha : raw33480step0 = (fun i j => raw33480 (permutation179 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33480step0 raw33480; decide +kernel
      have hl : raw33480step0Labels = raw33480Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33480 raw33480Labels permutation179 permutation2
    _ = mixedMoment B node4775 node4775Labels := by rfl

def raw33481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33481Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33481step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33481step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33481step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33481step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33481 raw33481Labels = mixedMoment B node4856 node4856Labels := by
  calc
    mixedMoment B raw33481 raw33481Labels = mixedMoment B raw33481step0 raw33481step0Labels := by
      have hz : ∀ j, raw33481 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33481step0 = (fun i j => raw33481 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33481step0 raw33481; decide +kernel
      have hl : raw33481step0Labels = raw33481Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33481 raw33481Labels permutation346 hz
    mixedMoment B raw33481step0 raw33481step0Labels = mixedMoment B raw33481step1 raw33481step1Labels := by
      have ha : raw33481step1 = (fun i j => raw33481step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33481step1 raw33481step0; decide +kernel
      have hl : raw33481step1Labels = raw33481step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33481step0 raw33481step0Labels permutation35 permutation2
    _ = mixedMoment B node4856 node4856Labels := by rfl

def raw33482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33482Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33482step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33482step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33482step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33482step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33482 raw33482Labels = mixedMoment B node4703 node4703Labels := by
  calc
    mixedMoment B raw33482 raw33482Labels = mixedMoment B raw33482step0 raw33482step0Labels := by
      have hz : ∀ j, raw33482 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33482step0 = (fun i j => raw33482 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33482step0 raw33482; decide +kernel
      have hl : raw33482step0Labels = raw33482Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33482 raw33482Labels permutation346 hz
    mixedMoment B raw33482step0 raw33482step0Labels = mixedMoment B raw33482step1 raw33482step1Labels := by
      have ha : raw33482step1 = (fun i j => raw33482step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33482step1 raw33482step0; decide +kernel
      have hl : raw33482step1Labels = raw33482step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33482step0 raw33482step0Labels permutation33 permutation2
    _ = mixedMoment B node4703 node4703Labels := by rfl

def raw33483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33483Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33483step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33483step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33483 raw33483Labels = mixedMoment B node4775 node4775Labels := by
  calc
    mixedMoment B raw33483 raw33483Labels = mixedMoment B raw33483step0 raw33483step0Labels := by
      have ha : raw33483step0 = (fun i j => raw33483 (permutation177 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33483step0 raw33483; decide +kernel
      have hl : raw33483step0Labels = raw33483Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33483 raw33483Labels permutation177 permutation2
    _ = mixedMoment B node4775 node4775Labels := by rfl

def raw33484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33484Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33484step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33484step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33484step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33484step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33484 raw33484Labels = mixedMoment B node4856 node4856Labels := by
  calc
    mixedMoment B raw33484 raw33484Labels = mixedMoment B raw33484step0 raw33484step0Labels := by
      have hz : ∀ j, raw33484 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33484step0 = (fun i j => raw33484 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33484step0 raw33484; decide +kernel
      have hl : raw33484step0Labels = raw33484Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33484 raw33484Labels permutation346 hz
    mixedMoment B raw33484step0 raw33484step0Labels = mixedMoment B raw33484step1 raw33484step1Labels := by
      have ha : raw33484step1 = (fun i j => raw33484step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33484step1 raw33484step0; decide +kernel
      have hl : raw33484step1Labels = raw33484step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33484step0 raw33484step0Labels permutation33 permutation2
    _ = mixedMoment B node4856 node4856Labels := by rfl

def raw33485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33485Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33485step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33485step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33485 raw33485Labels = mixedMoment B node4702 node4702Labels := by
  calc
    mixedMoment B raw33485 raw33485Labels = mixedMoment B raw33485step0 raw33485step0Labels := by
      have hz : ∀ j, raw33485 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33485step0 = (fun i j => raw33485 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33485step0 raw33485; decide +kernel
      have hl : raw33485step0Labels = raw33485Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33485 raw33485Labels permutation346 hz
    _ = mixedMoment B node4702 node4702Labels := by rfl

def raw33486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33486Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33486step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw33486step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33486step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw33486step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33486step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw33486step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33486 raw33486Labels = mixedMoment B node4765 node4765Labels := by
  calc
    mixedMoment B raw33486 raw33486Labels = mixedMoment B raw33486step0 raw33486step0Labels := by
      have ha : raw33486step0 = (fun i j => raw33486 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33486step0 raw33486; decide +kernel
      have hl : raw33486step0Labels = raw33486Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33486 raw33486Labels permutation664 permutation3
    mixedMoment B raw33486step0 raw33486step0Labels = mixedMoment B raw33486step1 raw33486step1Labels := by
      have ha : raw33486step1 = -raw33486step0 := by apply Matrix.ext; change ∀ i j, raw33486step1 i j = -(raw33486step0 i j); unfold raw33486step1 raw33486step0; decide +kernel
      have hl : raw33486step1Labels = raw33486step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33486step1 raw33486step1Labels = mixedMoment B raw33486step2 raw33486step2Labels := by
      have ha : raw33486step2 = raw33486step1 := by apply Matrix.ext; unfold raw33486step2 raw33486step1; decide +kernel
      have hl : raw33486step1Labels = labelEmbedding6 ∘ raw33486step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33486step1 raw33486step1Labels raw33486step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4765 node4765Labels := by rfl

def raw33487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33487Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33487step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33487step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw33487step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33487step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw33487step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33487step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw33487step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33487 raw33487Labels = mixedMoment B node4808 node4808Labels := by
  calc
    mixedMoment B raw33487 raw33487Labels = mixedMoment B raw33487step0 raw33487step0Labels := by
      have hz : ∀ j, raw33487 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33487step0 = (fun i j => raw33487 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33487step0 raw33487; decide +kernel
      have hl : raw33487step0Labels = raw33487Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33487 raw33487Labels permutation346 hz
    mixedMoment B raw33487step0 raw33487step0Labels = mixedMoment B raw33487step1 raw33487step1Labels := by
      have ha : raw33487step1 = (fun i j => raw33487step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33487step1 raw33487step0; decide +kernel
      have hl : raw33487step1Labels = raw33487step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33487step0 raw33487step0Labels permutation151 permutation3
    mixedMoment B raw33487step1 raw33487step1Labels = mixedMoment B raw33487step2 raw33487step2Labels := by
      have ha : raw33487step2 = -raw33487step1 := by apply Matrix.ext; change ∀ i j, raw33487step2 i j = -(raw33487step1 i j); unfold raw33487step2 raw33487step1; decide +kernel
      have hl : raw33487step2Labels = raw33487step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33487step2 raw33487step2Labels = mixedMoment B raw33487step3 raw33487step3Labels := by
      have ha : raw33487step3 = raw33487step2 := by apply Matrix.ext; unfold raw33487step3 raw33487step2; decide +kernel
      have hl : raw33487step2Labels = labelEmbedding6 ∘ raw33487step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33487step2 raw33487step2Labels raw33487step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4808 node4808Labels := by rfl

def raw33488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw33488Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33488step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw33488step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33488step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw33488step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33488step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw33488step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33488step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![3, -3, 0]]
def raw33488step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33488 raw33488Labels = mixedMoment B node4808 node4808Labels := by
  calc
    mixedMoment B raw33488 raw33488Labels = mixedMoment B raw33488step0 raw33488step0Labels := by
      have hz : ∀ j, raw33488 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33488step0 = (fun i j => raw33488 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33488step0 raw33488; decide +kernel
      have hl : raw33488step0Labels = raw33488Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33488 raw33488Labels permutation346 hz
    mixedMoment B raw33488step0 raw33488step0Labels = mixedMoment B raw33488step1 raw33488step1Labels := by
      have ha : raw33488step1 = (fun i j => raw33488step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33488step1 raw33488step0; decide +kernel
      have hl : raw33488step1Labels = raw33488step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33488step0 raw33488step0Labels permutation145 permutation3
    mixedMoment B raw33488step1 raw33488step1Labels = mixedMoment B raw33488step2 raw33488step2Labels := by
      have ha : raw33488step2 = -raw33488step1 := by apply Matrix.ext; change ∀ i j, raw33488step2 i j = -(raw33488step1 i j); unfold raw33488step2 raw33488step1; decide +kernel
      have hl : raw33488step2Labels = raw33488step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33488step2 raw33488step2Labels = mixedMoment B raw33488step3 raw33488step3Labels := by
      have ha : raw33488step3 = raw33488step2 := by apply Matrix.ext; unfold raw33488step3 raw33488step2; decide +kernel
      have hl : raw33488step2Labels = labelEmbedding6 ∘ raw33488step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33488step2 raw33488step2Labels raw33488step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4808 node4808Labels := by rfl

def raw33489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33489Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33489step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33489step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![-2, 0, 2]]
def raw33489step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33489step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw33489step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33489step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw33489step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33489 raw33489Labels = mixedMoment B node2748 node2748Labels := by
  calc
    mixedMoment B raw33489 raw33489Labels = mixedMoment B raw33489step0 raw33489step0Labels := by
      have hz : ∀ j, raw33489 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33489step0 = (fun i j => raw33489 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33489step0 raw33489; decide +kernel
      have hl : raw33489step0Labels = raw33489Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33489 raw33489Labels permutation346 hz
    mixedMoment B raw33489step0 raw33489step0Labels = mixedMoment B raw33489step1 raw33489step1Labels := by
      have ha : raw33489step1 = (fun i j => raw33489step0 (permutation64 i) (permutation5 j)) := by apply Matrix.ext; unfold raw33489step1 raw33489step0; decide +kernel
      have hl : raw33489step1Labels = raw33489step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33489step0 raw33489step0Labels permutation64 permutation5
    mixedMoment B raw33489step1 raw33489step1Labels = mixedMoment B raw33489step2 raw33489step2Labels := by
      have ha : raw33489step2 = -raw33489step1 := by apply Matrix.ext; change ∀ i j, raw33489step2 i j = -(raw33489step1 i j); unfold raw33489step2 raw33489step1; decide +kernel
      have hl : raw33489step2Labels = raw33489step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33489step2 raw33489step2Labels = mixedMoment B raw33489step3 raw33489step3Labels := by
      have ha : raw33489step3 = raw33489step2 := by apply Matrix.ext; unfold raw33489step3 raw33489step2; decide +kernel
      have hl : raw33489step2Labels = labelEmbedding1 ∘ raw33489step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33489step2 raw33489step2Labels raw33489step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2748 node2748Labels := by rfl

def raw33490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33490Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33490step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw33490step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33490step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33490step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33490step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33490step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33490 raw33490Labels = mixedMoment B node2728 node2728Labels := by
  calc
    mixedMoment B raw33490 raw33490Labels = mixedMoment B raw33490step0 raw33490step0Labels := by
      have ha : raw33490step0 = (fun i j => raw33490 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33490step0 raw33490; decide +kernel
      have hl : raw33490step0Labels = raw33490Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33490 raw33490Labels permutation194 permutation7
    mixedMoment B raw33490step0 raw33490step0Labels = mixedMoment B raw33490step1 raw33490step1Labels := by
      have ha : raw33490step1 = -raw33490step0 := by apply Matrix.ext; change ∀ i j, raw33490step1 i j = -(raw33490step0 i j); unfold raw33490step1 raw33490step0; decide +kernel
      have hl : raw33490step1Labels = raw33490step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33490step1 raw33490step1Labels = mixedMoment B raw33490step2 raw33490step2Labels := by
      have ha : raw33490step2 = raw33490step1 := by apply Matrix.ext; unfold raw33490step2 raw33490step1; decide +kernel
      have hl : raw33490step1Labels = labelEmbedding1 ∘ raw33490step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33490step1 raw33490step1Labels raw33490step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2728 node2728Labels := by rfl

def raw33491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33491Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33491step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33491step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33491step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw33491step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33491step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw33491step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33491step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw33491step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33491 raw33491Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw33491 raw33491Labels = mixedMoment B raw33491step0 raw33491step0Labels := by
      have hz : ∀ j, raw33491 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33491step0 = (fun i j => raw33491 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33491step0 raw33491; decide +kernel
      have hl : raw33491step0Labels = raw33491Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33491 raw33491Labels permutation346 hz
    mixedMoment B raw33491step0 raw33491step0Labels = mixedMoment B raw33491step1 raw33491step1Labels := by
      have ha : raw33491step1 = (fun i j => raw33491step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33491step1 raw33491step0; decide +kernel
      have hl : raw33491step1Labels = raw33491step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33491step0 raw33491step0Labels permutation50 permutation7
    mixedMoment B raw33491step1 raw33491step1Labels = mixedMoment B raw33491step2 raw33491step2Labels := by
      have ha : raw33491step2 = -raw33491step1 := by apply Matrix.ext; change ∀ i j, raw33491step2 i j = -(raw33491step1 i j); unfold raw33491step2 raw33491step1; decide +kernel
      have hl : raw33491step2Labels = raw33491step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33491step2 raw33491step2Labels = mixedMoment B raw33491step3 raw33491step3Labels := by
      have ha : raw33491step3 = raw33491step2 := by apply Matrix.ext; unfold raw33491step3 raw33491step2; decide +kernel
      have hl : raw33491step2Labels = labelEmbedding1 ∘ raw33491step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33491step2 raw33491step2Labels raw33491step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2773 node2773Labels := by rfl

def raw33492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33492Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33492step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33492step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw33492step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33492step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw33492step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33492step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw33492step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33492 raw33492Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw33492 raw33492Labels = mixedMoment B raw33492step0 raw33492step0Labels := by
      have hz : ∀ j, raw33492 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33492step0 = (fun i j => raw33492 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33492step0 raw33492; decide +kernel
      have hl : raw33492step0Labels = raw33492Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33492 raw33492Labels permutation346 hz
    mixedMoment B raw33492step0 raw33492step0Labels = mixedMoment B raw33492step1 raw33492step1Labels := by
      have ha : raw33492step1 = (fun i j => raw33492step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33492step1 raw33492step0; decide +kernel
      have hl : raw33492step1Labels = raw33492step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33492step0 raw33492step0Labels permutation51 permutation7
    mixedMoment B raw33492step1 raw33492step1Labels = mixedMoment B raw33492step2 raw33492step2Labels := by
      have ha : raw33492step2 = -raw33492step1 := by apply Matrix.ext; change ∀ i j, raw33492step2 i j = -(raw33492step1 i j); unfold raw33492step2 raw33492step1; decide +kernel
      have hl : raw33492step2Labels = raw33492step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33492step2 raw33492step2Labels = mixedMoment B raw33492step3 raw33492step3Labels := by
      have ha : raw33492step3 = raw33492step2 := by apply Matrix.ext; unfold raw33492step3 raw33492step2; decide +kernel
      have hl : raw33492step2Labels = labelEmbedding1 ∘ raw33492step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33492step2 raw33492step2Labels raw33492step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2773 node2773Labels := by rfl

def raw33493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw33493Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33493step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw33493step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33493step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw33493step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33493step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33493step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33493step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33493step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33493 raw33493Labels = mixedMoment B node2764 node2764Labels := by
  calc
    mixedMoment B raw33493 raw33493Labels = mixedMoment B raw33493step0 raw33493step0Labels := by
      have hz : ∀ j, raw33493 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33493step0 = (fun i j => raw33493 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33493step0 raw33493; decide +kernel
      have hl : raw33493step0Labels = raw33493Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33493 raw33493Labels permutation346 hz
    mixedMoment B raw33493step0 raw33493step0Labels = mixedMoment B raw33493step1 raw33493step1Labels := by
      have ha : raw33493step1 = (fun i j => raw33493step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33493step1 raw33493step0; decide +kernel
      have hl : raw33493step1Labels = raw33493step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33493step0 raw33493step0Labels permutation50 permutation7
    mixedMoment B raw33493step1 raw33493step1Labels = mixedMoment B raw33493step2 raw33493step2Labels := by
      have ha : raw33493step2 = -raw33493step1 := by apply Matrix.ext; change ∀ i j, raw33493step2 i j = -(raw33493step1 i j); unfold raw33493step2 raw33493step1; decide +kernel
      have hl : raw33493step2Labels = raw33493step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33493step2 raw33493step2Labels = mixedMoment B raw33493step3 raw33493step3Labels := by
      have ha : raw33493step3 = raw33493step2 := by apply Matrix.ext; unfold raw33493step3 raw33493step2; decide +kernel
      have hl : raw33493step2Labels = labelEmbedding1 ∘ raw33493step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33493step2 raw33493step2Labels raw33493step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2764 node2764Labels := by rfl

def raw33494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33494Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33494step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33494step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33494step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw33494step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33494step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33494step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33494step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw33494step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33494 raw33494Labels = mixedMoment B node1737 node1737Labels := by
  calc
    mixedMoment B raw33494 raw33494Labels = mixedMoment B raw33494step0 raw33494step0Labels := by
      have hz : ∀ j, raw33494 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33494step0 = (fun i j => raw33494 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33494step0 raw33494; decide +kernel
      have hl : raw33494step0Labels = raw33494Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33494 raw33494Labels permutation346 hz
    mixedMoment B raw33494step0 raw33494step0Labels = mixedMoment B raw33494step1 raw33494step1Labels := by
      have ha : raw33494step1 = (fun i j => raw33494step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33494step1 raw33494step0; decide +kernel
      have hl : raw33494step1Labels = raw33494step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33494step0 raw33494step0Labels permutation50 permutation7
    mixedMoment B raw33494step1 raw33494step1Labels = mixedMoment B raw33494step2 raw33494step2Labels := by
      have ha : raw33494step2 = -raw33494step1 := by apply Matrix.ext; change ∀ i j, raw33494step2 i j = -(raw33494step1 i j); unfold raw33494step2 raw33494step1; decide +kernel
      have hl : raw33494step2Labels = raw33494step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33494step2 raw33494step2Labels = mixedMoment B raw33494step3 raw33494step3Labels := by
      have ha : raw33494step3 = raw33494step2 := by apply Matrix.ext; unfold raw33494step3 raw33494step2; decide +kernel
      have hl : raw33494step2Labels = labelEmbedding1 ∘ raw33494step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33494step2 raw33494step2Labels raw33494step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1737 node1737Labels := by rfl

def raw33495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33495Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33495step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 3, -2], ![-1, 0, 1], ![-1, 0, 1]]
def raw33495step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33495step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw33495step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33495step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw33495step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33495 raw33495Labels = mixedMoment B node2248 node2248Labels := by
  calc
    mixedMoment B raw33495 raw33495Labels = mixedMoment B raw33495step0 raw33495step0Labels := by
      have ha : raw33495step0 = (fun i j => raw33495 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33495step0 raw33495; decide +kernel
      have hl : raw33495step0Labels = raw33495Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33495 raw33495Labels permutation194 permutation7
    mixedMoment B raw33495step0 raw33495step0Labels = mixedMoment B raw33495step1 raw33495step1Labels := by
      have ha : raw33495step1 = -raw33495step0 := by apply Matrix.ext; change ∀ i j, raw33495step1 i j = -(raw33495step0 i j); unfold raw33495step1 raw33495step0; decide +kernel
      have hl : raw33495step1Labels = raw33495step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33495step1 raw33495step1Labels = mixedMoment B raw33495step2 raw33495step2Labels := by
      have ha : raw33495step2 = raw33495step1 := by apply Matrix.ext; unfold raw33495step2 raw33495step1; decide +kernel
      have hl : raw33495step1Labels = labelEmbedding1 ∘ raw33495step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33495step1 raw33495step1Labels raw33495step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2248 node2248Labels := by rfl

def raw33496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33496Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33496step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw33496step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33496step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw33496step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33496step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw33496step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33496 raw33496Labels = mixedMoment B node2250 node2250Labels := by
  calc
    mixedMoment B raw33496 raw33496Labels = mixedMoment B raw33496step0 raw33496step0Labels := by
      have ha : raw33496step0 = (fun i j => raw33496 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33496step0 raw33496; decide +kernel
      have hl : raw33496step0Labels = raw33496Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33496 raw33496Labels permutation194 permutation7
    mixedMoment B raw33496step0 raw33496step0Labels = mixedMoment B raw33496step1 raw33496step1Labels := by
      have ha : raw33496step1 = -raw33496step0 := by apply Matrix.ext; change ∀ i j, raw33496step1 i j = -(raw33496step0 i j); unfold raw33496step1 raw33496step0; decide +kernel
      have hl : raw33496step1Labels = raw33496step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33496step1 raw33496step1Labels = mixedMoment B raw33496step2 raw33496step2Labels := by
      have ha : raw33496step2 = raw33496step1 := by apply Matrix.ext; unfold raw33496step2 raw33496step1; decide +kernel
      have hl : raw33496step1Labels = labelEmbedding1 ∘ raw33496step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33496step1 raw33496step1Labels raw33496step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2250 node2250Labels := by rfl

def raw33497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33497Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33497step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw33497step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33497step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw33497step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33497step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw33497step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33497 raw33497Labels = mixedMoment B node2250 node2250Labels := by
  calc
    mixedMoment B raw33497 raw33497Labels = mixedMoment B raw33497step0 raw33497step0Labels := by
      have ha : raw33497step0 = (fun i j => raw33497 (permutation195 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33497step0 raw33497; decide +kernel
      have hl : raw33497step0Labels = raw33497Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33497 raw33497Labels permutation195 permutation7
    mixedMoment B raw33497step0 raw33497step0Labels = mixedMoment B raw33497step1 raw33497step1Labels := by
      have ha : raw33497step1 = -raw33497step0 := by apply Matrix.ext; change ∀ i j, raw33497step1 i j = -(raw33497step0 i j); unfold raw33497step1 raw33497step0; decide +kernel
      have hl : raw33497step1Labels = raw33497step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33497step1 raw33497step1Labels = mixedMoment B raw33497step2 raw33497step2Labels := by
      have ha : raw33497step2 = raw33497step1 := by apply Matrix.ext; unfold raw33497step2 raw33497step1; decide +kernel
      have hl : raw33497step1Labels = labelEmbedding1 ∘ raw33497step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33497step1 raw33497step1Labels raw33497step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2250 node2250Labels := by rfl

def raw33498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw33498Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33498step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw33498step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33498step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33498step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33498step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33498step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33498 raw33498Labels = mixedMoment B node2241 node2241Labels := by
  calc
    mixedMoment B raw33498 raw33498Labels = mixedMoment B raw33498step0 raw33498step0Labels := by
      have ha : raw33498step0 = (fun i j => raw33498 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33498step0 raw33498; decide +kernel
      have hl : raw33498step0Labels = raw33498Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33498 raw33498Labels permutation194 permutation7
    mixedMoment B raw33498step0 raw33498step0Labels = mixedMoment B raw33498step1 raw33498step1Labels := by
      have ha : raw33498step1 = -raw33498step0 := by apply Matrix.ext; change ∀ i j, raw33498step1 i j = -(raw33498step0 i j); unfold raw33498step1 raw33498step0; decide +kernel
      have hl : raw33498step1Labels = raw33498step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33498step1 raw33498step1Labels = mixedMoment B raw33498step2 raw33498step2Labels := by
      have ha : raw33498step2 = raw33498step1 := by apply Matrix.ext; unfold raw33498step2 raw33498step1; decide +kernel
      have hl : raw33498step1Labels = labelEmbedding1 ∘ raw33498step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33498step1 raw33498step1Labels raw33498step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2241 node2241Labels := by rfl

def raw33499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33499Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33499step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33499step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33499step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2]]
def raw33499step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33499step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw33499step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33499step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw33499step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33499 raw33499Labels = mixedMoment B node2272 node2272Labels := by
  calc
    mixedMoment B raw33499 raw33499Labels = mixedMoment B raw33499step0 raw33499step0Labels := by
      have hz : ∀ j, raw33499 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33499step0 = (fun i j => raw33499 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33499step0 raw33499; decide +kernel
      have hl : raw33499step0Labels = raw33499Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33499 raw33499Labels permutation346 hz
    mixedMoment B raw33499step0 raw33499step0Labels = mixedMoment B raw33499step1 raw33499step1Labels := by
      have ha : raw33499step1 = (fun i j => raw33499step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33499step1 raw33499step0; decide +kernel
      have hl : raw33499step1Labels = raw33499step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33499step0 raw33499step0Labels permutation51 permutation7
    mixedMoment B raw33499step1 raw33499step1Labels = mixedMoment B raw33499step2 raw33499step2Labels := by
      have ha : raw33499step2 = -raw33499step1 := by apply Matrix.ext; change ∀ i j, raw33499step2 i j = -(raw33499step1 i j); unfold raw33499step2 raw33499step1; decide +kernel
      have hl : raw33499step2Labels = raw33499step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33499step2 raw33499step2Labels = mixedMoment B raw33499step3 raw33499step3Labels := by
      have ha : raw33499step3 = raw33499step2 := by apply Matrix.ext; unfold raw33499step3 raw33499step2; decide +kernel
      have hl : raw33499step2Labels = labelEmbedding1 ∘ raw33499step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33499step2 raw33499step2Labels raw33499step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2272 node2272Labels := by rfl

def raw33500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33500Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33500step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33500step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33500step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33500step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33500step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33500step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33500 raw33500Labels = mixedMoment B node2211 node2211Labels := by
  calc
    mixedMoment B raw33500 raw33500Labels = mixedMoment B raw33500step0 raw33500step0Labels := by
      have ha : raw33500step0 = (fun i j => raw33500 (permutation195 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33500step0 raw33500; decide +kernel
      have hl : raw33500step0Labels = raw33500Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33500 raw33500Labels permutation195 permutation7
    mixedMoment B raw33500step0 raw33500step0Labels = mixedMoment B raw33500step1 raw33500step1Labels := by
      have ha : raw33500step1 = -raw33500step0 := by apply Matrix.ext; change ∀ i j, raw33500step1 i j = -(raw33500step0 i j); unfold raw33500step1 raw33500step0; decide +kernel
      have hl : raw33500step1Labels = raw33500step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33500step1 raw33500step1Labels = mixedMoment B raw33500step2 raw33500step2Labels := by
      have ha : raw33500step2 = raw33500step1 := by apply Matrix.ext; unfold raw33500step2 raw33500step1; decide +kernel
      have hl : raw33500step1Labels = labelEmbedding1 ∘ raw33500step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33500step1 raw33500step1Labels raw33500step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2211 node2211Labels := by rfl

def raw33501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33501Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33501step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw33501step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33501step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw33501step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33501step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw33501step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33501step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw33501step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33501 raw33501Labels = mixedMoment B node2274 node2274Labels := by
  calc
    mixedMoment B raw33501 raw33501Labels = mixedMoment B raw33501step0 raw33501step0Labels := by
      have hz : ∀ j, raw33501 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33501step0 = (fun i j => raw33501 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33501step0 raw33501; decide +kernel
      have hl : raw33501step0Labels = raw33501Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33501 raw33501Labels permutation346 hz
    mixedMoment B raw33501step0 raw33501step0Labels = mixedMoment B raw33501step1 raw33501step1Labels := by
      have ha : raw33501step1 = (fun i j => raw33501step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33501step1 raw33501step0; decide +kernel
      have hl : raw33501step1Labels = raw33501step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33501step0 raw33501step0Labels permutation51 permutation7
    mixedMoment B raw33501step1 raw33501step1Labels = mixedMoment B raw33501step2 raw33501step2Labels := by
      have ha : raw33501step2 = -raw33501step1 := by apply Matrix.ext; change ∀ i j, raw33501step2 i j = -(raw33501step1 i j); unfold raw33501step2 raw33501step1; decide +kernel
      have hl : raw33501step2Labels = raw33501step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33501step2 raw33501step2Labels = mixedMoment B raw33501step3 raw33501step3Labels := by
      have ha : raw33501step3 = raw33501step2 := by apply Matrix.ext; unfold raw33501step3 raw33501step2; decide +kernel
      have hl : raw33501step2Labels = labelEmbedding1 ∘ raw33501step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33501step2 raw33501step2Labels raw33501step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2274 node2274Labels := by rfl

def raw33502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw33502Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33502step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw33502step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33502step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33502step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33502step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33502step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33502step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33502step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33502 raw33502Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw33502 raw33502Labels = mixedMoment B raw33502step0 raw33502step0Labels := by
      have hz : ∀ j, raw33502 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33502step0 = (fun i j => raw33502 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33502step0 raw33502; decide +kernel
      have hl : raw33502step0Labels = raw33502Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33502 raw33502Labels permutation346 hz
    mixedMoment B raw33502step0 raw33502step0Labels = mixedMoment B raw33502step1 raw33502step1Labels := by
      have ha : raw33502step1 = (fun i j => raw33502step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33502step1 raw33502step0; decide +kernel
      have hl : raw33502step1Labels = raw33502step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33502step0 raw33502step0Labels permutation51 permutation7
    mixedMoment B raw33502step1 raw33502step1Labels = mixedMoment B raw33502step2 raw33502step2Labels := by
      have ha : raw33502step2 = -raw33502step1 := by apply Matrix.ext; change ∀ i j, raw33502step2 i j = -(raw33502step1 i j); unfold raw33502step2 raw33502step1; decide +kernel
      have hl : raw33502step2Labels = raw33502step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33502step2 raw33502step2Labels = mixedMoment B raw33502step3 raw33502step3Labels := by
      have ha : raw33502step3 = raw33502step2 := by apply Matrix.ext; unfold raw33502step3 raw33502step2; decide +kernel
      have hl : raw33502step2Labels = labelEmbedding1 ∘ raw33502step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33502step2 raw33502step2Labels raw33502step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2260 node2260Labels := by rfl

def raw33503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33503Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33503step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33503step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2]]
def raw33503step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33503step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw33503step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33503step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw33503step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33503 raw33503Labels = mixedMoment B node2272 node2272Labels := by
  calc
    mixedMoment B raw33503 raw33503Labels = mixedMoment B raw33503step0 raw33503step0Labels := by
      have hz : ∀ j, raw33503 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33503step0 = (fun i j => raw33503 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33503step0 raw33503; decide +kernel
      have hl : raw33503step0Labels = raw33503Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33503 raw33503Labels permutation346 hz
    mixedMoment B raw33503step0 raw33503step0Labels = mixedMoment B raw33503step1 raw33503step1Labels := by
      have ha : raw33503step1 = (fun i j => raw33503step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33503step1 raw33503step0; decide +kernel
      have hl : raw33503step1Labels = raw33503step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33503step0 raw33503step0Labels permutation50 permutation7
    mixedMoment B raw33503step1 raw33503step1Labels = mixedMoment B raw33503step2 raw33503step2Labels := by
      have ha : raw33503step2 = -raw33503step1 := by apply Matrix.ext; change ∀ i j, raw33503step2 i j = -(raw33503step1 i j); unfold raw33503step2 raw33503step1; decide +kernel
      have hl : raw33503step2Labels = raw33503step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33503step2 raw33503step2Labels = mixedMoment B raw33503step3 raw33503step3Labels := by
      have ha : raw33503step3 = raw33503step2 := by apply Matrix.ext; unfold raw33503step3 raw33503step2; decide +kernel
      have hl : raw33503step2Labels = labelEmbedding1 ∘ raw33503step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33503step2 raw33503step2Labels raw33503step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2272 node2272Labels := by rfl

def raw33504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33504Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33504step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33504step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33504step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33504step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33504step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33504step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33504 raw33504Labels = mixedMoment B node2211 node2211Labels := by
  calc
    mixedMoment B raw33504 raw33504Labels = mixedMoment B raw33504step0 raw33504step0Labels := by
      have ha : raw33504step0 = (fun i j => raw33504 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33504step0 raw33504; decide +kernel
      have hl : raw33504step0Labels = raw33504Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33504 raw33504Labels permutation194 permutation7
    mixedMoment B raw33504step0 raw33504step0Labels = mixedMoment B raw33504step1 raw33504step1Labels := by
      have ha : raw33504step1 = -raw33504step0 := by apply Matrix.ext; change ∀ i j, raw33504step1 i j = -(raw33504step0 i j); unfold raw33504step1 raw33504step0; decide +kernel
      have hl : raw33504step1Labels = raw33504step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33504step1 raw33504step1Labels = mixedMoment B raw33504step2 raw33504step2Labels := by
      have ha : raw33504step2 = raw33504step1 := by apply Matrix.ext; unfold raw33504step2 raw33504step1; decide +kernel
      have hl : raw33504step1Labels = labelEmbedding1 ∘ raw33504step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33504step1 raw33504step1Labels raw33504step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2211 node2211Labels := by rfl

def raw33505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33505Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33505step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33505step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33505step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw33505step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33505step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw33505step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33505step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw33505step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33505 raw33505Labels = mixedMoment B node2274 node2274Labels := by
  calc
    mixedMoment B raw33505 raw33505Labels = mixedMoment B raw33505step0 raw33505step0Labels := by
      have hz : ∀ j, raw33505 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33505step0 = (fun i j => raw33505 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33505step0 raw33505; decide +kernel
      have hl : raw33505step0Labels = raw33505Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33505 raw33505Labels permutation346 hz
    mixedMoment B raw33505step0 raw33505step0Labels = mixedMoment B raw33505step1 raw33505step1Labels := by
      have ha : raw33505step1 = (fun i j => raw33505step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33505step1 raw33505step0; decide +kernel
      have hl : raw33505step1Labels = raw33505step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33505step0 raw33505step0Labels permutation50 permutation7
    mixedMoment B raw33505step1 raw33505step1Labels = mixedMoment B raw33505step2 raw33505step2Labels := by
      have ha : raw33505step2 = -raw33505step1 := by apply Matrix.ext; change ∀ i j, raw33505step2 i j = -(raw33505step1 i j); unfold raw33505step2 raw33505step1; decide +kernel
      have hl : raw33505step2Labels = raw33505step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33505step2 raw33505step2Labels = mixedMoment B raw33505step3 raw33505step3Labels := by
      have ha : raw33505step3 = raw33505step2 := by apply Matrix.ext; unfold raw33505step3 raw33505step2; decide +kernel
      have hl : raw33505step2Labels = labelEmbedding1 ∘ raw33505step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33505step2 raw33505step2Labels raw33505step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2274 node2274Labels := by rfl

def raw33506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw33506Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33506step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw33506step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33506step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw33506step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33506step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33506step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33506step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw33506step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33506 raw33506Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw33506 raw33506Labels = mixedMoment B raw33506step0 raw33506step0Labels := by
      have hz : ∀ j, raw33506 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33506step0 = (fun i j => raw33506 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33506step0 raw33506; decide +kernel
      have hl : raw33506step0Labels = raw33506Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33506 raw33506Labels permutation346 hz
    mixedMoment B raw33506step0 raw33506step0Labels = mixedMoment B raw33506step1 raw33506step1Labels := by
      have ha : raw33506step1 = (fun i j => raw33506step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33506step1 raw33506step0; decide +kernel
      have hl : raw33506step1Labels = raw33506step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33506step0 raw33506step0Labels permutation50 permutation7
    mixedMoment B raw33506step1 raw33506step1Labels = mixedMoment B raw33506step2 raw33506step2Labels := by
      have ha : raw33506step2 = -raw33506step1 := by apply Matrix.ext; change ∀ i j, raw33506step2 i j = -(raw33506step1 i j); unfold raw33506step2 raw33506step1; decide +kernel
      have hl : raw33506step2Labels = raw33506step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33506step2 raw33506step2Labels = mixedMoment B raw33506step3 raw33506step3Labels := by
      have ha : raw33506step3 = raw33506step2 := by apply Matrix.ext; unfold raw33506step3 raw33506step2; decide +kernel
      have hl : raw33506step2Labels = labelEmbedding1 ∘ raw33506step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33506step2 raw33506step2Labels raw33506step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2260 node2260Labels := by rfl

def raw33507 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33507Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33507step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33507step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33507step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]
def raw33507step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33507step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![3, -1, -2]]
def raw33507step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33507 raw33507Labels = mixedMoment B node2180 node2180Labels := by
  calc
    mixedMoment B raw33507 raw33507Labels = mixedMoment B raw33507step0 raw33507step0Labels := by
      have hz : ∀ j, raw33507 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33507step0 = (fun i j => raw33507 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33507step0 raw33507; decide +kernel
      have hl : raw33507step0Labels = raw33507Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33507 raw33507Labels permutation346 hz
    mixedMoment B raw33507step0 raw33507step0Labels = mixedMoment B raw33507step1 raw33507step1Labels := by
      have ha : raw33507step1 = (fun i j => raw33507step0 (permutation144 i) (permutation5 j)) := by apply Matrix.ext; unfold raw33507step1 raw33507step0; decide +kernel
      have hl : raw33507step1Labels = raw33507step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33507step0 raw33507step0Labels permutation144 permutation5
    mixedMoment B raw33507step1 raw33507step1Labels = mixedMoment B raw33507step2 raw33507step2Labels := by
      have ha : raw33507step2 = raw33507step1 := by apply Matrix.ext; unfold raw33507step2 raw33507step1; decide +kernel
      have hl : raw33507step1Labels = labelEmbedding1 ∘ raw33507step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33507step1 raw33507step1Labels raw33507step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2180 node2180Labels := by rfl

def raw33508 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33508Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33508step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw33508step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33508step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw33508step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33508 raw33508Labels = mixedMoment B node2179 node2179Labels := by
  calc
    mixedMoment B raw33508 raw33508Labels = mixedMoment B raw33508step0 raw33508step0Labels := by
      have ha : raw33508step0 = (fun i j => raw33508 (permutation660 i) (permutation5 j)) := by apply Matrix.ext; unfold raw33508step0 raw33508; decide +kernel
      have hl : raw33508step0Labels = raw33508Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33508 raw33508Labels permutation660 permutation5
    mixedMoment B raw33508step0 raw33508step0Labels = mixedMoment B raw33508step1 raw33508step1Labels := by
      have ha : raw33508step1 = raw33508step0 := by apply Matrix.ext; unfold raw33508step1 raw33508step0; decide +kernel
      have hl : raw33508step0Labels = labelEmbedding1 ∘ raw33508step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33508step0 raw33508step0Labels raw33508step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2179 node2179Labels := by rfl

def raw33509 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33509Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33509step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33509step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw33509step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33509step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw33509step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33509 raw33509Labels = mixedMoment B node2220 node2220Labels := by
  calc
    mixedMoment B raw33509 raw33509Labels = mixedMoment B raw33509step0 raw33509step0Labels := by
      have hz : ∀ j, raw33509 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33509step0 = (fun i j => raw33509 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33509step0 raw33509; decide +kernel
      have hl : raw33509step0Labels = raw33509Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33509 raw33509Labels permutation346 hz
    mixedMoment B raw33509step0 raw33509step0Labels = mixedMoment B raw33509step1 raw33509step1Labels := by
      have ha : raw33509step1 = (fun i j => raw33509step0 (permutation147 i) (permutation5 j)) := by apply Matrix.ext; unfold raw33509step1 raw33509step0; decide +kernel
      have hl : raw33509step1Labels = raw33509step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33509step0 raw33509step0Labels permutation147 permutation5
    mixedMoment B raw33509step1 raw33509step1Labels = mixedMoment B raw33509step2 raw33509step2Labels := by
      have ha : raw33509step2 = raw33509step1 := by apply Matrix.ext; unfold raw33509step2 raw33509step1; decide +kernel
      have hl : raw33509step1Labels = labelEmbedding1 ∘ raw33509step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33509step1 raw33509step1Labels raw33509step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2220 node2220Labels := by rfl

def raw33510 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw33510Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33510step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw33510step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33510step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw33510step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33510step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![2, -1, -1]]
def raw33510step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33510 raw33510Labels = mixedMoment B node2220 node2220Labels := by
  calc
    mixedMoment B raw33510 raw33510Labels = mixedMoment B raw33510step0 raw33510step0Labels := by
      have hz : ∀ j, raw33510 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33510step0 = (fun i j => raw33510 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33510step0 raw33510; decide +kernel
      have hl : raw33510step0Labels = raw33510Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33510 raw33510Labels permutation346 hz
    mixedMoment B raw33510step0 raw33510step0Labels = mixedMoment B raw33510step1 raw33510step1Labels := by
      have ha : raw33510step1 = (fun i j => raw33510step0 (permutation141 i) (permutation5 j)) := by apply Matrix.ext; unfold raw33510step1 raw33510step0; decide +kernel
      have hl : raw33510step1Labels = raw33510step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33510step0 raw33510step0Labels permutation141 permutation5
    mixedMoment B raw33510step1 raw33510step1Labels = mixedMoment B raw33510step2 raw33510step2Labels := by
      have ha : raw33510step2 = raw33510step1 := by apply Matrix.ext; unfold raw33510step2 raw33510step1; decide +kernel
      have hl : raw33510step1Labels = labelEmbedding1 ∘ raw33510step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33510step1 raw33510step1Labels raw33510step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2220 node2220Labels := by rfl

def raw33511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33511Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33511step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33511step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![-1, -2, 3], ![-2, 2, 0]]
def raw33511step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33511step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, -2, 0]]
def raw33511step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33511 raw33511Labels = mixedMoment B node3079 node3079Labels := by
  calc
    mixedMoment B raw33511 raw33511Labels = mixedMoment B raw33511step0 raw33511step0Labels := by
      have hz : ∀ j, raw33511 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33511step0 = (fun i j => raw33511 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33511step0 raw33511; decide +kernel
      have hl : raw33511step0Labels = raw33511Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33511 raw33511Labels permutation346 hz
    mixedMoment B raw33511step0 raw33511step0Labels = mixedMoment B raw33511step1 raw33511step1Labels := by
      have ha : raw33511step1 = (fun i j => raw33511step0 (permutation64 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33511step1 raw33511step0; decide +kernel
      have hl : raw33511step1Labels = raw33511step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33511step0 raw33511step0Labels permutation64 permutation4
    mixedMoment B raw33511step1 raw33511step1Labels = mixedMoment B raw33511step2 raw33511step2Labels := by
      have ha : raw33511step2 = -raw33511step1 := by apply Matrix.ext; change ∀ i j, raw33511step2 i j = -(raw33511step1 i j); unfold raw33511step2 raw33511step1; decide +kernel
      have hl : raw33511step2Labels = raw33511step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3079 node3079Labels := by rfl

def raw33512 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33512Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33512 raw33512Labels = mixedMoment B node1824 node1824Labels := by
  calc
    _ = mixedMoment B node1824 node1824Labels := by rfl

def raw33513 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33513Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33513step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33513step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33513step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33513 raw33513Labels = mixedMoment B node1829 node1829Labels := by
  calc
    mixedMoment B raw33513 raw33513Labels = mixedMoment B raw33513step0 raw33513step0Labels := by
      have hz : ∀ j, raw33513 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33513step0 = (fun i j => raw33513 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33513step0 raw33513; decide +kernel
      have hl : raw33513step0Labels = raw33513Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33513 raw33513Labels permutation346 hz
    mixedMoment B raw33513step0 raw33513step0Labels = mixedMoment B raw33513step1 raw33513step1Labels := by
      have ha : raw33513step1 = (fun i j => raw33513step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33513step1 raw33513step0; decide +kernel
      have hl : raw33513step1Labels = raw33513step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33513step0 raw33513step0Labels permutation35 permutation2
    _ = mixedMoment B node1829 node1829Labels := by rfl

def raw33514 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33514Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw33514step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33514step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw33514step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33514 raw33514Labels = mixedMoment B node1829 node1829Labels := by
  calc
    mixedMoment B raw33514 raw33514Labels = mixedMoment B raw33514step0 raw33514step0Labels := by
      have hz : ∀ j, raw33514 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33514step0 = (fun i j => raw33514 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33514step0 raw33514; decide +kernel
      have hl : raw33514step0Labels = raw33514Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33514 raw33514Labels permutation346 hz
    mixedMoment B raw33514step0 raw33514step0Labels = mixedMoment B raw33514step1 raw33514step1Labels := by
      have ha : raw33514step1 = (fun i j => raw33514step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33514step1 raw33514step0; decide +kernel
      have hl : raw33514step1Labels = raw33514step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33514step0 raw33514step0Labels permutation33 permutation2
    _ = mixedMoment B node1829 node1829Labels := by rfl

def raw33515 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33515Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw33515step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33515 raw33515Labels = mixedMoment B node1828 node1828Labels := by
  calc
    mixedMoment B raw33515 raw33515Labels = mixedMoment B raw33515step0 raw33515step0Labels := by
      have hz : ∀ j, raw33515 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33515step0 = (fun i j => raw33515 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33515step0 raw33515; decide +kernel
      have hl : raw33515step0Labels = raw33515Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33515 raw33515Labels permutation346 hz
    _ = mixedMoment B node1828 node1828Labels := by rfl

def raw33516 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33516Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33516step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33516step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33516step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33516step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33516step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33516step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33516 raw33516Labels = mixedMoment B node5448 node5448Labels := by
  calc
    mixedMoment B raw33516 raw33516Labels = mixedMoment B raw33516step0 raw33516step0Labels := by
      have hz : ∀ j, raw33516 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33516step0 = (fun i j => raw33516 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33516step0 raw33516; decide +kernel
      have hl : raw33516step0Labels = raw33516Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33516 raw33516Labels permutation346 hz
    mixedMoment B raw33516step0 raw33516step0Labels = mixedMoment B raw33516step1 raw33516step1Labels := by
      have ha : raw33516step1 = (fun i j => raw33516step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33516step1 raw33516step0; decide +kernel
      have hl : raw33516step1Labels = raw33516step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33516step0 raw33516step0Labels permutation36 permutation3
    mixedMoment B raw33516step1 raw33516step1Labels = mixedMoment B raw33516step2 raw33516step2Labels := by
      have ha : raw33516step2 = raw33516step1 := by apply Matrix.ext; unfold raw33516step2 raw33516step1; decide +kernel
      have hl : raw33516step1Labels = labelEmbedding6 ∘ raw33516step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33516step1 raw33516step1Labels raw33516step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5448 node5448Labels := by rfl

def raw33517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33517Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33517step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33517step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33517step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33517step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33517 raw33517Labels = mixedMoment B node4236 node4236Labels := by
  calc
    mixedMoment B raw33517 raw33517Labels = mixedMoment B raw33517step0 raw33517step0Labels := by
      have ha : raw33517step0 = (fun i j => raw33517 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33517step0 raw33517; decide +kernel
      have hl : raw33517step0Labels = raw33517Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33517 raw33517Labels permutation152 permutation3
    mixedMoment B raw33517step0 raw33517step0Labels = mixedMoment B raw33517step1 raw33517step1Labels := by
      have ha : raw33517step1 = raw33517step0 := by apply Matrix.ext; unfold raw33517step1 raw33517step0; decide +kernel
      have hl : raw33517step0Labels = labelEmbedding6 ∘ raw33517step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33517step0 raw33517step0Labels raw33517step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4236 node4236Labels := by rfl

def raw33518 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33518Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33518step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33518step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33518step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33518step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33518 raw33518Labels = mixedMoment B node4685 node4685Labels := by
  calc
    mixedMoment B raw33518 raw33518Labels = mixedMoment B raw33518step0 raw33518step0Labels := by
      have ha : raw33518step0 = (fun i j => raw33518 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33518step0 raw33518; decide +kernel
      have hl : raw33518step0Labels = raw33518Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33518 raw33518Labels permutation152 permutation3
    mixedMoment B raw33518step0 raw33518step0Labels = mixedMoment B raw33518step1 raw33518step1Labels := by
      have ha : raw33518step1 = raw33518step0 := by apply Matrix.ext; unfold raw33518step1 raw33518step0; decide +kernel
      have hl : raw33518step0Labels = labelEmbedding6 ∘ raw33518step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33518step0 raw33518step0Labels raw33518step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4685 node4685Labels := by rfl

def raw33519 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33519Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33519step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33519step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33519step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33519step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33519step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33519step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33519 raw33519Labels = mixedMoment B node4869 node4869Labels := by
  calc
    mixedMoment B raw33519 raw33519Labels = mixedMoment B raw33519step0 raw33519step0Labels := by
      have hz : ∀ j, raw33519 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33519step0 = (fun i j => raw33519 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33519step0 raw33519; decide +kernel
      have hl : raw33519step0Labels = raw33519Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33519 raw33519Labels permutation520 hz
    mixedMoment B raw33519step0 raw33519step0Labels = mixedMoment B raw33519step1 raw33519step1Labels := by
      have ha : raw33519step1 = (fun i j => raw33519step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33519step1 raw33519step0; decide +kernel
      have hl : raw33519step1Labels = raw33519step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33519step0 raw33519step0Labels permutation32 permutation3
    mixedMoment B raw33519step1 raw33519step1Labels = mixedMoment B raw33519step2 raw33519step2Labels := by
      have ha : raw33519step2 = raw33519step1 := by apply Matrix.ext; unfold raw33519step2 raw33519step1; decide +kernel
      have hl : raw33519step1Labels = labelEmbedding6 ∘ raw33519step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33519step1 raw33519step1Labels raw33519step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4869 node4869Labels := by rfl

def raw33520 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33520Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33520step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33520step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33520step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33520step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33520step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33520 raw33520Labels = mixedMoment B node4238 node4238Labels := by
  calc
    mixedMoment B raw33520 raw33520Labels = mixedMoment B raw33520step0 raw33520step0Labels := by
      have hz : ∀ j, raw33520 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33520step0 = (fun i j => raw33520 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33520step0 raw33520; decide +kernel
      have hl : raw33520step0Labels = raw33520Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33520 raw33520Labels permutation346 hz
    mixedMoment B raw33520step0 raw33520step0Labels = mixedMoment B raw33520step1 raw33520step1Labels := by
      have ha : raw33520step1 = (fun i j => raw33520step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33520step1 raw33520step0; decide +kernel
      have hl : raw33520step1Labels = raw33520step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33520step0 raw33520step0Labels permutation35 permutation3
    mixedMoment B raw33520step1 raw33520step1Labels = mixedMoment B raw33520step2 raw33520step2Labels := by
      have ha : raw33520step2 = raw33520step1 := by apply Matrix.ext; unfold raw33520step2 raw33520step1; decide +kernel
      have hl : raw33520step1Labels = labelEmbedding6 ∘ raw33520step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33520step1 raw33520step1Labels raw33520step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4238 node4238Labels := by rfl

def raw33521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33521Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33521step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33521step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33521step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33521step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33521step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33521 raw33521Labels = mixedMoment B node4688 node4688Labels := by
  calc
    mixedMoment B raw33521 raw33521Labels = mixedMoment B raw33521step0 raw33521step0Labels := by
      have hz : ∀ j, raw33521 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33521step0 = (fun i j => raw33521 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33521step0 raw33521; decide +kernel
      have hl : raw33521step0Labels = raw33521Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33521 raw33521Labels permutation346 hz
    mixedMoment B raw33521step0 raw33521step0Labels = mixedMoment B raw33521step1 raw33521step1Labels := by
      have ha : raw33521step1 = (fun i j => raw33521step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33521step1 raw33521step0; decide +kernel
      have hl : raw33521step1Labels = raw33521step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33521step0 raw33521step0Labels permutation35 permutation3
    mixedMoment B raw33521step1 raw33521step1Labels = mixedMoment B raw33521step2 raw33521step2Labels := by
      have ha : raw33521step2 = raw33521step1 := by apply Matrix.ext; unfold raw33521step2 raw33521step1; decide +kernel
      have hl : raw33521step1Labels = labelEmbedding6 ∘ raw33521step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33521step1 raw33521step1Labels raw33521step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4688 node4688Labels := by rfl

def raw33522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33522Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33522step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33522step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33522step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33522step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33522 raw33522Labels = mixedMoment B node4724 node4724Labels := by
  calc
    mixedMoment B raw33522 raw33522Labels = mixedMoment B raw33522step0 raw33522step0Labels := by
      have ha : raw33522step0 = (fun i j => raw33522 (permutation179 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33522step0 raw33522; decide +kernel
      have hl : raw33522step0Labels = raw33522Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33522 raw33522Labels permutation179 permutation3
    mixedMoment B raw33522step0 raw33522step0Labels = mixedMoment B raw33522step1 raw33522step1Labels := by
      have ha : raw33522step1 = raw33522step0 := by apply Matrix.ext; unfold raw33522step1 raw33522step0; decide +kernel
      have hl : raw33522step0Labels = labelEmbedding6 ∘ raw33522step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33522step0 raw33522step0Labels raw33522step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4724 node4724Labels := by rfl

def raw33523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33523Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw33523step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33523step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -2, 0], ![2, 0, -2]]
def raw33523step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33523step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33523step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33523step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -2, 0], ![2, 0, -2]]
def raw33523step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33523 raw33523Labels = mixedMoment B node4874 node4874Labels := by
  calc
    mixedMoment B raw33523 raw33523Labels = mixedMoment B raw33523step0 raw33523step0Labels := by
      have hz : ∀ j, raw33523 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33523step0 = (fun i j => raw33523 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33523step0 raw33523; decide +kernel
      have hl : raw33523step0Labels = raw33523Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33523 raw33523Labels permutation520 hz
    mixedMoment B raw33523step0 raw33523step0Labels = mixedMoment B raw33523step1 raw33523step1Labels := by
      have hz : ∀ j, raw33523step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33523step1 = (fun i j => raw33523step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33523step1 raw33523step0; decide +kernel
      have hl : raw33523step1Labels = raw33523step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33523step0 raw33523step0Labels permutation80 hz
    mixedMoment B raw33523step1 raw33523step1Labels = mixedMoment B raw33523step2 raw33523step2Labels := by
      have ha : raw33523step2 = (fun i j => raw33523step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33523step2 raw33523step1; decide +kernel
      have hl : raw33523step2Labels = raw33523step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33523step1 raw33523step1Labels permutation9 permutation3
    mixedMoment B raw33523step2 raw33523step2Labels = mixedMoment B raw33523step3 raw33523step3Labels := by
      have ha : raw33523step3 = raw33523step2 := by apply Matrix.ext; unfold raw33523step3 raw33523step2; decide +kernel
      have hl : raw33523step2Labels = labelEmbedding6 ∘ raw33523step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33523step2 raw33523step2Labels raw33523step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4874 node4874Labels := by rfl

def raw33524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33524Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33524step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33524step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33524step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33524step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33524step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33524 raw33524Labels = mixedMoment B node4237 node4237Labels := by
  calc
    mixedMoment B raw33524 raw33524Labels = mixedMoment B raw33524step0 raw33524step0Labels := by
      have hz : ∀ j, raw33524 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33524step0 = (fun i j => raw33524 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33524step0 raw33524; decide +kernel
      have hl : raw33524step0Labels = raw33524Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33524 raw33524Labels permutation346 hz
    mixedMoment B raw33524step0 raw33524step0Labels = mixedMoment B raw33524step1 raw33524step1Labels := by
      have ha : raw33524step1 = (fun i j => raw33524step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33524step1 raw33524step0; decide +kernel
      have hl : raw33524step1Labels = raw33524step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33524step0 raw33524step0Labels permutation32 permutation3
    mixedMoment B raw33524step1 raw33524step1Labels = mixedMoment B raw33524step2 raw33524step2Labels := by
      have ha : raw33524step2 = raw33524step1 := by apply Matrix.ext; unfold raw33524step2 raw33524step1; decide +kernel
      have hl : raw33524step1Labels = labelEmbedding6 ∘ raw33524step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33524step1 raw33524step1Labels raw33524step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4237 node4237Labels := by rfl

def raw33525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33525Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33525step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33525step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33525step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33525step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33525step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33525 raw33525Labels = mixedMoment B node4686 node4686Labels := by
  calc
    mixedMoment B raw33525 raw33525Labels = mixedMoment B raw33525step0 raw33525step0Labels := by
      have hz : ∀ j, raw33525 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33525step0 = (fun i j => raw33525 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33525step0 raw33525; decide +kernel
      have hl : raw33525step0Labels = raw33525Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33525 raw33525Labels permutation346 hz
    mixedMoment B raw33525step0 raw33525step0Labels = mixedMoment B raw33525step1 raw33525step1Labels := by
      have ha : raw33525step1 = (fun i j => raw33525step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33525step1 raw33525step0; decide +kernel
      have hl : raw33525step1Labels = raw33525step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33525step0 raw33525step0Labels permutation32 permutation3
    mixedMoment B raw33525step1 raw33525step1Labels = mixedMoment B raw33525step2 raw33525step2Labels := by
      have ha : raw33525step2 = raw33525step1 := by apply Matrix.ext; unfold raw33525step2 raw33525step1; decide +kernel
      have hl : raw33525step1Labels = labelEmbedding6 ∘ raw33525step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33525step1 raw33525step1Labels raw33525step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4686 node4686Labels := by rfl

def raw33526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33526Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33526step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33526step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33526step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33526step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33526 raw33526Labels = mixedMoment B node4723 node4723Labels := by
  calc
    mixedMoment B raw33526 raw33526Labels = mixedMoment B raw33526step0 raw33526step0Labels := by
      have ha : raw33526step0 = (fun i j => raw33526 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33526step0 raw33526; decide +kernel
      have hl : raw33526step0Labels = raw33526Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33526 raw33526Labels permutation176 permutation3
    mixedMoment B raw33526step0 raw33526step0Labels = mixedMoment B raw33526step1 raw33526step1Labels := by
      have ha : raw33526step1 = raw33526step0 := by apply Matrix.ext; unfold raw33526step1 raw33526step0; decide +kernel
      have hl : raw33526step0Labels = labelEmbedding6 ∘ raw33526step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33526step0 raw33526step0Labels raw33526step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4723 node4723Labels := by rfl

def raw33527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw33527Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw33527step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33527step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![3, -1, -2]]
def raw33527step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33527step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33527step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33527step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw33527step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33527 raw33527Labels = mixedMoment B node4871 node4871Labels := by
  calc
    mixedMoment B raw33527 raw33527Labels = mixedMoment B raw33527step0 raw33527step0Labels := by
      have hz : ∀ j, raw33527 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33527step0 = (fun i j => raw33527 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33527step0 raw33527; decide +kernel
      have hl : raw33527step0Labels = raw33527Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33527 raw33527Labels permutation520 hz
    mixedMoment B raw33527step0 raw33527step0Labels = mixedMoment B raw33527step1 raw33527step1Labels := by
      have hz : ∀ j, raw33527step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33527step1 = (fun i j => raw33527step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33527step1 raw33527step0; decide +kernel
      have hl : raw33527step1Labels = raw33527step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33527step0 raw33527step0Labels permutation80 hz
    mixedMoment B raw33527step1 raw33527step1Labels = mixedMoment B raw33527step2 raw33527step2Labels := by
      have ha : raw33527step2 = (fun i j => raw33527step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33527step2 raw33527step1; decide +kernel
      have hl : raw33527step2Labels = raw33527step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33527step1 raw33527step1Labels permutation8 permutation3
    mixedMoment B raw33527step2 raw33527step2Labels = mixedMoment B raw33527step3 raw33527step3Labels := by
      have ha : raw33527step3 = raw33527step2 := by apply Matrix.ext; unfold raw33527step3 raw33527step2; decide +kernel
      have hl : raw33527step2Labels = labelEmbedding6 ∘ raw33527step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33527step2 raw33527step2Labels raw33527step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4871 node4871Labels := by rfl

def raw33528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33528Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33528step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33528step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33528step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33528 raw33528Labels = mixedMoment B node3739 node3739Labels := by
  calc
    mixedMoment B raw33528 raw33528Labels = mixedMoment B raw33528step0 raw33528step0Labels := by
      have hz : ∀ j, raw33528 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33528step0 = (fun i j => raw33528 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33528step0 raw33528; decide +kernel
      have hl : raw33528step0Labels = raw33528Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33528 raw33528Labels permutation346 hz
    mixedMoment B raw33528step0 raw33528step0Labels = mixedMoment B raw33528step1 raw33528step1Labels := by
      have ha : raw33528step1 = (fun i j => raw33528step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33528step1 raw33528step0; decide +kernel
      have hl : raw33528step1Labels = raw33528step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33528step0 raw33528step0Labels permutation32 permutation3
    _ = mixedMoment B node3739 node3739Labels := by rfl

def raw33529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33529Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33529step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33529step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33529 raw33529Labels = mixedMoment B node3789 node3789Labels := by
  calc
    mixedMoment B raw33529 raw33529Labels = mixedMoment B raw33529step0 raw33529step0Labels := by
      have ha : raw33529step0 = (fun i j => raw33529 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33529step0 raw33529; decide +kernel
      have hl : raw33529step0Labels = raw33529Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33529 raw33529Labels permutation176 permutation3
    _ = mixedMoment B node3789 node3789Labels := by rfl

def raw33530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33530Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33530step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33530step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33530step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw33530step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33530step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33530step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33530 raw33530Labels = mixedMoment B node3889 node3889Labels := by
  calc
    mixedMoment B raw33530 raw33530Labels = mixedMoment B raw33530step0 raw33530step0Labels := by
      have hz : ∀ j, raw33530 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33530step0 = (fun i j => raw33530 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33530step0 raw33530; decide +kernel
      have hl : raw33530step0Labels = raw33530Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33530 raw33530Labels permutation520 hz
    mixedMoment B raw33530step0 raw33530step0Labels = mixedMoment B raw33530step1 raw33530step1Labels := by
      have hz : ∀ j, raw33530step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33530step1 = (fun i j => raw33530step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33530step1 raw33530step0; decide +kernel
      have hl : raw33530step1Labels = raw33530step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33530step0 raw33530step0Labels permutation80 hz
    mixedMoment B raw33530step1 raw33530step1Labels = mixedMoment B raw33530step2 raw33530step2Labels := by
      have ha : raw33530step2 = (fun i j => raw33530step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33530step2 raw33530step1; decide +kernel
      have hl : raw33530step2Labels = raw33530step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33530step1 raw33530step1Labels permutation8 permutation3
    _ = mixedMoment B node3889 node3889Labels := by rfl

def raw33531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33531Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33531step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33531step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33531step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33531 raw33531Labels = mixedMoment B node3885 node3885Labels := by
  calc
    mixedMoment B raw33531 raw33531Labels = mixedMoment B raw33531step0 raw33531step0Labels := by
      have hz : ∀ j, raw33531 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33531step0 = (fun i j => raw33531 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33531step0 raw33531; decide +kernel
      have hl : raw33531step0Labels = raw33531Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33531 raw33531Labels permutation346 hz
    mixedMoment B raw33531step0 raw33531step0Labels = mixedMoment B raw33531step1 raw33531step1Labels := by
      have ha : raw33531step1 = (fun i j => raw33531step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33531step1 raw33531step0; decide +kernel
      have hl : raw33531step1Labels = raw33531step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33531step0 raw33531step0Labels permutation36 permutation3
    _ = mixedMoment B node3885 node3885Labels := by rfl

def raw33532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33532Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33532step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33532step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33532step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33532 raw33532Labels = mixedMoment B node827 node827Labels := by
  calc
    mixedMoment B raw33532 raw33532Labels = mixedMoment B raw33532step0 raw33532step0Labels := by
      have hz : ∀ j, raw33532 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33532step0 = (fun i j => raw33532 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33532step0 raw33532; decide +kernel
      have hl : raw33532step0Labels = raw33532Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33532 raw33532Labels permutation346 hz
    mixedMoment B raw33532step0 raw33532step0Labels = mixedMoment B raw33532step1 raw33532step1Labels := by
      have ha : raw33532step1 = (fun i j => raw33532step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33532step1 raw33532step0; decide +kernel
      have hl : raw33532step1Labels = raw33532step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33532step0 raw33532step0Labels permutation32 permutation3
    _ = mixedMoment B node827 node827Labels := by rfl

def raw33533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33533Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33533step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw33533step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33533 raw33533Labels = mixedMoment B node1925 node1925Labels := by
  calc
    mixedMoment B raw33533 raw33533Labels = mixedMoment B raw33533step0 raw33533step0Labels := by
      have ha : raw33533step0 = (fun i j => raw33533 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33533step0 raw33533; decide +kernel
      have hl : raw33533step0Labels = raw33533Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33533 raw33533Labels permutation176 permutation3
    _ = mixedMoment B node1925 node1925Labels := by rfl

def raw33534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw33534Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw33534step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33534step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw33534step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33534step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw33534step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33534 raw33534Labels = mixedMoment B node2279 node2279Labels := by
  calc
    mixedMoment B raw33534 raw33534Labels = mixedMoment B raw33534step0 raw33534step0Labels := by
      have hz : ∀ j, raw33534 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33534step0 = (fun i j => raw33534 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33534step0 raw33534; decide +kernel
      have hl : raw33534step0Labels = raw33534Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33534 raw33534Labels permutation520 hz
    mixedMoment B raw33534step0 raw33534step0Labels = mixedMoment B raw33534step1 raw33534step1Labels := by
      have hz : ∀ j, raw33534step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33534step1 = (fun i j => raw33534step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33534step1 raw33534step0; decide +kernel
      have hl : raw33534step1Labels = raw33534step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33534step0 raw33534step0Labels permutation80 hz
    mixedMoment B raw33534step1 raw33534step1Labels = mixedMoment B raw33534step2 raw33534step2Labels := by
      have ha : raw33534step2 = (fun i j => raw33534step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33534step2 raw33534step1; decide +kernel
      have hl : raw33534step2Labels = raw33534step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33534step1 raw33534step1Labels permutation8 permutation3
    _ = mixedMoment B node2279 node2279Labels := by rfl

def raw33535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33535Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33535step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33535step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33535step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33535step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33535 raw33535Labels = mixedMoment B node2275 node2275Labels := by
  calc
    mixedMoment B raw33535 raw33535Labels = mixedMoment B raw33535step0 raw33535step0Labels := by
      have hz : ∀ j, raw33535 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33535step0 = (fun i j => raw33535 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33535step0 raw33535; decide +kernel
      have hl : raw33535step0Labels = raw33535Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33535 raw33535Labels permutation346 hz
    mixedMoment B raw33535step0 raw33535step0Labels = mixedMoment B raw33535step1 raw33535step1Labels := by
      have ha : raw33535step1 = (fun i j => raw33535step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33535step1 raw33535step0; decide +kernel
      have hl : raw33535step1Labels = raw33535step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33535step0 raw33535step0Labels permutation36 permutation3
    _ = mixedMoment B node2275 node2275Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
