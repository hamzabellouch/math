import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw36992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw36992Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw36992step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36992step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36992step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36992 raw36992Labels = mixedMoment B node5018 node5018Labels := by
  calc
    mixedMoment B raw36992 raw36992Labels = mixedMoment B raw36992step0 raw36992step0Labels := by
      have hz : ∀ j, raw36992 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36992step0 = (fun i j => raw36992 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36992step0 raw36992; decide +kernel
      have hl : raw36992step0Labels = raw36992Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36992 raw36992Labels permutation346 hz
    mixedMoment B raw36992step0 raw36992step0Labels = mixedMoment B raw36992step1 raw36992step1Labels := by
      have ha : raw36992step1 = (fun i j => raw36992step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36992step1 raw36992step0; decide +kernel
      have hl : raw36992step1Labels = raw36992step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36992step0 raw36992step0Labels permutation34 permutation2
    _ = mixedMoment B node5018 node5018Labels := by rfl

def raw36993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw36993Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36993step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw36993step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36993step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36993step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36993step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36993step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36993 raw36993Labels = mixedMoment B node5346 node5346Labels := by
  calc
    mixedMoment B raw36993 raw36993Labels = mixedMoment B raw36993step0 raw36993step0Labels := by
      have ha : raw36993step0 = (fun i j => raw36993 (permutation155 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36993step0 raw36993; decide +kernel
      have hl : raw36993step0Labels = raw36993Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36993 raw36993Labels permutation155 permutation7
    mixedMoment B raw36993step0 raw36993step0Labels = mixedMoment B raw36993step1 raw36993step1Labels := by
      have ha : raw36993step1 = -raw36993step0 := by apply Matrix.ext; change ∀ i j, raw36993step1 i j = -(raw36993step0 i j); unfold raw36993step1 raw36993step0; decide +kernel
      have hl : raw36993step1Labels = raw36993step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36993step1 raw36993step1Labels = mixedMoment B raw36993step2 raw36993step2Labels := by
      have ha : raw36993step2 = raw36993step1 := by apply Matrix.ext; unfold raw36993step2 raw36993step1; decide +kernel
      have hl : raw36993step1Labels = labelEmbedding10 ∘ raw36993step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36993step1 raw36993step1Labels raw36993step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5346 node5346Labels := by rfl

def raw36994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw36994Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw36994step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36994step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw36994step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36994step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36994step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36994step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36994step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36994 raw36994Labels = mixedMoment B node5370 node5370Labels := by
  calc
    mixedMoment B raw36994 raw36994Labels = mixedMoment B raw36994step0 raw36994step0Labels := by
      have hz : ∀ j, raw36994 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36994step0 = (fun i j => raw36994 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36994step0 raw36994; decide +kernel
      have hl : raw36994step0Labels = raw36994Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36994 raw36994Labels permutation346 hz
    mixedMoment B raw36994step0 raw36994step0Labels = mixedMoment B raw36994step1 raw36994step1Labels := by
      have ha : raw36994step1 = (fun i j => raw36994step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36994step1 raw36994step0; decide +kernel
      have hl : raw36994step1Labels = raw36994step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36994step0 raw36994step0Labels permutation35 permutation7
    mixedMoment B raw36994step1 raw36994step1Labels = mixedMoment B raw36994step2 raw36994step2Labels := by
      have ha : raw36994step2 = -raw36994step1 := by apply Matrix.ext; change ∀ i j, raw36994step2 i j = -(raw36994step1 i j); unfold raw36994step2 raw36994step1; decide +kernel
      have hl : raw36994step2Labels = raw36994step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36994step2 raw36994step2Labels = mixedMoment B raw36994step3 raw36994step3Labels := by
      have ha : raw36994step3 = raw36994step2 := by apply Matrix.ext; unfold raw36994step3 raw36994step2; decide +kernel
      have hl : raw36994step2Labels = labelEmbedding10 ∘ raw36994step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36994step2 raw36994step2Labels raw36994step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5370 node5370Labels := by rfl

def raw36995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -1, -1]]
def raw36995Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 1, -2], ![0, 1, -1], ![2, -1, -1]]
def raw36995step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36995step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw36995step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36995step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36995step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36995step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36995step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36995 raw36995Labels = mixedMoment B node5368 node5368Labels := by
  calc
    mixedMoment B raw36995 raw36995Labels = mixedMoment B raw36995step0 raw36995step0Labels := by
      have hz : ∀ j, raw36995 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36995step0 = (fun i j => raw36995 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36995step0 raw36995; decide +kernel
      have hl : raw36995step0Labels = raw36995Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36995 raw36995Labels permutation346 hz
    mixedMoment B raw36995step0 raw36995step0Labels = mixedMoment B raw36995step1 raw36995step1Labels := by
      have ha : raw36995step1 = (fun i j => raw36995step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36995step1 raw36995step0; decide +kernel
      have hl : raw36995step1Labels = raw36995step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36995step0 raw36995step0Labels permutation35 permutation7
    mixedMoment B raw36995step1 raw36995step1Labels = mixedMoment B raw36995step2 raw36995step2Labels := by
      have ha : raw36995step2 = -raw36995step1 := by apply Matrix.ext; change ∀ i j, raw36995step2 i j = -(raw36995step1 i j); unfold raw36995step2 raw36995step1; decide +kernel
      have hl : raw36995step2Labels = raw36995step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36995step2 raw36995step2Labels = mixedMoment B raw36995step3 raw36995step3Labels := by
      have ha : raw36995step3 = raw36995step2 := by apply Matrix.ext; unfold raw36995step3 raw36995step2; decide +kernel
      have hl : raw36995step2Labels = labelEmbedding10 ∘ raw36995step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36995step2 raw36995step2Labels raw36995step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5368 node5368Labels := by rfl

def raw36996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw36996Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw36996step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36996step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw36996step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36996step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36996step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36996step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36996step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36996 raw36996Labels = mixedMoment B node5369 node5369Labels := by
  calc
    mixedMoment B raw36996 raw36996Labels = mixedMoment B raw36996step0 raw36996step0Labels := by
      have hz : ∀ j, raw36996 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36996step0 = (fun i j => raw36996 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36996step0 raw36996; decide +kernel
      have hl : raw36996step0Labels = raw36996Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36996 raw36996Labels permutation346 hz
    mixedMoment B raw36996step0 raw36996step0Labels = mixedMoment B raw36996step1 raw36996step1Labels := by
      have ha : raw36996step1 = (fun i j => raw36996step0 (permutation35 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36996step1 raw36996step0; decide +kernel
      have hl : raw36996step1Labels = raw36996step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36996step0 raw36996step0Labels permutation35 permutation7
    mixedMoment B raw36996step1 raw36996step1Labels = mixedMoment B raw36996step2 raw36996step2Labels := by
      have ha : raw36996step2 = -raw36996step1 := by apply Matrix.ext; change ∀ i j, raw36996step2 i j = -(raw36996step1 i j); unfold raw36996step2 raw36996step1; decide +kernel
      have hl : raw36996step2Labels = raw36996step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36996step2 raw36996step2Labels = mixedMoment B raw36996step3 raw36996step3Labels := by
      have ha : raw36996step3 = raw36996step2 := by apply Matrix.ext; unfold raw36996step3 raw36996step2; decide +kernel
      have hl : raw36996step2Labels = labelEmbedding10 ∘ raw36996step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36996step2 raw36996step2Labels raw36996step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5369 node5369Labels := by rfl

def raw36997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw36997Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36997step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36997step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36997 raw36997Labels = mixedMoment B node4912 node4912Labels := by
  calc
    mixedMoment B raw36997 raw36997Labels = mixedMoment B raw36997step0 raw36997step0Labels := by
      have ha : raw36997step0 = (fun i j => raw36997 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36997step0 raw36997; decide +kernel
      have hl : raw36997step0Labels = raw36997Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36997 raw36997Labels permutation154 permutation2
    _ = mixedMoment B node4912 node4912Labels := by rfl

def raw36998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw36998Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36998step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw36998step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36998 raw36998Labels = mixedMoment B node4912 node4912Labels := by
  calc
    mixedMoment B raw36998 raw36998Labels = mixedMoment B raw36998step0 raw36998step0Labels := by
      have ha : raw36998step0 = (fun i j => raw36998 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36998step0 raw36998; decide +kernel
      have hl : raw36998step0Labels = raw36998Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36998 raw36998Labels permutation267 permutation2
    _ = mixedMoment B node4912 node4912Labels := by rfl

def raw36999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, -1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw36999Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36999step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw36999step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36999step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36999step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36999step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36999step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36999 raw36999Labels = mixedMoment B node5326 node5326Labels := by
  calc
    mixedMoment B raw36999 raw36999Labels = mixedMoment B raw36999step0 raw36999step0Labels := by
      have ha : raw36999step0 = (fun i j => raw36999 (permutation155 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36999step0 raw36999; decide +kernel
      have hl : raw36999step0Labels = raw36999Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36999 raw36999Labels permutation155 permutation7
    mixedMoment B raw36999step0 raw36999step0Labels = mixedMoment B raw36999step1 raw36999step1Labels := by
      have ha : raw36999step1 = -raw36999step0 := by apply Matrix.ext; change ∀ i j, raw36999step1 i j = -(raw36999step0 i j); unfold raw36999step1 raw36999step0; decide +kernel
      have hl : raw36999step1Labels = raw36999step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36999step1 raw36999step1Labels = mixedMoment B raw36999step2 raw36999step2Labels := by
      have ha : raw36999step2 = raw36999step1 := by apply Matrix.ext; unfold raw36999step2 raw36999step1; decide +kernel
      have hl : raw36999step1Labels = labelEmbedding10 ∘ raw36999step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36999step1 raw36999step1Labels raw36999step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5326 node5326Labels := by rfl

def raw37000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![0, 1, -1], ![2, -1, -1]]
def raw37000Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37000step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw37000step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37000 raw37000Labels = mixedMoment B node5324 node5324Labels := by
  calc
    mixedMoment B raw37000 raw37000Labels = mixedMoment B raw37000step0 raw37000step0Labels := by
      have ha : raw37000step0 = (fun i j => raw37000 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37000step0 raw37000; decide +kernel
      have hl : raw37000step0Labels = raw37000Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37000 raw37000Labels permutation164 permutation2
    _ = mixedMoment B node5324 node5324Labels := by rfl

def raw37001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, 0, -1]]
def raw37001Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37001step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw37001step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37001step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37001step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37001step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37001step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37001 raw37001Labels = mixedMoment B node5325 node5325Labels := by
  calc
    mixedMoment B raw37001 raw37001Labels = mixedMoment B raw37001step0 raw37001step0Labels := by
      have ha : raw37001step0 = (fun i j => raw37001 (permutation155 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37001step0 raw37001; decide +kernel
      have hl : raw37001step0Labels = raw37001Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37001 raw37001Labels permutation155 permutation7
    mixedMoment B raw37001step0 raw37001step0Labels = mixedMoment B raw37001step1 raw37001step1Labels := by
      have ha : raw37001step1 = -raw37001step0 := by apply Matrix.ext; change ∀ i j, raw37001step1 i j = -(raw37001step0 i j); unfold raw37001step1 raw37001step0; decide +kernel
      have hl : raw37001step1Labels = raw37001step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37001step1 raw37001step1Labels = mixedMoment B raw37001step2 raw37001step2Labels := by
      have ha : raw37001step2 = raw37001step1 := by apply Matrix.ext; unfold raw37001step2 raw37001step1; decide +kernel
      have hl : raw37001step1Labels = labelEmbedding10 ∘ raw37001step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37001step1 raw37001step1Labels raw37001step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5325 node5325Labels := by rfl

def raw37002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![2, -1, -1]]
def raw37002Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![2, 0, -2], ![1, 0, -1], ![2, -1, -1]]
def raw37002step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37002step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw37002step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37002 raw37002Labels = mixedMoment B node4921 node4921Labels := by
  calc
    mixedMoment B raw37002 raw37002Labels = mixedMoment B raw37002step0 raw37002step0Labels := by
      have hz : ∀ j, raw37002 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37002step0 = (fun i j => raw37002 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37002step0 raw37002; decide +kernel
      have hl : raw37002step0Labels = raw37002Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37002 raw37002Labels permutation346 hz
    mixedMoment B raw37002step0 raw37002step0Labels = mixedMoment B raw37002step1 raw37002step1Labels := by
      have ha : raw37002step1 = (fun i j => raw37002step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37002step1 raw37002step0; decide +kernel
      have hl : raw37002step1Labels = raw37002step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37002step0 raw37002step0Labels permutation35 permutation2
    _ = mixedMoment B node4921 node4921Labels := by rfl

def raw37003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 1, 2], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![2, -1, -1]]
def raw37003Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 1, 2], ![2, 0, -2], ![1, 0, -1], ![2, -1, -1]]
def raw37003step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37003step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw37003step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37003 raw37003Labels = mixedMoment B node4921 node4921Labels := by
  calc
    mixedMoment B raw37003 raw37003Labels = mixedMoment B raw37003step0 raw37003step0Labels := by
      have hz : ∀ j, raw37003 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37003step0 = (fun i j => raw37003 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37003step0 raw37003; decide +kernel
      have hl : raw37003step0Labels = raw37003Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37003 raw37003Labels permutation346 hz
    mixedMoment B raw37003step0 raw37003step0Labels = mixedMoment B raw37003step1 raw37003step1Labels := by
      have ha : raw37003step1 = (fun i j => raw37003step0 (permutation59 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37003step1 raw37003step0; decide +kernel
      have hl : raw37003step1Labels = raw37003step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37003step0 raw37003step0Labels permutation59 permutation2
    _ = mixedMoment B node4921 node4921Labels := by rfl

def raw37004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 1, 0], ![2, 0, -2], ![1, 0, -1], ![2, -1, -1]]
def raw37004Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37004step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw37004step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37004 raw37004Labels = mixedMoment B node5314 node5314Labels := by
  calc
    mixedMoment B raw37004 raw37004Labels = mixedMoment B raw37004step0 raw37004step0Labels := by
      have ha : raw37004step0 = (fun i j => raw37004 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37004step0 raw37004; decide +kernel
      have hl : raw37004step0Labels = raw37004Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37004 raw37004Labels permutation155 permutation2
    _ = mixedMoment B node5314 node5314Labels := by rfl

def raw37005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![0, 1, -1], ![2, -1, -1]]
def raw37005Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37005step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![2, 0, -2], ![0, 1, -1], ![2, -1, -1]]
def raw37005step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37005step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw37005step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37005 raw37005Labels = mixedMoment B node5327 node5327Labels := by
  calc
    mixedMoment B raw37005 raw37005Labels = mixedMoment B raw37005step0 raw37005step0Labels := by
      have hz : ∀ j, raw37005 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37005step0 = (fun i j => raw37005 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37005step0 raw37005; decide +kernel
      have hl : raw37005step0Labels = raw37005Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37005 raw37005Labels permutation346 hz
    mixedMoment B raw37005step0 raw37005step0Labels = mixedMoment B raw37005step1 raw37005step1Labels := by
      have ha : raw37005step1 = (fun i j => raw37005step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37005step1 raw37005step0; decide +kernel
      have hl : raw37005step1Labels = raw37005step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37005step0 raw37005step0Labels permutation35 permutation2
    _ = mixedMoment B node5327 node5327Labels := by rfl

def raw37006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, 0, -1]]
def raw37006Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![2, 0, -2], ![1, 0, -1], ![1, 0, -1]]
def raw37006step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37006step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![1, -1], ![1, -1]]
def raw37006step1Labels : Fin 2 → Fin 3 := ![0, 2]

def raw37006step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw37006step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw37006step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw37006step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical37006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37006 raw37006Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw37006 raw37006Labels = mixedMoment B raw37006step0 raw37006step0Labels := by
      have hz : ∀ j, raw37006 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37006step0 = (fun i j => raw37006 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37006step0 raw37006; decide +kernel
      have hl : raw37006step0Labels = raw37006Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37006 raw37006Labels permutation346 hz
    mixedMoment B raw37006step0 raw37006step0Labels = mixedMoment B raw37006step1 raw37006step1Labels := by
      have hz : ∀ i, raw37006step0 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw37006step1 = (fun i j => raw37006step0 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw37006step1 raw37006step0; decide +kernel
      have hl : raw37006step1Labels = (fun j => raw37006step0Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37006step0 raw37006step0Labels permutation4 hz
    mixedMoment B raw37006step1 raw37006step1Labels = mixedMoment B raw37006step2 raw37006step2Labels := by
      have ha : raw37006step2 = (fun i j => raw37006step1 (permutation35 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37006step2 raw37006step1; decide +kernel
      have hl : raw37006step2Labels = raw37006step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37006step1 raw37006step1Labels permutation35 permutation0
    mixedMoment B raw37006step2 raw37006step2Labels = mixedMoment B raw37006step3 raw37006step3Labels := by
      have ha : raw37006step3 = raw37006step2 := by apply Matrix.ext; unfold raw37006step3 raw37006step2; decide +kernel
      have hl : raw37006step2Labels = labelEmbedding2 ∘ raw37006step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37006step2 raw37006step2Labels raw37006step3Labels labelEmbedding2 hl
    _ = mixedMoment B node4088 node4088Labels := by rfl

def raw37007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw37007Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw37007step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37007 raw37007Labels = mixedMoment B node4923 node4923Labels := by
  calc
    mixedMoment B raw37007 raw37007Labels = mixedMoment B raw37007step0 raw37007step0Labels := by
      have hz : ∀ j, raw37007 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37007step0 = (fun i j => raw37007 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37007step0 raw37007; decide +kernel
      have hl : raw37007step0Labels = raw37007Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37007 raw37007Labels permutation346 hz
    _ = mixedMoment B node4923 node4923Labels := by rfl

def raw37008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw37008Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37008step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 1, 2], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw37008step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37008step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw37008step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37008 raw37008Labels = mixedMoment B node4923 node4923Labels := by
  calc
    mixedMoment B raw37008 raw37008Labels = mixedMoment B raw37008step0 raw37008step0Labels := by
      have hz : ∀ j, raw37008 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37008step0 = (fun i j => raw37008 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37008step0 raw37008; decide +kernel
      have hl : raw37008step0Labels = raw37008Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37008 raw37008Labels permutation346 hz
    mixedMoment B raw37008step0 raw37008step0Labels = mixedMoment B raw37008step1 raw37008step1Labels := by
      have ha : raw37008step1 = (fun i j => raw37008step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37008step1 raw37008step0; decide +kernel
      have hl : raw37008step1Labels = raw37008step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37008step0 raw37008step0Labels permutation56 permutation2
    _ = mixedMoment B node4923 node4923Labels := by rfl

def raw37009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw37009Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37009 raw37009Labels = mixedMoment B node5316 node5316Labels := by
  calc
    _ = mixedMoment B node5316 node5316Labels := by rfl

def raw37010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw37010Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37010step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw37010step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37010 raw37010Labels = mixedMoment B node5330 node5330Labels := by
  calc
    mixedMoment B raw37010 raw37010Labels = mixedMoment B raw37010step0 raw37010step0Labels := by
      have hz : ∀ j, raw37010 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37010step0 = (fun i j => raw37010 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37010step0 raw37010; decide +kernel
      have hl : raw37010step0Labels = raw37010Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37010 raw37010Labels permutation346 hz
    _ = mixedMoment B node5330 node5330Labels := by rfl

def raw37011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, 0, -1]]
def raw37011Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37011step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, 1, -2], ![2, -1, -1], ![1, 0, -1]]
def raw37011step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37011step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37011step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37011 raw37011Labels = mixedMoment B node5331 node5331Labels := by
  calc
    mixedMoment B raw37011 raw37011Labels = mixedMoment B raw37011step0 raw37011step0Labels := by
      have hz : ∀ j, raw37011 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37011step0 = (fun i j => raw37011 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37011step0 raw37011; decide +kernel
      have hl : raw37011step0Labels = raw37011Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37011 raw37011Labels permutation346 hz
    mixedMoment B raw37011step0 raw37011step0Labels = mixedMoment B raw37011step1 raw37011step1Labels := by
      have ha : raw37011step1 = (fun i j => raw37011step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37011step1 raw37011step0; decide +kernel
      have hl : raw37011step1Labels = raw37011step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37011step0 raw37011step0Labels permutation36 permutation2
    _ = mixedMoment B node5331 node5331Labels := by rfl

def raw37012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![3, -2, -1]]
def raw37012Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 1, -2], ![1, 0, -1], ![3, -2, -1]]
def raw37012step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37012step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw37012step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37012 raw37012Labels = mixedMoment B node4919 node4919Labels := by
  calc
    mixedMoment B raw37012 raw37012Labels = mixedMoment B raw37012step0 raw37012step0Labels := by
      have hz : ∀ j, raw37012 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37012step0 = (fun i j => raw37012 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37012step0 raw37012; decide +kernel
      have hl : raw37012step0Labels = raw37012Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37012 raw37012Labels permutation346 hz
    mixedMoment B raw37012step0 raw37012step0Labels = mixedMoment B raw37012step1 raw37012step1Labels := by
      have ha : raw37012step1 = (fun i j => raw37012step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37012step1 raw37012step0; decide +kernel
      have hl : raw37012step1Labels = raw37012step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37012step0 raw37012step0Labels permutation34 permutation2
    _ = mixedMoment B node4919 node4919Labels := by rfl

def raw37013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 1, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![3, -2, -1]]
def raw37013Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 1, 2], ![1, 1, -2], ![1, 0, -1], ![3, -2, -1]]
def raw37013step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37013step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw37013step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37013 raw37013Labels = mixedMoment B node4919 node4919Labels := by
  calc
    mixedMoment B raw37013 raw37013Labels = mixedMoment B raw37013step0 raw37013step0Labels := by
      have hz : ∀ j, raw37013 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37013step0 = (fun i j => raw37013 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37013step0 raw37013; decide +kernel
      have hl : raw37013step0Labels = raw37013Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37013 raw37013Labels permutation346 hz
    mixedMoment B raw37013step0 raw37013step0Labels = mixedMoment B raw37013step1 raw37013step1Labels := by
      have ha : raw37013step1 = (fun i j => raw37013step0 (permutation58 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37013step1 raw37013step0; decide +kernel
      have hl : raw37013step1Labels = raw37013step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37013step0 raw37013step0Labels permutation58 permutation2
    _ = mixedMoment B node4919 node4919Labels := by rfl

def raw37014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![3, -2, -1]]
def raw37014Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37014step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0], ![-2, 2, 0]]
def raw37014step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37014step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -2, 0]]
def raw37014step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37014step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -2, 0]]
def raw37014step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37014 raw37014Labels = mixedMoment B node5120 node5120Labels := by
  calc
    mixedMoment B raw37014 raw37014Labels = mixedMoment B raw37014step0 raw37014step0Labels := by
      have ha : raw37014step0 = (fun i j => raw37014 (permutation687 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37014step0 raw37014; decide +kernel
      have hl : raw37014step0Labels = raw37014Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37014 raw37014Labels permutation687 permutation3
    mixedMoment B raw37014step0 raw37014step0Labels = mixedMoment B raw37014step1 raw37014step1Labels := by
      have ha : raw37014step1 = -raw37014step0 := by apply Matrix.ext; change ∀ i j, raw37014step1 i j = -(raw37014step0 i j); unfold raw37014step1 raw37014step0; decide +kernel
      have hl : raw37014step1Labels = raw37014step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37014step1 raw37014step1Labels = mixedMoment B raw37014step2 raw37014step2Labels := by
      have ha : raw37014step2 = raw37014step1 := by apply Matrix.ext; unfold raw37014step2 raw37014step1; decide +kernel
      have hl : raw37014step1Labels = labelEmbedding6 ∘ raw37014step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37014step1 raw37014step1Labels raw37014step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5120 node5120Labels := by rfl

def raw37015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw37015Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw37015step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37015step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 2, 0]]
def raw37015step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37015step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw37015step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37015step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw37015step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37015 raw37015Labels = mixedMoment B node5156 node5156Labels := by
  calc
    mixedMoment B raw37015 raw37015Labels = mixedMoment B raw37015step0 raw37015step0Labels := by
      have hz : ∀ j, raw37015 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37015step0 = (fun i j => raw37015 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37015step0 raw37015; decide +kernel
      have hl : raw37015step0Labels = raw37015Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37015 raw37015Labels permutation346 hz
    mixedMoment B raw37015step0 raw37015step0Labels = mixedMoment B raw37015step1 raw37015step1Labels := by
      have ha : raw37015step1 = (fun i j => raw37015step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37015step1 raw37015step0; decide +kernel
      have hl : raw37015step1Labels = raw37015step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37015step0 raw37015step0Labels permutation150 permutation3
    mixedMoment B raw37015step1 raw37015step1Labels = mixedMoment B raw37015step2 raw37015step2Labels := by
      have ha : raw37015step2 = -raw37015step1 := by apply Matrix.ext; change ∀ i j, raw37015step2 i j = -(raw37015step1 i j); unfold raw37015step2 raw37015step1; decide +kernel
      have hl : raw37015step2Labels = raw37015step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37015step2 raw37015step2Labels = mixedMoment B raw37015step3 raw37015step3Labels := by
      have ha : raw37015step3 = raw37015step2 := by apply Matrix.ext; unfold raw37015step3 raw37015step2; decide +kernel
      have hl : raw37015step2Labels = labelEmbedding6 ∘ raw37015step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37015step2 raw37015step2Labels raw37015step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5156 node5156Labels := by rfl

def raw37016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![3, -2, -1]]
def raw37016Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![1, 1, -2], ![0, 1, -1], ![3, -2, -1]]
def raw37016step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37016step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 2, 0]]
def raw37016step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37016step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw37016step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37016step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw37016step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37016 raw37016Labels = mixedMoment B node5193 node5193Labels := by
  calc
    mixedMoment B raw37016 raw37016Labels = mixedMoment B raw37016step0 raw37016step0Labels := by
      have hz : ∀ j, raw37016 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37016step0 = (fun i j => raw37016 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37016step0 raw37016; decide +kernel
      have hl : raw37016step0Labels = raw37016Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37016 raw37016Labels permutation346 hz
    mixedMoment B raw37016step0 raw37016step0Labels = mixedMoment B raw37016step1 raw37016step1Labels := by
      have ha : raw37016step1 = (fun i j => raw37016step0 (permutation144 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37016step1 raw37016step0; decide +kernel
      have hl : raw37016step1Labels = raw37016step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37016step0 raw37016step0Labels permutation144 permutation3
    mixedMoment B raw37016step1 raw37016step1Labels = mixedMoment B raw37016step2 raw37016step2Labels := by
      have ha : raw37016step2 = -raw37016step1 := by apply Matrix.ext; change ∀ i j, raw37016step2 i j = -(raw37016step1 i j); unfold raw37016step2 raw37016step1; decide +kernel
      have hl : raw37016step2Labels = raw37016step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37016step2 raw37016step2Labels = mixedMoment B raw37016step3 raw37016step3Labels := by
      have ha : raw37016step3 = raw37016step2 := by apply Matrix.ext; unfold raw37016step3 raw37016step2; decide +kernel
      have hl : raw37016step2Labels = labelEmbedding6 ∘ raw37016step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37016step2 raw37016step2Labels raw37016step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5193 node5193Labels := by rfl

def raw37017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw37017Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 3, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw37017step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37017step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-3, 3], ![1, -1], ![1, -1], ![2, -2]]
def raw37017step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37017step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw37017step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical37017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37017 raw37017Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw37017 raw37017Labels = mixedMoment B raw37017step0 raw37017step0Labels := by
      have hz : ∀ j, raw37017 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37017step0 = (fun i j => raw37017 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37017step0 raw37017; decide +kernel
      have hl : raw37017step0Labels = raw37017Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37017 raw37017Labels permutation346 hz
    mixedMoment B raw37017step0 raw37017step0Labels = mixedMoment B raw37017step1 raw37017step1Labels := by
      have hz : ∀ i, raw37017step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37017step1 = (fun i j => raw37017step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37017step1 raw37017step0; decide +kernel
      have hl : raw37017step1Labels = (fun j => raw37017step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37017step0 raw37017step0Labels permutation6 hz
    mixedMoment B raw37017step1 raw37017step1Labels = mixedMoment B raw37017step2 raw37017step2Labels := by
      have ha : raw37017step2 = (fun i j => raw37017step1 (permutation56 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37017step2 raw37017step1; decide +kernel
      have hl : raw37017step2Labels = raw37017step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37017step1 raw37017step1Labels permutation56 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw37018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw37018Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw37018step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37018step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0]]
def raw37018step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37018step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]
def raw37018step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37018step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw37018step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical37018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37018 raw37018Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw37018 raw37018Labels = mixedMoment B raw37018step0 raw37018step0Labels := by
      have hz : ∀ j, raw37018 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37018step0 = (fun i j => raw37018 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37018step0 raw37018; decide +kernel
      have hl : raw37018step0Labels = raw37018Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37018 raw37018Labels permutation520 hz
    mixedMoment B raw37018step0 raw37018step0Labels = mixedMoment B raw37018step1 raw37018step1Labels := by
      have hz : ∀ j, raw37018step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37018step1 = (fun i j => raw37018step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37018step1 raw37018step0; decide +kernel
      have hl : raw37018step1Labels = raw37018step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37018step0 raw37018step0Labels permutation80 hz
    mixedMoment B raw37018step1 raw37018step1Labels = mixedMoment B raw37018step2 raw37018step2Labels := by
      have hz : ∀ i, raw37018step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37018step2 = (fun i j => raw37018step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37018step2 raw37018step1; decide +kernel
      have hl : raw37018step2Labels = (fun j => raw37018step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37018step1 raw37018step1Labels permutation6 hz
    mixedMoment B raw37018step2 raw37018step2Labels = mixedMoment B raw37018step3 raw37018step3Labels := by
      have ha : raw37018step3 = (fun i j => raw37018step2 (permutation14 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37018step3 raw37018step2; decide +kernel
      have hl : raw37018step3Labels = raw37018step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37018step2 raw37018step2Labels permutation14 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw37019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 3, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw37019Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37019step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-3, 3], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]
def raw37019step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37019step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]
def raw37019step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical37019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37019 raw37019Labels = mixedMoment B node4073 node4073Labels := by
  calc
    mixedMoment B raw37019 raw37019Labels = mixedMoment B raw37019step0 raw37019step0Labels := by
      have hz : ∀ i, raw37019 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37019step0 = (fun i j => raw37019 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37019step0 raw37019; decide +kernel
      have hl : raw37019step0Labels = (fun j => raw37019Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37019 raw37019Labels permutation6 hz
    mixedMoment B raw37019step0 raw37019step0Labels = mixedMoment B raw37019step1 raw37019step1Labels := by
      have ha : raw37019step1 = (fun i j => raw37019step0 (permutation265 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37019step1 raw37019step0; decide +kernel
      have hl : raw37019step1Labels = raw37019step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37019step0 raw37019step0Labels permutation265 permutation0
    _ = mixedMoment B node4073 node4073Labels := by rfl

def raw37020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw37020Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw37020step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37020step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw37020step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical37020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37020 raw37020Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw37020 raw37020Labels = mixedMoment B raw37020step0 raw37020step0Labels := by
      have hz : ∀ j, raw37020 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37020step0 = (fun i j => raw37020 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37020step0 raw37020; decide +kernel
      have hl : raw37020step0Labels = raw37020Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37020 raw37020Labels permutation520 hz
    mixedMoment B raw37020step0 raw37020step0Labels = mixedMoment B raw37020step1 raw37020step1Labels := by
      have hz : ∀ i, raw37020step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37020step1 = (fun i j => raw37020step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37020step1 raw37020step0; decide +kernel
      have hl : raw37020step1Labels = (fun j => raw37020step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37020step0 raw37020step0Labels permutation6 hz
    _ = mixedMoment B node4088 node4088Labels := by rfl

def raw37021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 3, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, -2, 0]]
def raw37021Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 3, 0], ![2, -2, 0], ![1, -1, 0], ![2, -2, 0]]
def raw37021step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37021step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-3, 3], ![2, -2], ![1, -1], ![2, -2]]
def raw37021step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37021step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![2, -2], ![2, -2]]
def raw37021step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical37021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37021 raw37021Labels = mixedMoment B node4075 node4075Labels := by
  calc
    mixedMoment B raw37021 raw37021Labels = mixedMoment B raw37021step0 raw37021step0Labels := by
      have hz : ∀ j, raw37021 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37021step0 = (fun i j => raw37021 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37021step0 raw37021; decide +kernel
      have hl : raw37021step0Labels = raw37021Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37021 raw37021Labels permutation346 hz
    mixedMoment B raw37021step0 raw37021step0Labels = mixedMoment B raw37021step1 raw37021step1Labels := by
      have hz : ∀ i, raw37021step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37021step1 = (fun i j => raw37021step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37021step1 raw37021step0; decide +kernel
      have hl : raw37021step1Labels = (fun j => raw37021step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37021step0 raw37021step0Labels permutation6 hz
    mixedMoment B raw37021step1 raw37021step1Labels = mixedMoment B raw37021step2 raw37021step2Labels := by
      have ha : raw37021step2 = (fun i j => raw37021step1 (permutation58 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37021step2 raw37021step1; decide +kernel
      have hl : raw37021step2Labels = raw37021step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37021step1 raw37021step1Labels permutation58 permutation0
    _ = mixedMoment B node4075 node4075Labels := by rfl

def raw37022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, -2, 0]]
def raw37022Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37022step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![-1, 1], ![2, -2], ![1, -1], ![2, -2]]
def raw37022step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37022step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]
def raw37022step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical37022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37022 raw37022Labels = mixedMoment B node4086 node4086Labels := by
  calc
    mixedMoment B raw37022 raw37022Labels = mixedMoment B raw37022step0 raw37022step0Labels := by
      have hz : ∀ i, raw37022 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37022step0 = (fun i j => raw37022 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37022step0 raw37022; decide +kernel
      have hl : raw37022step0Labels = (fun j => raw37022Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37022 raw37022Labels permutation6 hz
    mixedMoment B raw37022step0 raw37022step0Labels = mixedMoment B raw37022step1 raw37022step1Labels := by
      have ha : raw37022step1 = (fun i j => raw37022step0 (permutation154 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37022step1 raw37022step0; decide +kernel
      have hl : raw37022step1Labels = raw37022step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37022step0 raw37022step0Labels permutation154 permutation0
    _ = mixedMoment B node4086 node4086Labels := by rfl

def raw37023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, -2, 0]]
def raw37023Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37023step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![2, -2, 0]]
def raw37023step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37023step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![2, -2, 0], ![2, -2, 0]]
def raw37023step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37023step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![2, -2]]
def raw37023step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical37023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37023 raw37023Labels = mixedMoment B node4089 node4089Labels := by
  calc
    mixedMoment B raw37023 raw37023Labels = mixedMoment B raw37023step0 raw37023step0Labels := by
      have hz : ∀ j, raw37023 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37023step0 = (fun i j => raw37023 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37023step0 raw37023; decide +kernel
      have hl : raw37023step0Labels = raw37023Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37023 raw37023Labels permutation520 hz
    mixedMoment B raw37023step0 raw37023step0Labels = mixedMoment B raw37023step1 raw37023step1Labels := by
      have hz : ∀ j, raw37023step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37023step1 = (fun i j => raw37023step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37023step1 raw37023step0; decide +kernel
      have hl : raw37023step1Labels = raw37023step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37023step0 raw37023step0Labels permutation80 hz
    mixedMoment B raw37023step1 raw37023step1Labels = mixedMoment B raw37023step2 raw37023step2Labels := by
      have hz : ∀ i, raw37023step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37023step2 = (fun i j => raw37023step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37023step2 raw37023step1; decide +kernel
      have hl : raw37023step2Labels = (fun j => raw37023step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37023step1 raw37023step1Labels permutation6 hz
    _ = mixedMoment B node4089 node4089Labels := by rfl

def raw37024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw37024Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 3, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw37024step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37024step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-3, 3], ![1, -1], ![1, -1], ![3, -3]]
def raw37024step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37024step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![3, -3]]
def raw37024step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical37024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37024 raw37024Labels = mixedMoment B node4074 node4074Labels := by
  calc
    mixedMoment B raw37024 raw37024Labels = mixedMoment B raw37024step0 raw37024step0Labels := by
      have hz : ∀ j, raw37024 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw37024step0 = (fun i j => raw37024 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw37024step0 raw37024; decide +kernel
      have hl : raw37024step0Labels = raw37024Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37024 raw37024Labels permutation346 hz
    mixedMoment B raw37024step0 raw37024step0Labels = mixedMoment B raw37024step1 raw37024step1Labels := by
      have hz : ∀ i, raw37024step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37024step1 = (fun i j => raw37024step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37024step1 raw37024step0; decide +kernel
      have hl : raw37024step1Labels = (fun j => raw37024step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37024step0 raw37024step0Labels permutation6 hz
    mixedMoment B raw37024step1 raw37024step1Labels = mixedMoment B raw37024step2 raw37024step2Labels := by
      have ha : raw37024step2 = (fun i j => raw37024step1 (permutation56 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37024step2 raw37024step1; decide +kernel
      have hl : raw37024step2Labels = raw37024step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37024step1 raw37024step1Labels permutation56 permutation0
    _ = mixedMoment B node4074 node4074Labels := by rfl

def raw37025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw37025Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37025step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![3, -3]]
def raw37025step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37025step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![1, -1], ![-1, 1], ![-2, 2], ![-2, 2]]
def raw37025step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37025step2 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2], ![2, -2]]
def raw37025step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical37025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37025 raw37025Labels = mixedMoment B node4078 node4078Labels := by
  calc
    mixedMoment B raw37025 raw37025Labels = mixedMoment B raw37025step0 raw37025step0Labels := by
      have hz : ∀ i, raw37025 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37025step0 = (fun i j => raw37025 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37025step0 raw37025; decide +kernel
      have hl : raw37025step0Labels = (fun j => raw37025Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37025 raw37025Labels permutation6 hz
    mixedMoment B raw37025step0 raw37025step0Labels = mixedMoment B raw37025step1 raw37025step1Labels := by
      have ha : raw37025step1 = (fun i j => raw37025step0 (permutation663 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37025step1 raw37025step0; decide +kernel
      have hl : raw37025step1Labels = raw37025step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37025step0 raw37025step0Labels permutation663 permutation0
    mixedMoment B raw37025step1 raw37025step1Labels = mixedMoment B raw37025step2 raw37025step2Labels := by
      have ha : raw37025step2 = -raw37025step1 := by apply Matrix.ext; change ∀ i j, raw37025step2 i j = -(raw37025step1 i j); unfold raw37025step2 raw37025step1; decide +kernel
      have hl : raw37025step2Labels = raw37025step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4078 node4078Labels := by rfl

def raw37026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, -3, 0]]
def raw37026Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0]]
def raw37026step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37026step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![1, -1, 0], ![3, -3, 0]]
def raw37026step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37026step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![3, -3]]
def raw37026step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37026step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-2, 2], ![-2, 2]]
def raw37026step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37026step4 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw37026step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical37026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37026 raw37026Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw37026 raw37026Labels = mixedMoment B raw37026step0 raw37026step0Labels := by
      have hz : ∀ j, raw37026 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37026step0 = (fun i j => raw37026 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37026step0 raw37026; decide +kernel
      have hl : raw37026step0Labels = raw37026Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37026 raw37026Labels permutation520 hz
    mixedMoment B raw37026step0 raw37026step0Labels = mixedMoment B raw37026step1 raw37026step1Labels := by
      have hz : ∀ j, raw37026step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw37026step1 = (fun i j => raw37026step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw37026step1 raw37026step0; decide +kernel
      have hl : raw37026step1Labels = raw37026step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37026step0 raw37026step0Labels permutation80 hz
    mixedMoment B raw37026step1 raw37026step1Labels = mixedMoment B raw37026step2 raw37026step2Labels := by
      have hz : ∀ i, raw37026step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37026step2 = (fun i j => raw37026step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37026step2 raw37026step1; decide +kernel
      have hl : raw37026step2Labels = (fun j => raw37026step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37026step1 raw37026step1Labels permutation6 hz
    mixedMoment B raw37026step2 raw37026step2Labels = mixedMoment B raw37026step3 raw37026step3Labels := by
      have ha : raw37026step3 = (fun i j => raw37026step2 (permutation30 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37026step3 raw37026step2; decide +kernel
      have hl : raw37026step3Labels = raw37026step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37026step2 raw37026step2Labels permutation30 permutation0
    mixedMoment B raw37026step3 raw37026step3Labels = mixedMoment B raw37026step4 raw37026step4Labels := by
      have ha : raw37026step4 = -raw37026step3 := by apply Matrix.ext; change ∀ i j, raw37026step4 i j = -(raw37026step3 i j); unfold raw37026step4 raw37026step3; decide +kernel
      have hl : raw37026step4Labels = raw37026step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4082 node4082Labels := by rfl

def raw37027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw37027Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37027step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37027step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37027step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37027step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37027 raw37027Labels = mixedMoment B node4859 node4859Labels := by
  calc
    mixedMoment B raw37027 raw37027Labels = mixedMoment B raw37027step0 raw37027step0Labels := by
      have ha : raw37027step0 = (fun i j => raw37027 (permutation283 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37027step0 raw37027; decide +kernel
      have hl : raw37027step0Labels = raw37027Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37027 raw37027Labels permutation283 permutation3
    mixedMoment B raw37027step0 raw37027step0Labels = mixedMoment B raw37027step1 raw37027step1Labels := by
      have ha : raw37027step1 = raw37027step0 := by apply Matrix.ext; unfold raw37027step1 raw37027step0; decide +kernel
      have hl : raw37027step0Labels = labelEmbedding6 ∘ raw37027step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37027step0 raw37027step0Labels raw37027step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4859 node4859Labels := by rfl

def raw37028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw37028Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw37028step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37028step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37028step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37028step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37028step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37028 raw37028Labels = mixedMoment B node5448 node5448Labels := by
  calc
    mixedMoment B raw37028 raw37028Labels = mixedMoment B raw37028step0 raw37028step0Labels := by
      have hz : ∀ j, raw37028 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37028step0 = (fun i j => raw37028 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37028step0 raw37028; decide +kernel
      have hl : raw37028step0Labels = raw37028Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37028 raw37028Labels permutation434 hz
    mixedMoment B raw37028step0 raw37028step0Labels = mixedMoment B raw37028step1 raw37028step1Labels := by
      have ha : raw37028step1 = (fun i j => raw37028step0 (permutation60 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37028step1 raw37028step0; decide +kernel
      have hl : raw37028step1Labels = raw37028step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37028step0 raw37028step0Labels permutation60 permutation3
    mixedMoment B raw37028step1 raw37028step1Labels = mixedMoment B raw37028step2 raw37028step2Labels := by
      have ha : raw37028step2 = raw37028step1 := by apply Matrix.ext; unfold raw37028step2 raw37028step1; decide +kernel
      have hl : raw37028step1Labels = labelEmbedding6 ∘ raw37028step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37028step1 raw37028step1Labels raw37028step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5448 node5448Labels := by rfl

def raw37029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw37029Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw37029step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37029step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37029step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37029step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37029step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37029 raw37029Labels = mixedMoment B node5448 node5448Labels := by
  calc
    mixedMoment B raw37029 raw37029Labels = mixedMoment B raw37029step0 raw37029step0Labels := by
      have hz : ∀ j, raw37029 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37029step0 = (fun i j => raw37029 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37029step0 raw37029; decide +kernel
      have hl : raw37029step0Labels = raw37029Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37029 raw37029Labels permutation520 hz
    mixedMoment B raw37029step0 raw37029step0Labels = mixedMoment B raw37029step1 raw37029step1Labels := by
      have ha : raw37029step1 = (fun i j => raw37029step0 (permutation60 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37029step1 raw37029step0; decide +kernel
      have hl : raw37029step1Labels = raw37029step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37029step0 raw37029step0Labels permutation60 permutation3
    mixedMoment B raw37029step1 raw37029step1Labels = mixedMoment B raw37029step2 raw37029step2Labels := by
      have ha : raw37029step2 = raw37029step1 := by apply Matrix.ext; unfold raw37029step2 raw37029step1; decide +kernel
      have hl : raw37029step1Labels = labelEmbedding6 ∘ raw37029step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37029step1 raw37029step1Labels raw37029step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5448 node5448Labels := by rfl

def raw37030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw37030Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37030step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37030step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37030step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37030step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37030step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37030step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37030 raw37030Labels = mixedMoment B node5383 node5383Labels := by
  calc
    mixedMoment B raw37030 raw37030Labels = mixedMoment B raw37030step0 raw37030step0Labels := by
      have ha : raw37030step0 = (fun i j => raw37030 (permutation333 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37030step0 raw37030; decide +kernel
      have hl : raw37030step0Labels = raw37030Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37030 raw37030Labels permutation333 permutation5
    mixedMoment B raw37030step0 raw37030step0Labels = mixedMoment B raw37030step1 raw37030step1Labels := by
      have ha : raw37030step1 = -raw37030step0 := by apply Matrix.ext; change ∀ i j, raw37030step1 i j = -(raw37030step0 i j); unfold raw37030step1 raw37030step0; decide +kernel
      have hl : raw37030step1Labels = raw37030step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37030step1 raw37030step1Labels = mixedMoment B raw37030step2 raw37030step2Labels := by
      have ha : raw37030step2 = raw37030step1 := by apply Matrix.ext; unfold raw37030step2 raw37030step1; decide +kernel
      have hl : raw37030step1Labels = labelEmbedding8 ∘ raw37030step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37030step1 raw37030step1Labels raw37030step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5383 node5383Labels := by rfl

def raw37031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw37031Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37031step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37031step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37031step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37031step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37031 raw37031Labels = mixedMoment B node4672 node4672Labels := by
  calc
    mixedMoment B raw37031 raw37031Labels = mixedMoment B raw37031step0 raw37031step0Labels := by
      have ha : raw37031step0 = (fun i j => raw37031 (permutation286 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37031step0 raw37031; decide +kernel
      have hl : raw37031step0Labels = raw37031Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37031 raw37031Labels permutation286 permutation3
    mixedMoment B raw37031step0 raw37031step0Labels = mixedMoment B raw37031step1 raw37031step1Labels := by
      have ha : raw37031step1 = raw37031step0 := by apply Matrix.ext; unfold raw37031step1 raw37031step0; decide +kernel
      have hl : raw37031step0Labels = labelEmbedding6 ∘ raw37031step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37031step0 raw37031step0Labels raw37031step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4672 node4672Labels := by rfl

def raw37032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw37032Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw37032step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37032step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw37032step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37032step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw37032step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37032 raw37032Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw37032 raw37032Labels = mixedMoment B raw37032step0 raw37032step0Labels := by
      have hz : ∀ j, raw37032 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37032step0 = (fun i j => raw37032 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37032step0 raw37032; decide +kernel
      have hl : raw37032step0Labels = raw37032Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37032 raw37032Labels permutation434 hz
    mixedMoment B raw37032step0 raw37032step0Labels = mixedMoment B raw37032step1 raw37032step1Labels := by
      have ha : raw37032step1 = (fun i j => raw37032step0 (permutation61 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37032step1 raw37032step0; decide +kernel
      have hl : raw37032step1Labels = raw37032step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37032step0 raw37032step0Labels permutation61 permutation3
    mixedMoment B raw37032step1 raw37032step1Labels = mixedMoment B raw37032step2 raw37032step2Labels := by
      have ha : raw37032step2 = raw37032step1 := by apply Matrix.ext; unfold raw37032step2 raw37032step1; decide +kernel
      have hl : raw37032step1Labels = labelEmbedding6 ∘ raw37032step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37032step1 raw37032step1Labels raw37032step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5384 node5384Labels := by rfl

def raw37033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw37033Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw37033step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37033step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw37033step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37033step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw37033step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37033 raw37033Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw37033 raw37033Labels = mixedMoment B raw37033step0 raw37033step0Labels := by
      have hz : ∀ j, raw37033 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37033step0 = (fun i j => raw37033 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37033step0 raw37033; decide +kernel
      have hl : raw37033step0Labels = raw37033Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37033 raw37033Labels permutation520 hz
    mixedMoment B raw37033step0 raw37033step0Labels = mixedMoment B raw37033step1 raw37033step1Labels := by
      have ha : raw37033step1 = (fun i j => raw37033step0 (permutation61 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37033step1 raw37033step0; decide +kernel
      have hl : raw37033step1Labels = raw37033step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37033step0 raw37033step0Labels permutation61 permutation3
    mixedMoment B raw37033step1 raw37033step1Labels = mixedMoment B raw37033step2 raw37033step2Labels := by
      have ha : raw37033step2 = raw37033step1 := by apply Matrix.ext; unfold raw37033step2 raw37033step1; decide +kernel
      have hl : raw37033step1Labels = labelEmbedding6 ∘ raw37033step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37033step1 raw37033step1Labels raw37033step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5384 node5384Labels := by rfl

def raw37034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw37034Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37034step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37034step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37034step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37034step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37034 raw37034Labels = mixedMoment B node5374 node5374Labels := by
  calc
    mixedMoment B raw37034 raw37034Labels = mixedMoment B raw37034step0 raw37034step0Labels := by
      have ha : raw37034step0 = (fun i j => raw37034 (permutation286 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37034step0 raw37034; decide +kernel
      have hl : raw37034step0Labels = raw37034Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37034 raw37034Labels permutation286 permutation3
    mixedMoment B raw37034step0 raw37034step0Labels = mixedMoment B raw37034step1 raw37034step1Labels := by
      have ha : raw37034step1 = raw37034step0 := by apply Matrix.ext; unfold raw37034step1 raw37034step0; decide +kernel
      have hl : raw37034step0Labels = labelEmbedding6 ∘ raw37034step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37034step0 raw37034step0Labels raw37034step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5374 node5374Labels := by rfl

def raw37035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw37035Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37035step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37035step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37035step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37035step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37035 raw37035Labels = mixedMoment B node4672 node4672Labels := by
  calc
    mixedMoment B raw37035 raw37035Labels = mixedMoment B raw37035step0 raw37035step0Labels := by
      have ha : raw37035step0 = (fun i j => raw37035 (permutation284 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37035step0 raw37035; decide +kernel
      have hl : raw37035step0Labels = raw37035Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37035 raw37035Labels permutation284 permutation3
    mixedMoment B raw37035step0 raw37035step0Labels = mixedMoment B raw37035step1 raw37035step1Labels := by
      have ha : raw37035step1 = raw37035step0 := by apply Matrix.ext; unfold raw37035step1 raw37035step0; decide +kernel
      have hl : raw37035step0Labels = labelEmbedding6 ∘ raw37035step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37035step0 raw37035step0Labels raw37035step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4672 node4672Labels := by rfl

def raw37036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![1, 1, -2]]
def raw37036Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37036step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw37036step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37036step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw37036step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37036step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw37036step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37036 raw37036Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw37036 raw37036Labels = mixedMoment B raw37036step0 raw37036step0Labels := by
      have hz : ∀ j, raw37036 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37036step0 = (fun i j => raw37036 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37036step0 raw37036; decide +kernel
      have hl : raw37036step0Labels = raw37036Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37036 raw37036Labels permutation520 hz
    mixedMoment B raw37036step0 raw37036step0Labels = mixedMoment B raw37036step1 raw37036step1Labels := by
      have ha : raw37036step1 = (fun i j => raw37036step0 (permutation60 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37036step1 raw37036step0; decide +kernel
      have hl : raw37036step1Labels = raw37036step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37036step0 raw37036step0Labels permutation60 permutation3
    mixedMoment B raw37036step1 raw37036step1Labels = mixedMoment B raw37036step2 raw37036step2Labels := by
      have ha : raw37036step2 = raw37036step1 := by apply Matrix.ext; unfold raw37036step2 raw37036step1; decide +kernel
      have hl : raw37036step1Labels = labelEmbedding6 ∘ raw37036step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37036step1 raw37036step1Labels raw37036step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5384 node5384Labels := by rfl

def raw37037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw37037Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37037step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37037step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37037step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37037step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37037 raw37037Labels = mixedMoment B node5374 node5374Labels := by
  calc
    mixedMoment B raw37037 raw37037Labels = mixedMoment B raw37037step0 raw37037step0Labels := by
      have ha : raw37037step0 = (fun i j => raw37037 (permutation284 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37037step0 raw37037; decide +kernel
      have hl : raw37037step0Labels = raw37037Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37037 raw37037Labels permutation284 permutation3
    mixedMoment B raw37037step0 raw37037step0Labels = mixedMoment B raw37037step1 raw37037step1Labels := by
      have ha : raw37037step1 = raw37037step0 := by apply Matrix.ext; unfold raw37037step1 raw37037step0; decide +kernel
      have hl : raw37037step0Labels = labelEmbedding6 ∘ raw37037step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37037step0 raw37037step0Labels raw37037step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5374 node5374Labels := by rfl

def raw37038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw37038Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37038step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37038step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37038step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37038step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37038 raw37038Labels = mixedMoment B node4672 node4672Labels := by
  calc
    mixedMoment B raw37038 raw37038Labels = mixedMoment B raw37038step0 raw37038step0Labels := by
      have ha : raw37038step0 = (fun i j => raw37038 (permutation283 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37038step0 raw37038; decide +kernel
      have hl : raw37038step0Labels = raw37038Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37038 raw37038Labels permutation283 permutation3
    mixedMoment B raw37038step0 raw37038step0Labels = mixedMoment B raw37038step1 raw37038step1Labels := by
      have ha : raw37038step1 = raw37038step0 := by apply Matrix.ext; unfold raw37038step1 raw37038step0; decide +kernel
      have hl : raw37038step0Labels = labelEmbedding6 ∘ raw37038step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37038step0 raw37038step0Labels raw37038step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4672 node4672Labels := by rfl

def raw37039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw37039Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37039step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37039step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37039step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37039step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37039 raw37039Labels = mixedMoment B node5374 node5374Labels := by
  calc
    mixedMoment B raw37039 raw37039Labels = mixedMoment B raw37039step0 raw37039step0Labels := by
      have ha : raw37039step0 = (fun i j => raw37039 (permutation283 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37039step0 raw37039; decide +kernel
      have hl : raw37039step0Labels = raw37039Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37039 raw37039Labels permutation283 permutation3
    mixedMoment B raw37039step0 raw37039step0Labels = mixedMoment B raw37039step1 raw37039step1Labels := by
      have ha : raw37039step1 = raw37039step0 := by apply Matrix.ext; unfold raw37039step1 raw37039step0; decide +kernel
      have hl : raw37039step0Labels = labelEmbedding6 ∘ raw37039step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37039step0 raw37039step0Labels raw37039step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5374 node5374Labels := by rfl

def raw37040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37040Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37040step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37040step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37040 raw37040Labels = mixedMoment B node5162 node5162Labels := by
  calc
    mixedMoment B raw37040 raw37040Labels = mixedMoment B raw37040step0 raw37040step0Labels := by
      have ha : raw37040step0 = (fun i j => raw37040 (permutation283 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37040step0 raw37040; decide +kernel
      have hl : raw37040step0Labels = raw37040Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37040 raw37040Labels permutation283 permutation2
    _ = mixedMoment B node5162 node5162Labels := by rfl

def raw37041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37041Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37041step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37041step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37041 raw37041Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw37041 raw37041Labels = mixedMoment B raw37041step0 raw37041step0Labels := by
      have ha : raw37041step0 = (fun i j => raw37041 (permutation269 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37041step0 raw37041; decide +kernel
      have hl : raw37041step0Labels = raw37041Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37041 raw37041Labels permutation269 permutation2
    _ = mixedMoment B node5431 node5431Labels := by rfl

def raw37042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37042Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37042step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37042step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37042 raw37042Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw37042 raw37042Labels = mixedMoment B raw37042step0 raw37042step0Labels := by
      have ha : raw37042step0 = (fun i j => raw37042 (permutation275 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37042step0 raw37042; decide +kernel
      have hl : raw37042step0Labels = raw37042Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37042 raw37042Labels permutation275 permutation2
    _ = mixedMoment B node5431 node5431Labels := by rfl

def raw37043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw37043Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37043step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37043step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37043 raw37043Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw37043 raw37043Labels = mixedMoment B raw37043step0 raw37043step0Labels := by
      have ha : raw37043step0 = (fun i j => raw37043 (permutation281 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37043step0 raw37043; decide +kernel
      have hl : raw37043step0Labels = raw37043Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37043 raw37043Labels permutation281 permutation2
    _ = mixedMoment B node5431 node5431Labels := by rfl

def raw37044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw37044Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37044step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37044step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37044 raw37044Labels = mixedMoment B node5427 node5427Labels := by
  calc
    mixedMoment B raw37044 raw37044Labels = mixedMoment B raw37044step0 raw37044step0Labels := by
      have ha : raw37044step0 = (fun i j => raw37044 (permutation283 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37044step0 raw37044; decide +kernel
      have hl : raw37044step0Labels = raw37044Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37044 raw37044Labels permutation283 permutation2
    _ = mixedMoment B node5427 node5427Labels := by rfl

def raw37045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37045Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37045step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw37045step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37045step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw37045step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37045 raw37045Labels = mixedMoment B node4863 node4863Labels := by
  calc
    mixedMoment B raw37045 raw37045Labels = mixedMoment B raw37045step0 raw37045step0Labels := by
      have ha : raw37045step0 = (fun i j => raw37045 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37045step0 raw37045; decide +kernel
      have hl : raw37045step0Labels = raw37045Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37045 raw37045Labels permutation152 permutation3
    mixedMoment B raw37045step0 raw37045step0Labels = mixedMoment B raw37045step1 raw37045step1Labels := by
      have ha : raw37045step1 = raw37045step0 := by apply Matrix.ext; unfold raw37045step1 raw37045step0; decide +kernel
      have hl : raw37045step0Labels = labelEmbedding6 ∘ raw37045step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37045step0 raw37045step0Labels raw37045step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4863 node4863Labels := by rfl

def raw37046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37046Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37046step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw37046step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37046step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw37046step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37046step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw37046step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37046 raw37046Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw37046 raw37046Labels = mixedMoment B raw37046step0 raw37046step0Labels := by
      have ha : raw37046step0 = (fun i j => raw37046 (permutation184 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37046step0 raw37046; decide +kernel
      have hl : raw37046step0Labels = raw37046Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37046 raw37046Labels permutation184 permutation5
    mixedMoment B raw37046step0 raw37046step0Labels = mixedMoment B raw37046step1 raw37046step1Labels := by
      have ha : raw37046step1 = -raw37046step0 := by apply Matrix.ext; change ∀ i j, raw37046step1 i j = -(raw37046step0 i j); unfold raw37046step1 raw37046step0; decide +kernel
      have hl : raw37046step1Labels = raw37046step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37046step1 raw37046step1Labels = mixedMoment B raw37046step2 raw37046step2Labels := by
      have ha : raw37046step2 = raw37046step1 := by apply Matrix.ext; unfold raw37046step2 raw37046step1; decide +kernel
      have hl : raw37046step1Labels = labelEmbedding8 ∘ raw37046step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37046step1 raw37046step1Labels raw37046step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5429 node5429Labels := by rfl

def raw37047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37047Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37047step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw37047step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37047step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw37047step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37047step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw37047step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37047 raw37047Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw37047 raw37047Labels = mixedMoment B raw37047step0 raw37047step0Labels := by
      have ha : raw37047step0 = (fun i j => raw37047 (permutation208 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37047step0 raw37047; decide +kernel
      have hl : raw37047step0Labels = raw37047Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37047 raw37047Labels permutation208 permutation5
    mixedMoment B raw37047step0 raw37047step0Labels = mixedMoment B raw37047step1 raw37047step1Labels := by
      have ha : raw37047step1 = -raw37047step0 := by apply Matrix.ext; change ∀ i j, raw37047step1 i j = -(raw37047step0 i j); unfold raw37047step1 raw37047step0; decide +kernel
      have hl : raw37047step1Labels = raw37047step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37047step1 raw37047step1Labels = mixedMoment B raw37047step2 raw37047step2Labels := by
      have ha : raw37047step2 = raw37047step1 := by apply Matrix.ext; unfold raw37047step2 raw37047step1; decide +kernel
      have hl : raw37047step1Labels = labelEmbedding8 ∘ raw37047step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37047step1 raw37047step1Labels raw37047step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5429 node5429Labels := by rfl

def raw37048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw37048Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37048step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw37048step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37048step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw37048step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37048step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw37048step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37048 raw37048Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw37048 raw37048Labels = mixedMoment B raw37048step0 raw37048step0Labels := by
      have ha : raw37048step0 = (fun i j => raw37048 (permutation232 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37048step0 raw37048; decide +kernel
      have hl : raw37048step0Labels = raw37048Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37048 raw37048Labels permutation232 permutation5
    mixedMoment B raw37048step0 raw37048step0Labels = mixedMoment B raw37048step1 raw37048step1Labels := by
      have ha : raw37048step1 = -raw37048step0 := by apply Matrix.ext; change ∀ i j, raw37048step1 i j = -(raw37048step0 i j); unfold raw37048step1 raw37048step0; decide +kernel
      have hl : raw37048step1Labels = raw37048step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37048step1 raw37048step1Labels = mixedMoment B raw37048step2 raw37048step2Labels := by
      have ha : raw37048step2 = raw37048step1 := by apply Matrix.ext; unfold raw37048step2 raw37048step1; decide +kernel
      have hl : raw37048step1Labels = labelEmbedding8 ∘ raw37048step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37048step1 raw37048step1Labels raw37048step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5429 node5429Labels := by rfl

def raw37049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw37049Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37049step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw37049step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37049step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw37049step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37049 raw37049Labels = mixedMoment B node5447 node5447Labels := by
  calc
    mixedMoment B raw37049 raw37049Labels = mixedMoment B raw37049step0 raw37049step0Labels := by
      have ha : raw37049step0 = (fun i j => raw37049 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37049step0 raw37049; decide +kernel
      have hl : raw37049step0Labels = raw37049Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37049 raw37049Labels permutation170 permutation3
    mixedMoment B raw37049step0 raw37049step0Labels = mixedMoment B raw37049step1 raw37049step1Labels := by
      have ha : raw37049step1 = raw37049step0 := by apply Matrix.ext; unfold raw37049step1 raw37049step0; decide +kernel
      have hl : raw37049step0Labels = labelEmbedding6 ∘ raw37049step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37049step0 raw37049step0Labels raw37049step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5447 node5447Labels := by rfl

def raw37050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37050Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37050step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw37050step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37050step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw37050step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37050 raw37050Labels = mixedMoment B node4677 node4677Labels := by
  calc
    mixedMoment B raw37050 raw37050Labels = mixedMoment B raw37050step0 raw37050step0Labels := by
      have ha : raw37050step0 = (fun i j => raw37050 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37050step0 raw37050; decide +kernel
      have hl : raw37050step0Labels = raw37050Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37050 raw37050Labels permutation161 permutation3
    mixedMoment B raw37050step0 raw37050step0Labels = mixedMoment B raw37050step1 raw37050step1Labels := by
      have ha : raw37050step1 = raw37050step0 := by apply Matrix.ext; unfold raw37050step1 raw37050step0; decide +kernel
      have hl : raw37050step0Labels = labelEmbedding6 ∘ raw37050step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37050step0 raw37050step0Labels raw37050step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4677 node4677Labels := by rfl

def raw37051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37051Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37051step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37051step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37051 raw37051Labels = mixedMoment B node4964 node4964Labels := by
  calc
    mixedMoment B raw37051 raw37051Labels = mixedMoment B raw37051step0 raw37051step0Labels := by
      have ha : raw37051step0 = (fun i j => raw37051 (permutation286 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37051step0 raw37051; decide +kernel
      have hl : raw37051step0Labels = raw37051Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37051 raw37051Labels permutation286 permutation2
    _ = mixedMoment B node4964 node4964Labels := by rfl

def raw37052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37052Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37052step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw37052step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37052step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw37052step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37052 raw37052Labels = mixedMoment B node5379 node5379Labels := by
  calc
    mixedMoment B raw37052 raw37052Labels = mixedMoment B raw37052step0 raw37052step0Labels := by
      have ha : raw37052step0 = (fun i j => raw37052 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37052step0 raw37052; decide +kernel
      have hl : raw37052step0Labels = raw37052Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37052 raw37052Labels permutation161 permutation3
    mixedMoment B raw37052step0 raw37052step0Labels = mixedMoment B raw37052step1 raw37052step1Labels := by
      have ha : raw37052step1 = raw37052step0 := by apply Matrix.ext; unfold raw37052step1 raw37052step0; decide +kernel
      have hl : raw37052step0Labels = labelEmbedding6 ∘ raw37052step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37052step0 raw37052step0Labels raw37052step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5379 node5379Labels := by rfl

def raw37053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw37053Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37053step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw37053step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37053step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw37053step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37053 raw37053Labels = mixedMoment B node5379 node5379Labels := by
  calc
    mixedMoment B raw37053 raw37053Labels = mixedMoment B raw37053step0 raw37053step0Labels := by
      have ha : raw37053step0 = (fun i j => raw37053 (permutation167 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37053step0 raw37053; decide +kernel
      have hl : raw37053step0Labels = raw37053Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37053 raw37053Labels permutation167 permutation3
    mixedMoment B raw37053step0 raw37053step0Labels = mixedMoment B raw37053step1 raw37053step1Labels := by
      have ha : raw37053step1 = raw37053step0 := by apply Matrix.ext; unfold raw37053step1 raw37053step0; decide +kernel
      have hl : raw37053step0Labels = labelEmbedding6 ∘ raw37053step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37053step0 raw37053step0Labels raw37053step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5379 node5379Labels := by rfl

def raw37054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw37054Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37054step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37054step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37054 raw37054Labels = mixedMoment B node5380 node5380Labels := by
  calc
    mixedMoment B raw37054 raw37054Labels = mixedMoment B raw37054step0 raw37054step0Labels := by
      have ha : raw37054step0 = (fun i j => raw37054 (permutation286 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37054step0 raw37054; decide +kernel
      have hl : raw37054step0Labels = raw37054Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37054 raw37054Labels permutation286 permutation2
    _ = mixedMoment B node5380 node5380Labels := by rfl

def raw37055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37055Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37055step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw37055step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37055step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw37055step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37055 raw37055Labels = mixedMoment B node4677 node4677Labels := by
  calc
    mixedMoment B raw37055 raw37055Labels = mixedMoment B raw37055step0 raw37055step0Labels := by
      have ha : raw37055step0 = (fun i j => raw37055 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37055step0 raw37055; decide +kernel
      have hl : raw37055step0Labels = raw37055Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37055 raw37055Labels permutation155 permutation3
    mixedMoment B raw37055step0 raw37055step0Labels = mixedMoment B raw37055step1 raw37055step1Labels := by
      have ha : raw37055step1 = raw37055step0 := by apply Matrix.ext; unfold raw37055step1 raw37055step0; decide +kernel
      have hl : raw37055step0Labels = labelEmbedding6 ∘ raw37055step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37055step0 raw37055step0Labels raw37055step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4677 node4677Labels := by rfl

def raw37056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37056Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37056step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37056step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37056 raw37056Labels = mixedMoment B node4964 node4964Labels := by
  calc
    mixedMoment B raw37056 raw37056Labels = mixedMoment B raw37056step0 raw37056step0Labels := by
      have ha : raw37056step0 = (fun i j => raw37056 (permutation284 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37056step0 raw37056; decide +kernel
      have hl : raw37056step0Labels = raw37056Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37056 raw37056Labels permutation284 permutation2
    _ = mixedMoment B node4964 node4964Labels := by rfl

def raw37057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37057Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37057step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw37057step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37057step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw37057step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37057 raw37057Labels = mixedMoment B node5379 node5379Labels := by
  calc
    mixedMoment B raw37057 raw37057Labels = mixedMoment B raw37057step0 raw37057step0Labels := by
      have ha : raw37057step0 = (fun i j => raw37057 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37057step0 raw37057; decide +kernel
      have hl : raw37057step0Labels = raw37057Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37057 raw37057Labels permutation155 permutation3
    mixedMoment B raw37057step0 raw37057step0Labels = mixedMoment B raw37057step1 raw37057step1Labels := by
      have ha : raw37057step1 = raw37057step0 := by apply Matrix.ext; unfold raw37057step1 raw37057step0; decide +kernel
      have hl : raw37057step0Labels = labelEmbedding6 ∘ raw37057step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37057step0 raw37057step0Labels raw37057step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5379 node5379Labels := by rfl

def raw37058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw37058Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37058step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw37058step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37058step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw37058step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37058 raw37058Labels = mixedMoment B node5379 node5379Labels := by
  calc
    mixedMoment B raw37058 raw37058Labels = mixedMoment B raw37058step0 raw37058step0Labels := by
      have ha : raw37058step0 = (fun i j => raw37058 (permutation165 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37058step0 raw37058; decide +kernel
      have hl : raw37058step0Labels = raw37058Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37058 raw37058Labels permutation165 permutation3
    mixedMoment B raw37058step0 raw37058step0Labels = mixedMoment B raw37058step1 raw37058step1Labels := by
      have ha : raw37058step1 = raw37058step0 := by apply Matrix.ext; unfold raw37058step1 raw37058step0; decide +kernel
      have hl : raw37058step0Labels = labelEmbedding6 ∘ raw37058step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37058step0 raw37058step0Labels raw37058step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5379 node5379Labels := by rfl

def raw37059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw37059Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37059step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37059step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37059 raw37059Labels = mixedMoment B node5380 node5380Labels := by
  calc
    mixedMoment B raw37059 raw37059Labels = mixedMoment B raw37059step0 raw37059step0Labels := by
      have ha : raw37059step0 = (fun i j => raw37059 (permutation284 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37059step0 raw37059; decide +kernel
      have hl : raw37059step0Labels = raw37059Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37059 raw37059Labels permutation284 permutation2
    _ = mixedMoment B node5380 node5380Labels := by rfl

def raw37060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw37060Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37060step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw37060step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37060step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw37060step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37060 raw37060Labels = mixedMoment B node4677 node4677Labels := by
  calc
    mixedMoment B raw37060 raw37060Labels = mixedMoment B raw37060step0 raw37060step0Labels := by
      have ha : raw37060step0 = (fun i j => raw37060 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37060step0 raw37060; decide +kernel
      have hl : raw37060step0Labels = raw37060Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37060 raw37060Labels permutation153 permutation3
    mixedMoment B raw37060step0 raw37060step0Labels = mixedMoment B raw37060step1 raw37060step1Labels := by
      have ha : raw37060step1 = raw37060step0 := by apply Matrix.ext; unfold raw37060step1 raw37060step0; decide +kernel
      have hl : raw37060step0Labels = labelEmbedding6 ∘ raw37060step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37060step0 raw37060step0Labels raw37060step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4677 node4677Labels := by rfl

def raw37061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw37061Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37061step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37061step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37061 raw37061Labels = mixedMoment B node4964 node4964Labels := by
  calc
    mixedMoment B raw37061 raw37061Labels = mixedMoment B raw37061step0 raw37061step0Labels := by
      have ha : raw37061step0 = (fun i j => raw37061 (permutation283 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37061step0 raw37061; decide +kernel
      have hl : raw37061step0Labels = raw37061Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37061 raw37061Labels permutation283 permutation2
    _ = mixedMoment B node4964 node4964Labels := by rfl

def raw37062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw37062Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37062step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw37062step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37062step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw37062step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37062 raw37062Labels = mixedMoment B node5379 node5379Labels := by
  calc
    mixedMoment B raw37062 raw37062Labels = mixedMoment B raw37062step0 raw37062step0Labels := by
      have ha : raw37062step0 = (fun i j => raw37062 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37062step0 raw37062; decide +kernel
      have hl : raw37062step0Labels = raw37062Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37062 raw37062Labels permutation153 permutation3
    mixedMoment B raw37062step0 raw37062step0Labels = mixedMoment B raw37062step1 raw37062step1Labels := by
      have ha : raw37062step1 = raw37062step0 := by apply Matrix.ext; unfold raw37062step1 raw37062step0; decide +kernel
      have hl : raw37062step0Labels = labelEmbedding6 ∘ raw37062step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37062step0 raw37062step0Labels raw37062step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5379 node5379Labels := by rfl

def raw37063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw37063Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37063step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw37063step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37063step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw37063step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37063 raw37063Labels = mixedMoment B node5379 node5379Labels := by
  calc
    mixedMoment B raw37063 raw37063Labels = mixedMoment B raw37063step0 raw37063step0Labels := by
      have ha : raw37063step0 = (fun i j => raw37063 (permutation159 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37063step0 raw37063; decide +kernel
      have hl : raw37063step0Labels = raw37063Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37063 raw37063Labels permutation159 permutation3
    mixedMoment B raw37063step0 raw37063step0Labels = mixedMoment B raw37063step1 raw37063step1Labels := by
      have ha : raw37063step1 = raw37063step0 := by apply Matrix.ext; unfold raw37063step1 raw37063step0; decide +kernel
      have hl : raw37063step0Labels = labelEmbedding6 ∘ raw37063step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37063step0 raw37063step0Labels raw37063step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5379 node5379Labels := by rfl

def raw37064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![0, -1, 1]]
def raw37064Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37064step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37064step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37064 raw37064Labels = mixedMoment B node5380 node5380Labels := by
  calc
    mixedMoment B raw37064 raw37064Labels = mixedMoment B raw37064step0 raw37064step0Labels := by
      have ha : raw37064step0 = (fun i j => raw37064 (permutation283 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37064step0 raw37064; decide +kernel
      have hl : raw37064step0Labels = raw37064Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37064 raw37064Labels permutation283 permutation2
    _ = mixedMoment B node5380 node5380Labels := by rfl

def raw37065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw37065Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37065step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw37065step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37065step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw37065step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37065 raw37065Labels = mixedMoment B node4675 node4675Labels := by
  calc
    mixedMoment B raw37065 raw37065Labels = mixedMoment B raw37065step0 raw37065step0Labels := by
      have ha : raw37065step0 = (fun i j => raw37065 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37065step0 raw37065; decide +kernel
      have hl : raw37065step0Labels = raw37065Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37065 raw37065Labels permutation152 permutation3
    mixedMoment B raw37065step0 raw37065step0Labels = mixedMoment B raw37065step1 raw37065step1Labels := by
      have ha : raw37065step1 = raw37065step0 := by apply Matrix.ext; unfold raw37065step1 raw37065step0; decide +kernel
      have hl : raw37065step0Labels = labelEmbedding6 ∘ raw37065step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37065step0 raw37065step0Labels raw37065step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4675 node4675Labels := by rfl

def raw37066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw37066Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37066step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw37066step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37066 raw37066Labels = mixedMoment B node4975 node4975Labels := by
  calc
    mixedMoment B raw37066 raw37066Labels = mixedMoment B raw37066step0 raw37066step0Labels := by
      have ha : raw37066step0 = (fun i j => raw37066 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37066step0 raw37066; decide +kernel
      have hl : raw37066step0Labels = raw37066Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37066 raw37066Labels permutation265 permutation2
    _ = mixedMoment B node4975 node4975Labels := by rfl

def raw37067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw37067Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37067step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw37067step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37067step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw37067step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37067 raw37067Labels = mixedMoment B node5243 node5243Labels := by
  calc
    mixedMoment B raw37067 raw37067Labels = mixedMoment B raw37067step0 raw37067step0Labels := by
      have ha : raw37067step0 = (fun i j => raw37067 (permutation662 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37067step0 raw37067; decide +kernel
      have hl : raw37067step0Labels = raw37067Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37067 raw37067Labels permutation662 permutation5
    mixedMoment B raw37067step0 raw37067step0Labels = mixedMoment B raw37067step1 raw37067step1Labels := by
      have ha : raw37067step1 = raw37067step0 := by apply Matrix.ext; unfold raw37067step1 raw37067step0; decide +kernel
      have hl : raw37067step0Labels = labelEmbedding8 ∘ raw37067step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37067step0 raw37067step0Labels raw37067step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5243 node5243Labels := by rfl

def raw37068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw37068Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37068step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw37068step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37068step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw37068step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37068 raw37068Labels = mixedMoment B node5243 node5243Labels := by
  calc
    mixedMoment B raw37068 raw37068Labels = mixedMoment B raw37068step0 raw37068step0Labels := by
      have ha : raw37068step0 = (fun i j => raw37068 (permutation644 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37068step0 raw37068; decide +kernel
      have hl : raw37068step0Labels = raw37068Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37068 raw37068Labels permutation644 permutation5
    mixedMoment B raw37068step0 raw37068step0Labels = mixedMoment B raw37068step1 raw37068step1Labels := by
      have ha : raw37068step1 = raw37068step0 := by apply Matrix.ext; unfold raw37068step1 raw37068step0; decide +kernel
      have hl : raw37068step0Labels = labelEmbedding8 ∘ raw37068step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37068step0 raw37068step0Labels raw37068step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5243 node5243Labels := by rfl

def raw37069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw37069Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37069step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw37069step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37069step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw37069step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37069 raw37069Labels = mixedMoment B node5243 node5243Labels := by
  calc
    mixedMoment B raw37069 raw37069Labels = mixedMoment B raw37069step0 raw37069step0Labels := by
      have ha : raw37069step0 = (fun i j => raw37069 (permutation638 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37069step0 raw37069; decide +kernel
      have hl : raw37069step0Labels = raw37069Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37069 raw37069Labels permutation638 permutation5
    mixedMoment B raw37069step0 raw37069step0Labels = mixedMoment B raw37069step1 raw37069step1Labels := by
      have ha : raw37069step1 = raw37069step0 := by apply Matrix.ext; unfold raw37069step1 raw37069step0; decide +kernel
      have hl : raw37069step0Labels = labelEmbedding8 ∘ raw37069step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37069step0 raw37069step0Labels raw37069step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5243 node5243Labels := by rfl

def raw37070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37070Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37070step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37070step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37070step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37070step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37070step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37070step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37070 raw37070Labels = mixedMoment B node3563 node3563Labels := by
  calc
    mixedMoment B raw37070 raw37070Labels = mixedMoment B raw37070step0 raw37070step0Labels := by
      have ha : raw37070step0 = (fun i j => raw37070 (permutation333 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37070step0 raw37070; decide +kernel
      have hl : raw37070step0Labels = raw37070Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37070 raw37070Labels permutation333 permutation7
    mixedMoment B raw37070step0 raw37070step0Labels = mixedMoment B raw37070step1 raw37070step1Labels := by
      have ha : raw37070step1 = -raw37070step0 := by apply Matrix.ext; change ∀ i j, raw37070step1 i j = -(raw37070step0 i j); unfold raw37070step1 raw37070step0; decide +kernel
      have hl : raw37070step1Labels = raw37070step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37070step1 raw37070step1Labels = mixedMoment B raw37070step2 raw37070step2Labels := by
      have ha : raw37070step2 = raw37070step1 := by apply Matrix.ext; unfold raw37070step2 raw37070step1; decide +kernel
      have hl : raw37070step1Labels = labelEmbedding1 ∘ raw37070step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37070step1 raw37070step1Labels raw37070step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3563 node3563Labels := by rfl

def raw37071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37071Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37071step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37071step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37071step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37071step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37071step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37071step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37071 raw37071Labels = mixedMoment B node3875 node3875Labels := by
  calc
    mixedMoment B raw37071 raw37071Labels = mixedMoment B raw37071step0 raw37071step0Labels := by
      have ha : raw37071step0 = (fun i j => raw37071 (permutation333 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37071step0 raw37071; decide +kernel
      have hl : raw37071step0Labels = raw37071Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37071 raw37071Labels permutation333 permutation7
    mixedMoment B raw37071step0 raw37071step0Labels = mixedMoment B raw37071step1 raw37071step1Labels := by
      have ha : raw37071step1 = -raw37071step0 := by apply Matrix.ext; change ∀ i j, raw37071step1 i j = -(raw37071step0 i j); unfold raw37071step1 raw37071step0; decide +kernel
      have hl : raw37071step1Labels = raw37071step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37071step1 raw37071step1Labels = mixedMoment B raw37071step2 raw37071step2Labels := by
      have ha : raw37071step2 = raw37071step1 := by apply Matrix.ext; unfold raw37071step2 raw37071step1; decide +kernel
      have hl : raw37071step1Labels = labelEmbedding1 ∘ raw37071step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37071step1 raw37071step1Labels raw37071step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3875 node3875Labels := by rfl

def raw37072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37072Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37072step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37072step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37072step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37072step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37072step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37072step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37072 raw37072Labels = mixedMoment B node3875 node3875Labels := by
  calc
    mixedMoment B raw37072 raw37072Labels = mixedMoment B raw37072step0 raw37072step0Labels := by
      have ha : raw37072step0 = (fun i j => raw37072 (permutation335 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37072step0 raw37072; decide +kernel
      have hl : raw37072step0Labels = raw37072Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37072 raw37072Labels permutation335 permutation7
    mixedMoment B raw37072step0 raw37072step0Labels = mixedMoment B raw37072step1 raw37072step1Labels := by
      have ha : raw37072step1 = -raw37072step0 := by apply Matrix.ext; change ∀ i j, raw37072step1 i j = -(raw37072step0 i j); unfold raw37072step1 raw37072step0; decide +kernel
      have hl : raw37072step1Labels = raw37072step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37072step1 raw37072step1Labels = mixedMoment B raw37072step2 raw37072step2Labels := by
      have ha : raw37072step2 = raw37072step1 := by apply Matrix.ext; unfold raw37072step2 raw37072step1; decide +kernel
      have hl : raw37072step1Labels = labelEmbedding1 ∘ raw37072step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37072step1 raw37072step1Labels raw37072step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3875 node3875Labels := by rfl

def raw37073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw37073Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37073step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37073step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37073step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37073step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37073step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37073step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37073 raw37073Labels = mixedMoment B node3875 node3875Labels := by
  calc
    mixedMoment B raw37073 raw37073Labels = mixedMoment B raw37073step0 raw37073step0Labels := by
      have ha : raw37073step0 = (fun i j => raw37073 (permutation337 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37073step0 raw37073; decide +kernel
      have hl : raw37073step0Labels = raw37073Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37073 raw37073Labels permutation337 permutation7
    mixedMoment B raw37073step0 raw37073step0Labels = mixedMoment B raw37073step1 raw37073step1Labels := by
      have ha : raw37073step1 = -raw37073step0 := by apply Matrix.ext; change ∀ i j, raw37073step1 i j = -(raw37073step0 i j); unfold raw37073step1 raw37073step0; decide +kernel
      have hl : raw37073step1Labels = raw37073step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37073step1 raw37073step1Labels = mixedMoment B raw37073step2 raw37073step2Labels := by
      have ha : raw37073step2 = raw37073step1 := by apply Matrix.ext; unfold raw37073step2 raw37073step1; decide +kernel
      have hl : raw37073step1Labels = labelEmbedding1 ∘ raw37073step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37073step1 raw37073step1Labels raw37073step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3875 node3875Labels := by rfl

def raw37074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw37074Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37074step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37074step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37074step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37074step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37074step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37074step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37074 raw37074Labels = mixedMoment B node3844 node3844Labels := by
  calc
    mixedMoment B raw37074 raw37074Labels = mixedMoment B raw37074step0 raw37074step0Labels := by
      have ha : raw37074step0 = (fun i j => raw37074 (permutation333 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37074step0 raw37074; decide +kernel
      have hl : raw37074step0Labels = raw37074Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37074 raw37074Labels permutation333 permutation7
    mixedMoment B raw37074step0 raw37074step0Labels = mixedMoment B raw37074step1 raw37074step1Labels := by
      have ha : raw37074step1 = -raw37074step0 := by apply Matrix.ext; change ∀ i j, raw37074step1 i j = -(raw37074step0 i j); unfold raw37074step1 raw37074step0; decide +kernel
      have hl : raw37074step1Labels = raw37074step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37074step1 raw37074step1Labels = mixedMoment B raw37074step2 raw37074step2Labels := by
      have ha : raw37074step2 = raw37074step1 := by apply Matrix.ext; unfold raw37074step2 raw37074step1; decide +kernel
      have hl : raw37074step1Labels = labelEmbedding1 ∘ raw37074step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37074step1 raw37074step1Labels raw37074step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3844 node3844Labels := by rfl

def raw37075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37075Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37075step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw37075step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37075step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw37075step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37075step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw37075step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37075 raw37075Labels = mixedMoment B node2232 node2232Labels := by
  calc
    mixedMoment B raw37075 raw37075Labels = mixedMoment B raw37075step0 raw37075step0Labels := by
      have ha : raw37075step0 = (fun i j => raw37075 (permutation184 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37075step0 raw37075; decide +kernel
      have hl : raw37075step0Labels = raw37075Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37075 raw37075Labels permutation184 permutation5
    mixedMoment B raw37075step0 raw37075step0Labels = mixedMoment B raw37075step1 raw37075step1Labels := by
      have ha : raw37075step1 = -raw37075step0 := by apply Matrix.ext; change ∀ i j, raw37075step1 i j = -(raw37075step0 i j); unfold raw37075step1 raw37075step0; decide +kernel
      have hl : raw37075step1Labels = raw37075step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37075step1 raw37075step1Labels = mixedMoment B raw37075step2 raw37075step2Labels := by
      have ha : raw37075step2 = raw37075step1 := by apply Matrix.ext; unfold raw37075step2 raw37075step1; decide +kernel
      have hl : raw37075step1Labels = labelEmbedding1 ∘ raw37075step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37075step1 raw37075step1Labels raw37075step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2232 node2232Labels := by rfl

def raw37076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37076Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37076step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw37076step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37076step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw37076step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37076step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw37076step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37076 raw37076Labels = mixedMoment B node3846 node3846Labels := by
  calc
    mixedMoment B raw37076 raw37076Labels = mixedMoment B raw37076step0 raw37076step0Labels := by
      have ha : raw37076step0 = (fun i j => raw37076 (permutation184 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37076step0 raw37076; decide +kernel
      have hl : raw37076step0Labels = raw37076Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37076 raw37076Labels permutation184 permutation5
    mixedMoment B raw37076step0 raw37076step0Labels = mixedMoment B raw37076step1 raw37076step1Labels := by
      have ha : raw37076step1 = -raw37076step0 := by apply Matrix.ext; change ∀ i j, raw37076step1 i j = -(raw37076step0 i j); unfold raw37076step1 raw37076step0; decide +kernel
      have hl : raw37076step1Labels = raw37076step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37076step1 raw37076step1Labels = mixedMoment B raw37076step2 raw37076step2Labels := by
      have ha : raw37076step2 = raw37076step1 := by apply Matrix.ext; unfold raw37076step2 raw37076step1; decide +kernel
      have hl : raw37076step1Labels = labelEmbedding1 ∘ raw37076step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37076step1 raw37076step1Labels raw37076step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3846 node3846Labels := by rfl

def raw37077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37077Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37077step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw37077step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37077step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw37077step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37077step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw37077step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37077 raw37077Labels = mixedMoment B node3846 node3846Labels := by
  calc
    mixedMoment B raw37077 raw37077Labels = mixedMoment B raw37077step0 raw37077step0Labels := by
      have ha : raw37077step0 = (fun i j => raw37077 (permutation208 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37077step0 raw37077; decide +kernel
      have hl : raw37077step0Labels = raw37077Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37077 raw37077Labels permutation208 permutation5
    mixedMoment B raw37077step0 raw37077step0Labels = mixedMoment B raw37077step1 raw37077step1Labels := by
      have ha : raw37077step1 = -raw37077step0 := by apply Matrix.ext; change ∀ i j, raw37077step1 i j = -(raw37077step0 i j); unfold raw37077step1 raw37077step0; decide +kernel
      have hl : raw37077step1Labels = raw37077step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37077step1 raw37077step1Labels = mixedMoment B raw37077step2 raw37077step2Labels := by
      have ha : raw37077step2 = raw37077step1 := by apply Matrix.ext; unfold raw37077step2 raw37077step1; decide +kernel
      have hl : raw37077step1Labels = labelEmbedding1 ∘ raw37077step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37077step1 raw37077step1Labels raw37077step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3846 node3846Labels := by rfl

def raw37078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw37078Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37078step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw37078step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37078step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw37078step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37078step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw37078step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37078 raw37078Labels = mixedMoment B node3846 node3846Labels := by
  calc
    mixedMoment B raw37078 raw37078Labels = mixedMoment B raw37078step0 raw37078step0Labels := by
      have ha : raw37078step0 = (fun i j => raw37078 (permutation232 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37078step0 raw37078; decide +kernel
      have hl : raw37078step0Labels = raw37078Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37078 raw37078Labels permutation232 permutation5
    mixedMoment B raw37078step0 raw37078step0Labels = mixedMoment B raw37078step1 raw37078step1Labels := by
      have ha : raw37078step1 = -raw37078step0 := by apply Matrix.ext; change ∀ i j, raw37078step1 i j = -(raw37078step0 i j); unfold raw37078step1 raw37078step0; decide +kernel
      have hl : raw37078step1Labels = raw37078step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37078step1 raw37078step1Labels = mixedMoment B raw37078step2 raw37078step2Labels := by
      have ha : raw37078step2 = raw37078step1 := by apply Matrix.ext; unfold raw37078step2 raw37078step1; decide +kernel
      have hl : raw37078step1Labels = labelEmbedding1 ∘ raw37078step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37078step1 raw37078step1Labels raw37078step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3846 node3846Labels := by rfl

def raw37079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw37079Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37079step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0]]
def raw37079step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37079step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0]]
def raw37079step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37079step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0]]
def raw37079step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37079 raw37079Labels = mixedMoment B node3909 node3909Labels := by
  calc
    mixedMoment B raw37079 raw37079Labels = mixedMoment B raw37079step0 raw37079step0Labels := by
      have ha : raw37079step0 = (fun i j => raw37079 (permutation184 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37079step0 raw37079; decide +kernel
      have hl : raw37079step0Labels = raw37079Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37079 raw37079Labels permutation184 permutation5
    mixedMoment B raw37079step0 raw37079step0Labels = mixedMoment B raw37079step1 raw37079step1Labels := by
      have ha : raw37079step1 = -raw37079step0 := by apply Matrix.ext; change ∀ i j, raw37079step1 i j = -(raw37079step0 i j); unfold raw37079step1 raw37079step0; decide +kernel
      have hl : raw37079step1Labels = raw37079step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37079step1 raw37079step1Labels = mixedMoment B raw37079step2 raw37079step2Labels := by
      have ha : raw37079step2 = raw37079step1 := by apply Matrix.ext; unfold raw37079step2 raw37079step1; decide +kernel
      have hl : raw37079step1Labels = labelEmbedding1 ∘ raw37079step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37079step1 raw37079step1Labels raw37079step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3909 node3909Labels := by rfl

def raw37080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37080Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37080step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw37080step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37080step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37080step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37080step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37080step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37080 raw37080Labels = mixedMoment B node2142 node2142Labels := by
  calc
    mixedMoment B raw37080 raw37080Labels = mixedMoment B raw37080step0 raw37080step0Labels := by
      have ha : raw37080step0 = (fun i j => raw37080 (permutation160 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37080step0 raw37080; decide +kernel
      have hl : raw37080step0Labels = raw37080Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37080 raw37080Labels permutation160 permutation5
    mixedMoment B raw37080step0 raw37080step0Labels = mixedMoment B raw37080step1 raw37080step1Labels := by
      have ha : raw37080step1 = -raw37080step0 := by apply Matrix.ext; change ∀ i j, raw37080step1 i j = -(raw37080step0 i j); unfold raw37080step1 raw37080step0; decide +kernel
      have hl : raw37080step1Labels = raw37080step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37080step1 raw37080step1Labels = mixedMoment B raw37080step2 raw37080step2Labels := by
      have ha : raw37080step2 = raw37080step1 := by apply Matrix.ext; unfold raw37080step2 raw37080step1; decide +kernel
      have hl : raw37080step1Labels = labelEmbedding1 ∘ raw37080step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37080step1 raw37080step1Labels raw37080step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2142 node2142Labels := by rfl

def raw37081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37081Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37081step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37081step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37081step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37081step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37081step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37081step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37081 raw37081Labels = mixedMoment B node3554 node3554Labels := by
  calc
    mixedMoment B raw37081 raw37081Labels = mixedMoment B raw37081step0 raw37081step0Labels := by
      have ha : raw37081step0 = (fun i j => raw37081 (permutation336 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37081step0 raw37081; decide +kernel
      have hl : raw37081step0Labels = raw37081Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37081 raw37081Labels permutation336 permutation7
    mixedMoment B raw37081step0 raw37081step0Labels = mixedMoment B raw37081step1 raw37081step1Labels := by
      have ha : raw37081step1 = -raw37081step0 := by apply Matrix.ext; change ∀ i j, raw37081step1 i j = -(raw37081step0 i j); unfold raw37081step1 raw37081step0; decide +kernel
      have hl : raw37081step1Labels = raw37081step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37081step1 raw37081step1Labels = mixedMoment B raw37081step2 raw37081step2Labels := by
      have ha : raw37081step2 = raw37081step1 := by apply Matrix.ext; unfold raw37081step2 raw37081step1; decide +kernel
      have hl : raw37081step1Labels = labelEmbedding1 ∘ raw37081step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37081step1 raw37081step1Labels raw37081step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3554 node3554Labels := by rfl

def raw37082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37082Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37082step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw37082step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37082step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37082step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37082step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37082step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37082 raw37082Labels = mixedMoment B node3832 node3832Labels := by
  calc
    mixedMoment B raw37082 raw37082Labels = mixedMoment B raw37082step0 raw37082step0Labels := by
      have ha : raw37082step0 = (fun i j => raw37082 (permutation202 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37082step0 raw37082; decide +kernel
      have hl : raw37082step0Labels = raw37082Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37082 raw37082Labels permutation202 permutation5
    mixedMoment B raw37082step0 raw37082step0Labels = mixedMoment B raw37082step1 raw37082step1Labels := by
      have ha : raw37082step1 = -raw37082step0 := by apply Matrix.ext; change ∀ i j, raw37082step1 i j = -(raw37082step0 i j); unfold raw37082step1 raw37082step0; decide +kernel
      have hl : raw37082step1Labels = raw37082step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37082step1 raw37082step1Labels = mixedMoment B raw37082step2 raw37082step2Labels := by
      have ha : raw37082step2 = raw37082step1 := by apply Matrix.ext; unfold raw37082step2 raw37082step1; decide +kernel
      have hl : raw37082step1Labels = labelEmbedding1 ∘ raw37082step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37082step1 raw37082step1Labels raw37082step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3832 node3832Labels := by rfl

def raw37083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1]]
def raw37083Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37083step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw37083step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37083step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37083step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37083step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37083step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37083 raw37083Labels = mixedMoment B node3832 node3832Labels := by
  calc
    mixedMoment B raw37083 raw37083Labels = mixedMoment B raw37083step0 raw37083step0Labels := by
      have ha : raw37083step0 = (fun i j => raw37083 (permutation226 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37083step0 raw37083; decide +kernel
      have hl : raw37083step0Labels = raw37083Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37083 raw37083Labels permutation226 permutation5
    mixedMoment B raw37083step0 raw37083step0Labels = mixedMoment B raw37083step1 raw37083step1Labels := by
      have ha : raw37083step1 = -raw37083step0 := by apply Matrix.ext; change ∀ i j, raw37083step1 i j = -(raw37083step0 i j); unfold raw37083step1 raw37083step0; decide +kernel
      have hl : raw37083step1Labels = raw37083step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37083step1 raw37083step1Labels = mixedMoment B raw37083step2 raw37083step2Labels := by
      have ha : raw37083step2 = raw37083step1 := by apply Matrix.ext; unfold raw37083step2 raw37083step1; decide +kernel
      have hl : raw37083step1Labels = labelEmbedding1 ∘ raw37083step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37083step1 raw37083step1Labels raw37083step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3832 node3832Labels := by rfl

def raw37084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1]]
def raw37084Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37084step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37084step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37084step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37084step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37084step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37084step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37084 raw37084Labels = mixedMoment B node3836 node3836Labels := by
  calc
    mixedMoment B raw37084 raw37084Labels = mixedMoment B raw37084step0 raw37084step0Labels := by
      have ha : raw37084step0 = (fun i j => raw37084 (permutation336 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37084step0 raw37084; decide +kernel
      have hl : raw37084step0Labels = raw37084Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37084 raw37084Labels permutation336 permutation7
    mixedMoment B raw37084step0 raw37084step0Labels = mixedMoment B raw37084step1 raw37084step1Labels := by
      have ha : raw37084step1 = -raw37084step0 := by apply Matrix.ext; change ∀ i j, raw37084step1 i j = -(raw37084step0 i j); unfold raw37084step1 raw37084step0; decide +kernel
      have hl : raw37084step1Labels = raw37084step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37084step1 raw37084step1Labels = mixedMoment B raw37084step2 raw37084step2Labels := by
      have ha : raw37084step2 = raw37084step1 := by apply Matrix.ext; unfold raw37084step2 raw37084step1; decide +kernel
      have hl : raw37084step1Labels = labelEmbedding1 ∘ raw37084step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37084step1 raw37084step1Labels raw37084step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3836 node3836Labels := by rfl

def raw37085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37085Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37085step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw37085step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37085step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37085step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37085step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37085step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37085 raw37085Labels = mixedMoment B node2142 node2142Labels := by
  calc
    mixedMoment B raw37085 raw37085Labels = mixedMoment B raw37085step0 raw37085step0Labels := by
      have ha : raw37085step0 = (fun i j => raw37085 (permutation154 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37085step0 raw37085; decide +kernel
      have hl : raw37085step0Labels = raw37085Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37085 raw37085Labels permutation154 permutation5
    mixedMoment B raw37085step0 raw37085step0Labels = mixedMoment B raw37085step1 raw37085step1Labels := by
      have ha : raw37085step1 = -raw37085step0 := by apply Matrix.ext; change ∀ i j, raw37085step1 i j = -(raw37085step0 i j); unfold raw37085step1 raw37085step0; decide +kernel
      have hl : raw37085step1Labels = raw37085step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37085step1 raw37085step1Labels = mixedMoment B raw37085step2 raw37085step2Labels := by
      have ha : raw37085step2 = raw37085step1 := by apply Matrix.ext; unfold raw37085step2 raw37085step1; decide +kernel
      have hl : raw37085step1Labels = labelEmbedding1 ∘ raw37085step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37085step1 raw37085step1Labels raw37085step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2142 node2142Labels := by rfl

def raw37086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37086Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37086step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37086step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37086step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37086step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37086step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37086step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37086 raw37086Labels = mixedMoment B node3554 node3554Labels := by
  calc
    mixedMoment B raw37086 raw37086Labels = mixedMoment B raw37086step0 raw37086step0Labels := by
      have ha : raw37086step0 = (fun i j => raw37086 (permutation334 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37086step0 raw37086; decide +kernel
      have hl : raw37086step0Labels = raw37086Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37086 raw37086Labels permutation334 permutation7
    mixedMoment B raw37086step0 raw37086step0Labels = mixedMoment B raw37086step1 raw37086step1Labels := by
      have ha : raw37086step1 = -raw37086step0 := by apply Matrix.ext; change ∀ i j, raw37086step1 i j = -(raw37086step0 i j); unfold raw37086step1 raw37086step0; decide +kernel
      have hl : raw37086step1Labels = raw37086step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37086step1 raw37086step1Labels = mixedMoment B raw37086step2 raw37086step2Labels := by
      have ha : raw37086step2 = raw37086step1 := by apply Matrix.ext; unfold raw37086step2 raw37086step1; decide +kernel
      have hl : raw37086step1Labels = labelEmbedding1 ∘ raw37086step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37086step1 raw37086step1Labels raw37086step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3554 node3554Labels := by rfl

def raw37087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw37087Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37087step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw37087step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37087step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37087step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37087step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37087step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37087 raw37087Labels = mixedMoment B node3832 node3832Labels := by
  calc
    mixedMoment B raw37087 raw37087Labels = mixedMoment B raw37087step0 raw37087step0Labels := by
      have ha : raw37087step0 = (fun i j => raw37087 (permutation178 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37087step0 raw37087; decide +kernel
      have hl : raw37087step0Labels = raw37087Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37087 raw37087Labels permutation178 permutation5
    mixedMoment B raw37087step0 raw37087step0Labels = mixedMoment B raw37087step1 raw37087step1Labels := by
      have ha : raw37087step1 = -raw37087step0 := by apply Matrix.ext; change ∀ i j, raw37087step1 i j = -(raw37087step0 i j); unfold raw37087step1 raw37087step0; decide +kernel
      have hl : raw37087step1Labels = raw37087step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37087step1 raw37087step1Labels = mixedMoment B raw37087step2 raw37087step2Labels := by
      have ha : raw37087step2 = raw37087step1 := by apply Matrix.ext; unfold raw37087step2 raw37087step1; decide +kernel
      have hl : raw37087step1Labels = labelEmbedding1 ∘ raw37087step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37087step1 raw37087step1Labels raw37087step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3832 node3832Labels := by rfl

def raw37088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1], ![1, -2, 1]]
def raw37088Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37088step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw37088step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37088step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37088step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37088step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37088step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37088 raw37088Labels = mixedMoment B node3832 node3832Labels := by
  calc
    mixedMoment B raw37088 raw37088Labels = mixedMoment B raw37088step0 raw37088step0Labels := by
      have ha : raw37088step0 = (fun i j => raw37088 (permutation224 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37088step0 raw37088; decide +kernel
      have hl : raw37088step0Labels = raw37088Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37088 raw37088Labels permutation224 permutation5
    mixedMoment B raw37088step0 raw37088step0Labels = mixedMoment B raw37088step1 raw37088step1Labels := by
      have ha : raw37088step1 = -raw37088step0 := by apply Matrix.ext; change ∀ i j, raw37088step1 i j = -(raw37088step0 i j); unfold raw37088step1 raw37088step0; decide +kernel
      have hl : raw37088step1Labels = raw37088step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37088step1 raw37088step1Labels = mixedMoment B raw37088step2 raw37088step2Labels := by
      have ha : raw37088step2 = raw37088step1 := by apply Matrix.ext; unfold raw37088step2 raw37088step1; decide +kernel
      have hl : raw37088step1Labels = labelEmbedding1 ∘ raw37088step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37088step1 raw37088step1Labels raw37088step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3832 node3832Labels := by rfl

def raw37089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![0, -1, 1]]
def raw37089Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37089step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37089step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37089step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37089step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37089step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37089step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37089 raw37089Labels = mixedMoment B node3836 node3836Labels := by
  calc
    mixedMoment B raw37089 raw37089Labels = mixedMoment B raw37089step0 raw37089step0Labels := by
      have ha : raw37089step0 = (fun i j => raw37089 (permutation334 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37089step0 raw37089; decide +kernel
      have hl : raw37089step0Labels = raw37089Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37089 raw37089Labels permutation334 permutation7
    mixedMoment B raw37089step0 raw37089step0Labels = mixedMoment B raw37089step1 raw37089step1Labels := by
      have ha : raw37089step1 = -raw37089step0 := by apply Matrix.ext; change ∀ i j, raw37089step1 i j = -(raw37089step0 i j); unfold raw37089step1 raw37089step0; decide +kernel
      have hl : raw37089step1Labels = raw37089step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37089step1 raw37089step1Labels = mixedMoment B raw37089step2 raw37089step2Labels := by
      have ha : raw37089step2 = raw37089step1 := by apply Matrix.ext; unfold raw37089step2 raw37089step1; decide +kernel
      have hl : raw37089step1Labels = labelEmbedding1 ∘ raw37089step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37089step1 raw37089step1Labels raw37089step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3836 node3836Labels := by rfl

def raw37090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw37090Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37090step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw37090step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37090step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37090step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37090step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37090step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37090 raw37090Labels = mixedMoment B node2142 node2142Labels := by
  calc
    mixedMoment B raw37090 raw37090Labels = mixedMoment B raw37090step0 raw37090step0Labels := by
      have ha : raw37090step0 = (fun i j => raw37090 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37090step0 raw37090; decide +kernel
      have hl : raw37090step0Labels = raw37090Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37090 raw37090Labels permutation152 permutation5
    mixedMoment B raw37090step0 raw37090step0Labels = mixedMoment B raw37090step1 raw37090step1Labels := by
      have ha : raw37090step1 = -raw37090step0 := by apply Matrix.ext; change ∀ i j, raw37090step1 i j = -(raw37090step0 i j); unfold raw37090step1 raw37090step0; decide +kernel
      have hl : raw37090step1Labels = raw37090step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37090step1 raw37090step1Labels = mixedMoment B raw37090step2 raw37090step2Labels := by
      have ha : raw37090step2 = raw37090step1 := by apply Matrix.ext; unfold raw37090step2 raw37090step1; decide +kernel
      have hl : raw37090step1Labels = labelEmbedding1 ∘ raw37090step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37090step1 raw37090step1Labels raw37090step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2142 node2142Labels := by rfl

def raw37091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw37091Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37091step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37091step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37091step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37091step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37091step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37091step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37091 raw37091Labels = mixedMoment B node3554 node3554Labels := by
  calc
    mixedMoment B raw37091 raw37091Labels = mixedMoment B raw37091step0 raw37091step0Labels := by
      have ha : raw37091step0 = (fun i j => raw37091 (permutation333 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37091step0 raw37091; decide +kernel
      have hl : raw37091step0Labels = raw37091Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37091 raw37091Labels permutation333 permutation7
    mixedMoment B raw37091step0 raw37091step0Labels = mixedMoment B raw37091step1 raw37091step1Labels := by
      have ha : raw37091step1 = -raw37091step0 := by apply Matrix.ext; change ∀ i j, raw37091step1 i j = -(raw37091step0 i j); unfold raw37091step1 raw37091step0; decide +kernel
      have hl : raw37091step1Labels = raw37091step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37091step1 raw37091step1Labels = mixedMoment B raw37091step2 raw37091step2Labels := by
      have ha : raw37091step2 = raw37091step1 := by apply Matrix.ext; unfold raw37091step2 raw37091step1; decide +kernel
      have hl : raw37091step1Labels = labelEmbedding1 ∘ raw37091step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37091step1 raw37091step1Labels raw37091step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3554 node3554Labels := by rfl

def raw37092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw37092Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37092step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw37092step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37092step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37092step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37092step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37092step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37092 raw37092Labels = mixedMoment B node3832 node3832Labels := by
  calc
    mixedMoment B raw37092 raw37092Labels = mixedMoment B raw37092step0 raw37092step0Labels := by
      have ha : raw37092step0 = (fun i j => raw37092 (permutation176 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37092step0 raw37092; decide +kernel
      have hl : raw37092step0Labels = raw37092Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37092 raw37092Labels permutation176 permutation5
    mixedMoment B raw37092step0 raw37092step0Labels = mixedMoment B raw37092step1 raw37092step1Labels := by
      have ha : raw37092step1 = -raw37092step0 := by apply Matrix.ext; change ∀ i j, raw37092step1 i j = -(raw37092step0 i j); unfold raw37092step1 raw37092step0; decide +kernel
      have hl : raw37092step1Labels = raw37092step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37092step1 raw37092step1Labels = mixedMoment B raw37092step2 raw37092step2Labels := by
      have ha : raw37092step2 = raw37092step1 := by apply Matrix.ext; unfold raw37092step2 raw37092step1; decide +kernel
      have hl : raw37092step1Labels = labelEmbedding1 ∘ raw37092step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37092step1 raw37092step1Labels raw37092step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3832 node3832Labels := by rfl

def raw37093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1], ![1, -2, 1]]
def raw37093Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37093step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw37093step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37093step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37093step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37093step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37093step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37093 raw37093Labels = mixedMoment B node3832 node3832Labels := by
  calc
    mixedMoment B raw37093 raw37093Labels = mixedMoment B raw37093step0 raw37093step0Labels := by
      have ha : raw37093step0 = (fun i j => raw37093 (permutation200 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37093step0 raw37093; decide +kernel
      have hl : raw37093step0Labels = raw37093Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37093 raw37093Labels permutation200 permutation5
    mixedMoment B raw37093step0 raw37093step0Labels = mixedMoment B raw37093step1 raw37093step1Labels := by
      have ha : raw37093step1 = -raw37093step0 := by apply Matrix.ext; change ∀ i j, raw37093step1 i j = -(raw37093step0 i j); unfold raw37093step1 raw37093step0; decide +kernel
      have hl : raw37093step1Labels = raw37093step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37093step1 raw37093step1Labels = mixedMoment B raw37093step2 raw37093step2Labels := by
      have ha : raw37093step2 = raw37093step1 := by apply Matrix.ext; unfold raw37093step2 raw37093step1; decide +kernel
      have hl : raw37093step1Labels = labelEmbedding1 ∘ raw37093step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37093step1 raw37093step1Labels raw37093step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3832 node3832Labels := by rfl

def raw37094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![0, -1, 1]]
def raw37094Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37094step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37094step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37094step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37094step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37094step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37094step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37094 raw37094Labels = mixedMoment B node3836 node3836Labels := by
  calc
    mixedMoment B raw37094 raw37094Labels = mixedMoment B raw37094step0 raw37094step0Labels := by
      have ha : raw37094step0 = (fun i j => raw37094 (permutation333 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37094step0 raw37094; decide +kernel
      have hl : raw37094step0Labels = raw37094Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37094 raw37094Labels permutation333 permutation7
    mixedMoment B raw37094step0 raw37094step0Labels = mixedMoment B raw37094step1 raw37094step1Labels := by
      have ha : raw37094step1 = -raw37094step0 := by apply Matrix.ext; change ∀ i j, raw37094step1 i j = -(raw37094step0 i j); unfold raw37094step1 raw37094step0; decide +kernel
      have hl : raw37094step1Labels = raw37094step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37094step1 raw37094step1Labels = mixedMoment B raw37094step2 raw37094step2Labels := by
      have ha : raw37094step2 = raw37094step1 := by apply Matrix.ext; unfold raw37094step2 raw37094step1; decide +kernel
      have hl : raw37094step1Labels = labelEmbedding1 ∘ raw37094step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37094step1 raw37094step1Labels raw37094step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3836 node3836Labels := by rfl

def raw37095 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw37095Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37095step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw37095step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37095step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw37095step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37095step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw37095step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37095 raw37095Labels = mixedMoment B node2139 node2139Labels := by
  calc
    mixedMoment B raw37095 raw37095Labels = mixedMoment B raw37095step0 raw37095step0Labels := by
      have ha : raw37095step0 = (fun i j => raw37095 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37095step0 raw37095; decide +kernel
      have hl : raw37095step0Labels = raw37095Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37095 raw37095Labels permutation152 permutation5
    mixedMoment B raw37095step0 raw37095step0Labels = mixedMoment B raw37095step1 raw37095step1Labels := by
      have ha : raw37095step1 = -raw37095step0 := by apply Matrix.ext; change ∀ i j, raw37095step1 i j = -(raw37095step0 i j); unfold raw37095step1 raw37095step0; decide +kernel
      have hl : raw37095step1Labels = raw37095step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37095step1 raw37095step1Labels = mixedMoment B raw37095step2 raw37095step2Labels := by
      have ha : raw37095step2 = raw37095step1 := by apply Matrix.ext; unfold raw37095step2 raw37095step1; decide +kernel
      have hl : raw37095step1Labels = labelEmbedding1 ∘ raw37095step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37095step1 raw37095step1Labels raw37095step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2139 node2139Labels := by rfl

def raw37096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw37096Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37096step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw37096step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37096step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw37096step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37096 raw37096Labels = mixedMoment B node2690 node2690Labels := by
  calc
    mixedMoment B raw37096 raw37096Labels = mixedMoment B raw37096step0 raw37096step0Labels := by
      have ha : raw37096step0 = (fun i j => raw37096 (permutation640 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37096step0 raw37096; decide +kernel
      have hl : raw37096step0Labels = raw37096Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37096 raw37096Labels permutation640 permutation5
    mixedMoment B raw37096step0 raw37096step0Labels = mixedMoment B raw37096step1 raw37096step1Labels := by
      have ha : raw37096step1 = raw37096step0 := by apply Matrix.ext; unfold raw37096step1 raw37096step0; decide +kernel
      have hl : raw37096step0Labels = labelEmbedding1 ∘ raw37096step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37096step0 raw37096step0Labels raw37096step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2690 node2690Labels := by rfl

def raw37097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw37097Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37097step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw37097step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37097step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw37097step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37097 raw37097Labels = mixedMoment B node2697 node2697Labels := by
  calc
    mixedMoment B raw37097 raw37097Labels = mixedMoment B raw37097step0 raw37097step0Labels := by
      have ha : raw37097step0 = (fun i j => raw37097 (permutation662 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37097step0 raw37097; decide +kernel
      have hl : raw37097step0Labels = raw37097Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37097 raw37097Labels permutation662 permutation5
    mixedMoment B raw37097step0 raw37097step0Labels = mixedMoment B raw37097step1 raw37097step1Labels := by
      have ha : raw37097step1 = raw37097step0 := by apply Matrix.ext; unfold raw37097step1 raw37097step0; decide +kernel
      have hl : raw37097step0Labels = labelEmbedding1 ∘ raw37097step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37097step0 raw37097step0Labels raw37097step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2697 node2697Labels := by rfl

def raw37098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw37098Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37098step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw37098step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37098step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw37098step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37098 raw37098Labels = mixedMoment B node2697 node2697Labels := by
  calc
    mixedMoment B raw37098 raw37098Labels = mixedMoment B raw37098step0 raw37098step0Labels := by
      have ha : raw37098step0 = (fun i j => raw37098 (permutation644 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37098step0 raw37098; decide +kernel
      have hl : raw37098step0Labels = raw37098Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37098 raw37098Labels permutation644 permutation5
    mixedMoment B raw37098step0 raw37098step0Labels = mixedMoment B raw37098step1 raw37098step1Labels := by
      have ha : raw37098step1 = raw37098step0 := by apply Matrix.ext; unfold raw37098step1 raw37098step0; decide +kernel
      have hl : raw37098step0Labels = labelEmbedding1 ∘ raw37098step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37098step0 raw37098step0Labels raw37098step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2697 node2697Labels := by rfl

def raw37099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw37099Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37099step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw37099step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37099step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw37099step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37099 raw37099Labels = mixedMoment B node2697 node2697Labels := by
  calc
    mixedMoment B raw37099 raw37099Labels = mixedMoment B raw37099step0 raw37099step0Labels := by
      have ha : raw37099step0 = (fun i j => raw37099 (permutation638 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37099step0 raw37099; decide +kernel
      have hl : raw37099step0Labels = raw37099Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37099 raw37099Labels permutation638 permutation5
    mixedMoment B raw37099step0 raw37099step0Labels = mixedMoment B raw37099step1 raw37099step1Labels := by
      have ha : raw37099step1 = raw37099step0 := by apply Matrix.ext; unfold raw37099step1 raw37099step0; decide +kernel
      have hl : raw37099step0Labels = labelEmbedding1 ∘ raw37099step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37099step0 raw37099step0Labels raw37099step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2697 node2697Labels := by rfl

def raw37100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 3, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37100Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37100step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37100step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37100step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37100step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37100 raw37100Labels = mixedMoment B node4864 node4864Labels := by
  calc
    mixedMoment B raw37100 raw37100Labels = mixedMoment B raw37100step0 raw37100step0Labels := by
      have ha : raw37100step0 = (fun i j => raw37100 (permutation281 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37100step0 raw37100; decide +kernel
      have hl : raw37100step0Labels = raw37100Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37100 raw37100Labels permutation281 permutation3
    mixedMoment B raw37100step0 raw37100step0Labels = mixedMoment B raw37100step1 raw37100step1Labels := by
      have ha : raw37100step1 = raw37100step0 := by apply Matrix.ext; unfold raw37100step1 raw37100step0; decide +kernel
      have hl : raw37100step0Labels = labelEmbedding6 ∘ raw37100step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37100step0 raw37100step0Labels raw37100step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4864 node4864Labels := by rfl

def raw37101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37101Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37101step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37101step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37101step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37101step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37101step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37101 raw37101Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw37101 raw37101Labels = mixedMoment B raw37101step0 raw37101step0Labels := by
      have hz : ∀ j, raw37101 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37101step0 = (fun i j => raw37101 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37101step0 raw37101; decide +kernel
      have hl : raw37101step0Labels = raw37101Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37101 raw37101Labels permutation434 hz
    mixedMoment B raw37101step0 raw37101step0Labels = mixedMoment B raw37101step1 raw37101step1Labels := by
      have ha : raw37101step1 = (fun i j => raw37101step0 (permutation59 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37101step1 raw37101step0; decide +kernel
      have hl : raw37101step1Labels = raw37101step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37101step0 raw37101step0Labels permutation59 permutation3
    mixedMoment B raw37101step1 raw37101step1Labels = mixedMoment B raw37101step2 raw37101step2Labels := by
      have ha : raw37101step2 = raw37101step1 := by apply Matrix.ext; unfold raw37101step2 raw37101step1; decide +kernel
      have hl : raw37101step1Labels = labelEmbedding6 ∘ raw37101step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37101step1 raw37101step1Labels raw37101step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw37102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw37102Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37102step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37102step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37102step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37102step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37102step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37102step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37102 raw37102Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw37102 raw37102Labels = mixedMoment B raw37102step0 raw37102step0Labels := by
      have ha : raw37102step0 = (fun i j => raw37102 (permutation329 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37102step0 raw37102; decide +kernel
      have hl : raw37102step0Labels = raw37102Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37102 raw37102Labels permutation329 permutation5
    mixedMoment B raw37102step0 raw37102step0Labels = mixedMoment B raw37102step1 raw37102step1Labels := by
      have ha : raw37102step1 = -raw37102step0 := by apply Matrix.ext; change ∀ i j, raw37102step1 i j = -(raw37102step0 i j); unfold raw37102step1 raw37102step0; decide +kernel
      have hl : raw37102step1Labels = raw37102step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37102step1 raw37102step1Labels = mixedMoment B raw37102step2 raw37102step2Labels := by
      have ha : raw37102step2 = raw37102step1 := by apply Matrix.ext; unfold raw37102step2 raw37102step1; decide +kernel
      have hl : raw37102step1Labels = labelEmbedding8 ∘ raw37102step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37102step1 raw37102step1Labels raw37102step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

def raw37103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw37103Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37103step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37103step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37103step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37103step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37103step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37103step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37103 raw37103Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw37103 raw37103Labels = mixedMoment B raw37103step0 raw37103step0Labels := by
      have ha : raw37103step0 = (fun i j => raw37103 (permutation344 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37103step0 raw37103; decide +kernel
      have hl : raw37103step0Labels = raw37103Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37103 raw37103Labels permutation344 permutation5
    mixedMoment B raw37103step0 raw37103step0Labels = mixedMoment B raw37103step1 raw37103step1Labels := by
      have ha : raw37103step1 = -raw37103step0 := by apply Matrix.ext; change ∀ i j, raw37103step1 i j = -(raw37103step0 i j); unfold raw37103step1 raw37103step0; decide +kernel
      have hl : raw37103step1Labels = raw37103step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37103step1 raw37103step1Labels = mixedMoment B raw37103step2 raw37103step2Labels := by
      have ha : raw37103step2 = raw37103step1 := by apply Matrix.ext; unfold raw37103step2 raw37103step1; decide +kernel
      have hl : raw37103step1Labels = labelEmbedding8 ∘ raw37103step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37103step1 raw37103step1Labels raw37103step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

def raw37104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37104Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37104step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37104step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37104step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37104step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37104 raw37104Labels = mixedMoment B node4676 node4676Labels := by
  calc
    mixedMoment B raw37104 raw37104Labels = mixedMoment B raw37104step0 raw37104step0Labels := by
      have ha : raw37104step0 = (fun i j => raw37104 (permutation282 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37104step0 raw37104; decide +kernel
      have hl : raw37104step0Labels = raw37104Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37104 raw37104Labels permutation282 permutation3
    mixedMoment B raw37104step0 raw37104step0Labels = mixedMoment B raw37104step1 raw37104step1Labels := by
      have ha : raw37104step1 = raw37104step0 := by apply Matrix.ext; unfold raw37104step1 raw37104step0; decide +kernel
      have hl : raw37104step0Labels = labelEmbedding6 ∘ raw37104step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37104step0 raw37104step0Labels raw37104step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4676 node4676Labels := by rfl

def raw37105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37105Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37105step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37105step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37105step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37105step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37105step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37105 raw37105Labels = mixedMoment B node5387 node5387Labels := by
  calc
    mixedMoment B raw37105 raw37105Labels = mixedMoment B raw37105step0 raw37105step0Labels := by
      have hz : ∀ j, raw37105 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37105step0 = (fun i j => raw37105 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37105step0 raw37105; decide +kernel
      have hl : raw37105step0Labels = raw37105Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37105 raw37105Labels permutation434 hz
    mixedMoment B raw37105step0 raw37105step0Labels = mixedMoment B raw37105step1 raw37105step1Labels := by
      have ha : raw37105step1 = (fun i j => raw37105step0 (permutation59 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37105step1 raw37105step0; decide +kernel
      have hl : raw37105step1Labels = raw37105step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37105step0 raw37105step0Labels permutation59 permutation3
    mixedMoment B raw37105step1 raw37105step1Labels = mixedMoment B raw37105step2 raw37105step2Labels := by
      have ha : raw37105step2 = raw37105step1 := by apply Matrix.ext; unfold raw37105step2 raw37105step1; decide +kernel
      have hl : raw37105step1Labels = labelEmbedding6 ∘ raw37105step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37105step1 raw37105step1Labels raw37105step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5387 node5387Labels := by rfl

def raw37106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw37106Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37106step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37106step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37106step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37106step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37106 raw37106Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw37106 raw37106Labels = mixedMoment B raw37106step0 raw37106step0Labels := by
      have ha : raw37106step0 = (fun i j => raw37106 (permutation282 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37106step0 raw37106; decide +kernel
      have hl : raw37106step0Labels = raw37106Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37106 raw37106Labels permutation282 permutation3
    mixedMoment B raw37106step0 raw37106step0Labels = mixedMoment B raw37106step1 raw37106step1Labels := by
      have ha : raw37106step1 = raw37106step0 := by apply Matrix.ext; unfold raw37106step1 raw37106step0; decide +kernel
      have hl : raw37106step0Labels = labelEmbedding6 ∘ raw37106step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37106step0 raw37106step0Labels raw37106step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

def raw37107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw37107Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37107step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37107step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37107step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37107step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37107 raw37107Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw37107 raw37107Labels = mixedMoment B raw37107step0 raw37107step0Labels := by
      have ha : raw37107step0 = (fun i j => raw37107 (permutation288 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37107step0 raw37107; decide +kernel
      have hl : raw37107step0Labels = raw37107Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37107 raw37107Labels permutation288 permutation3
    mixedMoment B raw37107step0 raw37107step0Labels = mixedMoment B raw37107step1 raw37107step1Labels := by
      have ha : raw37107step1 = raw37107step0 := by apply Matrix.ext; unfold raw37107step1 raw37107step0; decide +kernel
      have hl : raw37107step0Labels = labelEmbedding6 ∘ raw37107step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37107step0 raw37107step0Labels raw37107step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

def raw37108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37108Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37108step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37108step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37108step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37108step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37108 raw37108Labels = mixedMoment B node4676 node4676Labels := by
  calc
    mixedMoment B raw37108 raw37108Labels = mixedMoment B raw37108step0 raw37108step0Labels := by
      have ha : raw37108step0 = (fun i j => raw37108 (permutation281 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37108step0 raw37108; decide +kernel
      have hl : raw37108step0Labels = raw37108Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37108 raw37108Labels permutation281 permutation3
    mixedMoment B raw37108step0 raw37108step0Labels = mixedMoment B raw37108step1 raw37108step1Labels := by
      have ha : raw37108step1 = raw37108step0 := by apply Matrix.ext; unfold raw37108step1 raw37108step0; decide +kernel
      have hl : raw37108step0Labels = labelEmbedding6 ∘ raw37108step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37108step0 raw37108step0Labels raw37108step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4676 node4676Labels := by rfl

def raw37109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1], ![1, 0, -1]]
def raw37109Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37109step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37109step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37109step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37109step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37109 raw37109Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw37109 raw37109Labels = mixedMoment B raw37109step0 raw37109step0Labels := by
      have ha : raw37109step0 = (fun i j => raw37109 (permutation281 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37109step0 raw37109; decide +kernel
      have hl : raw37109step0Labels = raw37109Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37109 raw37109Labels permutation281 permutation3
    mixedMoment B raw37109step0 raw37109step0Labels = mixedMoment B raw37109step1 raw37109step1Labels := by
      have ha : raw37109step1 = raw37109step0 := by apply Matrix.ext; unfold raw37109step1 raw37109step0; decide +kernel
      have hl : raw37109step0Labels = labelEmbedding6 ∘ raw37109step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37109step0 raw37109step0Labels raw37109step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

def raw37110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![0, 1, -1]]
def raw37110Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37110step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37110step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37110step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37110step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37110 raw37110Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw37110 raw37110Labels = mixedMoment B raw37110step0 raw37110step0Labels := by
      have ha : raw37110step0 = (fun i j => raw37110 (permutation287 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37110step0 raw37110; decide +kernel
      have hl : raw37110step0Labels = raw37110Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37110 raw37110Labels permutation287 permutation3
    mixedMoment B raw37110step0 raw37110step0Labels = mixedMoment B raw37110step1 raw37110step1Labels := by
      have ha : raw37110step1 = raw37110step0 := by apply Matrix.ext; unfold raw37110step1 raw37110step0; decide +kernel
      have hl : raw37110step0Labels = labelEmbedding6 ∘ raw37110step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37110step0 raw37110step0Labels raw37110step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

def raw37111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 3, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw37111Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37111step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37111step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37111step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37111step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37111 raw37111Labels = mixedMoment B node4679 node4679Labels := by
  calc
    mixedMoment B raw37111 raw37111Labels = mixedMoment B raw37111step0 raw37111step0Labels := by
      have ha : raw37111step0 = (fun i j => raw37111 (permutation283 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37111step0 raw37111; decide +kernel
      have hl : raw37111step0Labels = raw37111Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37111 raw37111Labels permutation283 permutation3
    mixedMoment B raw37111step0 raw37111step0Labels = mixedMoment B raw37111step1 raw37111step1Labels := by
      have ha : raw37111step1 = raw37111step0 := by apply Matrix.ext; unfold raw37111step1 raw37111step0; decide +kernel
      have hl : raw37111step0Labels = labelEmbedding6 ∘ raw37111step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37111step0 raw37111step0Labels raw37111step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4679 node4679Labels := by rfl

def raw37112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![0, 1, -1]]
def raw37112Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37112step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37112step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37112step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37112step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37112 raw37112Labels = mixedMoment B node5380 node5380Labels := by
  calc
    mixedMoment B raw37112 raw37112Labels = mixedMoment B raw37112step0 raw37112step0Labels := by
      have ha : raw37112step0 = (fun i j => raw37112 (permutation283 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37112step0 raw37112; decide +kernel
      have hl : raw37112step0Labels = raw37112Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37112 raw37112Labels permutation283 permutation3
    mixedMoment B raw37112step0 raw37112step0Labels = mixedMoment B raw37112step1 raw37112step1Labels := by
      have ha : raw37112step1 = raw37112step0 := by apply Matrix.ext; unfold raw37112step1 raw37112step0; decide +kernel
      have hl : raw37112step0Labels = labelEmbedding6 ∘ raw37112step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37112step0 raw37112step0Labels raw37112step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5380 node5380Labels := by rfl

def raw37113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-3, 4, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37113Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37113step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37113step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37113step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37113step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37113step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37113step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37113 raw37113Labels = mixedMoment B node4451 node4451Labels := by
  calc
    mixedMoment B raw37113 raw37113Labels = mixedMoment B raw37113step0 raw37113step0Labels := by
      have ha : raw37113step0 = (fun i j => raw37113 (permutation333 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37113step0 raw37113; decide +kernel
      have hl : raw37113step0Labels = raw37113Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37113 raw37113Labels permutation333 permutation5
    mixedMoment B raw37113step0 raw37113step0Labels = mixedMoment B raw37113step1 raw37113step1Labels := by
      have ha : raw37113step1 = -raw37113step0 := by apply Matrix.ext; change ∀ i j, raw37113step1 i j = -(raw37113step0 i j); unfold raw37113step1 raw37113step0; decide +kernel
      have hl : raw37113step1Labels = raw37113step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37113step1 raw37113step1Labels = mixedMoment B raw37113step2 raw37113step2Labels := by
      have ha : raw37113step2 = raw37113step1 := by apply Matrix.ext; unfold raw37113step2 raw37113step1; decide +kernel
      have hl : raw37113step1Labels = labelEmbedding8 ∘ raw37113step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37113step1 raw37113step1Labels raw37113step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4451 node4451Labels := by rfl

def raw37114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37114Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37114step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37114step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37114step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37114step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37114step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37114step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37114step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37114 raw37114Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw37114 raw37114Labels = mixedMoment B raw37114step0 raw37114step0Labels := by
      have hz : ∀ j, raw37114 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37114step0 = (fun i j => raw37114 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37114step0 raw37114; decide +kernel
      have hl : raw37114step0Labels = raw37114Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37114 raw37114Labels permutation434 hz
    mixedMoment B raw37114step0 raw37114step0Labels = mixedMoment B raw37114step1 raw37114step1Labels := by
      have ha : raw37114step1 = (fun i j => raw37114step0 (permutation74 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37114step1 raw37114step0; decide +kernel
      have hl : raw37114step1Labels = raw37114step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37114step0 raw37114step0Labels permutation74 permutation5
    mixedMoment B raw37114step1 raw37114step1Labels = mixedMoment B raw37114step2 raw37114step2Labels := by
      have ha : raw37114step2 = -raw37114step1 := by apply Matrix.ext; change ∀ i j, raw37114step2 i j = -(raw37114step1 i j); unfold raw37114step2 raw37114step1; decide +kernel
      have hl : raw37114step2Labels = raw37114step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37114step2 raw37114step2Labels = mixedMoment B raw37114step3 raw37114step3Labels := by
      have ha : raw37114step3 = raw37114step2 := by apply Matrix.ext; unfold raw37114step3 raw37114step2; decide +kernel
      have hl : raw37114step2Labels = labelEmbedding8 ∘ raw37114step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37114step2 raw37114step2Labels raw37114step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

def raw37115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw37115Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37115step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37115step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37115step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37115step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37115step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37115step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37115step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37115 raw37115Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw37115 raw37115Labels = mixedMoment B raw37115step0 raw37115step0Labels := by
      have hz : ∀ j, raw37115 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37115step0 = (fun i j => raw37115 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37115step0 raw37115; decide +kernel
      have hl : raw37115step0Labels = raw37115Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37115 raw37115Labels permutation520 hz
    mixedMoment B raw37115step0 raw37115step0Labels = mixedMoment B raw37115step1 raw37115step1Labels := by
      have ha : raw37115step1 = (fun i j => raw37115step0 (permutation74 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37115step1 raw37115step0; decide +kernel
      have hl : raw37115step1Labels = raw37115step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37115step0 raw37115step0Labels permutation74 permutation5
    mixedMoment B raw37115step1 raw37115step1Labels = mixedMoment B raw37115step2 raw37115step2Labels := by
      have ha : raw37115step2 = -raw37115step1 := by apply Matrix.ext; change ∀ i j, raw37115step2 i j = -(raw37115step1 i j); unfold raw37115step2 raw37115step1; decide +kernel
      have hl : raw37115step2Labels = raw37115step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37115step2 raw37115step2Labels = mixedMoment B raw37115step3 raw37115step3Labels := by
      have ha : raw37115step3 = raw37115step2 := by apply Matrix.ext; unfold raw37115step3 raw37115step2; decide +kernel
      have hl : raw37115step2Labels = labelEmbedding8 ∘ raw37115step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37115step2 raw37115step2Labels raw37115step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

def raw37116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw37116Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37116step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37116step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37116step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37116step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37116step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37116step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37116 raw37116Labels = mixedMoment B node5162 node5162Labels := by
  calc
    mixedMoment B raw37116 raw37116Labels = mixedMoment B raw37116step0 raw37116step0Labels := by
      have ha : raw37116step0 = (fun i j => raw37116 (permutation333 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37116step0 raw37116; decide +kernel
      have hl : raw37116step0Labels = raw37116Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37116 raw37116Labels permutation333 permutation5
    mixedMoment B raw37116step0 raw37116step0Labels = mixedMoment B raw37116step1 raw37116step1Labels := by
      have ha : raw37116step1 = -raw37116step0 := by apply Matrix.ext; change ∀ i j, raw37116step1 i j = -(raw37116step0 i j); unfold raw37116step1 raw37116step0; decide +kernel
      have hl : raw37116step1Labels = raw37116step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37116step1 raw37116step1Labels = mixedMoment B raw37116step2 raw37116step2Labels := by
      have ha : raw37116step2 = raw37116step1 := by apply Matrix.ext; unfold raw37116step2 raw37116step1; decide +kernel
      have hl : raw37116step1Labels = labelEmbedding8 ∘ raw37116step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37116step1 raw37116step1Labels raw37116step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5162 node5162Labels := by rfl

def raw37117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 4, -1], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37117Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37117step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw37117step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37117step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37117step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37117step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37117step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37117 raw37117Labels = mixedMoment B node4376 node4376Labels := by
  calc
    mixedMoment B raw37117 raw37117Labels = mixedMoment B raw37117step0 raw37117step0Labels := by
      have ha : raw37117step0 = (fun i j => raw37117 (permutation286 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37117step0 raw37117; decide +kernel
      have hl : raw37117step0Labels = raw37117Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37117 raw37117Labels permutation286 permutation5
    mixedMoment B raw37117step0 raw37117step0Labels = mixedMoment B raw37117step1 raw37117step1Labels := by
      have ha : raw37117step1 = -raw37117step0 := by apply Matrix.ext; change ∀ i j, raw37117step1 i j = -(raw37117step0 i j); unfold raw37117step1 raw37117step0; decide +kernel
      have hl : raw37117step1Labels = raw37117step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37117step1 raw37117step1Labels = mixedMoment B raw37117step2 raw37117step2Labels := by
      have ha : raw37117step2 = raw37117step1 := by apply Matrix.ext; unfold raw37117step2 raw37117step1; decide +kernel
      have hl : raw37117step1Labels = labelEmbedding8 ∘ raw37117step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37117step1 raw37117step1Labels raw37117step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4376 node4376Labels := by rfl

def raw37118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37118Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37118step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37118step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw37118step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37118step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37118step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37118step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37118step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37118 raw37118Labels = mixedMoment B node5228 node5228Labels := by
  calc
    mixedMoment B raw37118 raw37118Labels = mixedMoment B raw37118step0 raw37118step0Labels := by
      have hz : ∀ j, raw37118 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37118step0 = (fun i j => raw37118 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37118step0 raw37118; decide +kernel
      have hl : raw37118step0Labels = raw37118Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37118 raw37118Labels permutation434 hz
    mixedMoment B raw37118step0 raw37118step0Labels = mixedMoment B raw37118step1 raw37118step1Labels := by
      have ha : raw37118step1 = (fun i j => raw37118step0 (permutation61 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37118step1 raw37118step0; decide +kernel
      have hl : raw37118step1Labels = raw37118step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37118step0 raw37118step0Labels permutation61 permutation5
    mixedMoment B raw37118step1 raw37118step1Labels = mixedMoment B raw37118step2 raw37118step2Labels := by
      have ha : raw37118step2 = -raw37118step1 := by apply Matrix.ext; change ∀ i j, raw37118step2 i j = -(raw37118step1 i j); unfold raw37118step2 raw37118step1; decide +kernel
      have hl : raw37118step2Labels = raw37118step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37118step2 raw37118step2Labels = mixedMoment B raw37118step3 raw37118step3Labels := by
      have ha : raw37118step3 = raw37118step2 := by apply Matrix.ext; unfold raw37118step3 raw37118step2; decide +kernel
      have hl : raw37118step2Labels = labelEmbedding8 ∘ raw37118step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37118step2 raw37118step2Labels raw37118step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5228 node5228Labels := by rfl

def raw37119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw37119Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37119step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37119step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw37119step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37119step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37119step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37119step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37119step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37119 raw37119Labels = mixedMoment B node5228 node5228Labels := by
  calc
    mixedMoment B raw37119 raw37119Labels = mixedMoment B raw37119step0 raw37119step0Labels := by
      have hz : ∀ j, raw37119 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37119step0 = (fun i j => raw37119 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37119step0 raw37119; decide +kernel
      have hl : raw37119step0Labels = raw37119Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37119 raw37119Labels permutation520 hz
    mixedMoment B raw37119step0 raw37119step0Labels = mixedMoment B raw37119step1 raw37119step1Labels := by
      have ha : raw37119step1 = (fun i j => raw37119step0 (permutation61 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37119step1 raw37119step0; decide +kernel
      have hl : raw37119step1Labels = raw37119step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37119step0 raw37119step0Labels permutation61 permutation5
    mixedMoment B raw37119step1 raw37119step1Labels = mixedMoment B raw37119step2 raw37119step2Labels := by
      have ha : raw37119step2 = -raw37119step1 := by apply Matrix.ext; change ∀ i j, raw37119step2 i j = -(raw37119step1 i j); unfold raw37119step2 raw37119step1; decide +kernel
      have hl : raw37119step2Labels = raw37119step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37119step2 raw37119step2Labels = mixedMoment B raw37119step3 raw37119step3Labels := by
      have ha : raw37119step3 = raw37119step2 := by apply Matrix.ext; unfold raw37119step3 raw37119step2; decide +kernel
      have hl : raw37119step2Labels = labelEmbedding8 ∘ raw37119step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37119step2 raw37119step2Labels raw37119step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5228 node5228Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
