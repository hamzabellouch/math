import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw4992 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw4992Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw4992step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4992step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4992step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw4992step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw4992step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4992 raw4992Labels = mixedMoment B node4832 node4832Labels := by
  calc
    mixedMoment B raw4992 raw4992Labels = mixedMoment B raw4992step0 raw4992step0Labels := by
      have hz : ∀ j, raw4992 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4992step0 = (fun i j => raw4992 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4992step0 raw4992; decide +kernel
      have hl : raw4992step0Labels = raw4992Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4992 raw4992Labels permutation346 hz
    mixedMoment B raw4992step0 raw4992step0Labels = mixedMoment B raw4992step1 raw4992step1Labels := by
      have ha : raw4992step1 = (fun i j => raw4992step0 (permutation137 i) (permutation4 j)) := by apply Matrix.ext; unfold raw4992step1 raw4992step0; decide +kernel
      have hl : raw4992step1Labels = raw4992step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4992step0 raw4992step0Labels permutation137 permutation4
    mixedMoment B raw4992step1 raw4992step1Labels = mixedMoment B raw4992step2 raw4992step2Labels := by
      have ha : raw4992step2 = raw4992step1 := by apply Matrix.ext; unfold raw4992step2 raw4992step1; decide +kernel
      have hl : raw4992step1Labels = labelEmbedding7 ∘ raw4992step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4992step1 raw4992step1Labels raw4992step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4832 node4832Labels := by rfl

def raw4993 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -3, 3]]
def raw4993Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -3, 3]]
def raw4993step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4993step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 2, 0], ![0, -3, 3]]
def raw4993step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw4993step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw4993step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw4993step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw4993step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical4993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4993 raw4993Labels = mixedMoment B node4845 node4845Labels := by
  calc
    mixedMoment B raw4993 raw4993Labels = mixedMoment B raw4993step0 raw4993step0Labels := by
      have hz : ∀ j, raw4993 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4993step0 = (fun i j => raw4993 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4993step0 raw4993; decide +kernel
      have hl : raw4993step0Labels = raw4993Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4993 raw4993Labels permutation434 hz
    mixedMoment B raw4993step0 raw4993step0Labels = mixedMoment B raw4993step1 raw4993step1Labels := by
      have hz : ∀ j, raw4993step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4993step1 = (fun i j => raw4993step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4993step1 raw4993step0; decide +kernel
      have hl : raw4993step1Labels = raw4993step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4993step0 raw4993step0Labels permutation80 hz
    mixedMoment B raw4993step1 raw4993step1Labels = mixedMoment B raw4993step2 raw4993step2Labels := by
      have ha : raw4993step2 = (fun i j => raw4993step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw4993step2 raw4993step1; decide +kernel
      have hl : raw4993step2Labels = raw4993step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4993step1 raw4993step1Labels permutation29 permutation4
    mixedMoment B raw4993step2 raw4993step2Labels = mixedMoment B raw4993step3 raw4993step3Labels := by
      have ha : raw4993step3 = raw4993step2 := by apply Matrix.ext; unfold raw4993step3 raw4993step2; decide +kernel
      have hl : raw4993step2Labels = labelEmbedding7 ∘ raw4993step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw4993step2 raw4993step2Labels raw4993step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4845 node4845Labels := by rfl

def raw4994 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4994Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4994step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4994step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4994step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4994step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, -2, 3]]
def raw4994step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4994step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-3, 2, 1]]
def raw4994step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4994step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw4994step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4994 raw4994Labels = mixedMoment B node2770 node2770Labels := by
  calc
    mixedMoment B raw4994 raw4994Labels = mixedMoment B raw4994step0 raw4994step0Labels := by
      have hz : ∀ j, raw4994 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4994step0 = (fun i j => raw4994 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4994step0 raw4994; decide +kernel
      have hl : raw4994step0Labels = raw4994Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4994 raw4994Labels permutation434 hz
    mixedMoment B raw4994step0 raw4994step0Labels = mixedMoment B raw4994step1 raw4994step1Labels := by
      have hz : ∀ j, raw4994step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4994step1 = (fun i j => raw4994step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4994step1 raw4994step0; decide +kernel
      have hl : raw4994step1Labels = raw4994step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4994step0 raw4994step0Labels permutation80 hz
    mixedMoment B raw4994step1 raw4994step1Labels = mixedMoment B raw4994step2 raw4994step2Labels := by
      have hz : ∀ j, raw4994step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw4994step2 = (fun i j => raw4994step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw4994step2 raw4994step1; decide +kernel
      have hl : raw4994step2Labels = raw4994step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4994step1 raw4994step1Labels permutation14 hz
    mixedMoment B raw4994step2 raw4994step2Labels = mixedMoment B raw4994step3 raw4994step3Labels := by
      have ha : raw4994step3 = (fun i j => raw4994step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4994step3 raw4994step2; decide +kernel
      have hl : raw4994step3Labels = raw4994step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4994step2 raw4994step2Labels permutation7 permutation6
    mixedMoment B raw4994step3 raw4994step3Labels = mixedMoment B raw4994step4 raw4994step4Labels := by
      have ha : raw4994step4 = -raw4994step3 := by apply Matrix.ext; change ∀ i j, raw4994step4 i j = -(raw4994step3 i j); unfold raw4994step4 raw4994step3; decide +kernel
      have hl : raw4994step4Labels = raw4994step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2770 node2770Labels := by rfl

def raw4995 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4995Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4995step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4995step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw4995step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4995step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4995step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4995 raw4995Labels = mixedMoment B node2712 node2712Labels := by
  calc
    mixedMoment B raw4995 raw4995Labels = mixedMoment B raw4995step0 raw4995step0Labels := by
      have hz : ∀ j, raw4995 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4995step0 = (fun i j => raw4995 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4995step0 raw4995; decide +kernel
      have hl : raw4995step0Labels = raw4995Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4995 raw4995Labels permutation434 hz
    mixedMoment B raw4995step0 raw4995step0Labels = mixedMoment B raw4995step1 raw4995step1Labels := by
      have ha : raw4995step1 = (fun i j => raw4995step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4995step1 raw4995step0; decide +kernel
      have hl : raw4995step1Labels = raw4995step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4995step0 raw4995step0Labels permutation137 permutation6
    mixedMoment B raw4995step1 raw4995step1Labels = mixedMoment B raw4995step2 raw4995step2Labels := by
      have ha : raw4995step2 = -raw4995step1 := by apply Matrix.ext; change ∀ i j, raw4995step2 i j = -(raw4995step1 i j); unfold raw4995step2 raw4995step1; decide +kernel
      have hl : raw4995step2Labels = raw4995step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2712 node2712Labels := by rfl

def raw4996 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4996Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4996step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4996step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw4996step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4996step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw4996step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4996 raw4996Labels = mixedMoment B node2712 node2712Labels := by
  calc
    mixedMoment B raw4996 raw4996Labels = mixedMoment B raw4996step0 raw4996step0Labels := by
      have hz : ∀ j, raw4996 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw4996step0 = (fun i j => raw4996 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw4996step0 raw4996; decide +kernel
      have hl : raw4996step0Labels = raw4996Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4996 raw4996Labels permutation346 hz
    mixedMoment B raw4996step0 raw4996step0Labels = mixedMoment B raw4996step1 raw4996step1Labels := by
      have ha : raw4996step1 = (fun i j => raw4996step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4996step1 raw4996step0; decide +kernel
      have hl : raw4996step1Labels = raw4996step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4996step0 raw4996step0Labels permutation137 permutation6
    mixedMoment B raw4996step1 raw4996step1Labels = mixedMoment B raw4996step2 raw4996step2Labels := by
      have ha : raw4996step2 = -raw4996step1 := by apply Matrix.ext; change ∀ i j, raw4996step2 i j = -(raw4996step1 i j); unfold raw4996step2 raw4996step1; decide +kernel
      have hl : raw4996step2Labels = raw4996step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2712 node2712Labels := by rfl

def raw4997 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw4997Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw4997step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4997step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw4997step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4997step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-3, 2, 1]]
def raw4997step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw4997step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw4997step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4997 raw4997Labels = mixedMoment B node2734 node2734Labels := by
  calc
    mixedMoment B raw4997 raw4997Labels = mixedMoment B raw4997step0 raw4997step0Labels := by
      have hz : ∀ j, raw4997 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4997step0 = (fun i j => raw4997 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4997step0 raw4997; decide +kernel
      have hl : raw4997step0Labels = raw4997Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4997 raw4997Labels permutation434 hz
    mixedMoment B raw4997step0 raw4997step0Labels = mixedMoment B raw4997step1 raw4997step1Labels := by
      have hz : ∀ j, raw4997step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4997step1 = (fun i j => raw4997step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4997step1 raw4997step0; decide +kernel
      have hl : raw4997step1Labels = raw4997step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4997step0 raw4997step0Labels permutation80 hz
    mixedMoment B raw4997step1 raw4997step1Labels = mixedMoment B raw4997step2 raw4997step2Labels := by
      have ha : raw4997step2 = (fun i j => raw4997step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4997step2 raw4997step1; decide +kernel
      have hl : raw4997step2Labels = raw4997step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4997step1 raw4997step1Labels permutation29 permutation6
    mixedMoment B raw4997step2 raw4997step2Labels = mixedMoment B raw4997step3 raw4997step3Labels := by
      have ha : raw4997step3 = -raw4997step2 := by apply Matrix.ext; change ∀ i j, raw4997step3 i j = -(raw4997step2 i j); unfold raw4997step3 raw4997step2; decide +kernel
      have hl : raw4997step3Labels = raw4997step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2734 node2734Labels := by rfl

def raw4998 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw4998Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw4998step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4998step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw4998step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4998step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw4998step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4998 raw4998Labels = mixedMoment B node3090 node3090Labels := by
  calc
    mixedMoment B raw4998 raw4998Labels = mixedMoment B raw4998step0 raw4998step0Labels := by
      have hz : ∀ j, raw4998 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4998step0 = (fun i j => raw4998 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4998step0 raw4998; decide +kernel
      have hl : raw4998step0Labels = raw4998Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4998 raw4998Labels permutation434 hz
    mixedMoment B raw4998step0 raw4998step0Labels = mixedMoment B raw4998step1 raw4998step1Labels := by
      have hz : ∀ j, raw4998step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4998step1 = (fun i j => raw4998step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4998step1 raw4998step0; decide +kernel
      have hl : raw4998step1Labels = raw4998step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4998step0 raw4998step0Labels permutation80 hz
    mixedMoment B raw4998step1 raw4998step1Labels = mixedMoment B raw4998step2 raw4998step2Labels := by
      have ha : raw4998step2 = (fun i j => raw4998step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4998step2 raw4998step1; decide +kernel
      have hl : raw4998step2Labels = raw4998step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4998step1 raw4998step1Labels permutation10 permutation6
    _ = mixedMoment B node3090 node3090Labels := by rfl

def raw4999 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4999Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4999step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4999step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw4999step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw4999step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw4999step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical4999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw4999 raw4999Labels = mixedMoment B node2218 node2218Labels := by
  calc
    mixedMoment B raw4999 raw4999Labels = mixedMoment B raw4999step0 raw4999step0Labels := by
      have hz : ∀ j, raw4999 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw4999step0 = (fun i j => raw4999 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw4999step0 raw4999; decide +kernel
      have hl : raw4999step0Labels = raw4999Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4999 raw4999Labels permutation434 hz
    mixedMoment B raw4999step0 raw4999step0Labels = mixedMoment B raw4999step1 raw4999step1Labels := by
      have hz : ∀ j, raw4999step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw4999step1 = (fun i j => raw4999step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw4999step1 raw4999step0; decide +kernel
      have hl : raw4999step1Labels = raw4999step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw4999step0 raw4999step0Labels permutation80 hz
    mixedMoment B raw4999step1 raw4999step1Labels = mixedMoment B raw4999step2 raw4999step2Labels := by
      have ha : raw4999step2 = (fun i j => raw4999step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw4999step2 raw4999step1; decide +kernel
      have hl : raw4999step2Labels = raw4999step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw4999step1 raw4999step1Labels permutation10 permutation6
    _ = mixedMoment B node2218 node2218Labels := by rfl

def raw5000 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5000Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5000step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5000step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw5000step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5000step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw5000step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5000 raw5000Labels = mixedMoment B node2664 node2664Labels := by
  calc
    mixedMoment B raw5000 raw5000Labels = mixedMoment B raw5000step0 raw5000step0Labels := by
      have hz : ∀ j, raw5000 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5000step0 = (fun i j => raw5000 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5000step0 raw5000; decide +kernel
      have hl : raw5000step0Labels = raw5000Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5000 raw5000Labels permutation434 hz
    mixedMoment B raw5000step0 raw5000step0Labels = mixedMoment B raw5000step1 raw5000step1Labels := by
      have ha : raw5000step1 = (fun i j => raw5000step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5000step1 raw5000step0; decide +kernel
      have hl : raw5000step1Labels = raw5000step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5000step0 raw5000step0Labels permutation137 permutation6
    mixedMoment B raw5000step1 raw5000step1Labels = mixedMoment B raw5000step2 raw5000step2Labels := by
      have ha : raw5000step2 = -raw5000step1 := by apply Matrix.ext; change ∀ i j, raw5000step2 i j = -(raw5000step1 i j); unfold raw5000step2 raw5000step1; decide +kernel
      have hl : raw5000step2Labels = raw5000step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2664 node2664Labels := by rfl

def raw5001 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5001Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5001step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5001step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw5001step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5001step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw5001step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5001 raw5001Labels = mixedMoment B node2664 node2664Labels := by
  calc
    mixedMoment B raw5001 raw5001Labels = mixedMoment B raw5001step0 raw5001step0Labels := by
      have hz : ∀ j, raw5001 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5001step0 = (fun i j => raw5001 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5001step0 raw5001; decide +kernel
      have hl : raw5001step0Labels = raw5001Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5001 raw5001Labels permutation346 hz
    mixedMoment B raw5001step0 raw5001step0Labels = mixedMoment B raw5001step1 raw5001step1Labels := by
      have ha : raw5001step1 = (fun i j => raw5001step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5001step1 raw5001step0; decide +kernel
      have hl : raw5001step1Labels = raw5001step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5001step0 raw5001step0Labels permutation137 permutation6
    mixedMoment B raw5001step1 raw5001step1Labels = mixedMoment B raw5001step2 raw5001step2Labels := by
      have ha : raw5001step2 = -raw5001step1 := by apply Matrix.ext; change ∀ i j, raw5001step2 i j = -(raw5001step1 i j); unfold raw5001step2 raw5001step1; decide +kernel
      have hl : raw5001step2Labels = raw5001step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2664 node2664Labels := by rfl

def raw5002 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw5002Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw5002step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5002step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw5002step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5002step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw5002step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5002 raw5002Labels = mixedMoment B node2680 node2680Labels := by
  calc
    mixedMoment B raw5002 raw5002Labels = mixedMoment B raw5002step0 raw5002step0Labels := by
      have hz : ∀ j, raw5002 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5002step0 = (fun i j => raw5002 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5002step0 raw5002; decide +kernel
      have hl : raw5002step0Labels = raw5002Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5002 raw5002Labels permutation434 hz
    mixedMoment B raw5002step0 raw5002step0Labels = mixedMoment B raw5002step1 raw5002step1Labels := by
      have hz : ∀ j, raw5002step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5002step1 = (fun i j => raw5002step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5002step1 raw5002step0; decide +kernel
      have hl : raw5002step1Labels = raw5002step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5002step0 raw5002step0Labels permutation80 hz
    mixedMoment B raw5002step1 raw5002step1Labels = mixedMoment B raw5002step2 raw5002step2Labels := by
      have ha : raw5002step2 = (fun i j => raw5002step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5002step2 raw5002step1; decide +kernel
      have hl : raw5002step2Labels = raw5002step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5002step1 raw5002step1Labels permutation10 permutation6
    _ = mixedMoment B node2680 node2680Labels := by rfl

def raw5003 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw5003Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw5003step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5003step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw5003step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5003step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw5003step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5003 raw5003Labels = mixedMoment B node2734 node2734Labels := by
  calc
    mixedMoment B raw5003 raw5003Labels = mixedMoment B raw5003step0 raw5003step0Labels := by
      have hz : ∀ j, raw5003 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5003step0 = (fun i j => raw5003 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5003step0 raw5003; decide +kernel
      have hl : raw5003step0Labels = raw5003Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5003 raw5003Labels permutation434 hz
    mixedMoment B raw5003step0 raw5003step0Labels = mixedMoment B raw5003step1 raw5003step1Labels := by
      have hz : ∀ j, raw5003step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5003step1 = (fun i j => raw5003step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5003step1 raw5003step0; decide +kernel
      have hl : raw5003step1Labels = raw5003step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5003step0 raw5003step0Labels permutation80 hz
    mixedMoment B raw5003step1 raw5003step1Labels = mixedMoment B raw5003step2 raw5003step2Labels := by
      have ha : raw5003step2 = (fun i j => raw5003step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5003step2 raw5003step1; decide +kernel
      have hl : raw5003step2Labels = raw5003step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5003step1 raw5003step1Labels permutation10 permutation6
    _ = mixedMoment B node2734 node2734Labels := by rfl

def raw5004 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5004Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5004step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5004step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw5004step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5004 raw5004Labels = mixedMoment B node2193 node2193Labels := by
  calc
    mixedMoment B raw5004 raw5004Labels = mixedMoment B raw5004step0 raw5004step0Labels := by
      have hz : ∀ j, raw5004 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5004step0 = (fun i j => raw5004 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5004step0 raw5004; decide +kernel
      have hl : raw5004step0Labels = raw5004Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5004 raw5004Labels permutation434 hz
    mixedMoment B raw5004step0 raw5004step0Labels = mixedMoment B raw5004step1 raw5004step1Labels := by
      have ha : raw5004step1 = (fun i j => raw5004step0 (permutation44 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5004step1 raw5004step0; decide +kernel
      have hl : raw5004step1Labels = raw5004step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5004step0 raw5004step0Labels permutation44 permutation6
    _ = mixedMoment B node2193 node2193Labels := by rfl

def raw5005 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5005Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5005step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5005step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5005step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5005step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5005step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw5005step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5005 raw5005Labels = mixedMoment B node2726 node2726Labels := by
  calc
    mixedMoment B raw5005 raw5005Labels = mixedMoment B raw5005step0 raw5005step0Labels := by
      have hz : ∀ j, raw5005 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5005step0 = (fun i j => raw5005 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5005step0 raw5005; decide +kernel
      have hl : raw5005step0Labels = raw5005Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5005 raw5005Labels permutation434 hz
    mixedMoment B raw5005step0 raw5005step0Labels = mixedMoment B raw5005step1 raw5005step1Labels := by
      have hz : ∀ j, raw5005step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5005step1 = (fun i j => raw5005step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5005step1 raw5005step0; decide +kernel
      have hl : raw5005step1Labels = raw5005step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5005step0 raw5005step0Labels permutation56 hz
    mixedMoment B raw5005step1 raw5005step1Labels = mixedMoment B raw5005step2 raw5005step2Labels := by
      have ha : raw5005step2 = (fun i j => raw5005step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5005step2 raw5005step1; decide +kernel
      have hl : raw5005step2Labels = raw5005step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5005step1 raw5005step1Labels permutation10 permutation6
    _ = mixedMoment B node2726 node2726Labels := by rfl

def raw5006 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5006Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5006step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw5006step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5006 raw5006Labels = mixedMoment B node2691 node2691Labels := by
  calc
    mixedMoment B raw5006 raw5006Labels = mixedMoment B raw5006step0 raw5006step0Labels := by
      have ha : raw5006step0 = (fun i j => raw5006 (permutation212 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5006step0 raw5006; decide +kernel
      have hl : raw5006step0Labels = raw5006Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5006 raw5006Labels permutation212 permutation6
    _ = mixedMoment B node2691 node2691Labels := by rfl

def raw5007 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw5007Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw5007step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5007step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw5007step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5007 raw5007Labels = mixedMoment B node2664 node2664Labels := by
  calc
    mixedMoment B raw5007 raw5007Labels = mixedMoment B raw5007step0 raw5007step0Labels := by
      have hz : ∀ j, raw5007 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5007step0 = (fun i j => raw5007 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5007step0 raw5007; decide +kernel
      have hl : raw5007step0Labels = raw5007Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5007 raw5007Labels permutation434 hz
    mixedMoment B raw5007step0 raw5007step0Labels = mixedMoment B raw5007step1 raw5007step1Labels := by
      have ha : raw5007step1 = (fun i j => raw5007step0 (permutation44 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5007step1 raw5007step0; decide +kernel
      have hl : raw5007step1Labels = raw5007step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5007step0 raw5007step0Labels permutation44 permutation6
    _ = mixedMoment B node2664 node2664Labels := by rfl

def raw5008 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw5008Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5008step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw5008step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5008step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5008step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5008 raw5008Labels = mixedMoment B node2712 node2712Labels := by
  calc
    mixedMoment B raw5008 raw5008Labels = mixedMoment B raw5008step0 raw5008step0Labels := by
      have hz : ∀ j, raw5008 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5008step0 = (fun i j => raw5008 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5008step0 raw5008; decide +kernel
      have hl : raw5008step0Labels = raw5008Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5008 raw5008Labels permutation434 hz
    mixedMoment B raw5008step0 raw5008step0Labels = mixedMoment B raw5008step1 raw5008step1Labels := by
      have ha : raw5008step1 = (fun i j => raw5008step0 (permutation44 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5008step1 raw5008step0; decide +kernel
      have hl : raw5008step1Labels = raw5008step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5008step0 raw5008step0Labels permutation44 permutation6
    _ = mixedMoment B node2712 node2712Labels := by rfl

def raw5009 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5009Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5009step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5009step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw5009step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5009 raw5009Labels = mixedMoment B node2193 node2193Labels := by
  calc
    mixedMoment B raw5009 raw5009Labels = mixedMoment B raw5009step0 raw5009step0Labels := by
      have hz : ∀ j, raw5009 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5009step0 = (fun i j => raw5009 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5009step0 raw5009; decide +kernel
      have hl : raw5009step0Labels = raw5009Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5009 raw5009Labels permutation346 hz
    mixedMoment B raw5009step0 raw5009step0Labels = mixedMoment B raw5009step1 raw5009step1Labels := by
      have ha : raw5009step1 = (fun i j => raw5009step0 (permutation44 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5009step1 raw5009step0; decide +kernel
      have hl : raw5009step1Labels = raw5009step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5009step0 raw5009step0Labels permutation44 permutation6
    _ = mixedMoment B node2193 node2193Labels := by rfl

def raw5010 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5010Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5010step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5010step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5010step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5010step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5010step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw5010step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5010 raw5010Labels = mixedMoment B node2726 node2726Labels := by
  calc
    mixedMoment B raw5010 raw5010Labels = mixedMoment B raw5010step0 raw5010step0Labels := by
      have hz : ∀ j, raw5010 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5010step0 = (fun i j => raw5010 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5010step0 raw5010; decide +kernel
      have hl : raw5010step0Labels = raw5010Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5010 raw5010Labels permutation346 hz
    mixedMoment B raw5010step0 raw5010step0Labels = mixedMoment B raw5010step1 raw5010step1Labels := by
      have hz : ∀ j, raw5010step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5010step1 = (fun i j => raw5010step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5010step1 raw5010step0; decide +kernel
      have hl : raw5010step1Labels = raw5010step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5010step0 raw5010step0Labels permutation56 hz
    mixedMoment B raw5010step1 raw5010step1Labels = mixedMoment B raw5010step2 raw5010step2Labels := by
      have ha : raw5010step2 = (fun i j => raw5010step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5010step2 raw5010step1; decide +kernel
      have hl : raw5010step2Labels = raw5010step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5010step1 raw5010step1Labels permutation10 permutation6
    _ = mixedMoment B node2726 node2726Labels := by rfl

def raw5011 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5011Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5011step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw5011step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5011 raw5011Labels = mixedMoment B node2691 node2691Labels := by
  calc
    mixedMoment B raw5011 raw5011Labels = mixedMoment B raw5011step0 raw5011step0Labels := by
      have ha : raw5011step0 = (fun i j => raw5011 (permutation188 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5011step0 raw5011; decide +kernel
      have hl : raw5011step0Labels = raw5011Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5011 raw5011Labels permutation188 permutation6
    _ = mixedMoment B node2691 node2691Labels := by rfl

def raw5012 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw5012Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw5012step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5012step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw5012step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5012 raw5012Labels = mixedMoment B node2664 node2664Labels := by
  calc
    mixedMoment B raw5012 raw5012Labels = mixedMoment B raw5012step0 raw5012step0Labels := by
      have hz : ∀ j, raw5012 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5012step0 = (fun i j => raw5012 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5012step0 raw5012; decide +kernel
      have hl : raw5012step0Labels = raw5012Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5012 raw5012Labels permutation346 hz
    mixedMoment B raw5012step0 raw5012step0Labels = mixedMoment B raw5012step1 raw5012step1Labels := by
      have ha : raw5012step1 = (fun i j => raw5012step0 (permutation44 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5012step1 raw5012step0; decide +kernel
      have hl : raw5012step1Labels = raw5012step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5012step0 raw5012step0Labels permutation44 permutation6
    _ = mixedMoment B node2664 node2664Labels := by rfl

def raw5013 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw5013Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw5013step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5013step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5013step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5013 raw5013Labels = mixedMoment B node2712 node2712Labels := by
  calc
    mixedMoment B raw5013 raw5013Labels = mixedMoment B raw5013step0 raw5013step0Labels := by
      have hz : ∀ j, raw5013 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5013step0 = (fun i j => raw5013 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5013step0 raw5013; decide +kernel
      have hl : raw5013step0Labels = raw5013Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5013 raw5013Labels permutation346 hz
    mixedMoment B raw5013step0 raw5013step0Labels = mixedMoment B raw5013step1 raw5013step1Labels := by
      have ha : raw5013step1 = (fun i j => raw5013step0 (permutation44 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5013step1 raw5013step0; decide +kernel
      have hl : raw5013step1Labels = raw5013step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5013step0 raw5013step0Labels permutation44 permutation6
    _ = mixedMoment B node2712 node2712Labels := by rfl

def raw5014 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5014Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5014step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5014step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5014step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5014step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, -2, 3]]
def raw5014step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5014step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw5014step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5014 raw5014Labels = mixedMoment B node2268 node2268Labels := by
  calc
    mixedMoment B raw5014 raw5014Labels = mixedMoment B raw5014step0 raw5014step0Labels := by
      have hz : ∀ j, raw5014 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5014step0 = (fun i j => raw5014 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5014step0 raw5014; decide +kernel
      have hl : raw5014step0Labels = raw5014Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5014 raw5014Labels permutation520 hz
    mixedMoment B raw5014step0 raw5014step0Labels = mixedMoment B raw5014step1 raw5014step1Labels := by
      have hz : ∀ j, raw5014step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5014step1 = (fun i j => raw5014step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5014step1 raw5014step0; decide +kernel
      have hl : raw5014step1Labels = raw5014step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5014step0 raw5014step0Labels permutation104 hz
    mixedMoment B raw5014step1 raw5014step1Labels = mixedMoment B raw5014step2 raw5014step2Labels := by
      have hz : ∀ j, raw5014step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw5014step2 = (fun i j => raw5014step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw5014step2 raw5014step1; decide +kernel
      have hl : raw5014step2Labels = raw5014step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5014step1 raw5014step1Labels permutation20 hz
    mixedMoment B raw5014step2 raw5014step2Labels = mixedMoment B raw5014step3 raw5014step3Labels := by
      have ha : raw5014step3 = (fun i j => raw5014step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5014step3 raw5014step2; decide +kernel
      have hl : raw5014step3Labels = raw5014step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5014step2 raw5014step2Labels permutation2 permutation6
    _ = mixedMoment B node2268 node2268Labels := by rfl

def raw5015 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5015Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5015step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5015step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5015step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5015step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw5015step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5015 raw5015Labels = mixedMoment B node2726 node2726Labels := by
  calc
    mixedMoment B raw5015 raw5015Labels = mixedMoment B raw5015step0 raw5015step0Labels := by
      have hz : ∀ j, raw5015 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5015step0 = (fun i j => raw5015 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5015step0 raw5015; decide +kernel
      have hl : raw5015step0Labels = raw5015Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5015 raw5015Labels permutation520 hz
    mixedMoment B raw5015step0 raw5015step0Labels = mixedMoment B raw5015step1 raw5015step1Labels := by
      have hz : ∀ j, raw5015step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5015step1 = (fun i j => raw5015step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5015step1 raw5015step0; decide +kernel
      have hl : raw5015step1Labels = raw5015step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5015step0 raw5015step0Labels permutation104 hz
    mixedMoment B raw5015step1 raw5015step1Labels = mixedMoment B raw5015step2 raw5015step2Labels := by
      have ha : raw5015step2 = (fun i j => raw5015step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5015step2 raw5015step1; decide +kernel
      have hl : raw5015step2Labels = raw5015step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5015step1 raw5015step1Labels permutation10 permutation6
    _ = mixedMoment B node2726 node2726Labels := by rfl

def raw5016 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5016Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5016step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5016step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5016step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5016step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw5016step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5016 raw5016Labels = mixedMoment B node2726 node2726Labels := by
  calc
    mixedMoment B raw5016 raw5016Labels = mixedMoment B raw5016step0 raw5016step0Labels := by
      have hz : ∀ j, raw5016 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5016step0 = (fun i j => raw5016 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5016step0 raw5016; decide +kernel
      have hl : raw5016step0Labels = raw5016Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5016 raw5016Labels permutation520 hz
    mixedMoment B raw5016step0 raw5016step0Labels = mixedMoment B raw5016step1 raw5016step1Labels := by
      have hz : ∀ j, raw5016step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5016step1 = (fun i j => raw5016step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5016step1 raw5016step0; decide +kernel
      have hl : raw5016step1Labels = raw5016step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5016step0 raw5016step0Labels permutation80 hz
    mixedMoment B raw5016step1 raw5016step1Labels = mixedMoment B raw5016step2 raw5016step2Labels := by
      have ha : raw5016step2 = (fun i j => raw5016step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5016step2 raw5016step1; decide +kernel
      have hl : raw5016step2Labels = raw5016step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5016step1 raw5016step1Labels permutation10 permutation6
    _ = mixedMoment B node2726 node2726Labels := by rfl

def raw5017 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5017Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5017step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5017step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5017step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5017step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw5017step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5017 raw5017Labels = mixedMoment B node2208 node2208Labels := by
  calc
    mixedMoment B raw5017 raw5017Labels = mixedMoment B raw5017step0 raw5017step0Labels := by
      have hz : ∀ j, raw5017 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5017step0 = (fun i j => raw5017 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5017step0 raw5017; decide +kernel
      have hl : raw5017step0Labels = raw5017Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5017 raw5017Labels permutation434 hz
    mixedMoment B raw5017step0 raw5017step0Labels = mixedMoment B raw5017step1 raw5017step1Labels := by
      have hz : ∀ j, raw5017step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5017step1 = (fun i j => raw5017step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5017step1 raw5017step0; decide +kernel
      have hl : raw5017step1Labels = raw5017step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5017step0 raw5017step0Labels permutation80 hz
    mixedMoment B raw5017step1 raw5017step1Labels = mixedMoment B raw5017step2 raw5017step2Labels := by
      have ha : raw5017step2 = (fun i j => raw5017step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5017step2 raw5017step1; decide +kernel
      have hl : raw5017step2Labels = raw5017step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5017step1 raw5017step1Labels permutation10 permutation6
    _ = mixedMoment B node2208 node2208Labels := by rfl

def raw5018 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5018Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5018step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5018step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5018step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5018step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, -3, 3]]
def raw5018step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5018step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw5018step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5018step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw5018step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5018 raw5018Labels = mixedMoment B node2268 node2268Labels := by
  calc
    mixedMoment B raw5018 raw5018Labels = mixedMoment B raw5018step0 raw5018step0Labels := by
      have hz : ∀ j, raw5018 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5018step0 = (fun i j => raw5018 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5018step0 raw5018; decide +kernel
      have hl : raw5018step0Labels = raw5018Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5018 raw5018Labels permutation434 hz
    mixedMoment B raw5018step0 raw5018step0Labels = mixedMoment B raw5018step1 raw5018step1Labels := by
      have hz : ∀ j, raw5018step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5018step1 = (fun i j => raw5018step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5018step1 raw5018step0; decide +kernel
      have hl : raw5018step1Labels = raw5018step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5018step0 raw5018step0Labels permutation80 hz
    mixedMoment B raw5018step1 raw5018step1Labels = mixedMoment B raw5018step2 raw5018step2Labels := by
      have hz : ∀ j, raw5018step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5018step2 = (fun i j => raw5018step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5018step2 raw5018step1; decide +kernel
      have hl : raw5018step2Labels = raw5018step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5018step1 raw5018step1Labels permutation14 hz
    mixedMoment B raw5018step2 raw5018step2Labels = mixedMoment B raw5018step3 raw5018step3Labels := by
      have ha : raw5018step3 = (fun i j => raw5018step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5018step3 raw5018step2; decide +kernel
      have hl : raw5018step3Labels = raw5018step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5018step2 raw5018step2Labels permutation7 permutation6
    mixedMoment B raw5018step3 raw5018step3Labels = mixedMoment B raw5018step4 raw5018step4Labels := by
      have ha : raw5018step4 = -raw5018step3 := by apply Matrix.ext; change ∀ i j, raw5018step4 i j = -(raw5018step3 i j); unfold raw5018step4 raw5018step3; decide +kernel
      have hl : raw5018step4Labels = raw5018step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2268 node2268Labels := by rfl

def raw5019 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5019Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5019step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5019step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw5019step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5019step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw5019step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5019 raw5019Labels = mixedMoment B node2193 node2193Labels := by
  calc
    mixedMoment B raw5019 raw5019Labels = mixedMoment B raw5019step0 raw5019step0Labels := by
      have hz : ∀ j, raw5019 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5019step0 = (fun i j => raw5019 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5019step0 raw5019; decide +kernel
      have hl : raw5019step0Labels = raw5019Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5019 raw5019Labels permutation434 hz
    mixedMoment B raw5019step0 raw5019step0Labels = mixedMoment B raw5019step1 raw5019step1Labels := by
      have ha : raw5019step1 = (fun i j => raw5019step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5019step1 raw5019step0; decide +kernel
      have hl : raw5019step1Labels = raw5019step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5019step0 raw5019step0Labels permutation137 permutation6
    mixedMoment B raw5019step1 raw5019step1Labels = mixedMoment B raw5019step2 raw5019step2Labels := by
      have ha : raw5019step2 = -raw5019step1 := by apply Matrix.ext; change ∀ i j, raw5019step2 i j = -(raw5019step1 i j); unfold raw5019step2 raw5019step1; decide +kernel
      have hl : raw5019step2Labels = raw5019step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2193 node2193Labels := by rfl

def raw5020 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5020Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5020step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5020step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw5020step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5020step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw5020step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5020 raw5020Labels = mixedMoment B node2193 node2193Labels := by
  calc
    mixedMoment B raw5020 raw5020Labels = mixedMoment B raw5020step0 raw5020step0Labels := by
      have hz : ∀ j, raw5020 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5020step0 = (fun i j => raw5020 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5020step0 raw5020; decide +kernel
      have hl : raw5020step0Labels = raw5020Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5020 raw5020Labels permutation346 hz
    mixedMoment B raw5020step0 raw5020step0Labels = mixedMoment B raw5020step1 raw5020step1Labels := by
      have ha : raw5020step1 = (fun i j => raw5020step0 (permutation137 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5020step1 raw5020step0; decide +kernel
      have hl : raw5020step1Labels = raw5020step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5020step0 raw5020step0Labels permutation137 permutation6
    mixedMoment B raw5020step1 raw5020step1Labels = mixedMoment B raw5020step2 raw5020step2Labels := by
      have ha : raw5020step2 = -raw5020step1 := by apply Matrix.ext; change ∀ i j, raw5020step2 i j = -(raw5020step1 i j); unfold raw5020step2 raw5020step1; decide +kernel
      have hl : raw5020step2Labels = raw5020step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2193 node2193Labels := by rfl

def raw5021 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -3, 3]]
def raw5021Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -3, 3]]
def raw5021step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5021step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 2, 0], ![0, -3, 3]]
def raw5021step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5021step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-3, 1, 2]]
def raw5021step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5021step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw5021step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5021 raw5021Labels = mixedMoment B node2218 node2218Labels := by
  calc
    mixedMoment B raw5021 raw5021Labels = mixedMoment B raw5021step0 raw5021step0Labels := by
      have hz : ∀ j, raw5021 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5021step0 = (fun i j => raw5021 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5021step0 raw5021; decide +kernel
      have hl : raw5021step0Labels = raw5021Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5021 raw5021Labels permutation434 hz
    mixedMoment B raw5021step0 raw5021step0Labels = mixedMoment B raw5021step1 raw5021step1Labels := by
      have hz : ∀ j, raw5021step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5021step1 = (fun i j => raw5021step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5021step1 raw5021step0; decide +kernel
      have hl : raw5021step1Labels = raw5021step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5021step0 raw5021step0Labels permutation80 hz
    mixedMoment B raw5021step1 raw5021step1Labels = mixedMoment B raw5021step2 raw5021step2Labels := by
      have ha : raw5021step2 = (fun i j => raw5021step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5021step2 raw5021step1; decide +kernel
      have hl : raw5021step2Labels = raw5021step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5021step1 raw5021step1Labels permutation29 permutation6
    mixedMoment B raw5021step2 raw5021step2Labels = mixedMoment B raw5021step3 raw5021step3Labels := by
      have ha : raw5021step3 = -raw5021step2 := by apply Matrix.ext; change ∀ i j, raw5021step3 i j = -(raw5021step2 i j); unfold raw5021step3 raw5021step2; decide +kernel
      have hl : raw5021step3Labels = raw5021step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2218 node2218Labels := by rfl

def raw5022 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5022Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5022step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5022step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5022step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5022step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, -2, 3]]
def raw5022step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5022step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw5022step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5022step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw5022step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5022 raw5022Labels = mixedMoment B node2770 node2770Labels := by
  calc
    mixedMoment B raw5022 raw5022Labels = mixedMoment B raw5022step0 raw5022step0Labels := by
      have hz : ∀ j, raw5022 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5022step0 = (fun i j => raw5022 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5022step0 raw5022; decide +kernel
      have hl : raw5022step0Labels = raw5022Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5022 raw5022Labels permutation434 hz
    mixedMoment B raw5022step0 raw5022step0Labels = mixedMoment B raw5022step1 raw5022step1Labels := by
      have hz : ∀ j, raw5022step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5022step1 = (fun i j => raw5022step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5022step1 raw5022step0; decide +kernel
      have hl : raw5022step1Labels = raw5022step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5022step0 raw5022step0Labels permutation80 hz
    mixedMoment B raw5022step1 raw5022step1Labels = mixedMoment B raw5022step2 raw5022step2Labels := by
      have hz : ∀ j, raw5022step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5022step2 = (fun i j => raw5022step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5022step2 raw5022step1; decide +kernel
      have hl : raw5022step2Labels = raw5022step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5022step1 raw5022step1Labels permutation14 hz
    mixedMoment B raw5022step2 raw5022step2Labels = mixedMoment B raw5022step3 raw5022step3Labels := by
      have ha : raw5022step3 = (fun i j => raw5022step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5022step3 raw5022step2; decide +kernel
      have hl : raw5022step3Labels = raw5022step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5022step2 raw5022step2Labels permutation2 permutation7
    mixedMoment B raw5022step3 raw5022step3Labels = mixedMoment B raw5022step4 raw5022step4Labels := by
      have ha : raw5022step4 = raw5022step3 := by apply Matrix.ext; unfold raw5022step4 raw5022step3; decide +kernel
      have hl : raw5022step3Labels = labelEmbedding1 ∘ raw5022step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5022step3 raw5022step3Labels raw5022step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2770 node2770Labels := by rfl

def raw5023 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5023Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5023step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5023step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5023step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5023step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5023step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5023step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5023 raw5023Labels = mixedMoment B node2712 node2712Labels := by
  calc
    mixedMoment B raw5023 raw5023Labels = mixedMoment B raw5023step0 raw5023step0Labels := by
      have hz : ∀ j, raw5023 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5023step0 = (fun i j => raw5023 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5023step0 raw5023; decide +kernel
      have hl : raw5023step0Labels = raw5023Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5023 raw5023Labels permutation434 hz
    mixedMoment B raw5023step0 raw5023step0Labels = mixedMoment B raw5023step1 raw5023step1Labels := by
      have ha : raw5023step1 = (fun i j => raw5023step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5023step1 raw5023step0; decide +kernel
      have hl : raw5023step1Labels = raw5023step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5023step0 raw5023step0Labels permutation32 permutation7
    mixedMoment B raw5023step1 raw5023step1Labels = mixedMoment B raw5023step2 raw5023step2Labels := by
      have ha : raw5023step2 = raw5023step1 := by apply Matrix.ext; unfold raw5023step2 raw5023step1; decide +kernel
      have hl : raw5023step1Labels = labelEmbedding1 ∘ raw5023step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5023step1 raw5023step1Labels raw5023step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2712 node2712Labels := by rfl

def raw5024 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5024Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5024step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5024step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5024step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5024step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5024step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5024 raw5024Labels = mixedMoment B node2712 node2712Labels := by
  calc
    mixedMoment B raw5024 raw5024Labels = mixedMoment B raw5024step0 raw5024step0Labels := by
      have hz : ∀ j, raw5024 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5024step0 = (fun i j => raw5024 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5024step0 raw5024; decide +kernel
      have hl : raw5024step0Labels = raw5024Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5024 raw5024Labels permutation346 hz
    mixedMoment B raw5024step0 raw5024step0Labels = mixedMoment B raw5024step1 raw5024step1Labels := by
      have ha : raw5024step1 = (fun i j => raw5024step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5024step1 raw5024step0; decide +kernel
      have hl : raw5024step1Labels = raw5024step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5024step0 raw5024step0Labels permutation32 permutation7
    mixedMoment B raw5024step1 raw5024step1Labels = mixedMoment B raw5024step2 raw5024step2Labels := by
      have ha : raw5024step2 = raw5024step1 := by apply Matrix.ext; unfold raw5024step2 raw5024step1; decide +kernel
      have hl : raw5024step1Labels = labelEmbedding1 ∘ raw5024step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5024step1 raw5024step1Labels raw5024step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2712 node2712Labels := by rfl

def raw5025 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw5025Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw5025step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5025step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw5025step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5025step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw5025step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5025step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw5025step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5025 raw5025Labels = mixedMoment B node2734 node2734Labels := by
  calc
    mixedMoment B raw5025 raw5025Labels = mixedMoment B raw5025step0 raw5025step0Labels := by
      have hz : ∀ j, raw5025 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5025step0 = (fun i j => raw5025 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5025step0 raw5025; decide +kernel
      have hl : raw5025step0Labels = raw5025Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5025 raw5025Labels permutation434 hz
    mixedMoment B raw5025step0 raw5025step0Labels = mixedMoment B raw5025step1 raw5025step1Labels := by
      have hz : ∀ j, raw5025step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5025step1 = (fun i j => raw5025step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5025step1 raw5025step0; decide +kernel
      have hl : raw5025step1Labels = raw5025step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5025step0 raw5025step0Labels permutation80 hz
    mixedMoment B raw5025step1 raw5025step1Labels = mixedMoment B raw5025step2 raw5025step2Labels := by
      have ha : raw5025step2 = (fun i j => raw5025step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5025step2 raw5025step1; decide +kernel
      have hl : raw5025step2Labels = raw5025step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5025step1 raw5025step1Labels permutation8 permutation7
    mixedMoment B raw5025step2 raw5025step2Labels = mixedMoment B raw5025step3 raw5025step3Labels := by
      have ha : raw5025step3 = raw5025step2 := by apply Matrix.ext; unfold raw5025step3 raw5025step2; decide +kernel
      have hl : raw5025step2Labels = labelEmbedding1 ∘ raw5025step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5025step2 raw5025step2Labels raw5025step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2734 node2734Labels := by rfl

def raw5026 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw5026Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw5026step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5026step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw5026step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5026step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw5026step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5026step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw5026step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5026 raw5026Labels = mixedMoment B node2726 node2726Labels := by
  calc
    mixedMoment B raw5026 raw5026Labels = mixedMoment B raw5026step0 raw5026step0Labels := by
      have hz : ∀ j, raw5026 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5026step0 = (fun i j => raw5026 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5026step0 raw5026; decide +kernel
      have hl : raw5026step0Labels = raw5026Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5026 raw5026Labels permutation434 hz
    mixedMoment B raw5026step0 raw5026step0Labels = mixedMoment B raw5026step1 raw5026step1Labels := by
      have hz : ∀ j, raw5026step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5026step1 = (fun i j => raw5026step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5026step1 raw5026step0; decide +kernel
      have hl : raw5026step1Labels = raw5026step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5026step0 raw5026step0Labels permutation80 hz
    mixedMoment B raw5026step1 raw5026step1Labels = mixedMoment B raw5026step2 raw5026step2Labels := by
      have ha : raw5026step2 = (fun i j => raw5026step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5026step2 raw5026step1; decide +kernel
      have hl : raw5026step2Labels = raw5026step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5026step1 raw5026step1Labels permutation8 permutation7
    mixedMoment B raw5026step2 raw5026step2Labels = mixedMoment B raw5026step3 raw5026step3Labels := by
      have ha : raw5026step3 = raw5026step2 := by apply Matrix.ext; unfold raw5026step3 raw5026step2; decide +kernel
      have hl : raw5026step2Labels = labelEmbedding1 ∘ raw5026step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5026step2 raw5026step2Labels raw5026step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2726 node2726Labels := by rfl

def raw5027 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5027Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5027step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5027step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5027step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5027step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -2, 2], ![-3, 3, 0]]
def raw5027step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5027step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![3, -3, 0]]
def raw5027step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5027step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![3, -3, 0]]
def raw5027step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5027 raw5027Labels = mixedMoment B node3095 node3095Labels := by
  calc
    mixedMoment B raw5027 raw5027Labels = mixedMoment B raw5027step0 raw5027step0Labels := by
      have hz : ∀ j, raw5027 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5027step0 = (fun i j => raw5027 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5027step0 raw5027; decide +kernel
      have hl : raw5027step0Labels = raw5027Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5027 raw5027Labels permutation434 hz
    mixedMoment B raw5027step0 raw5027step0Labels = mixedMoment B raw5027step1 raw5027step1Labels := by
      have hz : ∀ j, raw5027step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5027step1 = (fun i j => raw5027step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5027step1 raw5027step0; decide +kernel
      have hl : raw5027step1Labels = raw5027step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5027step0 raw5027step0Labels permutation80 hz
    mixedMoment B raw5027step1 raw5027step1Labels = mixedMoment B raw5027step2 raw5027step2Labels := by
      have ha : raw5027step2 = (fun i j => raw5027step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5027step2 raw5027step1; decide +kernel
      have hl : raw5027step2Labels = raw5027step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5027step1 raw5027step1Labels permutation31 permutation7
    mixedMoment B raw5027step2 raw5027step2Labels = mixedMoment B raw5027step3 raw5027step3Labels := by
      have ha : raw5027step3 = -raw5027step2 := by apply Matrix.ext; change ∀ i j, raw5027step3 i j = -(raw5027step2 i j); unfold raw5027step3 raw5027step2; decide +kernel
      have hl : raw5027step3Labels = raw5027step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5027step3 raw5027step3Labels = mixedMoment B raw5027step4 raw5027step4Labels := by
      have ha : raw5027step4 = raw5027step3 := by apply Matrix.ext; unfold raw5027step4 raw5027step3; decide +kernel
      have hl : raw5027step3Labels = labelEmbedding1 ∘ raw5027step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5027step3 raw5027step3Labels raw5027step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3095 node3095Labels := by rfl

def raw5028 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5028Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5028step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5028step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5028step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5028step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5028step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5028 raw5028Labels = mixedMoment B node3031 node3031Labels := by
  calc
    mixedMoment B raw5028 raw5028Labels = mixedMoment B raw5028step0 raw5028step0Labels := by
      have hz : ∀ j, raw5028 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5028step0 = (fun i j => raw5028 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5028step0 raw5028; decide +kernel
      have hl : raw5028step0Labels = raw5028Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5028 raw5028Labels permutation434 hz
    mixedMoment B raw5028step0 raw5028step0Labels = mixedMoment B raw5028step1 raw5028step1Labels := by
      have ha : raw5028step1 = (fun i j => raw5028step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5028step1 raw5028step0; decide +kernel
      have hl : raw5028step1Labels = raw5028step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5028step0 raw5028step0Labels permutation32 permutation7
    mixedMoment B raw5028step1 raw5028step1Labels = mixedMoment B raw5028step2 raw5028step2Labels := by
      have ha : raw5028step2 = raw5028step1 := by apply Matrix.ext; unfold raw5028step2 raw5028step1; decide +kernel
      have hl : raw5028step1Labels = labelEmbedding1 ∘ raw5028step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5028step1 raw5028step1Labels raw5028step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3031 node3031Labels := by rfl

def raw5029 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5029Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5029step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5029step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5029step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5029step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5029step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5029 raw5029Labels = mixedMoment B node3031 node3031Labels := by
  calc
    mixedMoment B raw5029 raw5029Labels = mixedMoment B raw5029step0 raw5029step0Labels := by
      have hz : ∀ j, raw5029 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5029step0 = (fun i j => raw5029 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5029step0 raw5029; decide +kernel
      have hl : raw5029step0Labels = raw5029Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5029 raw5029Labels permutation346 hz
    mixedMoment B raw5029step0 raw5029step0Labels = mixedMoment B raw5029step1 raw5029step1Labels := by
      have ha : raw5029step1 = (fun i j => raw5029step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5029step1 raw5029step0; decide +kernel
      have hl : raw5029step1Labels = raw5029step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5029step0 raw5029step0Labels permutation32 permutation7
    mixedMoment B raw5029step1 raw5029step1Labels = mixedMoment B raw5029step2 raw5029step2Labels := by
      have ha : raw5029step2 = raw5029step1 := by apply Matrix.ext; unfold raw5029step2 raw5029step1; decide +kernel
      have hl : raw5029step1Labels = labelEmbedding1 ∘ raw5029step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5029step1 raw5029step1Labels raw5029step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3031 node3031Labels := by rfl

def raw5030 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw5030Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5030step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw5030step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5030step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw5030step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5030step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![3, -2, -1]]
def raw5030step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5030step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![3, -2, -1]]
def raw5030step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5030 raw5030Labels = mixedMoment B node3046 node3046Labels := by
  calc
    mixedMoment B raw5030 raw5030Labels = mixedMoment B raw5030step0 raw5030step0Labels := by
      have hz : ∀ j, raw5030 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5030step0 = (fun i j => raw5030 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5030step0 raw5030; decide +kernel
      have hl : raw5030step0Labels = raw5030Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5030 raw5030Labels permutation434 hz
    mixedMoment B raw5030step0 raw5030step0Labels = mixedMoment B raw5030step1 raw5030step1Labels := by
      have hz : ∀ j, raw5030step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5030step1 = (fun i j => raw5030step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5030step1 raw5030step0; decide +kernel
      have hl : raw5030step1Labels = raw5030step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5030step0 raw5030step0Labels permutation80 hz
    mixedMoment B raw5030step1 raw5030step1Labels = mixedMoment B raw5030step2 raw5030step2Labels := by
      have ha : raw5030step2 = (fun i j => raw5030step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5030step2 raw5030step1; decide +kernel
      have hl : raw5030step2Labels = raw5030step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5030step1 raw5030step1Labels permutation8 permutation7
    mixedMoment B raw5030step2 raw5030step2Labels = mixedMoment B raw5030step3 raw5030step3Labels := by
      have ha : raw5030step3 = raw5030step2 := by apply Matrix.ext; unfold raw5030step3 raw5030step2; decide +kernel
      have hl : raw5030step2Labels = labelEmbedding1 ∘ raw5030step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5030step2 raw5030step2Labels raw5030step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3046 node3046Labels := by rfl

def raw5031 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw5031Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw5031step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5031step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw5031step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5031step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-3, 2, 1]]
def raw5031step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5031step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw5031step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5031step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw5031step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5031 raw5031Labels = mixedMoment B node2734 node2734Labels := by
  calc
    mixedMoment B raw5031 raw5031Labels = mixedMoment B raw5031step0 raw5031step0Labels := by
      have hz : ∀ j, raw5031 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5031step0 = (fun i j => raw5031 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5031step0 raw5031; decide +kernel
      have hl : raw5031step0Labels = raw5031Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5031 raw5031Labels permutation434 hz
    mixedMoment B raw5031step0 raw5031step0Labels = mixedMoment B raw5031step1 raw5031step1Labels := by
      have hz : ∀ j, raw5031step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5031step1 = (fun i j => raw5031step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5031step1 raw5031step0; decide +kernel
      have hl : raw5031step1Labels = raw5031step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5031step0 raw5031step0Labels permutation80 hz
    mixedMoment B raw5031step1 raw5031step1Labels = mixedMoment B raw5031step2 raw5031step2Labels := by
      have ha : raw5031step2 = (fun i j => raw5031step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5031step2 raw5031step1; decide +kernel
      have hl : raw5031step2Labels = raw5031step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5031step1 raw5031step1Labels permutation31 permutation7
    mixedMoment B raw5031step2 raw5031step2Labels = mixedMoment B raw5031step3 raw5031step3Labels := by
      have ha : raw5031step3 = -raw5031step2 := by apply Matrix.ext; change ∀ i j, raw5031step3 i j = -(raw5031step2 i j); unfold raw5031step3 raw5031step2; decide +kernel
      have hl : raw5031step3Labels = raw5031step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5031step3 raw5031step3Labels = mixedMoment B raw5031step4 raw5031step4Labels := by
      have ha : raw5031step4 = raw5031step3 := by apply Matrix.ext; unfold raw5031step4 raw5031step3; decide +kernel
      have hl : raw5031step3Labels = labelEmbedding1 ∘ raw5031step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5031step3 raw5031step3Labels raw5031step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2734 node2734Labels := by rfl

def raw5032 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5032Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5032step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5032step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 3, 0]]
def raw5032step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5032step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw5032step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5032step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw5032step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5032 raw5032Labels = mixedMoment B node3082 node3082Labels := by
  calc
    mixedMoment B raw5032 raw5032Labels = mixedMoment B raw5032step0 raw5032step0Labels := by
      have hz : ∀ j, raw5032 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5032step0 = (fun i j => raw5032 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5032step0 raw5032; decide +kernel
      have hl : raw5032step0Labels = raw5032Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5032 raw5032Labels permutation434 hz
    mixedMoment B raw5032step0 raw5032step0Labels = mixedMoment B raw5032step1 raw5032step1Labels := by
      have ha : raw5032step1 = (fun i j => raw5032step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5032step1 raw5032step0; decide +kernel
      have hl : raw5032step1Labels = raw5032step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5032step0 raw5032step0Labels permutation149 permutation7
    mixedMoment B raw5032step1 raw5032step1Labels = mixedMoment B raw5032step2 raw5032step2Labels := by
      have ha : raw5032step2 = -raw5032step1 := by apply Matrix.ext; change ∀ i j, raw5032step2 i j = -(raw5032step1 i j); unfold raw5032step2 raw5032step1; decide +kernel
      have hl : raw5032step2Labels = raw5032step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5032step2 raw5032step2Labels = mixedMoment B raw5032step3 raw5032step3Labels := by
      have ha : raw5032step3 = raw5032step2 := by apply Matrix.ext; unfold raw5032step3 raw5032step2; decide +kernel
      have hl : raw5032step2Labels = labelEmbedding1 ∘ raw5032step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5032step2 raw5032step2Labels raw5032step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3082 node3082Labels := by rfl

def raw5033 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5033Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5033step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5033step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5033step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5033step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw5033step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5033step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw5033step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5033 raw5033Labels = mixedMoment B node3090 node3090Labels := by
  calc
    mixedMoment B raw5033 raw5033Labels = mixedMoment B raw5033step0 raw5033step0Labels := by
      have hz : ∀ j, raw5033 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5033step0 = (fun i j => raw5033 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5033step0 raw5033; decide +kernel
      have hl : raw5033step0Labels = raw5033Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5033 raw5033Labels permutation434 hz
    mixedMoment B raw5033step0 raw5033step0Labels = mixedMoment B raw5033step1 raw5033step1Labels := by
      have hz : ∀ j, raw5033step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5033step1 = (fun i j => raw5033step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5033step1 raw5033step0; decide +kernel
      have hl : raw5033step1Labels = raw5033step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5033step0 raw5033step0Labels permutation56 hz
    mixedMoment B raw5033step1 raw5033step1Labels = mixedMoment B raw5033step2 raw5033step2Labels := by
      have ha : raw5033step2 = (fun i j => raw5033step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5033step2 raw5033step1; decide +kernel
      have hl : raw5033step2Labels = raw5033step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5033step1 raw5033step1Labels permutation8 permutation7
    mixedMoment B raw5033step2 raw5033step2Labels = mixedMoment B raw5033step3 raw5033step3Labels := by
      have ha : raw5033step3 = raw5033step2 := by apply Matrix.ext; unfold raw5033step3 raw5033step2; decide +kernel
      have hl : raw5033step2Labels = labelEmbedding1 ∘ raw5033step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5033step2 raw5033step2Labels raw5033step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3090 node3090Labels := by rfl

def raw5034 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5034Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5034step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5034step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5034step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5034step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5034 raw5034Labels = mixedMoment B node3061 node3061Labels := by
  calc
    mixedMoment B raw5034 raw5034Labels = mixedMoment B raw5034step0 raw5034step0Labels := by
      have ha : raw5034step0 = (fun i j => raw5034 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5034step0 raw5034; decide +kernel
      have hl : raw5034step0Labels = raw5034Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5034 raw5034Labels permutation152 permutation7
    mixedMoment B raw5034step0 raw5034step0Labels = mixedMoment B raw5034step1 raw5034step1Labels := by
      have ha : raw5034step1 = raw5034step0 := by apply Matrix.ext; unfold raw5034step1 raw5034step0; decide +kernel
      have hl : raw5034step0Labels = labelEmbedding1 ∘ raw5034step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5034step0 raw5034step0Labels raw5034step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3061 node3061Labels := by rfl

def raw5035 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw5035Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5035step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw5035step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5035step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw5035step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5035step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5035step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5035step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5035step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5035 raw5035Labels = mixedMoment B node3031 node3031Labels := by
  calc
    mixedMoment B raw5035 raw5035Labels = mixedMoment B raw5035step0 raw5035step0Labels := by
      have hz : ∀ j, raw5035 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5035step0 = (fun i j => raw5035 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5035step0 raw5035; decide +kernel
      have hl : raw5035step0Labels = raw5035Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5035 raw5035Labels permutation434 hz
    mixedMoment B raw5035step0 raw5035step0Labels = mixedMoment B raw5035step1 raw5035step1Labels := by
      have ha : raw5035step1 = (fun i j => raw5035step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5035step1 raw5035step0; decide +kernel
      have hl : raw5035step1Labels = raw5035step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5035step0 raw5035step0Labels permutation149 permutation7
    mixedMoment B raw5035step1 raw5035step1Labels = mixedMoment B raw5035step2 raw5035step2Labels := by
      have ha : raw5035step2 = -raw5035step1 := by apply Matrix.ext; change ∀ i j, raw5035step2 i j = -(raw5035step1 i j); unfold raw5035step2 raw5035step1; decide +kernel
      have hl : raw5035step2Labels = raw5035step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5035step2 raw5035step2Labels = mixedMoment B raw5035step3 raw5035step3Labels := by
      have ha : raw5035step3 = raw5035step2 := by apply Matrix.ext; unfold raw5035step3 raw5035step2; decide +kernel
      have hl : raw5035step2Labels = labelEmbedding1 ∘ raw5035step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5035step2 raw5035step2Labels raw5035step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3031 node3031Labels := by rfl

def raw5036 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw5036Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5036step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw5036step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5036step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw5036step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5036step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5036step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5036step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5036step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5036 raw5036Labels = mixedMoment B node2712 node2712Labels := by
  calc
    mixedMoment B raw5036 raw5036Labels = mixedMoment B raw5036step0 raw5036step0Labels := by
      have hz : ∀ j, raw5036 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5036step0 = (fun i j => raw5036 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5036step0 raw5036; decide +kernel
      have hl : raw5036step0Labels = raw5036Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5036 raw5036Labels permutation434 hz
    mixedMoment B raw5036step0 raw5036step0Labels = mixedMoment B raw5036step1 raw5036step1Labels := by
      have ha : raw5036step1 = (fun i j => raw5036step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5036step1 raw5036step0; decide +kernel
      have hl : raw5036step1Labels = raw5036step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5036step0 raw5036step0Labels permutation149 permutation7
    mixedMoment B raw5036step1 raw5036step1Labels = mixedMoment B raw5036step2 raw5036step2Labels := by
      have ha : raw5036step2 = -raw5036step1 := by apply Matrix.ext; change ∀ i j, raw5036step2 i j = -(raw5036step1 i j); unfold raw5036step2 raw5036step1; decide +kernel
      have hl : raw5036step2Labels = raw5036step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5036step2 raw5036step2Labels = mixedMoment B raw5036step3 raw5036step3Labels := by
      have ha : raw5036step3 = raw5036step2 := by apply Matrix.ext; unfold raw5036step3 raw5036step2; decide +kernel
      have hl : raw5036step2Labels = labelEmbedding1 ∘ raw5036step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5036step2 raw5036step2Labels raw5036step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2712 node2712Labels := by rfl

def raw5037 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5037Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5037step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5037step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5037step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 3, 0]]
def raw5037step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5037step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw5037step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5037step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw5037step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5037 raw5037Labels = mixedMoment B node3082 node3082Labels := by
  calc
    mixedMoment B raw5037 raw5037Labels = mixedMoment B raw5037step0 raw5037step0Labels := by
      have hz : ∀ j, raw5037 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5037step0 = (fun i j => raw5037 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5037step0 raw5037; decide +kernel
      have hl : raw5037step0Labels = raw5037Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5037 raw5037Labels permutation346 hz
    mixedMoment B raw5037step0 raw5037step0Labels = mixedMoment B raw5037step1 raw5037step1Labels := by
      have ha : raw5037step1 = (fun i j => raw5037step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5037step1 raw5037step0; decide +kernel
      have hl : raw5037step1Labels = raw5037step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5037step0 raw5037step0Labels permutation149 permutation7
    mixedMoment B raw5037step1 raw5037step1Labels = mixedMoment B raw5037step2 raw5037step2Labels := by
      have ha : raw5037step2 = -raw5037step1 := by apply Matrix.ext; change ∀ i j, raw5037step2 i j = -(raw5037step1 i j); unfold raw5037step2 raw5037step1; decide +kernel
      have hl : raw5037step2Labels = raw5037step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5037step2 raw5037step2Labels = mixedMoment B raw5037step3 raw5037step3Labels := by
      have ha : raw5037step3 = raw5037step2 := by apply Matrix.ext; unfold raw5037step3 raw5037step2; decide +kernel
      have hl : raw5037step2Labels = labelEmbedding1 ∘ raw5037step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5037step2 raw5037step2Labels raw5037step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3082 node3082Labels := by rfl

def raw5038 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5038Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5038step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5038step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5038step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5038step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5038step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw5038step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5038step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw5038step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5038 raw5038Labels = mixedMoment B node3090 node3090Labels := by
  calc
    mixedMoment B raw5038 raw5038Labels = mixedMoment B raw5038step0 raw5038step0Labels := by
      have hz : ∀ j, raw5038 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5038step0 = (fun i j => raw5038 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5038step0 raw5038; decide +kernel
      have hl : raw5038step0Labels = raw5038Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5038 raw5038Labels permutation346 hz
    mixedMoment B raw5038step0 raw5038step0Labels = mixedMoment B raw5038step1 raw5038step1Labels := by
      have hz : ∀ j, raw5038step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5038step1 = (fun i j => raw5038step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5038step1 raw5038step0; decide +kernel
      have hl : raw5038step1Labels = raw5038step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5038step0 raw5038step0Labels permutation56 hz
    mixedMoment B raw5038step1 raw5038step1Labels = mixedMoment B raw5038step2 raw5038step2Labels := by
      have ha : raw5038step2 = (fun i j => raw5038step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5038step2 raw5038step1; decide +kernel
      have hl : raw5038step2Labels = raw5038step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5038step1 raw5038step1Labels permutation8 permutation7
    mixedMoment B raw5038step2 raw5038step2Labels = mixedMoment B raw5038step3 raw5038step3Labels := by
      have ha : raw5038step3 = raw5038step2 := by apply Matrix.ext; unfold raw5038step3 raw5038step2; decide +kernel
      have hl : raw5038step2Labels = labelEmbedding1 ∘ raw5038step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5038step2 raw5038step2Labels raw5038step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3090 node3090Labels := by rfl

def raw5039 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5039Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5039step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5039step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5039step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5039step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5039 raw5039Labels = mixedMoment B node3061 node3061Labels := by
  calc
    mixedMoment B raw5039 raw5039Labels = mixedMoment B raw5039step0 raw5039step0Labels := by
      have ha : raw5039step0 = (fun i j => raw5039 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5039step0 raw5039; decide +kernel
      have hl : raw5039step0Labels = raw5039Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5039 raw5039Labels permutation158 permutation7
    mixedMoment B raw5039step0 raw5039step0Labels = mixedMoment B raw5039step1 raw5039step1Labels := by
      have ha : raw5039step1 = raw5039step0 := by apply Matrix.ext; unfold raw5039step1 raw5039step0; decide +kernel
      have hl : raw5039step0Labels = labelEmbedding1 ∘ raw5039step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5039step0 raw5039step0Labels raw5039step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3061 node3061Labels := by rfl

def raw5040 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw5040Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 2, 0], ![-1, -2, 3]]
def raw5040step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5040step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw5040step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5040step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5040step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5040step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5040step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5040 raw5040Labels = mixedMoment B node3031 node3031Labels := by
  calc
    mixedMoment B raw5040 raw5040Labels = mixedMoment B raw5040step0 raw5040step0Labels := by
      have hz : ∀ j, raw5040 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5040step0 = (fun i j => raw5040 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5040step0 raw5040; decide +kernel
      have hl : raw5040step0Labels = raw5040Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5040 raw5040Labels permutation346 hz
    mixedMoment B raw5040step0 raw5040step0Labels = mixedMoment B raw5040step1 raw5040step1Labels := by
      have ha : raw5040step1 = (fun i j => raw5040step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5040step1 raw5040step0; decide +kernel
      have hl : raw5040step1Labels = raw5040step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5040step0 raw5040step0Labels permutation149 permutation7
    mixedMoment B raw5040step1 raw5040step1Labels = mixedMoment B raw5040step2 raw5040step2Labels := by
      have ha : raw5040step2 = -raw5040step1 := by apply Matrix.ext; change ∀ i j, raw5040step2 i j = -(raw5040step1 i j); unfold raw5040step2 raw5040step1; decide +kernel
      have hl : raw5040step2Labels = raw5040step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5040step2 raw5040step2Labels = mixedMoment B raw5040step3 raw5040step3Labels := by
      have ha : raw5040step3 = raw5040step2 := by apply Matrix.ext; unfold raw5040step3 raw5040step2; decide +kernel
      have hl : raw5040step2Labels = labelEmbedding1 ∘ raw5040step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5040step2 raw5040step2Labels raw5040step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3031 node3031Labels := by rfl

def raw5041 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw5041Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5041step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw5041step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5041step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw5041step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5041step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5041step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5041step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw5041step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5041 raw5041Labels = mixedMoment B node2712 node2712Labels := by
  calc
    mixedMoment B raw5041 raw5041Labels = mixedMoment B raw5041step0 raw5041step0Labels := by
      have hz : ∀ j, raw5041 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5041step0 = (fun i j => raw5041 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5041step0 raw5041; decide +kernel
      have hl : raw5041step0Labels = raw5041Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5041 raw5041Labels permutation346 hz
    mixedMoment B raw5041step0 raw5041step0Labels = mixedMoment B raw5041step1 raw5041step1Labels := by
      have ha : raw5041step1 = (fun i j => raw5041step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5041step1 raw5041step0; decide +kernel
      have hl : raw5041step1Labels = raw5041step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5041step0 raw5041step0Labels permutation149 permutation7
    mixedMoment B raw5041step1 raw5041step1Labels = mixedMoment B raw5041step2 raw5041step2Labels := by
      have ha : raw5041step2 = -raw5041step1 := by apply Matrix.ext; change ∀ i j, raw5041step2 i j = -(raw5041step1 i j); unfold raw5041step2 raw5041step1; decide +kernel
      have hl : raw5041step2Labels = raw5041step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5041step2 raw5041step2Labels = mixedMoment B raw5041step3 raw5041step3Labels := by
      have ha : raw5041step3 = raw5041step2 := by apply Matrix.ext; unfold raw5041step3 raw5041step2; decide +kernel
      have hl : raw5041step2Labels = labelEmbedding1 ∘ raw5041step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5041step2 raw5041step2Labels raw5041step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2712 node2712Labels := by rfl

def raw5042 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5042Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5042step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5042step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5042step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5042step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, -2, 3]]
def raw5042step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5042step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -2, -1], ![0, -1, 1], ![-3, 3, 0]]
def raw5042step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5042step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![3, -3, 0]]
def raw5042step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5042step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![3, -3, 0]]
def raw5042step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5042 raw5042Labels = mixedMoment B node3114 node3114Labels := by
  calc
    mixedMoment B raw5042 raw5042Labels = mixedMoment B raw5042step0 raw5042step0Labels := by
      have hz : ∀ j, raw5042 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5042step0 = (fun i j => raw5042 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5042step0 raw5042; decide +kernel
      have hl : raw5042step0Labels = raw5042Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5042 raw5042Labels permutation520 hz
    mixedMoment B raw5042step0 raw5042step0Labels = mixedMoment B raw5042step1 raw5042step1Labels := by
      have hz : ∀ j, raw5042step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5042step1 = (fun i j => raw5042step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5042step1 raw5042step0; decide +kernel
      have hl : raw5042step1Labels = raw5042step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5042step0 raw5042step0Labels permutation104 hz
    mixedMoment B raw5042step1 raw5042step1Labels = mixedMoment B raw5042step2 raw5042step2Labels := by
      have hz : ∀ j, raw5042step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw5042step2 = (fun i j => raw5042step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw5042step2 raw5042step1; decide +kernel
      have hl : raw5042step2Labels = raw5042step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5042step1 raw5042step1Labels permutation20 hz
    mixedMoment B raw5042step2 raw5042step2Labels = mixedMoment B raw5042step3 raw5042step3Labels := by
      have ha : raw5042step3 = (fun i j => raw5042step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5042step3 raw5042step2; decide +kernel
      have hl : raw5042step3Labels = raw5042step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5042step2 raw5042step2Labels permutation7 permutation7
    mixedMoment B raw5042step3 raw5042step3Labels = mixedMoment B raw5042step4 raw5042step4Labels := by
      have ha : raw5042step4 = -raw5042step3 := by apply Matrix.ext; change ∀ i j, raw5042step4 i j = -(raw5042step3 i j); unfold raw5042step4 raw5042step3; decide +kernel
      have hl : raw5042step4Labels = raw5042step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5042step4 raw5042step4Labels = mixedMoment B raw5042step5 raw5042step5Labels := by
      have ha : raw5042step5 = raw5042step4 := by apply Matrix.ext; unfold raw5042step5 raw5042step4; decide +kernel
      have hl : raw5042step4Labels = labelEmbedding1 ∘ raw5042step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5042step4 raw5042step4Labels raw5042step5Labels labelEmbedding1 hl
    _ = mixedMoment B node3114 node3114Labels := by rfl

def raw5043 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5043Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5043step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5043step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5043step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5043step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5043step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, -2, 3]]
def raw5043step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5043step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![1, 2, -3], ![-1, -2, 3]]
def raw5043step3Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5043step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, 2, 1], ![3, -2, -1]]
def raw5043step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5043step5 : Matrix (Fin 2) (Fin 3) ℤ := ![![-3, 2, 1], ![3, -2, -1]]
def raw5043step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5043 raw5043Labels = mixedMoment B node3126 node3126Labels := by
  calc
    mixedMoment B raw5043 raw5043Labels = mixedMoment B raw5043step0 raw5043step0Labels := by
      have hz : ∀ j, raw5043 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5043step0 = (fun i j => raw5043 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5043step0 raw5043; decide +kernel
      have hl : raw5043step0Labels = raw5043Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5043 raw5043Labels permutation520 hz
    mixedMoment B raw5043step0 raw5043step0Labels = mixedMoment B raw5043step1 raw5043step1Labels := by
      have hz : ∀ j, raw5043step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5043step1 = (fun i j => raw5043step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5043step1 raw5043step0; decide +kernel
      have hl : raw5043step1Labels = raw5043step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5043step0 raw5043step0Labels permutation104 hz
    mixedMoment B raw5043step1 raw5043step1Labels = mixedMoment B raw5043step2 raw5043step2Labels := by
      have hz : ∀ j, raw5043step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw5043step2 = (fun i j => raw5043step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw5043step2 raw5043step1; decide +kernel
      have hl : raw5043step2Labels = raw5043step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5043step1 raw5043step1Labels permutation20 hz
    mixedMoment B raw5043step2 raw5043step2Labels = mixedMoment B raw5043step3 raw5043step3Labels := by
      have hz : ∀ j, raw5043step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw5043step3 = (fun i j => raw5043step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw5043step3 raw5043step2; decide +kernel
      have hl : raw5043step3Labels = raw5043step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5043step2 raw5043step2Labels permutation4 hz
    mixedMoment B raw5043step3 raw5043step3Labels = mixedMoment B raw5043step4 raw5043step4Labels := by
      have ha : raw5043step4 = (fun i j => raw5043step3 (permutation0 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5043step4 raw5043step3; decide +kernel
      have hl : raw5043step4Labels = raw5043step3Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5043step3 raw5043step3Labels permutation0 permutation7
    mixedMoment B raw5043step4 raw5043step4Labels = mixedMoment B raw5043step5 raw5043step5Labels := by
      have ha : raw5043step5 = raw5043step4 := by apply Matrix.ext; unfold raw5043step5 raw5043step4; decide +kernel
      have hl : raw5043step4Labels = labelEmbedding1 ∘ raw5043step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5043step4 raw5043step4Labels raw5043step5Labels labelEmbedding1 hl
    _ = mixedMoment B node3126 node3126Labels := by rfl

def raw5044 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5044Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5044step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5044step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5044step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5044step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5044step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw5044step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5044step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw5044step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5044 raw5044Labels = mixedMoment B node3090 node3090Labels := by
  calc
    mixedMoment B raw5044 raw5044Labels = mixedMoment B raw5044step0 raw5044step0Labels := by
      have hz : ∀ j, raw5044 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5044step0 = (fun i j => raw5044 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5044step0 raw5044; decide +kernel
      have hl : raw5044step0Labels = raw5044Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5044 raw5044Labels permutation520 hz
    mixedMoment B raw5044step0 raw5044step0Labels = mixedMoment B raw5044step1 raw5044step1Labels := by
      have hz : ∀ j, raw5044step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5044step1 = (fun i j => raw5044step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5044step1 raw5044step0; decide +kernel
      have hl : raw5044step1Labels = raw5044step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5044step0 raw5044step0Labels permutation104 hz
    mixedMoment B raw5044step1 raw5044step1Labels = mixedMoment B raw5044step2 raw5044step2Labels := by
      have ha : raw5044step2 = (fun i j => raw5044step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5044step2 raw5044step1; decide +kernel
      have hl : raw5044step2Labels = raw5044step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5044step1 raw5044step1Labels permutation8 permutation7
    mixedMoment B raw5044step2 raw5044step2Labels = mixedMoment B raw5044step3 raw5044step3Labels := by
      have ha : raw5044step3 = raw5044step2 := by apply Matrix.ext; unfold raw5044step3 raw5044step2; decide +kernel
      have hl : raw5044step2Labels = labelEmbedding1 ∘ raw5044step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5044step2 raw5044step2Labels raw5044step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3090 node3090Labels := by rfl

def raw5045 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5045Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5045step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5045step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5045step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5045step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5045step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw5045step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5045step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw5045step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5045 raw5045Labels = mixedMoment B node3090 node3090Labels := by
  calc
    mixedMoment B raw5045 raw5045Labels = mixedMoment B raw5045step0 raw5045step0Labels := by
      have hz : ∀ j, raw5045 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5045step0 = (fun i j => raw5045 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5045step0 raw5045; decide +kernel
      have hl : raw5045step0Labels = raw5045Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5045 raw5045Labels permutation520 hz
    mixedMoment B raw5045step0 raw5045step0Labels = mixedMoment B raw5045step1 raw5045step1Labels := by
      have hz : ∀ j, raw5045step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5045step1 = (fun i j => raw5045step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5045step1 raw5045step0; decide +kernel
      have hl : raw5045step1Labels = raw5045step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5045step0 raw5045step0Labels permutation80 hz
    mixedMoment B raw5045step1 raw5045step1Labels = mixedMoment B raw5045step2 raw5045step2Labels := by
      have ha : raw5045step2 = (fun i j => raw5045step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5045step2 raw5045step1; decide +kernel
      have hl : raw5045step2Labels = raw5045step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5045step1 raw5045step1Labels permutation8 permutation7
    mixedMoment B raw5045step2 raw5045step2Labels = mixedMoment B raw5045step3 raw5045step3Labels := by
      have ha : raw5045step3 = raw5045step2 := by apply Matrix.ext; unfold raw5045step3 raw5045step2; decide +kernel
      have hl : raw5045step2Labels = labelEmbedding1 ∘ raw5045step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5045step2 raw5045step2Labels raw5045step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3090 node3090Labels := by rfl

def raw5046 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw5046Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5046step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw5046step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5046step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, -1, 3]]
def raw5046step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5046step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, -1, 3]]
def raw5046step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5046step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-3, 2, 1]]
def raw5046step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5046step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw5046step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5046step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw5046step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5046 raw5046Labels = mixedMoment B node2770 node2770Labels := by
  calc
    mixedMoment B raw5046 raw5046Labels = mixedMoment B raw5046step0 raw5046step0Labels := by
      have hz : ∀ j, raw5046 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5046step0 = (fun i j => raw5046 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5046step0 raw5046; decide +kernel
      have hl : raw5046step0Labels = raw5046Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5046 raw5046Labels permutation520 hz
    mixedMoment B raw5046step0 raw5046step0Labels = mixedMoment B raw5046step1 raw5046step1Labels := by
      have hz : ∀ j, raw5046step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5046step1 = (fun i j => raw5046step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5046step1 raw5046step0; decide +kernel
      have hl : raw5046step1Labels = raw5046step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5046step0 raw5046step0Labels permutation104 hz
    mixedMoment B raw5046step1 raw5046step1Labels = mixedMoment B raw5046step2 raw5046step2Labels := by
      have hz : ∀ j, raw5046step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw5046step2 = (fun i j => raw5046step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw5046step2 raw5046step1; decide +kernel
      have hl : raw5046step2Labels = raw5046step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5046step1 raw5046step1Labels permutation20 hz
    mixedMoment B raw5046step2 raw5046step2Labels = mixedMoment B raw5046step3 raw5046step3Labels := by
      have ha : raw5046step3 = (fun i j => raw5046step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5046step3 raw5046step2; decide +kernel
      have hl : raw5046step3Labels = raw5046step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5046step2 raw5046step2Labels permutation7 permutation7
    mixedMoment B raw5046step3 raw5046step3Labels = mixedMoment B raw5046step4 raw5046step4Labels := by
      have ha : raw5046step4 = -raw5046step3 := by apply Matrix.ext; change ∀ i j, raw5046step4 i j = -(raw5046step3 i j); unfold raw5046step4 raw5046step3; decide +kernel
      have hl : raw5046step4Labels = raw5046step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5046step4 raw5046step4Labels = mixedMoment B raw5046step5 raw5046step5Labels := by
      have ha : raw5046step5 = raw5046step4 := by apply Matrix.ext; unfold raw5046step5 raw5046step4; decide +kernel
      have hl : raw5046step4Labels = labelEmbedding1 ∘ raw5046step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5046step4 raw5046step4Labels raw5046step5Labels labelEmbedding1 hl
    _ = mixedMoment B node2770 node2770Labels := by rfl

def raw5047 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5047Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5047step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5047step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5047step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5047step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5047step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -3, 0]]
def raw5047step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5047step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -3, 0]]
def raw5047step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5047 raw5047Labels = mixedMoment B node3215 node3215Labels := by
  calc
    mixedMoment B raw5047 raw5047Labels = mixedMoment B raw5047step0 raw5047step0Labels := by
      have hz : ∀ j, raw5047 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5047step0 = (fun i j => raw5047 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5047step0 raw5047; decide +kernel
      have hl : raw5047step0Labels = raw5047Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5047 raw5047Labels permutation434 hz
    mixedMoment B raw5047step0 raw5047step0Labels = mixedMoment B raw5047step1 raw5047step1Labels := by
      have hz : ∀ j, raw5047step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5047step1 = (fun i j => raw5047step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5047step1 raw5047step0; decide +kernel
      have hl : raw5047step1Labels = raw5047step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5047step0 raw5047step0Labels permutation80 hz
    mixedMoment B raw5047step1 raw5047step1Labels = mixedMoment B raw5047step2 raw5047step2Labels := by
      have ha : raw5047step2 = (fun i j => raw5047step1 (permutation29 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5047step2 raw5047step1; decide +kernel
      have hl : raw5047step2Labels = raw5047step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5047step1 raw5047step1Labels permutation29 permutation5
    mixedMoment B raw5047step2 raw5047step2Labels = mixedMoment B raw5047step3 raw5047step3Labels := by
      have ha : raw5047step3 = raw5047step2 := by apply Matrix.ext; unfold raw5047step3 raw5047step2; decide +kernel
      have hl : raw5047step2Labels = labelEmbedding1 ∘ raw5047step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5047step2 raw5047step2Labels raw5047step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3215 node3215Labels := by rfl

def raw5048 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5048Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5048step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5048step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5048step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5048step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5048step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, -3, 3]]
def raw5048step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5048step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![3, -3, 0]]
def raw5048step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5048step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![3, -3, 0]]
def raw5048step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5048 raw5048Labels = mixedMoment B node3114 node3114Labels := by
  calc
    mixedMoment B raw5048 raw5048Labels = mixedMoment B raw5048step0 raw5048step0Labels := by
      have hz : ∀ j, raw5048 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5048step0 = (fun i j => raw5048 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5048step0 raw5048; decide +kernel
      have hl : raw5048step0Labels = raw5048Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5048 raw5048Labels permutation434 hz
    mixedMoment B raw5048step0 raw5048step0Labels = mixedMoment B raw5048step1 raw5048step1Labels := by
      have hz : ∀ j, raw5048step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5048step1 = (fun i j => raw5048step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5048step1 raw5048step0; decide +kernel
      have hl : raw5048step1Labels = raw5048step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5048step0 raw5048step0Labels permutation80 hz
    mixedMoment B raw5048step1 raw5048step1Labels = mixedMoment B raw5048step2 raw5048step2Labels := by
      have hz : ∀ j, raw5048step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5048step2 = (fun i j => raw5048step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5048step2 raw5048step1; decide +kernel
      have hl : raw5048step2Labels = raw5048step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5048step1 raw5048step1Labels permutation14 hz
    mixedMoment B raw5048step2 raw5048step2Labels = mixedMoment B raw5048step3 raw5048step3Labels := by
      have ha : raw5048step3 = (fun i j => raw5048step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5048step3 raw5048step2; decide +kernel
      have hl : raw5048step3Labels = raw5048step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5048step2 raw5048step2Labels permutation2 permutation7
    mixedMoment B raw5048step3 raw5048step3Labels = mixedMoment B raw5048step4 raw5048step4Labels := by
      have ha : raw5048step4 = raw5048step3 := by apply Matrix.ext; unfold raw5048step4 raw5048step3; decide +kernel
      have hl : raw5048step3Labels = labelEmbedding1 ∘ raw5048step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5048step3 raw5048step3Labels raw5048step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3114 node3114Labels := by rfl

def raw5049 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5049Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5049step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5049step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw5049step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5049step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw5049step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5049 raw5049Labels = mixedMoment B node3082 node3082Labels := by
  calc
    mixedMoment B raw5049 raw5049Labels = mixedMoment B raw5049step0 raw5049step0Labels := by
      have hz : ∀ j, raw5049 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5049step0 = (fun i j => raw5049 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5049step0 raw5049; decide +kernel
      have hl : raw5049step0Labels = raw5049Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5049 raw5049Labels permutation434 hz
    mixedMoment B raw5049step0 raw5049step0Labels = mixedMoment B raw5049step1 raw5049step1Labels := by
      have ha : raw5049step1 = (fun i j => raw5049step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5049step1 raw5049step0; decide +kernel
      have hl : raw5049step1Labels = raw5049step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5049step0 raw5049step0Labels permutation32 permutation7
    mixedMoment B raw5049step1 raw5049step1Labels = mixedMoment B raw5049step2 raw5049step2Labels := by
      have ha : raw5049step2 = raw5049step1 := by apply Matrix.ext; unfold raw5049step2 raw5049step1; decide +kernel
      have hl : raw5049step1Labels = labelEmbedding1 ∘ raw5049step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5049step1 raw5049step1Labels raw5049step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3082 node3082Labels := by rfl

def raw5050 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5050Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5050step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5050step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw5050step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5050step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw5050step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5050 raw5050Labels = mixedMoment B node3082 node3082Labels := by
  calc
    mixedMoment B raw5050 raw5050Labels = mixedMoment B raw5050step0 raw5050step0Labels := by
      have hz : ∀ j, raw5050 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5050step0 = (fun i j => raw5050 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5050step0 raw5050; decide +kernel
      have hl : raw5050step0Labels = raw5050Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5050 raw5050Labels permutation346 hz
    mixedMoment B raw5050step0 raw5050step0Labels = mixedMoment B raw5050step1 raw5050step1Labels := by
      have ha : raw5050step1 = (fun i j => raw5050step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5050step1 raw5050step0; decide +kernel
      have hl : raw5050step1Labels = raw5050step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5050step0 raw5050step0Labels permutation32 permutation7
    mixedMoment B raw5050step1 raw5050step1Labels = mixedMoment B raw5050step2 raw5050step2Labels := by
      have ha : raw5050step2 = raw5050step1 := by apply Matrix.ext; unfold raw5050step2 raw5050step1; decide +kernel
      have hl : raw5050step1Labels = labelEmbedding1 ∘ raw5050step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5050step1 raw5050step1Labels raw5050step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3082 node3082Labels := by rfl

def raw5051 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -3, 3]]
def raw5051Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -3, 3]]
def raw5051step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5051step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-2, 2, 0], ![0, -3, 3]]
def raw5051step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5051step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![3, -3, 0]]
def raw5051step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5051step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![3, -3, 0]]
def raw5051step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5051 raw5051Labels = mixedMoment B node3095 node3095Labels := by
  calc
    mixedMoment B raw5051 raw5051Labels = mixedMoment B raw5051step0 raw5051step0Labels := by
      have hz : ∀ j, raw5051 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5051step0 = (fun i j => raw5051 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5051step0 raw5051; decide +kernel
      have hl : raw5051step0Labels = raw5051Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5051 raw5051Labels permutation434 hz
    mixedMoment B raw5051step0 raw5051step0Labels = mixedMoment B raw5051step1 raw5051step1Labels := by
      have hz : ∀ j, raw5051step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5051step1 = (fun i j => raw5051step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5051step1 raw5051step0; decide +kernel
      have hl : raw5051step1Labels = raw5051step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5051step0 raw5051step0Labels permutation80 hz
    mixedMoment B raw5051step1 raw5051step1Labels = mixedMoment B raw5051step2 raw5051step2Labels := by
      have ha : raw5051step2 = (fun i j => raw5051step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5051step2 raw5051step1; decide +kernel
      have hl : raw5051step2Labels = raw5051step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5051step1 raw5051step1Labels permutation8 permutation7
    mixedMoment B raw5051step2 raw5051step2Labels = mixedMoment B raw5051step3 raw5051step3Labels := by
      have ha : raw5051step3 = raw5051step2 := by apply Matrix.ext; unfold raw5051step3 raw5051step2; decide +kernel
      have hl : raw5051step2Labels = labelEmbedding1 ∘ raw5051step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5051step2 raw5051step2Labels raw5051step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3095 node3095Labels := by rfl

def raw5052 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5052Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5052step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5052step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5052step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5052step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5052step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw5052step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5052 raw5052Labels = mixedMoment B node3545 node3545Labels := by
  calc
    mixedMoment B raw5052 raw5052Labels = mixedMoment B raw5052step0 raw5052step0Labels := by
      have hz : ∀ j, raw5052 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5052step0 = (fun i j => raw5052 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5052step0 raw5052; decide +kernel
      have hl : raw5052step0Labels = raw5052Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5052 raw5052Labels permutation434 hz
    mixedMoment B raw5052step0 raw5052step0Labels = mixedMoment B raw5052step1 raw5052step1Labels := by
      have hz : ∀ j, raw5052step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5052step1 = (fun i j => raw5052step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5052step1 raw5052step0; decide +kernel
      have hl : raw5052step1Labels = raw5052step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5052step0 raw5052step0Labels permutation80 hz
    mixedMoment B raw5052step1 raw5052step1Labels = mixedMoment B raw5052step2 raw5052step2Labels := by
      have ha : raw5052step2 = (fun i j => raw5052step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5052step2 raw5052step1; decide +kernel
      have hl : raw5052step2Labels = raw5052step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5052step1 raw5052step1Labels permutation29 permutation4
    _ = mixedMoment B node3545 node3545Labels := by rfl

def raw5053 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5053Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5053step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5053step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5053step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5053step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5053step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-2, 2, 0], ![-2, -1, 3]]
def raw5053step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5053step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw5053step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5053 raw5053Labels = mixedMoment B node2065 node2065Labels := by
  calc
    mixedMoment B raw5053 raw5053Labels = mixedMoment B raw5053step0 raw5053step0Labels := by
      have hz : ∀ j, raw5053 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5053step0 = (fun i j => raw5053 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5053step0 raw5053; decide +kernel
      have hl : raw5053step0Labels = raw5053Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5053 raw5053Labels permutation434 hz
    mixedMoment B raw5053step0 raw5053step0Labels = mixedMoment B raw5053step1 raw5053step1Labels := by
      have hz : ∀ j, raw5053step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5053step1 = (fun i j => raw5053step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5053step1 raw5053step0; decide +kernel
      have hl : raw5053step1Labels = raw5053step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5053step0 raw5053step0Labels permutation80 hz
    mixedMoment B raw5053step1 raw5053step1Labels = mixedMoment B raw5053step2 raw5053step2Labels := by
      have ha : raw5053step2 = (fun i j => raw5053step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5053step2 raw5053step1; decide +kernel
      have hl : raw5053step2Labels = raw5053step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5053step1 raw5053step1Labels permutation10 permutation4
    mixedMoment B raw5053step2 raw5053step2Labels = mixedMoment B raw5053step3 raw5053step3Labels := by
      have ha : raw5053step3 = -raw5053step2 := by apply Matrix.ext; change ∀ i j, raw5053step3 i j = -(raw5053step2 i j); unfold raw5053step3 raw5053step2; decide +kernel
      have hl : raw5053step3Labels = raw5053step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2065 node2065Labels := by rfl

def raw5054 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5054Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5054step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5054step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5054step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw5054step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5054step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw5054step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5054 raw5054Labels = mixedMoment B node2052 node2052Labels := by
  calc
    mixedMoment B raw5054 raw5054Labels = mixedMoment B raw5054step0 raw5054step0Labels := by
      have hz : ∀ j, raw5054 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5054step0 = (fun i j => raw5054 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5054step0 raw5054; decide +kernel
      have hl : raw5054step0Labels = raw5054Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5054 raw5054Labels permutation434 hz
    mixedMoment B raw5054step0 raw5054step0Labels = mixedMoment B raw5054step1 raw5054step1Labels := by
      have ha : raw5054step1 = (fun i j => raw5054step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5054step1 raw5054step0; decide +kernel
      have hl : raw5054step1Labels = raw5054step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5054step0 raw5054step0Labels permutation44 permutation4
    mixedMoment B raw5054step1 raw5054step1Labels = mixedMoment B raw5054step2 raw5054step2Labels := by
      have ha : raw5054step2 = -raw5054step1 := by apply Matrix.ext; change ∀ i j, raw5054step2 i j = -(raw5054step1 i j); unfold raw5054step2 raw5054step1; decide +kernel
      have hl : raw5054step2Labels = raw5054step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2052 node2052Labels := by rfl

def raw5055 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5055Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5055step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5055step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw5055step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5055step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw5055step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5055 raw5055Labels = mixedMoment B node2052 node2052Labels := by
  calc
    mixedMoment B raw5055 raw5055Labels = mixedMoment B raw5055step0 raw5055step0Labels := by
      have hz : ∀ j, raw5055 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5055step0 = (fun i j => raw5055 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5055step0 raw5055; decide +kernel
      have hl : raw5055step0Labels = raw5055Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5055 raw5055Labels permutation346 hz
    mixedMoment B raw5055step0 raw5055step0Labels = mixedMoment B raw5055step1 raw5055step1Labels := by
      have ha : raw5055step1 = (fun i j => raw5055step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5055step1 raw5055step0; decide +kernel
      have hl : raw5055step1Labels = raw5055step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5055step0 raw5055step0Labels permutation44 permutation4
    mixedMoment B raw5055step1 raw5055step1Labels = mixedMoment B raw5055step2 raw5055step2Labels := by
      have ha : raw5055step2 = -raw5055step1 := by apply Matrix.ext; change ∀ i j, raw5055step2 i j = -(raw5055step1 i j); unfold raw5055step2 raw5055step1; decide +kernel
      have hl : raw5055step2Labels = raw5055step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2052 node2052Labels := by rfl

def raw5056 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5056Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5056step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5056step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5056step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5056step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5056step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, -2, 3]]
def raw5056step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5056step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, 1, 0], ![-2, -1, 3]]
def raw5056step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5056step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![2, 1, -3]]
def raw5056step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5056 raw5056Labels = mixedMoment B node2292 node2292Labels := by
  calc
    mixedMoment B raw5056 raw5056Labels = mixedMoment B raw5056step0 raw5056step0Labels := by
      have hz : ∀ j, raw5056 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5056step0 = (fun i j => raw5056 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5056step0 raw5056; decide +kernel
      have hl : raw5056step0Labels = raw5056Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5056 raw5056Labels permutation520 hz
    mixedMoment B raw5056step0 raw5056step0Labels = mixedMoment B raw5056step1 raw5056step1Labels := by
      have hz : ∀ j, raw5056step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5056step1 = (fun i j => raw5056step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5056step1 raw5056step0; decide +kernel
      have hl : raw5056step1Labels = raw5056step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5056step0 raw5056step0Labels permutation104 hz
    mixedMoment B raw5056step1 raw5056step1Labels = mixedMoment B raw5056step2 raw5056step2Labels := by
      have hz : ∀ j, raw5056step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw5056step2 = (fun i j => raw5056step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw5056step2 raw5056step1; decide +kernel
      have hl : raw5056step2Labels = raw5056step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5056step1 raw5056step1Labels permutation20 hz
    mixedMoment B raw5056step2 raw5056step2Labels = mixedMoment B raw5056step3 raw5056step3Labels := by
      have ha : raw5056step3 = (fun i j => raw5056step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5056step3 raw5056step2; decide +kernel
      have hl : raw5056step3Labels = raw5056step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5056step2 raw5056step2Labels permutation2 permutation4
    mixedMoment B raw5056step3 raw5056step3Labels = mixedMoment B raw5056step4 raw5056step4Labels := by
      have ha : raw5056step4 = -raw5056step3 := by apply Matrix.ext; change ∀ i j, raw5056step4 i j = -(raw5056step3 i j); unfold raw5056step4 raw5056step3; decide +kernel
      have hl : raw5056step4Labels = raw5056step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2292 node2292Labels := by rfl

def raw5057 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5057Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5057step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5057step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5057step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5057step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5057step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw5057step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5057 raw5057Labels = mixedMoment B node2056 node2056Labels := by
  calc
    mixedMoment B raw5057 raw5057Labels = mixedMoment B raw5057step0 raw5057step0Labels := by
      have hz : ∀ j, raw5057 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5057step0 = (fun i j => raw5057 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5057step0 raw5057; decide +kernel
      have hl : raw5057step0Labels = raw5057Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5057 raw5057Labels permutation434 hz
    mixedMoment B raw5057step0 raw5057step0Labels = mixedMoment B raw5057step1 raw5057step1Labels := by
      have hz : ∀ j, raw5057step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5057step1 = (fun i j => raw5057step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5057step1 raw5057step0; decide +kernel
      have hl : raw5057step1Labels = raw5057step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5057step0 raw5057step0Labels permutation80 hz
    mixedMoment B raw5057step1 raw5057step1Labels = mixedMoment B raw5057step2 raw5057step2Labels := by
      have ha : raw5057step2 = (fun i j => raw5057step1 (permutation29 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5057step2 raw5057step1; decide +kernel
      have hl : raw5057step2Labels = raw5057step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5057step1 raw5057step1Labels permutation29 permutation4
    _ = mixedMoment B node2056 node2056Labels := by rfl

def raw5058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw5058Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5058step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw5058step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5058step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw5058step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5058step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![3, -1, -2]]
def raw5058step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5058step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 1, 0], ![-2, 0, 2]]
def raw5058step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5058step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw5058step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5058 raw5058Labels = mixedMoment B node5308 node5308Labels := by
  calc
    mixedMoment B raw5058 raw5058Labels = mixedMoment B raw5058step0 raw5058step0Labels := by
      have hz : ∀ j, raw5058 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5058step0 = (fun i j => raw5058 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5058step0 raw5058; decide +kernel
      have hl : raw5058step0Labels = raw5058Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5058 raw5058Labels permutation520 hz
    mixedMoment B raw5058step0 raw5058step0Labels = mixedMoment B raw5058step1 raw5058step1Labels := by
      have hz : ∀ j, raw5058step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5058step1 = (fun i j => raw5058step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5058step1 raw5058step0; decide +kernel
      have hl : raw5058step1Labels = raw5058step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5058step0 raw5058step0Labels permutation104 hz
    mixedMoment B raw5058step1 raw5058step1Labels = mixedMoment B raw5058step2 raw5058step2Labels := by
      have hz : ∀ j, raw5058step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw5058step2 = (fun i j => raw5058step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw5058step2 raw5058step1; decide +kernel
      have hl : raw5058step2Labels = raw5058step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5058step1 raw5058step1Labels permutation20 hz
    mixedMoment B raw5058step2 raw5058step2Labels = mixedMoment B raw5058step3 raw5058step3Labels := by
      have ha : raw5058step3 = (fun i j => raw5058step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5058step3 raw5058step2; decide +kernel
      have hl : raw5058step3Labels = raw5058step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5058step2 raw5058step2Labels permutation7 permutation2
    mixedMoment B raw5058step3 raw5058step3Labels = mixedMoment B raw5058step4 raw5058step4Labels := by
      have ha : raw5058step4 = -raw5058step3 := by apply Matrix.ext; change ∀ i j, raw5058step4 i j = -(raw5058step3 i j); unfold raw5058step4 raw5058step3; decide +kernel
      have hl : raw5058step4Labels = raw5058step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5308 node5308Labels := by rfl

def raw5059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw5059Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw5059step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5059step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2]]
def raw5059step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5059step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![3, -1, -2]]
def raw5059step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5059step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 1, 0], ![-2, 0, 2]]
def raw5059step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5059step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw5059step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5059 raw5059Labels = mixedMoment B node5308 node5308Labels := by
  calc
    mixedMoment B raw5059 raw5059Labels = mixedMoment B raw5059step0 raw5059step0Labels := by
      have hz : ∀ j, raw5059 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5059step0 = (fun i j => raw5059 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5059step0 raw5059; decide +kernel
      have hl : raw5059step0Labels = raw5059Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5059 raw5059Labels permutation520 hz
    mixedMoment B raw5059step0 raw5059step0Labels = mixedMoment B raw5059step1 raw5059step1Labels := by
      have hz : ∀ j, raw5059step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5059step1 = (fun i j => raw5059step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5059step1 raw5059step0; decide +kernel
      have hl : raw5059step1Labels = raw5059step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5059step0 raw5059step0Labels permutation104 hz
    mixedMoment B raw5059step1 raw5059step1Labels = mixedMoment B raw5059step2 raw5059step2Labels := by
      have hz : ∀ j, raw5059step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5059step2 = (fun i j => raw5059step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5059step2 raw5059step1; decide +kernel
      have hl : raw5059step2Labels = raw5059step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5059step1 raw5059step1Labels permutation14 hz
    mixedMoment B raw5059step2 raw5059step2Labels = mixedMoment B raw5059step3 raw5059step3Labels := by
      have ha : raw5059step3 = (fun i j => raw5059step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5059step3 raw5059step2; decide +kernel
      have hl : raw5059step3Labels = raw5059step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5059step2 raw5059step2Labels permutation7 permutation2
    mixedMoment B raw5059step3 raw5059step3Labels = mixedMoment B raw5059step4 raw5059step4Labels := by
      have ha : raw5059step4 = -raw5059step3 := by apply Matrix.ext; change ∀ i j, raw5059step4 i j = -(raw5059step3 i j); unfold raw5059step4 raw5059step3; decide +kernel
      have hl : raw5059step4Labels = raw5059step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5308 node5308Labels := by rfl

def raw5060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw5060Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5060step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2]]
def raw5060step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5060step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2]]
def raw5060step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5060step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![3, -1, -2]]
def raw5060step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5060step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 1, 0], ![-2, 0, 2]]
def raw5060step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5060step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw5060step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5060 raw5060Labels = mixedMoment B node5308 node5308Labels := by
  calc
    mixedMoment B raw5060 raw5060Labels = mixedMoment B raw5060step0 raw5060step0Labels := by
      have hz : ∀ j, raw5060 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5060step0 = (fun i j => raw5060 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5060step0 raw5060; decide +kernel
      have hl : raw5060step0Labels = raw5060Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5060 raw5060Labels permutation520 hz
    mixedMoment B raw5060step0 raw5060step0Labels = mixedMoment B raw5060step1 raw5060step1Labels := by
      have hz : ∀ j, raw5060step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5060step1 = (fun i j => raw5060step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5060step1 raw5060step0; decide +kernel
      have hl : raw5060step1Labels = raw5060step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5060step0 raw5060step0Labels permutation80 hz
    mixedMoment B raw5060step1 raw5060step1Labels = mixedMoment B raw5060step2 raw5060step2Labels := by
      have hz : ∀ j, raw5060step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5060step2 = (fun i j => raw5060step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5060step2 raw5060step1; decide +kernel
      have hl : raw5060step2Labels = raw5060step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5060step1 raw5060step1Labels permutation14 hz
    mixedMoment B raw5060step2 raw5060step2Labels = mixedMoment B raw5060step3 raw5060step3Labels := by
      have ha : raw5060step3 = (fun i j => raw5060step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5060step3 raw5060step2; decide +kernel
      have hl : raw5060step3Labels = raw5060step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5060step2 raw5060step2Labels permutation7 permutation2
    mixedMoment B raw5060step3 raw5060step3Labels = mixedMoment B raw5060step4 raw5060step4Labels := by
      have ha : raw5060step4 = -raw5060step3 := by apply Matrix.ext; change ∀ i j, raw5060step4 i j = -(raw5060step3 i j); unfold raw5060step4 raw5060step3; decide +kernel
      have hl : raw5060step4Labels = raw5060step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5308 node5308Labels := by rfl

def raw5061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2]]
def raw5061Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5061step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2]]
def raw5061step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5061step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2]]
def raw5061step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5061step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![3, -1, -2]]
def raw5061step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5061step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![-1, 1, 0], ![-2, 0, 2]]
def raw5061step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5061step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw5061step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5061 raw5061Labels = mixedMoment B node5308 node5308Labels := by
  calc
    mixedMoment B raw5061 raw5061Labels = mixedMoment B raw5061step0 raw5061step0Labels := by
      have hz : ∀ j, raw5061 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5061step0 = (fun i j => raw5061 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5061step0 raw5061; decide +kernel
      have hl : raw5061step0Labels = raw5061Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5061 raw5061Labels permutation434 hz
    mixedMoment B raw5061step0 raw5061step0Labels = mixedMoment B raw5061step1 raw5061step1Labels := by
      have hz : ∀ j, raw5061step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5061step1 = (fun i j => raw5061step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5061step1 raw5061step0; decide +kernel
      have hl : raw5061step1Labels = raw5061step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5061step0 raw5061step0Labels permutation80 hz
    mixedMoment B raw5061step1 raw5061step1Labels = mixedMoment B raw5061step2 raw5061step2Labels := by
      have hz : ∀ j, raw5061step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5061step2 = (fun i j => raw5061step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5061step2 raw5061step1; decide +kernel
      have hl : raw5061step2Labels = raw5061step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5061step1 raw5061step1Labels permutation14 hz
    mixedMoment B raw5061step2 raw5061step2Labels = mixedMoment B raw5061step3 raw5061step3Labels := by
      have ha : raw5061step3 = (fun i j => raw5061step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5061step3 raw5061step2; decide +kernel
      have hl : raw5061step3Labels = raw5061step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5061step2 raw5061step2Labels permutation7 permutation2
    mixedMoment B raw5061step3 raw5061step3Labels = mixedMoment B raw5061step4 raw5061step4Labels := by
      have ha : raw5061step4 = -raw5061step3 := by apply Matrix.ext; change ∀ i j, raw5061step4 i j = -(raw5061step3 i j); unfold raw5061step4 raw5061step3; decide +kernel
      have hl : raw5061step4Labels = raw5061step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5308 node5308Labels := by rfl

def raw5062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw5062Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5062step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw5062step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5062step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw5062step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5062step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![2, 0, -2]]
def raw5062step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5062step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-2, 0, 2], ![2, 0, -2]]
def raw5062step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5062step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]
def raw5062step4Labels : Fin 2 → Fin 3 := ![0, 2]

def raw5062step5 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]
def raw5062step5Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical5062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5062 raw5062Labels = mixedMoment B node4094 node4094Labels := by
  calc
    mixedMoment B raw5062 raw5062Labels = mixedMoment B raw5062step0 raw5062step0Labels := by
      have hz : ∀ j, raw5062 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5062step0 = (fun i j => raw5062 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5062step0 raw5062; decide +kernel
      have hl : raw5062step0Labels = raw5062Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5062 raw5062Labels permutation520 hz
    mixedMoment B raw5062step0 raw5062step0Labels = mixedMoment B raw5062step1 raw5062step1Labels := by
      have hz : ∀ j, raw5062step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5062step1 = (fun i j => raw5062step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5062step1 raw5062step0; decide +kernel
      have hl : raw5062step1Labels = raw5062step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5062step0 raw5062step0Labels permutation104 hz
    mixedMoment B raw5062step1 raw5062step1Labels = mixedMoment B raw5062step2 raw5062step2Labels := by
      have hz : ∀ j, raw5062step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw5062step2 = (fun i j => raw5062step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw5062step2 raw5062step1; decide +kernel
      have hl : raw5062step2Labels = raw5062step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5062step1 raw5062step1Labels permutation20 hz
    mixedMoment B raw5062step2 raw5062step2Labels = mixedMoment B raw5062step3 raw5062step3Labels := by
      have hz : ∀ j, raw5062step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw5062step3 = (fun i j => raw5062step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw5062step3 raw5062step2; decide +kernel
      have hl : raw5062step3Labels = raw5062step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5062step2 raw5062step2Labels permutation4 hz
    mixedMoment B raw5062step3 raw5062step3Labels = mixedMoment B raw5062step4 raw5062step4Labels := by
      have hz : ∀ i, raw5062step3 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw5062step4 = (fun i j => raw5062step3 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw5062step4 raw5062step3; decide +kernel
      have hl : raw5062step4Labels = (fun j => raw5062step3Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5062step3 raw5062step3Labels permutation4 hz
    mixedMoment B raw5062step4 raw5062step4Labels = mixedMoment B raw5062step5 raw5062step5Labels := by
      have ha : raw5062step5 = raw5062step4 := by apply Matrix.ext; unfold raw5062step5 raw5062step4; decide +kernel
      have hl : raw5062step4Labels = labelEmbedding2 ∘ raw5062step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5062step4 raw5062step4Labels raw5062step5Labels labelEmbedding2 hl
    _ = mixedMoment B node4094 node4094Labels := by rfl

def raw5063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw5063Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw5063step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5063step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw5063step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5063step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw5063step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5063 raw5063Labels = mixedMoment B node4625 node4625Labels := by
  calc
    mixedMoment B raw5063 raw5063Labels = mixedMoment B raw5063step0 raw5063step0Labels := by
      have hz : ∀ j, raw5063 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5063step0 = (fun i j => raw5063 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5063step0 raw5063; decide +kernel
      have hl : raw5063step0Labels = raw5063Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5063 raw5063Labels permutation520 hz
    mixedMoment B raw5063step0 raw5063step0Labels = mixedMoment B raw5063step1 raw5063step1Labels := by
      have hz : ∀ j, raw5063step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5063step1 = (fun i j => raw5063step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5063step1 raw5063step0; decide +kernel
      have hl : raw5063step1Labels = raw5063step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5063step0 raw5063step0Labels permutation104 hz
    mixedMoment B raw5063step1 raw5063step1Labels = mixedMoment B raw5063step2 raw5063step2Labels := by
      have hz : ∀ j, raw5063step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw5063step2 = (fun i j => raw5063step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw5063step2 raw5063step1; decide +kernel
      have hl : raw5063step2Labels = raw5063step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5063step1 raw5063step1Labels permutation20 hz
    _ = mixedMoment B node4625 node4625Labels := by rfl

def raw5064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw5064Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw5064step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5064step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![3, -1, -2]]
def raw5064step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5064step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw5064step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5064 raw5064Labels = mixedMoment B node5171 node5171Labels := by
  calc
    mixedMoment B raw5064 raw5064Labels = mixedMoment B raw5064step0 raw5064step0Labels := by
      have hz : ∀ j, raw5064 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5064step0 = (fun i j => raw5064 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5064step0 raw5064; decide +kernel
      have hl : raw5064step0Labels = raw5064Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5064 raw5064Labels permutation520 hz
    mixedMoment B raw5064step0 raw5064step0Labels = mixedMoment B raw5064step1 raw5064step1Labels := by
      have hz : ∀ j, raw5064step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5064step1 = (fun i j => raw5064step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5064step1 raw5064step0; decide +kernel
      have hl : raw5064step1Labels = raw5064step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5064step0 raw5064step0Labels permutation104 hz
    mixedMoment B raw5064step1 raw5064step1Labels = mixedMoment B raw5064step2 raw5064step2Labels := by
      have ha : raw5064step2 = (fun i j => raw5064step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5064step2 raw5064step1; decide +kernel
      have hl : raw5064step2Labels = raw5064step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5064step1 raw5064step1Labels permutation10 permutation2
    _ = mixedMoment B node5171 node5171Labels := by rfl

def raw5065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw5065Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5065step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2]]
def raw5065step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5065step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![3, -1, -2]]
def raw5065step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5065step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw5065step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5065 raw5065Labels = mixedMoment B node5171 node5171Labels := by
  calc
    mixedMoment B raw5065 raw5065Labels = mixedMoment B raw5065step0 raw5065step0Labels := by
      have hz : ∀ j, raw5065 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5065step0 = (fun i j => raw5065 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5065step0 raw5065; decide +kernel
      have hl : raw5065step0Labels = raw5065Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5065 raw5065Labels permutation520 hz
    mixedMoment B raw5065step0 raw5065step0Labels = mixedMoment B raw5065step1 raw5065step1Labels := by
      have hz : ∀ j, raw5065step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5065step1 = (fun i j => raw5065step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5065step1 raw5065step0; decide +kernel
      have hl : raw5065step1Labels = raw5065step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5065step0 raw5065step0Labels permutation80 hz
    mixedMoment B raw5065step1 raw5065step1Labels = mixedMoment B raw5065step2 raw5065step2Labels := by
      have ha : raw5065step2 = (fun i j => raw5065step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5065step2 raw5065step1; decide +kernel
      have hl : raw5065step2Labels = raw5065step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5065step1 raw5065step1Labels permutation10 permutation2
    _ = mixedMoment B node5171 node5171Labels := by rfl

def raw5066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2]]
def raw5066Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5066step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2]]
def raw5066step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5066step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![3, -1, -2]]
def raw5066step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5066step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw5066step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5066 raw5066Labels = mixedMoment B node5171 node5171Labels := by
  calc
    mixedMoment B raw5066 raw5066Labels = mixedMoment B raw5066step0 raw5066step0Labels := by
      have hz : ∀ j, raw5066 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5066step0 = (fun i j => raw5066 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5066step0 raw5066; decide +kernel
      have hl : raw5066step0Labels = raw5066Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5066 raw5066Labels permutation434 hz
    mixedMoment B raw5066step0 raw5066step0Labels = mixedMoment B raw5066step1 raw5066step1Labels := by
      have hz : ∀ j, raw5066step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5066step1 = (fun i j => raw5066step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5066step1 raw5066step0; decide +kernel
      have hl : raw5066step1Labels = raw5066step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5066step0 raw5066step0Labels permutation80 hz
    mixedMoment B raw5066step1 raw5066step1Labels = mixedMoment B raw5066step2 raw5066step2Labels := by
      have ha : raw5066step2 = (fun i j => raw5066step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5066step2 raw5066step1; decide +kernel
      have hl : raw5066step2Labels = raw5066step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5066step1 raw5066step1Labels permutation10 permutation2
    _ = mixedMoment B node5171 node5171Labels := by rfl

def raw5067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw5067Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5067step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw5067step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5067step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw5067step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5067step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw5067step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5067 raw5067Labels = mixedMoment B node5308 node5308Labels := by
  calc
    mixedMoment B raw5067 raw5067Labels = mixedMoment B raw5067step0 raw5067step0Labels := by
      have hz : ∀ j, raw5067 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5067step0 = (fun i j => raw5067 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5067step0 raw5067; decide +kernel
      have hl : raw5067step0Labels = raw5067Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5067 raw5067Labels permutation520 hz
    mixedMoment B raw5067step0 raw5067step0Labels = mixedMoment B raw5067step1 raw5067step1Labels := by
      have hz : ∀ j, raw5067step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5067step1 = (fun i j => raw5067step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5067step1 raw5067step0; decide +kernel
      have hl : raw5067step1Labels = raw5067step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5067step0 raw5067step0Labels permutation104 hz
    mixedMoment B raw5067step1 raw5067step1Labels = mixedMoment B raw5067step2 raw5067step2Labels := by
      have hz : ∀ j, raw5067step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw5067step2 = (fun i j => raw5067step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw5067step2 raw5067step1; decide +kernel
      have hl : raw5067step2Labels = raw5067step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5067step1 raw5067step1Labels permutation20 hz
    _ = mixedMoment B node5308 node5308Labels := by rfl

def raw5068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw5068Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5068step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw5068step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5068step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw5068step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5068step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw5068step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5068 raw5068Labels = mixedMoment B node4625 node4625Labels := by
  calc
    mixedMoment B raw5068 raw5068Labels = mixedMoment B raw5068step0 raw5068step0Labels := by
      have hz : ∀ j, raw5068 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5068step0 = (fun i j => raw5068 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5068step0 raw5068; decide +kernel
      have hl : raw5068step0Labels = raw5068Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5068 raw5068Labels permutation520 hz
    mixedMoment B raw5068step0 raw5068step0Labels = mixedMoment B raw5068step1 raw5068step1Labels := by
      have hz : ∀ j, raw5068step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5068step1 = (fun i j => raw5068step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5068step1 raw5068step0; decide +kernel
      have hl : raw5068step1Labels = raw5068step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5068step0 raw5068step0Labels permutation104 hz
    mixedMoment B raw5068step1 raw5068step1Labels = mixedMoment B raw5068step2 raw5068step2Labels := by
      have hz : ∀ j, raw5068step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5068step2 = (fun i j => raw5068step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5068step2 raw5068step1; decide +kernel
      have hl : raw5068step2Labels = raw5068step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5068step1 raw5068step1Labels permutation14 hz
    _ = mixedMoment B node4625 node4625Labels := by rfl

def raw5069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2]]
def raw5069Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5069step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw5069step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5069step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw5069step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5069 raw5069Labels = mixedMoment B node5171 node5171Labels := by
  calc
    mixedMoment B raw5069 raw5069Labels = mixedMoment B raw5069step0 raw5069step0Labels := by
      have hz : ∀ j, raw5069 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5069step0 = (fun i j => raw5069 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5069step0 raw5069; decide +kernel
      have hl : raw5069step0Labels = raw5069Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5069 raw5069Labels permutation520 hz
    mixedMoment B raw5069step0 raw5069step0Labels = mixedMoment B raw5069step1 raw5069step1Labels := by
      have hz : ∀ j, raw5069step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5069step1 = (fun i j => raw5069step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5069step1 raw5069step0; decide +kernel
      have hl : raw5069step1Labels = raw5069step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5069step0 raw5069step0Labels permutation104 hz
    _ = mixedMoment B node5171 node5171Labels := by rfl

def raw5070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw5070Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5070step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![3, -1, -2]]
def raw5070step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5070step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![3, -1, -2]]
def raw5070step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5070step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw5070step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5070 raw5070Labels = mixedMoment B node5171 node5171Labels := by
  calc
    mixedMoment B raw5070 raw5070Labels = mixedMoment B raw5070step0 raw5070step0Labels := by
      have hz : ∀ j, raw5070 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5070step0 = (fun i j => raw5070 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5070step0 raw5070; decide +kernel
      have hl : raw5070step0Labels = raw5070Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5070 raw5070Labels permutation520 hz
    mixedMoment B raw5070step0 raw5070step0Labels = mixedMoment B raw5070step1 raw5070step1Labels := by
      have hz : ∀ j, raw5070step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5070step1 = (fun i j => raw5070step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5070step1 raw5070step0; decide +kernel
      have hl : raw5070step1Labels = raw5070step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5070step0 raw5070step0Labels permutation56 hz
    mixedMoment B raw5070step1 raw5070step1Labels = mixedMoment B raw5070step2 raw5070step2Labels := by
      have ha : raw5070step2 = (fun i j => raw5070step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5070step2 raw5070step1; decide +kernel
      have hl : raw5070step2Labels = raw5070step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5070step1 raw5070step1Labels permutation10 permutation2
    _ = mixedMoment B node5171 node5171Labels := by rfl

def raw5071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2]]
def raw5071Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5071step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![3, -1, -2]]
def raw5071step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5071step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![3, -1, -2]]
def raw5071step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5071step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw5071step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5071 raw5071Labels = mixedMoment B node5171 node5171Labels := by
  calc
    mixedMoment B raw5071 raw5071Labels = mixedMoment B raw5071step0 raw5071step0Labels := by
      have hz : ∀ j, raw5071 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5071step0 = (fun i j => raw5071 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5071step0 raw5071; decide +kernel
      have hl : raw5071step0Labels = raw5071Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5071 raw5071Labels permutation434 hz
    mixedMoment B raw5071step0 raw5071step0Labels = mixedMoment B raw5071step1 raw5071step1Labels := by
      have hz : ∀ j, raw5071step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5071step1 = (fun i j => raw5071step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5071step1 raw5071step0; decide +kernel
      have hl : raw5071step1Labels = raw5071step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5071step0 raw5071step0Labels permutation56 hz
    mixedMoment B raw5071step1 raw5071step1Labels = mixedMoment B raw5071step2 raw5071step2Labels := by
      have ha : raw5071step2 = (fun i j => raw5071step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5071step2 raw5071step1; decide +kernel
      have hl : raw5071step2Labels = raw5071step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5071step1 raw5071step1Labels permutation10 permutation2
    _ = mixedMoment B node5171 node5171Labels := by rfl

def raw5072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw5072Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5072step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw5072step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5072step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw5072step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5072step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw5072step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5072 raw5072Labels = mixedMoment B node5308 node5308Labels := by
  calc
    mixedMoment B raw5072 raw5072Labels = mixedMoment B raw5072step0 raw5072step0Labels := by
      have hz : ∀ j, raw5072 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5072step0 = (fun i j => raw5072 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5072step0 raw5072; decide +kernel
      have hl : raw5072step0Labels = raw5072Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5072 raw5072Labels permutation520 hz
    mixedMoment B raw5072step0 raw5072step0Labels = mixedMoment B raw5072step1 raw5072step1Labels := by
      have hz : ∀ j, raw5072step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5072step1 = (fun i j => raw5072step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5072step1 raw5072step0; decide +kernel
      have hl : raw5072step1Labels = raw5072step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5072step0 raw5072step0Labels permutation104 hz
    mixedMoment B raw5072step1 raw5072step1Labels = mixedMoment B raw5072step2 raw5072step2Labels := by
      have hz : ∀ j, raw5072step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5072step2 = (fun i j => raw5072step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5072step2 raw5072step1; decide +kernel
      have hl : raw5072step2Labels = raw5072step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5072step1 raw5072step1Labels permutation14 hz
    _ = mixedMoment B node5308 node5308Labels := by rfl

def raw5073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw5073Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5073step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw5073step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5073step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw5073step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5073step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw5073step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5073 raw5073Labels = mixedMoment B node4625 node4625Labels := by
  calc
    mixedMoment B raw5073 raw5073Labels = mixedMoment B raw5073step0 raw5073step0Labels := by
      have hz : ∀ j, raw5073 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5073step0 = (fun i j => raw5073 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5073step0 raw5073; decide +kernel
      have hl : raw5073step0Labels = raw5073Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5073 raw5073Labels permutation520 hz
    mixedMoment B raw5073step0 raw5073step0Labels = mixedMoment B raw5073step1 raw5073step1Labels := by
      have hz : ∀ j, raw5073step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5073step1 = (fun i j => raw5073step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5073step1 raw5073step0; decide +kernel
      have hl : raw5073step1Labels = raw5073step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5073step0 raw5073step0Labels permutation80 hz
    mixedMoment B raw5073step1 raw5073step1Labels = mixedMoment B raw5073step2 raw5073step2Labels := by
      have hz : ∀ j, raw5073step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5073step2 = (fun i j => raw5073step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5073step2 raw5073step1; decide +kernel
      have hl : raw5073step2Labels = raw5073step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5073step1 raw5073step1Labels permutation14 hz
    _ = mixedMoment B node4625 node4625Labels := by rfl

def raw5074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw5074Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw5074step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5074step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw5074step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5074 raw5074Labels = mixedMoment B node5171 node5171Labels := by
  calc
    mixedMoment B raw5074 raw5074Labels = mixedMoment B raw5074step0 raw5074step0Labels := by
      have hz : ∀ j, raw5074 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5074step0 = (fun i j => raw5074 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5074step0 raw5074; decide +kernel
      have hl : raw5074step0Labels = raw5074Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5074 raw5074Labels permutation520 hz
    mixedMoment B raw5074step0 raw5074step0Labels = mixedMoment B raw5074step1 raw5074step1Labels := by
      have hz : ∀ j, raw5074step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5074step1 = (fun i j => raw5074step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5074step1 raw5074step0; decide +kernel
      have hl : raw5074step1Labels = raw5074step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5074step0 raw5074step0Labels permutation80 hz
    _ = mixedMoment B node5171 node5171Labels := by rfl

def raw5075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw5075Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5075step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw5075step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5075step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw5075step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5075 raw5075Labels = mixedMoment B node5171 node5171Labels := by
  calc
    mixedMoment B raw5075 raw5075Labels = mixedMoment B raw5075step0 raw5075step0Labels := by
      have hz : ∀ j, raw5075 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5075step0 = (fun i j => raw5075 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5075step0 raw5075; decide +kernel
      have hl : raw5075step0Labels = raw5075Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5075 raw5075Labels permutation520 hz
    mixedMoment B raw5075step0 raw5075step0Labels = mixedMoment B raw5075step1 raw5075step1Labels := by
      have hz : ∀ j, raw5075step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5075step1 = (fun i j => raw5075step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5075step1 raw5075step0; decide +kernel
      have hl : raw5075step1Labels = raw5075step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5075step0 raw5075step0Labels permutation56 hz
    _ = mixedMoment B node5171 node5171Labels := by rfl

def raw5076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![3, -1, -2]]
def raw5076Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![3, -1, -2]]
def raw5076step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5076step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![3, -1, -2]]
def raw5076step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5076step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw5076step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5076 raw5076Labels = mixedMoment B node5171 node5171Labels := by
  calc
    mixedMoment B raw5076 raw5076Labels = mixedMoment B raw5076step0 raw5076step0Labels := by
      have hz : ∀ j, raw5076 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5076step0 = (fun i j => raw5076 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5076step0 raw5076; decide +kernel
      have hl : raw5076step0Labels = raw5076Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5076 raw5076Labels permutation346 hz
    mixedMoment B raw5076step0 raw5076step0Labels = mixedMoment B raw5076step1 raw5076step1Labels := by
      have hz : ∀ j, raw5076step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5076step1 = (fun i j => raw5076step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5076step1 raw5076step0; decide +kernel
      have hl : raw5076step1Labels = raw5076step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5076step0 raw5076step0Labels permutation56 hz
    mixedMoment B raw5076step1 raw5076step1Labels = mixedMoment B raw5076step2 raw5076step2Labels := by
      have ha : raw5076step2 = (fun i j => raw5076step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5076step2 raw5076step1; decide +kernel
      have hl : raw5076step2Labels = raw5076step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5076step1 raw5076step1Labels permutation10 permutation2
    _ = mixedMoment B node5171 node5171Labels := by rfl

def raw5077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw5077Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw5077step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5077step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw5077step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5077step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw5077step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5077 raw5077Labels = mixedMoment B node5308 node5308Labels := by
  calc
    mixedMoment B raw5077 raw5077Labels = mixedMoment B raw5077step0 raw5077step0Labels := by
      have hz : ∀ j, raw5077 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5077step0 = (fun i j => raw5077 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5077step0 raw5077; decide +kernel
      have hl : raw5077step0Labels = raw5077Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5077 raw5077Labels permutation520 hz
    mixedMoment B raw5077step0 raw5077step0Labels = mixedMoment B raw5077step1 raw5077step1Labels := by
      have hz : ∀ j, raw5077step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5077step1 = (fun i j => raw5077step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5077step1 raw5077step0; decide +kernel
      have hl : raw5077step1Labels = raw5077step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5077step0 raw5077step0Labels permutation80 hz
    mixedMoment B raw5077step1 raw5077step1Labels = mixedMoment B raw5077step2 raw5077step2Labels := by
      have hz : ∀ j, raw5077step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5077step2 = (fun i j => raw5077step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5077step2 raw5077step1; decide +kernel
      have hl : raw5077step2Labels = raw5077step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5077step1 raw5077step1Labels permutation14 hz
    _ = mixedMoment B node5308 node5308Labels := by rfl

def raw5078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw5078Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw5078step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5078step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw5078step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5078step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw5078step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5078 raw5078Labels = mixedMoment B node4625 node4625Labels := by
  calc
    mixedMoment B raw5078 raw5078Labels = mixedMoment B raw5078step0 raw5078step0Labels := by
      have hz : ∀ j, raw5078 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5078step0 = (fun i j => raw5078 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5078step0 raw5078; decide +kernel
      have hl : raw5078step0Labels = raw5078Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5078 raw5078Labels permutation434 hz
    mixedMoment B raw5078step0 raw5078step0Labels = mixedMoment B raw5078step1 raw5078step1Labels := by
      have hz : ∀ j, raw5078step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5078step1 = (fun i j => raw5078step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5078step1 raw5078step0; decide +kernel
      have hl : raw5078step1Labels = raw5078step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5078step0 raw5078step0Labels permutation80 hz
    mixedMoment B raw5078step1 raw5078step1Labels = mixedMoment B raw5078step2 raw5078step2Labels := by
      have hz : ∀ j, raw5078step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5078step2 = (fun i j => raw5078step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5078step2 raw5078step1; decide +kernel
      have hl : raw5078step2Labels = raw5078step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5078step1 raw5078step1Labels permutation14 hz
    _ = mixedMoment B node4625 node4625Labels := by rfl

def raw5079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw5079Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw5079step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5079step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw5079step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5079 raw5079Labels = mixedMoment B node5171 node5171Labels := by
  calc
    mixedMoment B raw5079 raw5079Labels = mixedMoment B raw5079step0 raw5079step0Labels := by
      have hz : ∀ j, raw5079 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5079step0 = (fun i j => raw5079 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5079step0 raw5079; decide +kernel
      have hl : raw5079step0Labels = raw5079Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5079 raw5079Labels permutation434 hz
    mixedMoment B raw5079step0 raw5079step0Labels = mixedMoment B raw5079step1 raw5079step1Labels := by
      have hz : ∀ j, raw5079step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5079step1 = (fun i j => raw5079step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5079step1 raw5079step0; decide +kernel
      have hl : raw5079step1Labels = raw5079step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5079step0 raw5079step0Labels permutation80 hz
    _ = mixedMoment B node5171 node5171Labels := by rfl

def raw5080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw5080Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5080step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw5080step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5080step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw5080step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5080 raw5080Labels = mixedMoment B node5171 node5171Labels := by
  calc
    mixedMoment B raw5080 raw5080Labels = mixedMoment B raw5080step0 raw5080step0Labels := by
      have hz : ∀ j, raw5080 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5080step0 = (fun i j => raw5080 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5080step0 raw5080; decide +kernel
      have hl : raw5080step0Labels = raw5080Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5080 raw5080Labels permutation434 hz
    mixedMoment B raw5080step0 raw5080step0Labels = mixedMoment B raw5080step1 raw5080step1Labels := by
      have hz : ∀ j, raw5080step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5080step1 = (fun i j => raw5080step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5080step1 raw5080step0; decide +kernel
      have hl : raw5080step1Labels = raw5080step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5080step0 raw5080step0Labels permutation56 hz
    _ = mixedMoment B node5171 node5171Labels := by rfl

def raw5081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw5081Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5081step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw5081step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5081step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw5081step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5081 raw5081Labels = mixedMoment B node5171 node5171Labels := by
  calc
    mixedMoment B raw5081 raw5081Labels = mixedMoment B raw5081step0 raw5081step0Labels := by
      have hz : ∀ j, raw5081 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5081step0 = (fun i j => raw5081 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5081step0 raw5081; decide +kernel
      have hl : raw5081step0Labels = raw5081Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5081 raw5081Labels permutation346 hz
    mixedMoment B raw5081step0 raw5081step0Labels = mixedMoment B raw5081step1 raw5081step1Labels := by
      have hz : ∀ j, raw5081step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5081step1 = (fun i j => raw5081step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5081step1 raw5081step0; decide +kernel
      have hl : raw5081step1Labels = raw5081step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5081step0 raw5081step0Labels permutation56 hz
    _ = mixedMoment B node5171 node5171Labels := by rfl

def raw5082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw5082Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw5082step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5082step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw5082step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5082step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw5082step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5082 raw5082Labels = mixedMoment B node5308 node5308Labels := by
  calc
    mixedMoment B raw5082 raw5082Labels = mixedMoment B raw5082step0 raw5082step0Labels := by
      have hz : ∀ j, raw5082 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5082step0 = (fun i j => raw5082 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5082step0 raw5082; decide +kernel
      have hl : raw5082step0Labels = raw5082Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5082 raw5082Labels permutation434 hz
    mixedMoment B raw5082step0 raw5082step0Labels = mixedMoment B raw5082step1 raw5082step1Labels := by
      have hz : ∀ j, raw5082step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5082step1 = (fun i j => raw5082step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5082step1 raw5082step0; decide +kernel
      have hl : raw5082step1Labels = raw5082step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5082step0 raw5082step0Labels permutation80 hz
    mixedMoment B raw5082step1 raw5082step1Labels = mixedMoment B raw5082step2 raw5082step2Labels := by
      have hz : ∀ j, raw5082step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5082step2 = (fun i j => raw5082step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5082step2 raw5082step1; decide +kernel
      have hl : raw5082step2Labels = raw5082step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5082step1 raw5082step1Labels permutation14 hz
    _ = mixedMoment B node5308 node5308Labels := by rfl

def raw5083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw5083Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw5083step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5083step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw5083step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5083step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![4, -2, -2]]
def raw5083step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5083step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 2, 2], ![4, -2, -2]]
def raw5083step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5083 raw5083Labels = mixedMoment B node4629 node4629Labels := by
  calc
    mixedMoment B raw5083 raw5083Labels = mixedMoment B raw5083step0 raw5083step0Labels := by
      have hz : ∀ j, raw5083 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5083step0 = (fun i j => raw5083 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5083step0 raw5083; decide +kernel
      have hl : raw5083step0Labels = raw5083Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5083 raw5083Labels permutation520 hz
    mixedMoment B raw5083step0 raw5083step0Labels = mixedMoment B raw5083step1 raw5083step1Labels := by
      have hz : ∀ j, raw5083step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5083step1 = (fun i j => raw5083step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5083step1 raw5083step0; decide +kernel
      have hl : raw5083step1Labels = raw5083step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5083step0 raw5083step0Labels permutation104 hz
    mixedMoment B raw5083step1 raw5083step1Labels = mixedMoment B raw5083step2 raw5083step2Labels := by
      have hz : ∀ j, raw5083step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw5083step2 = (fun i j => raw5083step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw5083step2 raw5083step1; decide +kernel
      have hl : raw5083step2Labels = raw5083step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5083step1 raw5083step1Labels permutation20 hz
    mixedMoment B raw5083step2 raw5083step2Labels = mixedMoment B raw5083step3 raw5083step3Labels := by
      have hz : ∀ j, raw5083step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw5083step3 = (fun i j => raw5083step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw5083step3 raw5083step2; decide +kernel
      have hl : raw5083step3Labels = raw5083step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5083step2 raw5083step2Labels permutation4 hz
    _ = mixedMoment B node4629 node4629Labels := by rfl

def raw5084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw5084Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw5084step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5084step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![4, -2, -2]]
def raw5084step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5084step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![4, -2, -2]]
def raw5084step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5084step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 1, 0], ![-3, 1, 2]]
def raw5084step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5084step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw5084step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5084 raw5084Labels = mixedMoment B node4625 node4625Labels := by
  calc
    mixedMoment B raw5084 raw5084Labels = mixedMoment B raw5084step0 raw5084step0Labels := by
      have hz : ∀ j, raw5084 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5084step0 = (fun i j => raw5084 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5084step0 raw5084; decide +kernel
      have hl : raw5084step0Labels = raw5084Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5084 raw5084Labels permutation520 hz
    mixedMoment B raw5084step0 raw5084step0Labels = mixedMoment B raw5084step1 raw5084step1Labels := by
      have hz : ∀ j, raw5084step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5084step1 = (fun i j => raw5084step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5084step1 raw5084step0; decide +kernel
      have hl : raw5084step1Labels = raw5084step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5084step0 raw5084step0Labels permutation104 hz
    mixedMoment B raw5084step1 raw5084step1Labels = mixedMoment B raw5084step2 raw5084step2Labels := by
      have hz : ∀ j, raw5084step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw5084step2 = (fun i j => raw5084step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw5084step2 raw5084step1; decide +kernel
      have hl : raw5084step2Labels = raw5084step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5084step1 raw5084step1Labels permutation20 hz
    mixedMoment B raw5084step2 raw5084step2Labels = mixedMoment B raw5084step3 raw5084step3Labels := by
      have ha : raw5084step3 = (fun i j => raw5084step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5084step3 raw5084step2; decide +kernel
      have hl : raw5084step3Labels = raw5084step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5084step2 raw5084step2Labels permutation7 permutation2
    mixedMoment B raw5084step3 raw5084step3Labels = mixedMoment B raw5084step4 raw5084step4Labels := by
      have ha : raw5084step4 = -raw5084step3 := by apply Matrix.ext; change ∀ i j, raw5084step4 i j = -(raw5084step3 i j); unfold raw5084step4 raw5084step3; decide +kernel
      have hl : raw5084step4Labels = raw5084step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4625 node4625Labels := by rfl

def raw5085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw5085Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![4, -2, -2]]
def raw5085step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5085step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw5085step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5085step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![4, -2, -2]]
def raw5085step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5085step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 1, 0], ![-3, 1, 2]]
def raw5085step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5085step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw5085step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5085 raw5085Labels = mixedMoment B node4625 node4625Labels := by
  calc
    mixedMoment B raw5085 raw5085Labels = mixedMoment B raw5085step0 raw5085step0Labels := by
      have hz : ∀ j, raw5085 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5085step0 = (fun i j => raw5085 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5085step0 raw5085; decide +kernel
      have hl : raw5085step0Labels = raw5085Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5085 raw5085Labels permutation520 hz
    mixedMoment B raw5085step0 raw5085step0Labels = mixedMoment B raw5085step1 raw5085step1Labels := by
      have hz : ∀ j, raw5085step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5085step1 = (fun i j => raw5085step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5085step1 raw5085step0; decide +kernel
      have hl : raw5085step1Labels = raw5085step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5085step0 raw5085step0Labels permutation104 hz
    mixedMoment B raw5085step1 raw5085step1Labels = mixedMoment B raw5085step2 raw5085step2Labels := by
      have hz : ∀ j, raw5085step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5085step2 = (fun i j => raw5085step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5085step2 raw5085step1; decide +kernel
      have hl : raw5085step2Labels = raw5085step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5085step1 raw5085step1Labels permutation14 hz
    mixedMoment B raw5085step2 raw5085step2Labels = mixedMoment B raw5085step3 raw5085step3Labels := by
      have ha : raw5085step3 = (fun i j => raw5085step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5085step3 raw5085step2; decide +kernel
      have hl : raw5085step3Labels = raw5085step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5085step2 raw5085step2Labels permutation7 permutation2
    mixedMoment B raw5085step3 raw5085step3Labels = mixedMoment B raw5085step4 raw5085step4Labels := by
      have ha : raw5085step4 = -raw5085step3 := by apply Matrix.ext; change ∀ i j, raw5085step4 i j = -(raw5085step3 i j); unfold raw5085step4 raw5085step3; decide +kernel
      have hl : raw5085step4Labels = raw5085step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4625 node4625Labels := by rfl

def raw5086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![4, -2, -2]]
def raw5086Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5086step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw5086step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5086step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw5086step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5086step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![4, -2, -2]]
def raw5086step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5086step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 1, 0], ![-3, 1, 2]]
def raw5086step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5086step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw5086step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5086 raw5086Labels = mixedMoment B node4625 node4625Labels := by
  calc
    mixedMoment B raw5086 raw5086Labels = mixedMoment B raw5086step0 raw5086step0Labels := by
      have hz : ∀ j, raw5086 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5086step0 = (fun i j => raw5086 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5086step0 raw5086; decide +kernel
      have hl : raw5086step0Labels = raw5086Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5086 raw5086Labels permutation520 hz
    mixedMoment B raw5086step0 raw5086step0Labels = mixedMoment B raw5086step1 raw5086step1Labels := by
      have hz : ∀ j, raw5086step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5086step1 = (fun i j => raw5086step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5086step1 raw5086step0; decide +kernel
      have hl : raw5086step1Labels = raw5086step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5086step0 raw5086step0Labels permutation80 hz
    mixedMoment B raw5086step1 raw5086step1Labels = mixedMoment B raw5086step2 raw5086step2Labels := by
      have hz : ∀ j, raw5086step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5086step2 = (fun i j => raw5086step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5086step2 raw5086step1; decide +kernel
      have hl : raw5086step2Labels = raw5086step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5086step1 raw5086step1Labels permutation14 hz
    mixedMoment B raw5086step2 raw5086step2Labels = mixedMoment B raw5086step3 raw5086step3Labels := by
      have ha : raw5086step3 = (fun i j => raw5086step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5086step3 raw5086step2; decide +kernel
      have hl : raw5086step3Labels = raw5086step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5086step2 raw5086step2Labels permutation7 permutation2
    mixedMoment B raw5086step3 raw5086step3Labels = mixedMoment B raw5086step4 raw5086step4Labels := by
      have ha : raw5086step4 = -raw5086step3 := by apply Matrix.ext; change ∀ i j, raw5086step4 i j = -(raw5086step3 i j); unfold raw5086step4 raw5086step3; decide +kernel
      have hl : raw5086step4Labels = raw5086step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4625 node4625Labels := by rfl

def raw5087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw5087Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw5087step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5087step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![4, -2, -2]]
def raw5087step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5087step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![4, -2, -2]]
def raw5087step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5087step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -2, -2], ![-1, 1, 0], ![-3, 1, 2]]
def raw5087step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5087step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw5087step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5087 raw5087Labels = mixedMoment B node4625 node4625Labels := by
  calc
    mixedMoment B raw5087 raw5087Labels = mixedMoment B raw5087step0 raw5087step0Labels := by
      have hz : ∀ j, raw5087 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5087step0 = (fun i j => raw5087 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5087step0 raw5087; decide +kernel
      have hl : raw5087step0Labels = raw5087Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5087 raw5087Labels permutation434 hz
    mixedMoment B raw5087step0 raw5087step0Labels = mixedMoment B raw5087step1 raw5087step1Labels := by
      have hz : ∀ j, raw5087step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5087step1 = (fun i j => raw5087step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5087step1 raw5087step0; decide +kernel
      have hl : raw5087step1Labels = raw5087step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5087step0 raw5087step0Labels permutation80 hz
    mixedMoment B raw5087step1 raw5087step1Labels = mixedMoment B raw5087step2 raw5087step2Labels := by
      have hz : ∀ j, raw5087step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5087step2 = (fun i j => raw5087step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5087step2 raw5087step1; decide +kernel
      have hl : raw5087step2Labels = raw5087step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5087step1 raw5087step1Labels permutation14 hz
    mixedMoment B raw5087step2 raw5087step2Labels = mixedMoment B raw5087step3 raw5087step3Labels := by
      have ha : raw5087step3 = (fun i j => raw5087step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5087step3 raw5087step2; decide +kernel
      have hl : raw5087step3Labels = raw5087step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5087step2 raw5087step2Labels permutation7 permutation2
    mixedMoment B raw5087step3 raw5087step3Labels = mixedMoment B raw5087step4 raw5087step4Labels := by
      have ha : raw5087step4 = -raw5087step3 := by apply Matrix.ext; change ∀ i j, raw5087step4 i j = -(raw5087step3 i j); unfold raw5087step4 raw5087step3; decide +kernel
      have hl : raw5087step4Labels = raw5087step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4625 node4625Labels := by rfl

def raw5088 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5088Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5088step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5088step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5088step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5088step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, -2, 3]]
def raw5088step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5088step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-3, 2, 1]]
def raw5088step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5088step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw5088step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5088step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw5088step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5088 raw5088Labels = mixedMoment B node5296 node5296Labels := by
  calc
    mixedMoment B raw5088 raw5088Labels = mixedMoment B raw5088step0 raw5088step0Labels := by
      have hz : ∀ j, raw5088 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5088step0 = (fun i j => raw5088 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5088step0 raw5088; decide +kernel
      have hl : raw5088step0Labels = raw5088Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5088 raw5088Labels permutation520 hz
    mixedMoment B raw5088step0 raw5088step0Labels = mixedMoment B raw5088step1 raw5088step1Labels := by
      have hz : ∀ j, raw5088step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5088step1 = (fun i j => raw5088step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5088step1 raw5088step0; decide +kernel
      have hl : raw5088step1Labels = raw5088step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5088step0 raw5088step0Labels permutation104 hz
    mixedMoment B raw5088step1 raw5088step1Labels = mixedMoment B raw5088step2 raw5088step2Labels := by
      have hz : ∀ j, raw5088step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw5088step2 = (fun i j => raw5088step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw5088step2 raw5088step1; decide +kernel
      have hl : raw5088step2Labels = raw5088step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5088step1 raw5088step1Labels permutation20 hz
    mixedMoment B raw5088step2 raw5088step2Labels = mixedMoment B raw5088step3 raw5088step3Labels := by
      have ha : raw5088step3 = (fun i j => raw5088step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5088step3 raw5088step2; decide +kernel
      have hl : raw5088step3Labels = raw5088step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5088step2 raw5088step2Labels permutation7 permutation6
    mixedMoment B raw5088step3 raw5088step3Labels = mixedMoment B raw5088step4 raw5088step4Labels := by
      have ha : raw5088step4 = -raw5088step3 := by apply Matrix.ext; change ∀ i j, raw5088step4 i j = -(raw5088step3 i j); unfold raw5088step4 raw5088step3; decide +kernel
      have hl : raw5088step4Labels = raw5088step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5088step4 raw5088step4Labels = mixedMoment B raw5088step5 raw5088step5Labels := by
      have ha : raw5088step5 = raw5088step4 := by apply Matrix.ext; unfold raw5088step5 raw5088step4; decide +kernel
      have hl : raw5088step4Labels = labelEmbedding9 ∘ raw5088step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5088step4 raw5088step4Labels raw5088step5Labels labelEmbedding9 hl
    _ = mixedMoment B node5296 node5296Labels := by rfl

def raw5089 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5089Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5089step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5089step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5089step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5089step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, -2, 3]]
def raw5089step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5089step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-3, 2, 1]]
def raw5089step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5089step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw5089step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5089step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw5089step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5089 raw5089Labels = mixedMoment B node5296 node5296Labels := by
  calc
    mixedMoment B raw5089 raw5089Labels = mixedMoment B raw5089step0 raw5089step0Labels := by
      have hz : ∀ j, raw5089 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5089step0 = (fun i j => raw5089 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5089step0 raw5089; decide +kernel
      have hl : raw5089step0Labels = raw5089Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5089 raw5089Labels permutation520 hz
    mixedMoment B raw5089step0 raw5089step0Labels = mixedMoment B raw5089step1 raw5089step1Labels := by
      have hz : ∀ j, raw5089step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5089step1 = (fun i j => raw5089step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5089step1 raw5089step0; decide +kernel
      have hl : raw5089step1Labels = raw5089step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5089step0 raw5089step0Labels permutation104 hz
    mixedMoment B raw5089step1 raw5089step1Labels = mixedMoment B raw5089step2 raw5089step2Labels := by
      have hz : ∀ j, raw5089step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5089step2 = (fun i j => raw5089step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5089step2 raw5089step1; decide +kernel
      have hl : raw5089step2Labels = raw5089step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5089step1 raw5089step1Labels permutation14 hz
    mixedMoment B raw5089step2 raw5089step2Labels = mixedMoment B raw5089step3 raw5089step3Labels := by
      have ha : raw5089step3 = (fun i j => raw5089step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5089step3 raw5089step2; decide +kernel
      have hl : raw5089step3Labels = raw5089step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5089step2 raw5089step2Labels permutation7 permutation6
    mixedMoment B raw5089step3 raw5089step3Labels = mixedMoment B raw5089step4 raw5089step4Labels := by
      have ha : raw5089step4 = -raw5089step3 := by apply Matrix.ext; change ∀ i j, raw5089step4 i j = -(raw5089step3 i j); unfold raw5089step4 raw5089step3; decide +kernel
      have hl : raw5089step4Labels = raw5089step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5089step4 raw5089step4Labels = mixedMoment B raw5089step5 raw5089step5Labels := by
      have ha : raw5089step5 = raw5089step4 := by apply Matrix.ext; unfold raw5089step5 raw5089step4; decide +kernel
      have hl : raw5089step4Labels = labelEmbedding9 ∘ raw5089step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5089step4 raw5089step4Labels raw5089step5Labels labelEmbedding9 hl
    _ = mixedMoment B node5296 node5296Labels := by rfl

def raw5090 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5090Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5090step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5090step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5090step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5090step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, -2, 3]]
def raw5090step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5090step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-3, 2, 1]]
def raw5090step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5090step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw5090step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5090step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![3, -2, -1]]
def raw5090step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5090 raw5090Labels = mixedMoment B node5296 node5296Labels := by
  calc
    mixedMoment B raw5090 raw5090Labels = mixedMoment B raw5090step0 raw5090step0Labels := by
      have hz : ∀ j, raw5090 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5090step0 = (fun i j => raw5090 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5090step0 raw5090; decide +kernel
      have hl : raw5090step0Labels = raw5090Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5090 raw5090Labels permutation520 hz
    mixedMoment B raw5090step0 raw5090step0Labels = mixedMoment B raw5090step1 raw5090step1Labels := by
      have hz : ∀ j, raw5090step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5090step1 = (fun i j => raw5090step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5090step1 raw5090step0; decide +kernel
      have hl : raw5090step1Labels = raw5090step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5090step0 raw5090step0Labels permutation80 hz
    mixedMoment B raw5090step1 raw5090step1Labels = mixedMoment B raw5090step2 raw5090step2Labels := by
      have hz : ∀ j, raw5090step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5090step2 = (fun i j => raw5090step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5090step2 raw5090step1; decide +kernel
      have hl : raw5090step2Labels = raw5090step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5090step1 raw5090step1Labels permutation14 hz
    mixedMoment B raw5090step2 raw5090step2Labels = mixedMoment B raw5090step3 raw5090step3Labels := by
      have ha : raw5090step3 = (fun i j => raw5090step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5090step3 raw5090step2; decide +kernel
      have hl : raw5090step3Labels = raw5090step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5090step2 raw5090step2Labels permutation7 permutation6
    mixedMoment B raw5090step3 raw5090step3Labels = mixedMoment B raw5090step4 raw5090step4Labels := by
      have ha : raw5090step4 = -raw5090step3 := by apply Matrix.ext; change ∀ i j, raw5090step4 i j = -(raw5090step3 i j); unfold raw5090step4 raw5090step3; decide +kernel
      have hl : raw5090step4Labels = raw5090step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5090step4 raw5090step4Labels = mixedMoment B raw5090step5 raw5090step5Labels := by
      have ha : raw5090step5 = raw5090step4 := by apply Matrix.ext; unfold raw5090step5 raw5090step4; decide +kernel
      have hl : raw5090step4Labels = labelEmbedding9 ∘ raw5090step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5090step4 raw5090step4Labels raw5090step5Labels labelEmbedding9 hl
    _ = mixedMoment B node5296 node5296Labels := by rfl

def raw5091 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5091Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5091step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5091step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5091step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5091step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5091step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw5091step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5091step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw5091step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5091 raw5091Labels = mixedMoment B node5261 node5261Labels := by
  calc
    mixedMoment B raw5091 raw5091Labels = mixedMoment B raw5091step0 raw5091step0Labels := by
      have hz : ∀ j, raw5091 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5091step0 = (fun i j => raw5091 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5091step0 raw5091; decide +kernel
      have hl : raw5091step0Labels = raw5091Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5091 raw5091Labels permutation434 hz
    mixedMoment B raw5091step0 raw5091step0Labels = mixedMoment B raw5091step1 raw5091step1Labels := by
      have hz : ∀ j, raw5091step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5091step1 = (fun i j => raw5091step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5091step1 raw5091step0; decide +kernel
      have hl : raw5091step1Labels = raw5091step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5091step0 raw5091step0Labels permutation80 hz
    mixedMoment B raw5091step1 raw5091step1Labels = mixedMoment B raw5091step2 raw5091step2Labels := by
      have ha : raw5091step2 = (fun i j => raw5091step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5091step2 raw5091step1; decide +kernel
      have hl : raw5091step2Labels = raw5091step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5091step1 raw5091step1Labels permutation10 permutation6
    mixedMoment B raw5091step2 raw5091step2Labels = mixedMoment B raw5091step3 raw5091step3Labels := by
      have ha : raw5091step3 = raw5091step2 := by apply Matrix.ext; unfold raw5091step3 raw5091step2; decide +kernel
      have hl : raw5091step2Labels = labelEmbedding9 ∘ raw5091step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5091step2 raw5091step2Labels raw5091step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5261 node5261Labels := by rfl

def raw5092 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5092Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5092step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5092step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw5092step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5092step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, -2, 3]]
def raw5092step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5092step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw5092step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5092step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw5092step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5092 raw5092Labels = mixedMoment B node4897 node4897Labels := by
  calc
    mixedMoment B raw5092 raw5092Labels = mixedMoment B raw5092step0 raw5092step0Labels := by
      have hz : ∀ j, raw5092 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5092step0 = (fun i j => raw5092 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5092step0 raw5092; decide +kernel
      have hl : raw5092step0Labels = raw5092Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5092 raw5092Labels permutation520 hz
    mixedMoment B raw5092step0 raw5092step0Labels = mixedMoment B raw5092step1 raw5092step1Labels := by
      have hz : ∀ j, raw5092step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5092step1 = (fun i j => raw5092step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5092step1 raw5092step0; decide +kernel
      have hl : raw5092step1Labels = raw5092step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5092step0 raw5092step0Labels permutation104 hz
    mixedMoment B raw5092step1 raw5092step1Labels = mixedMoment B raw5092step2 raw5092step2Labels := by
      have hz : ∀ j, raw5092step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5092step2 = (fun i j => raw5092step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5092step2 raw5092step1; decide +kernel
      have hl : raw5092step2Labels = raw5092step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5092step1 raw5092step1Labels permutation14 hz
    mixedMoment B raw5092step2 raw5092step2Labels = mixedMoment B raw5092step3 raw5092step3Labels := by
      have ha : raw5092step3 = (fun i j => raw5092step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5092step3 raw5092step2; decide +kernel
      have hl : raw5092step3Labels = raw5092step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5092step2 raw5092step2Labels permutation2 permutation6
    mixedMoment B raw5092step3 raw5092step3Labels = mixedMoment B raw5092step4 raw5092step4Labels := by
      have ha : raw5092step4 = raw5092step3 := by apply Matrix.ext; unfold raw5092step4 raw5092step3; decide +kernel
      have hl : raw5092step3Labels = labelEmbedding9 ∘ raw5092step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5092step3 raw5092step3Labels raw5092step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4897 node4897Labels := by rfl

def raw5093 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5093Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5093step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5093step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw5093step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5093step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw5093step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5093step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw5093step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5093 raw5093Labels = mixedMoment B node5261 node5261Labels := by
  calc
    mixedMoment B raw5093 raw5093Labels = mixedMoment B raw5093step0 raw5093step0Labels := by
      have hz : ∀ j, raw5093 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5093step0 = (fun i j => raw5093 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5093step0 raw5093; decide +kernel
      have hl : raw5093step0Labels = raw5093Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5093 raw5093Labels permutation520 hz
    mixedMoment B raw5093step0 raw5093step0Labels = mixedMoment B raw5093step1 raw5093step1Labels := by
      have hz : ∀ j, raw5093step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5093step1 = (fun i j => raw5093step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5093step1 raw5093step0; decide +kernel
      have hl : raw5093step1Labels = raw5093step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5093step0 raw5093step0Labels permutation104 hz
    mixedMoment B raw5093step1 raw5093step1Labels = mixedMoment B raw5093step2 raw5093step2Labels := by
      have ha : raw5093step2 = (fun i j => raw5093step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5093step2 raw5093step1; decide +kernel
      have hl : raw5093step2Labels = raw5093step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5093step1 raw5093step1Labels permutation8 permutation6
    mixedMoment B raw5093step2 raw5093step2Labels = mixedMoment B raw5093step3 raw5093step3Labels := by
      have ha : raw5093step3 = raw5093step2 := by apply Matrix.ext; unfold raw5093step3 raw5093step2; decide +kernel
      have hl : raw5093step2Labels = labelEmbedding9 ∘ raw5093step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5093step2 raw5093step2Labels raw5093step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5261 node5261Labels := by rfl

def raw5094 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5094Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5094step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5094step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5094step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw5094step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5094step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw5094step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5094step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw5094step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5094 raw5094Labels = mixedMoment B node5261 node5261Labels := by
  calc
    mixedMoment B raw5094 raw5094Labels = mixedMoment B raw5094step0 raw5094step0Labels := by
      have hz : ∀ j, raw5094 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5094step0 = (fun i j => raw5094 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5094step0 raw5094; decide +kernel
      have hl : raw5094step0Labels = raw5094Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5094 raw5094Labels permutation520 hz
    mixedMoment B raw5094step0 raw5094step0Labels = mixedMoment B raw5094step1 raw5094step1Labels := by
      have hz : ∀ j, raw5094step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5094step1 = (fun i j => raw5094step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5094step1 raw5094step0; decide +kernel
      have hl : raw5094step1Labels = raw5094step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5094step0 raw5094step0Labels permutation56 hz
    mixedMoment B raw5094step1 raw5094step1Labels = mixedMoment B raw5094step2 raw5094step2Labels := by
      have ha : raw5094step2 = (fun i j => raw5094step1 (permutation10 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5094step2 raw5094step1; decide +kernel
      have hl : raw5094step2Labels = raw5094step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5094step1 raw5094step1Labels permutation10 permutation6
    mixedMoment B raw5094step2 raw5094step2Labels = mixedMoment B raw5094step3 raw5094step3Labels := by
      have ha : raw5094step3 = raw5094step2 := by apply Matrix.ext; unfold raw5094step3 raw5094step2; decide +kernel
      have hl : raw5094step2Labels = labelEmbedding9 ∘ raw5094step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5094step2 raw5094step2Labels raw5094step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5261 node5261Labels := by rfl

def raw5095 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5095Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw5095step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5095step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw5095step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5095step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![-1, -2, 3]]
def raw5095step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5095step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw5095step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5095step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw5095step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5095 raw5095Labels = mixedMoment B node4897 node4897Labels := by
  calc
    mixedMoment B raw5095 raw5095Labels = mixedMoment B raw5095step0 raw5095step0Labels := by
      have hz : ∀ j, raw5095 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5095step0 = (fun i j => raw5095 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5095step0 raw5095; decide +kernel
      have hl : raw5095step0Labels = raw5095Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5095 raw5095Labels permutation520 hz
    mixedMoment B raw5095step0 raw5095step0Labels = mixedMoment B raw5095step1 raw5095step1Labels := by
      have hz : ∀ j, raw5095step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5095step1 = (fun i j => raw5095step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5095step1 raw5095step0; decide +kernel
      have hl : raw5095step1Labels = raw5095step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5095step0 raw5095step0Labels permutation80 hz
    mixedMoment B raw5095step1 raw5095step1Labels = mixedMoment B raw5095step2 raw5095step2Labels := by
      have hz : ∀ j, raw5095step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5095step2 = (fun i j => raw5095step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5095step2 raw5095step1; decide +kernel
      have hl : raw5095step2Labels = raw5095step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5095step1 raw5095step1Labels permutation14 hz
    mixedMoment B raw5095step2 raw5095step2Labels = mixedMoment B raw5095step3 raw5095step3Labels := by
      have ha : raw5095step3 = (fun i j => raw5095step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5095step3 raw5095step2; decide +kernel
      have hl : raw5095step3Labels = raw5095step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5095step2 raw5095step2Labels permutation2 permutation6
    mixedMoment B raw5095step3 raw5095step3Labels = mixedMoment B raw5095step4 raw5095step4Labels := by
      have ha : raw5095step4 = raw5095step3 := by apply Matrix.ext; unfold raw5095step4 raw5095step3; decide +kernel
      have hl : raw5095step3Labels = labelEmbedding9 ∘ raw5095step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5095step3 raw5095step3Labels raw5095step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4897 node4897Labels := by rfl

def raw5096 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, -2, 3]]
def raw5096Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw5096step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5096step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, -2, 3]]
def raw5096step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5096step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw5096step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5096step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw5096step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5096 raw5096Labels = mixedMoment B node5261 node5261Labels := by
  calc
    mixedMoment B raw5096 raw5096Labels = mixedMoment B raw5096step0 raw5096step0Labels := by
      have hz : ∀ j, raw5096 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5096step0 = (fun i j => raw5096 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5096step0 raw5096; decide +kernel
      have hl : raw5096step0Labels = raw5096Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5096 raw5096Labels permutation520 hz
    mixedMoment B raw5096step0 raw5096step0Labels = mixedMoment B raw5096step1 raw5096step1Labels := by
      have hz : ∀ j, raw5096step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5096step1 = (fun i j => raw5096step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5096step1 raw5096step0; decide +kernel
      have hl : raw5096step1Labels = raw5096step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5096step0 raw5096step0Labels permutation56 hz
    mixedMoment B raw5096step1 raw5096step1Labels = mixedMoment B raw5096step2 raw5096step2Labels := by
      have ha : raw5096step2 = (fun i j => raw5096step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5096step2 raw5096step1; decide +kernel
      have hl : raw5096step2Labels = raw5096step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5096step1 raw5096step1Labels permutation8 permutation6
    mixedMoment B raw5096step2 raw5096step2Labels = mixedMoment B raw5096step3 raw5096step3Labels := by
      have ha : raw5096step3 = raw5096step2 := by apply Matrix.ext; unfold raw5096step3 raw5096step2; decide +kernel
      have hl : raw5096step2Labels = labelEmbedding9 ∘ raw5096step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5096step2 raw5096step2Labels raw5096step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5261 node5261Labels := by rfl

def raw5097 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3]]
def raw5097Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3]]
def raw5097step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5097step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3]]
def raw5097step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5097step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, -3, 3]]
def raw5097step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5097step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![0, 3, -3], ![0, -3, 3]]
def raw5097step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5097step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![3, -3], ![-3, 3]]
def raw5097step4Labels : Fin 2 → Fin 3 := ![1, 2]

def raw5097step5 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]
def raw5097step5Labels : Fin 2 → Fin 3 := ![1, 2]

def raw5097step6 : Matrix (Fin 2) (Fin 2) ℤ := ![![-3, 3], ![3, -3]]
def raw5097step6Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical5097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5097 raw5097Labels = mixedMoment B node4085 node4085Labels := by
  calc
    mixedMoment B raw5097 raw5097Labels = mixedMoment B raw5097step0 raw5097step0Labels := by
      have hz : ∀ j, raw5097 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5097step0 = (fun i j => raw5097 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5097step0 raw5097; decide +kernel
      have hl : raw5097step0Labels = raw5097Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5097 raw5097Labels permutation520 hz
    mixedMoment B raw5097step0 raw5097step0Labels = mixedMoment B raw5097step1 raw5097step1Labels := by
      have hz : ∀ j, raw5097step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5097step1 = (fun i j => raw5097step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5097step1 raw5097step0; decide +kernel
      have hl : raw5097step1Labels = raw5097step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5097step0 raw5097step0Labels permutation104 hz
    mixedMoment B raw5097step1 raw5097step1Labels = mixedMoment B raw5097step2 raw5097step2Labels := by
      have hz : ∀ j, raw5097step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw5097step2 = (fun i j => raw5097step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw5097step2 raw5097step1; decide +kernel
      have hl : raw5097step2Labels = raw5097step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5097step1 raw5097step1Labels permutation20 hz
    mixedMoment B raw5097step2 raw5097step2Labels = mixedMoment B raw5097step3 raw5097step3Labels := by
      have hz : ∀ j, raw5097step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw5097step3 = (fun i j => raw5097step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw5097step3 raw5097step2; decide +kernel
      have hl : raw5097step3Labels = raw5097step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5097step2 raw5097step2Labels permutation4 hz
    mixedMoment B raw5097step3 raw5097step3Labels = mixedMoment B raw5097step4 raw5097step4Labels := by
      have hz : ∀ i, raw5097step3 i (permutation2 0) = 0 := by decide +kernel
      have ha : raw5097step4 = (fun i j => raw5097step3 i (permutation2 j.succ)) := by apply Matrix.ext; unfold raw5097step4 raw5097step3; decide +kernel
      have hl : raw5097step4Labels = (fun j => raw5097step3Labels (permutation2 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5097step3 raw5097step3Labels permutation2 hz
    mixedMoment B raw5097step4 raw5097step4Labels = mixedMoment B raw5097step5 raw5097step5Labels := by
      have ha : raw5097step5 = (fun i j => raw5097step4 (permutation1 i) (permutation0 j)) := by apply Matrix.ext; unfold raw5097step5 raw5097step4; decide +kernel
      have hl : raw5097step5Labels = raw5097step4Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5097step4 raw5097step4Labels permutation1 permutation0
    mixedMoment B raw5097step5 raw5097step5Labels = mixedMoment B raw5097step6 raw5097step6Labels := by
      have ha : raw5097step6 = raw5097step5 := by apply Matrix.ext; unfold raw5097step6 raw5097step5; decide +kernel
      have hl : raw5097step5Labels = labelEmbedding3 ∘ raw5097step6Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5097step5 raw5097step5Labels raw5097step6Labels labelEmbedding3 hl
    _ = mixedMoment B node4085 node4085Labels := by rfl

def raw5098 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3]]
def raw5098Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5098step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3]]
def raw5098step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5098step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, 0, 0], ![0, -3, 3]]
def raw5098step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5098step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, -3, 3]]
def raw5098step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5098step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw5098step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5098step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw5098step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5098step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw5098step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5098 raw5098Labels = mixedMoment B node4897 node4897Labels := by
  calc
    mixedMoment B raw5098 raw5098Labels = mixedMoment B raw5098step0 raw5098step0Labels := by
      have hz : ∀ j, raw5098 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5098step0 = (fun i j => raw5098 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5098step0 raw5098; decide +kernel
      have hl : raw5098step0Labels = raw5098Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5098 raw5098Labels permutation520 hz
    mixedMoment B raw5098step0 raw5098step0Labels = mixedMoment B raw5098step1 raw5098step1Labels := by
      have hz : ∀ j, raw5098step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5098step1 = (fun i j => raw5098step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5098step1 raw5098step0; decide +kernel
      have hl : raw5098step1Labels = raw5098step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5098step0 raw5098step0Labels permutation104 hz
    mixedMoment B raw5098step1 raw5098step1Labels = mixedMoment B raw5098step2 raw5098step2Labels := by
      have hz : ∀ j, raw5098step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw5098step2 = (fun i j => raw5098step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw5098step2 raw5098step1; decide +kernel
      have hl : raw5098step2Labels = raw5098step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5098step1 raw5098step1Labels permutation20 hz
    mixedMoment B raw5098step2 raw5098step2Labels = mixedMoment B raw5098step3 raw5098step3Labels := by
      have ha : raw5098step3 = (fun i j => raw5098step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5098step3 raw5098step2; decide +kernel
      have hl : raw5098step3Labels = raw5098step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5098step2 raw5098step2Labels permutation7 permutation6
    mixedMoment B raw5098step3 raw5098step3Labels = mixedMoment B raw5098step4 raw5098step4Labels := by
      have ha : raw5098step4 = -raw5098step3 := by apply Matrix.ext; change ∀ i j, raw5098step4 i j = -(raw5098step3 i j); unfold raw5098step4 raw5098step3; decide +kernel
      have hl : raw5098step4Labels = raw5098step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5098step4 raw5098step4Labels = mixedMoment B raw5098step5 raw5098step5Labels := by
      have ha : raw5098step5 = raw5098step4 := by apply Matrix.ext; unfold raw5098step5 raw5098step4; decide +kernel
      have hl : raw5098step4Labels = labelEmbedding9 ∘ raw5098step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5098step4 raw5098step4Labels raw5098step5Labels labelEmbedding9 hl
    _ = mixedMoment B node4897 node4897Labels := by rfl

def raw5099 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -3, 3]]
def raw5099Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -3, 3]]
def raw5099step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5099step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5099step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5099step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, -3, 3]]
def raw5099step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5099step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw5099step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5099step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw5099step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5099step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw5099step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5099 raw5099Labels = mixedMoment B node4897 node4897Labels := by
  calc
    mixedMoment B raw5099 raw5099Labels = mixedMoment B raw5099step0 raw5099step0Labels := by
      have hz : ∀ j, raw5099 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5099step0 = (fun i j => raw5099 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5099step0 raw5099; decide +kernel
      have hl : raw5099step0Labels = raw5099Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5099 raw5099Labels permutation520 hz
    mixedMoment B raw5099step0 raw5099step0Labels = mixedMoment B raw5099step1 raw5099step1Labels := by
      have hz : ∀ j, raw5099step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw5099step1 = (fun i j => raw5099step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw5099step1 raw5099step0; decide +kernel
      have hl : raw5099step1Labels = raw5099step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5099step0 raw5099step0Labels permutation104 hz
    mixedMoment B raw5099step1 raw5099step1Labels = mixedMoment B raw5099step2 raw5099step2Labels := by
      have hz : ∀ j, raw5099step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5099step2 = (fun i j => raw5099step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5099step2 raw5099step1; decide +kernel
      have hl : raw5099step2Labels = raw5099step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5099step1 raw5099step1Labels permutation14 hz
    mixedMoment B raw5099step2 raw5099step2Labels = mixedMoment B raw5099step3 raw5099step3Labels := by
      have ha : raw5099step3 = (fun i j => raw5099step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5099step3 raw5099step2; decide +kernel
      have hl : raw5099step3Labels = raw5099step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5099step2 raw5099step2Labels permutation7 permutation6
    mixedMoment B raw5099step3 raw5099step3Labels = mixedMoment B raw5099step4 raw5099step4Labels := by
      have ha : raw5099step4 = -raw5099step3 := by apply Matrix.ext; change ∀ i j, raw5099step4 i j = -(raw5099step3 i j); unfold raw5099step4 raw5099step3; decide +kernel
      have hl : raw5099step4Labels = raw5099step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5099step4 raw5099step4Labels = mixedMoment B raw5099step5 raw5099step5Labels := by
      have ha : raw5099step5 = raw5099step4 := by apply Matrix.ext; unfold raw5099step5 raw5099step4; decide +kernel
      have hl : raw5099step4Labels = labelEmbedding9 ∘ raw5099step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5099step4 raw5099step4Labels raw5099step5Labels labelEmbedding9 hl
    _ = mixedMoment B node4897 node4897Labels := by rfl

def raw5100 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -3, 3]]
def raw5100Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5100step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5100step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![-1, 1, 0], ![0, -3, 3]]
def raw5100step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5100step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![0, -3, 3]]
def raw5100step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5100step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-3, 1, 2]]
def raw5100step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5100step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw5100step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw5100step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw5100step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5100 raw5100Labels = mixedMoment B node4897 node4897Labels := by
  calc
    mixedMoment B raw5100 raw5100Labels = mixedMoment B raw5100step0 raw5100step0Labels := by
      have hz : ∀ j, raw5100 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5100step0 = (fun i j => raw5100 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5100step0 raw5100; decide +kernel
      have hl : raw5100step0Labels = raw5100Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5100 raw5100Labels permutation520 hz
    mixedMoment B raw5100step0 raw5100step0Labels = mixedMoment B raw5100step1 raw5100step1Labels := by
      have hz : ∀ j, raw5100step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5100step1 = (fun i j => raw5100step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5100step1 raw5100step0; decide +kernel
      have hl : raw5100step1Labels = raw5100step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5100step0 raw5100step0Labels permutation80 hz
    mixedMoment B raw5100step1 raw5100step1Labels = mixedMoment B raw5100step2 raw5100step2Labels := by
      have hz : ∀ j, raw5100step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5100step2 = (fun i j => raw5100step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5100step2 raw5100step1; decide +kernel
      have hl : raw5100step2Labels = raw5100step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5100step1 raw5100step1Labels permutation14 hz
    mixedMoment B raw5100step2 raw5100step2Labels = mixedMoment B raw5100step3 raw5100step3Labels := by
      have ha : raw5100step3 = (fun i j => raw5100step2 (permutation7 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5100step3 raw5100step2; decide +kernel
      have hl : raw5100step3Labels = raw5100step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5100step2 raw5100step2Labels permutation7 permutation6
    mixedMoment B raw5100step3 raw5100step3Labels = mixedMoment B raw5100step4 raw5100step4Labels := by
      have ha : raw5100step4 = -raw5100step3 := by apply Matrix.ext; change ∀ i j, raw5100step4 i j = -(raw5100step3 i j); unfold raw5100step4 raw5100step3; decide +kernel
      have hl : raw5100step4Labels = raw5100step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5100step4 raw5100step4Labels = mixedMoment B raw5100step5 raw5100step5Labels := by
      have ha : raw5100step5 = raw5100step4 := by apply Matrix.ext; unfold raw5100step5 raw5100step4; decide +kernel
      have hl : raw5100step4Labels = labelEmbedding9 ∘ raw5100step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5100step4 raw5100step4Labels raw5100step5Labels labelEmbedding9 hl
    _ = mixedMoment B node4897 node4897Labels := by rfl

def raw5101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5101Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5101step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5101step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5101step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5101step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw5101step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5101step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw5101step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5101 raw5101Labels = mixedMoment B node4894 node4894Labels := by
  calc
    mixedMoment B raw5101 raw5101Labels = mixedMoment B raw5101step0 raw5101step0Labels := by
      have hz : ∀ j, raw5101 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5101step0 = (fun i j => raw5101 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5101step0 raw5101; decide +kernel
      have hl : raw5101step0Labels = raw5101Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5101 raw5101Labels permutation434 hz
    mixedMoment B raw5101step0 raw5101step0Labels = mixedMoment B raw5101step1 raw5101step1Labels := by
      have hz : ∀ j, raw5101step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5101step1 = (fun i j => raw5101step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5101step1 raw5101step0; decide +kernel
      have hl : raw5101step1Labels = raw5101step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5101step0 raw5101step0Labels permutation80 hz
    mixedMoment B raw5101step1 raw5101step1Labels = mixedMoment B raw5101step2 raw5101step2Labels := by
      have ha : raw5101step2 = (fun i j => raw5101step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5101step2 raw5101step1; decide +kernel
      have hl : raw5101step2Labels = raw5101step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5101step1 raw5101step1Labels permutation31 permutation2
    mixedMoment B raw5101step2 raw5101step2Labels = mixedMoment B raw5101step3 raw5101step3Labels := by
      have ha : raw5101step3 = -raw5101step2 := by apply Matrix.ext; change ∀ i j, raw5101step3 i j = -(raw5101step2 i j); unfold raw5101step3 raw5101step2; decide +kernel
      have hl : raw5101step3Labels = raw5101step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4894 node4894Labels := by rfl

def raw5102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5102Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5102step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5102step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5102step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5102step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw5102step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5102step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw5102step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5102 raw5102Labels = mixedMoment B node4894 node4894Labels := by
  calc
    mixedMoment B raw5102 raw5102Labels = mixedMoment B raw5102step0 raw5102step0Labels := by
      have hz : ∀ j, raw5102 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5102step0 = (fun i j => raw5102 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5102step0 raw5102; decide +kernel
      have hl : raw5102step0Labels = raw5102Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5102 raw5102Labels permutation434 hz
    mixedMoment B raw5102step0 raw5102step0Labels = mixedMoment B raw5102step1 raw5102step1Labels := by
      have hz : ∀ j, raw5102step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5102step1 = (fun i j => raw5102step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5102step1 raw5102step0; decide +kernel
      have hl : raw5102step1Labels = raw5102step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5102step0 raw5102step0Labels permutation56 hz
    mixedMoment B raw5102step1 raw5102step1Labels = mixedMoment B raw5102step2 raw5102step2Labels := by
      have ha : raw5102step2 = (fun i j => raw5102step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5102step2 raw5102step1; decide +kernel
      have hl : raw5102step2Labels = raw5102step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5102step1 raw5102step1Labels permutation31 permutation2
    mixedMoment B raw5102step2 raw5102step2Labels = mixedMoment B raw5102step3 raw5102step3Labels := by
      have ha : raw5102step3 = -raw5102step2 := by apply Matrix.ext; change ∀ i j, raw5102step3 i j = -(raw5102step2 i j); unfold raw5102step3 raw5102step2; decide +kernel
      have hl : raw5102step3Labels = raw5102step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4894 node4894Labels := by rfl

def raw5103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5103Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5103step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5103step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5103step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5103step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw5103step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5103step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw5103step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5103 raw5103Labels = mixedMoment B node4894 node4894Labels := by
  calc
    mixedMoment B raw5103 raw5103Labels = mixedMoment B raw5103step0 raw5103step0Labels := by
      have hz : ∀ j, raw5103 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5103step0 = (fun i j => raw5103 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5103step0 raw5103; decide +kernel
      have hl : raw5103step0Labels = raw5103Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5103 raw5103Labels permutation346 hz
    mixedMoment B raw5103step0 raw5103step0Labels = mixedMoment B raw5103step1 raw5103step1Labels := by
      have hz : ∀ j, raw5103step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5103step1 = (fun i j => raw5103step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5103step1 raw5103step0; decide +kernel
      have hl : raw5103step1Labels = raw5103step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5103step0 raw5103step0Labels permutation56 hz
    mixedMoment B raw5103step1 raw5103step1Labels = mixedMoment B raw5103step2 raw5103step2Labels := by
      have ha : raw5103step2 = (fun i j => raw5103step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5103step2 raw5103step1; decide +kernel
      have hl : raw5103step2Labels = raw5103step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5103step1 raw5103step1Labels permutation31 permutation2
    mixedMoment B raw5103step2 raw5103step2Labels = mixedMoment B raw5103step3 raw5103step3Labels := by
      have ha : raw5103step3 = -raw5103step2 := by apply Matrix.ext; change ∀ i j, raw5103step3 i j = -(raw5103step2 i j); unfold raw5103step3 raw5103step2; decide +kernel
      have hl : raw5103step3Labels = raw5103step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4894 node4894Labels := by rfl

def raw5104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5104Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5104step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5104step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5104step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5104step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![3, 0, -3]]
def raw5104step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5104step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![3, -3]]
def raw5104step3Labels : Fin 2 → Fin 3 := ![0, 2]

def raw5104step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![3, -3], ![-1, 1], ![-2, 2]]
def raw5104step4Labels : Fin 2 → Fin 3 := ![0, 2]

def raw5104step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw5104step5Labels : Fin 2 → Fin 3 := ![0, 2]

def raw5104step6 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw5104step6Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical5104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5104 raw5104Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw5104 raw5104Labels = mixedMoment B raw5104step0 raw5104step0Labels := by
      have hz : ∀ j, raw5104 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5104step0 = (fun i j => raw5104 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5104step0 raw5104; decide +kernel
      have hl : raw5104step0Labels = raw5104Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5104 raw5104Labels permutation434 hz
    mixedMoment B raw5104step0 raw5104step0Labels = mixedMoment B raw5104step1 raw5104step1Labels := by
      have hz : ∀ j, raw5104step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5104step1 = (fun i j => raw5104step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5104step1 raw5104step0; decide +kernel
      have hl : raw5104step1Labels = raw5104step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5104step0 raw5104step0Labels permutation80 hz
    mixedMoment B raw5104step1 raw5104step1Labels = mixedMoment B raw5104step2 raw5104step2Labels := by
      have hz : ∀ j, raw5104step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5104step2 = (fun i j => raw5104step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5104step2 raw5104step1; decide +kernel
      have hl : raw5104step2Labels = raw5104step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5104step1 raw5104step1Labels permutation14 hz
    mixedMoment B raw5104step2 raw5104step2Labels = mixedMoment B raw5104step3 raw5104step3Labels := by
      have hz : ∀ i, raw5104step2 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw5104step3 = (fun i j => raw5104step2 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw5104step3 raw5104step2; decide +kernel
      have hl : raw5104step3Labels = (fun j => raw5104step2Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw5104step2 raw5104step2Labels permutation4 hz
    mixedMoment B raw5104step3 raw5104step3Labels = mixedMoment B raw5104step4 raw5104step4Labels := by
      have ha : raw5104step4 = (fun i j => raw5104step3 (permutation7 i) (permutation0 j)) := by apply Matrix.ext; unfold raw5104step4 raw5104step3; decide +kernel
      have hl : raw5104step4Labels = raw5104step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5104step3 raw5104step3Labels permutation7 permutation0
    mixedMoment B raw5104step4 raw5104step4Labels = mixedMoment B raw5104step5 raw5104step5Labels := by
      have ha : raw5104step5 = -raw5104step4 := by apply Matrix.ext; change ∀ i j, raw5104step5 i j = -(raw5104step4 i j); unfold raw5104step5 raw5104step4; decide +kernel
      have hl : raw5104step5Labels = raw5104step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5104step5 raw5104step5Labels = mixedMoment B raw5104step6 raw5104step6Labels := by
      have ha : raw5104step6 = raw5104step5 := by apply Matrix.ext; unfold raw5104step6 raw5104step5; decide +kernel
      have hl : raw5104step5Labels = labelEmbedding2 ∘ raw5104step6Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5104step5 raw5104step5Labels raw5104step6Labels labelEmbedding2 hl
    _ = mixedMoment B node4084 node4084Labels := by rfl

def raw5105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5105Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5105step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5105step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5105step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5105step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![2, 1, -3]]
def raw5105step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5105step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw5105step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw5105step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw5105step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5105 raw5105Labels = mixedMoment B node5308 node5308Labels := by
  calc
    mixedMoment B raw5105 raw5105Labels = mixedMoment B raw5105step0 raw5105step0Labels := by
      have hz : ∀ j, raw5105 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5105step0 = (fun i j => raw5105 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5105step0 raw5105; decide +kernel
      have hl : raw5105step0Labels = raw5105Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5105 raw5105Labels permutation434 hz
    mixedMoment B raw5105step0 raw5105step0Labels = mixedMoment B raw5105step1 raw5105step1Labels := by
      have hz : ∀ j, raw5105step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5105step1 = (fun i j => raw5105step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5105step1 raw5105step0; decide +kernel
      have hl : raw5105step1Labels = raw5105step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5105step0 raw5105step0Labels permutation80 hz
    mixedMoment B raw5105step1 raw5105step1Labels = mixedMoment B raw5105step2 raw5105step2Labels := by
      have hz : ∀ j, raw5105step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5105step2 = (fun i j => raw5105step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5105step2 raw5105step1; decide +kernel
      have hl : raw5105step2Labels = raw5105step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5105step1 raw5105step1Labels permutation14 hz
    mixedMoment B raw5105step2 raw5105step2Labels = mixedMoment B raw5105step3 raw5105step3Labels := by
      have ha : raw5105step3 = (fun i j => raw5105step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5105step3 raw5105step2; decide +kernel
      have hl : raw5105step3Labels = raw5105step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5105step2 raw5105step2Labels permutation7 permutation7
    mixedMoment B raw5105step3 raw5105step3Labels = mixedMoment B raw5105step4 raw5105step4Labels := by
      have ha : raw5105step4 = raw5105step3 := by apply Matrix.ext; unfold raw5105step4 raw5105step3; decide +kernel
      have hl : raw5105step3Labels = labelEmbedding10 ∘ raw5105step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5105step3 raw5105step3Labels raw5105step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5308 node5308Labels := by rfl

def raw5106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5106Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5106step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5106step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5106step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5106step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5106step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw5106step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5106 raw5106Labels = mixedMoment B node4605 node4605Labels := by
  calc
    mixedMoment B raw5106 raw5106Labels = mixedMoment B raw5106step0 raw5106step0Labels := by
      have hz : ∀ j, raw5106 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5106step0 = (fun i j => raw5106 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5106step0 raw5106; decide +kernel
      have hl : raw5106step0Labels = raw5106Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5106 raw5106Labels permutation434 hz
    mixedMoment B raw5106step0 raw5106step0Labels = mixedMoment B raw5106step1 raw5106step1Labels := by
      have hz : ∀ j, raw5106step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5106step1 = (fun i j => raw5106step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5106step1 raw5106step0; decide +kernel
      have hl : raw5106step1Labels = raw5106step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5106step0 raw5106step0Labels permutation80 hz
    mixedMoment B raw5106step1 raw5106step1Labels = mixedMoment B raw5106step2 raw5106step2Labels := by
      have ha : raw5106step2 = (fun i j => raw5106step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5106step2 raw5106step1; decide +kernel
      have hl : raw5106step2Labels = raw5106step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5106step1 raw5106step1Labels permutation10 permutation2
    _ = mixedMoment B node4605 node4605Labels := by rfl

def raw5107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5107Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5107step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5107step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw5107step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5107step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw5107step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5107 raw5107Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw5107 raw5107Labels = mixedMoment B raw5107step0 raw5107step0Labels := by
      have hz : ∀ j, raw5107 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5107step0 = (fun i j => raw5107 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5107step0 raw5107; decide +kernel
      have hl : raw5107step0Labels = raw5107Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5107 raw5107Labels permutation434 hz
    mixedMoment B raw5107step0 raw5107step0Labels = mixedMoment B raw5107step1 raw5107step1Labels := by
      have ha : raw5107step1 = (fun i j => raw5107step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5107step1 raw5107step0; decide +kernel
      have hl : raw5107step1Labels = raw5107step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5107step0 raw5107step0Labels permutation139 permutation2
    mixedMoment B raw5107step1 raw5107step1Labels = mixedMoment B raw5107step2 raw5107step2Labels := by
      have ha : raw5107step2 = -raw5107step1 := by apply Matrix.ext; change ∀ i j, raw5107step2 i j = -(raw5107step1 i j); unfold raw5107step2 raw5107step1; decide +kernel
      have hl : raw5107step2Labels = raw5107step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4804 node4804Labels := by rfl

def raw5108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5108Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5108step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5108step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5108step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw5108step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5108step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw5108step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5108 raw5108Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw5108 raw5108Labels = mixedMoment B raw5108step0 raw5108step0Labels := by
      have hz : ∀ j, raw5108 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5108step0 = (fun i j => raw5108 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5108step0 raw5108; decide +kernel
      have hl : raw5108step0Labels = raw5108Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5108 raw5108Labels permutation346 hz
    mixedMoment B raw5108step0 raw5108step0Labels = mixedMoment B raw5108step1 raw5108step1Labels := by
      have ha : raw5108step1 = (fun i j => raw5108step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5108step1 raw5108step0; decide +kernel
      have hl : raw5108step1Labels = raw5108step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5108step0 raw5108step0Labels permutation139 permutation2
    mixedMoment B raw5108step1 raw5108step1Labels = mixedMoment B raw5108step2 raw5108step2Labels := by
      have ha : raw5108step2 = -raw5108step1 := by apply Matrix.ext; change ∀ i j, raw5108step2 i j = -(raw5108step1 i j); unfold raw5108step2 raw5108step1; decide +kernel
      have hl : raw5108step2Labels = raw5108step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4804 node4804Labels := by rfl

def raw5109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5109Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5109step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5109step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5109step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5109step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw5109step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5109step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw5109step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5109 raw5109Labels = mixedMoment B node4841 node4841Labels := by
  calc
    mixedMoment B raw5109 raw5109Labels = mixedMoment B raw5109step0 raw5109step0Labels := by
      have hz : ∀ j, raw5109 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5109step0 = (fun i j => raw5109 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5109step0 raw5109; decide +kernel
      have hl : raw5109step0Labels = raw5109Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5109 raw5109Labels permutation434 hz
    mixedMoment B raw5109step0 raw5109step0Labels = mixedMoment B raw5109step1 raw5109step1Labels := by
      have hz : ∀ j, raw5109step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5109step1 = (fun i j => raw5109step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5109step1 raw5109step0; decide +kernel
      have hl : raw5109step1Labels = raw5109step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5109step0 raw5109step0Labels permutation80 hz
    mixedMoment B raw5109step1 raw5109step1Labels = mixedMoment B raw5109step2 raw5109step2Labels := by
      have ha : raw5109step2 = (fun i j => raw5109step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5109step2 raw5109step1; decide +kernel
      have hl : raw5109step2Labels = raw5109step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5109step1 raw5109step1Labels permutation29 permutation2
    mixedMoment B raw5109step2 raw5109step2Labels = mixedMoment B raw5109step3 raw5109step3Labels := by
      have ha : raw5109step3 = -raw5109step2 := by apply Matrix.ext; change ∀ i j, raw5109step3 i j = -(raw5109step2 i j); unfold raw5109step3 raw5109step2; decide +kernel
      have hl : raw5109step3Labels = raw5109step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4841 node4841Labels := by rfl

def raw5110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5110Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5110step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5110step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5110step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5110step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw5110step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5110 raw5110Labels = mixedMoment B node5272 node5272Labels := by
  calc
    mixedMoment B raw5110 raw5110Labels = mixedMoment B raw5110step0 raw5110step0Labels := by
      have hz : ∀ j, raw5110 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5110step0 = (fun i j => raw5110 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5110step0 raw5110; decide +kernel
      have hl : raw5110step0Labels = raw5110Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5110 raw5110Labels permutation434 hz
    mixedMoment B raw5110step0 raw5110step0Labels = mixedMoment B raw5110step1 raw5110step1Labels := by
      have hz : ∀ j, raw5110step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5110step1 = (fun i j => raw5110step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5110step1 raw5110step0; decide +kernel
      have hl : raw5110step1Labels = raw5110step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5110step0 raw5110step0Labels permutation80 hz
    mixedMoment B raw5110step1 raw5110step1Labels = mixedMoment B raw5110step2 raw5110step2Labels := by
      have ha : raw5110step2 = (fun i j => raw5110step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5110step2 raw5110step1; decide +kernel
      have hl : raw5110step2Labels = raw5110step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5110step1 raw5110step1Labels permutation10 permutation2
    _ = mixedMoment B node5272 node5272Labels := by rfl

def raw5111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5111Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5111step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5111step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5111step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5111step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw5111step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5111 raw5111Labels = mixedMoment B node4605 node4605Labels := by
  calc
    mixedMoment B raw5111 raw5111Labels = mixedMoment B raw5111step0 raw5111step0Labels := by
      have hz : ∀ j, raw5111 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5111step0 = (fun i j => raw5111 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5111step0 raw5111; decide +kernel
      have hl : raw5111step0Labels = raw5111Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5111 raw5111Labels permutation434 hz
    mixedMoment B raw5111step0 raw5111step0Labels = mixedMoment B raw5111step1 raw5111step1Labels := by
      have hz : ∀ j, raw5111step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5111step1 = (fun i j => raw5111step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5111step1 raw5111step0; decide +kernel
      have hl : raw5111step1Labels = raw5111step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5111step0 raw5111step0Labels permutation56 hz
    mixedMoment B raw5111step1 raw5111step1Labels = mixedMoment B raw5111step2 raw5111step2Labels := by
      have ha : raw5111step2 = (fun i j => raw5111step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5111step2 raw5111step1; decide +kernel
      have hl : raw5111step2Labels = raw5111step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5111step1 raw5111step1Labels permutation10 permutation2
    _ = mixedMoment B node4605 node4605Labels := by rfl

def raw5112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5112Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5112step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5112step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw5112step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5112step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw5112step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5112 raw5112Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw5112 raw5112Labels = mixedMoment B raw5112step0 raw5112step0Labels := by
      have hz : ∀ j, raw5112 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5112step0 = (fun i j => raw5112 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5112step0 raw5112; decide +kernel
      have hl : raw5112step0Labels = raw5112Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5112 raw5112Labels permutation434 hz
    mixedMoment B raw5112step0 raw5112step0Labels = mixedMoment B raw5112step1 raw5112step1Labels := by
      have ha : raw5112step1 = (fun i j => raw5112step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5112step1 raw5112step0; decide +kernel
      have hl : raw5112step1Labels = raw5112step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5112step0 raw5112step0Labels permutation145 permutation2
    mixedMoment B raw5112step1 raw5112step1Labels = mixedMoment B raw5112step2 raw5112step2Labels := by
      have ha : raw5112step2 = -raw5112step1 := by apply Matrix.ext; change ∀ i j, raw5112step2 i j = -(raw5112step1 i j); unfold raw5112step2 raw5112step1; decide +kernel
      have hl : raw5112step2Labels = raw5112step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4804 node4804Labels := by rfl

def raw5113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5113Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5113step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5113step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw5113step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5113step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw5113step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5113 raw5113Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw5113 raw5113Labels = mixedMoment B raw5113step0 raw5113step0Labels := by
      have hz : ∀ j, raw5113 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5113step0 = (fun i j => raw5113 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5113step0 raw5113; decide +kernel
      have hl : raw5113step0Labels = raw5113Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5113 raw5113Labels permutation265 hz
    mixedMoment B raw5113step0 raw5113step0Labels = mixedMoment B raw5113step1 raw5113step1Labels := by
      have ha : raw5113step1 = (fun i j => raw5113step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5113step1 raw5113step0; decide +kernel
      have hl : raw5113step1Labels = raw5113step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5113step0 raw5113step0Labels permutation139 permutation2
    mixedMoment B raw5113step1 raw5113step1Labels = mixedMoment B raw5113step2 raw5113step2Labels := by
      have ha : raw5113step2 = -raw5113step1 := by apply Matrix.ext; change ∀ i j, raw5113step2 i j = -(raw5113step1 i j); unfold raw5113step2 raw5113step1; decide +kernel
      have hl : raw5113step2Labels = raw5113step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4804 node4804Labels := by rfl

def raw5114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5114Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5114step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5114step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5114step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5114step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw5114step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5114step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw5114step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5114 raw5114Labels = mixedMoment B node4841 node4841Labels := by
  calc
    mixedMoment B raw5114 raw5114Labels = mixedMoment B raw5114step0 raw5114step0Labels := by
      have hz : ∀ j, raw5114 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5114step0 = (fun i j => raw5114 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5114step0 raw5114; decide +kernel
      have hl : raw5114step0Labels = raw5114Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5114 raw5114Labels permutation434 hz
    mixedMoment B raw5114step0 raw5114step0Labels = mixedMoment B raw5114step1 raw5114step1Labels := by
      have hz : ∀ j, raw5114step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5114step1 = (fun i j => raw5114step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5114step1 raw5114step0; decide +kernel
      have hl : raw5114step1Labels = raw5114step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5114step0 raw5114step0Labels permutation56 hz
    mixedMoment B raw5114step1 raw5114step1Labels = mixedMoment B raw5114step2 raw5114step2Labels := by
      have ha : raw5114step2 = (fun i j => raw5114step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5114step2 raw5114step1; decide +kernel
      have hl : raw5114step2Labels = raw5114step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5114step1 raw5114step1Labels permutation29 permutation2
    mixedMoment B raw5114step2 raw5114step2Labels = mixedMoment B raw5114step3 raw5114step3Labels := by
      have ha : raw5114step3 = -raw5114step2 := by apply Matrix.ext; change ∀ i j, raw5114step3 i j = -(raw5114step2 i j); unfold raw5114step3 raw5114step2; decide +kernel
      have hl : raw5114step3Labels = raw5114step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4841 node4841Labels := by rfl

def raw5115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5115Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5115step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5115step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![0, -1, 1], ![2, 1, -3]]
def raw5115step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5115step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw5115step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5115 raw5115Labels = mixedMoment B node5272 node5272Labels := by
  calc
    mixedMoment B raw5115 raw5115Labels = mixedMoment B raw5115step0 raw5115step0Labels := by
      have hz : ∀ j, raw5115 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5115step0 = (fun i j => raw5115 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5115step0 raw5115; decide +kernel
      have hl : raw5115step0Labels = raw5115Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5115 raw5115Labels permutation434 hz
    mixedMoment B raw5115step0 raw5115step0Labels = mixedMoment B raw5115step1 raw5115step1Labels := by
      have hz : ∀ j, raw5115step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5115step1 = (fun i j => raw5115step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5115step1 raw5115step0; decide +kernel
      have hl : raw5115step1Labels = raw5115step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5115step0 raw5115step0Labels permutation56 hz
    mixedMoment B raw5115step1 raw5115step1Labels = mixedMoment B raw5115step2 raw5115step2Labels := by
      have ha : raw5115step2 = (fun i j => raw5115step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5115step2 raw5115step1; decide +kernel
      have hl : raw5115step2Labels = raw5115step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5115step1 raw5115step1Labels permutation10 permutation2
    _ = mixedMoment B node5272 node5272Labels := by rfl

def raw5116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5116Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5116step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5116step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5116step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5116step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw5116step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5116 raw5116Labels = mixedMoment B node4605 node4605Labels := by
  calc
    mixedMoment B raw5116 raw5116Labels = mixedMoment B raw5116step0 raw5116step0Labels := by
      have hz : ∀ j, raw5116 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5116step0 = (fun i j => raw5116 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5116step0 raw5116; decide +kernel
      have hl : raw5116step0Labels = raw5116Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5116 raw5116Labels permutation346 hz
    mixedMoment B raw5116step0 raw5116step0Labels = mixedMoment B raw5116step1 raw5116step1Labels := by
      have hz : ∀ j, raw5116step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5116step1 = (fun i j => raw5116step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5116step1 raw5116step0; decide +kernel
      have hl : raw5116step1Labels = raw5116step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5116step0 raw5116step0Labels permutation56 hz
    mixedMoment B raw5116step1 raw5116step1Labels = mixedMoment B raw5116step2 raw5116step2Labels := by
      have ha : raw5116step2 = (fun i j => raw5116step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5116step2 raw5116step1; decide +kernel
      have hl : raw5116step2Labels = raw5116step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5116step1 raw5116step1Labels permutation10 permutation2
    _ = mixedMoment B node4605 node4605Labels := by rfl

def raw5117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5117Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5117step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5117step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw5117step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5117step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw5117step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5117 raw5117Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw5117 raw5117Labels = mixedMoment B raw5117step0 raw5117step0Labels := by
      have hz : ∀ j, raw5117 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5117step0 = (fun i j => raw5117 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5117step0 raw5117; decide +kernel
      have hl : raw5117step0Labels = raw5117Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5117 raw5117Labels permutation346 hz
    mixedMoment B raw5117step0 raw5117step0Labels = mixedMoment B raw5117step1 raw5117step1Labels := by
      have ha : raw5117step1 = (fun i j => raw5117step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5117step1 raw5117step0; decide +kernel
      have hl : raw5117step1Labels = raw5117step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5117step0 raw5117step0Labels permutation145 permutation2
    mixedMoment B raw5117step1 raw5117step1Labels = mixedMoment B raw5117step2 raw5117step2Labels := by
      have ha : raw5117step2 = -raw5117step1 := by apply Matrix.ext; change ∀ i j, raw5117step2 i j = -(raw5117step1 i j); unfold raw5117step2 raw5117step1; decide +kernel
      have hl : raw5117step2Labels = raw5117step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4804 node4804Labels := by rfl

def raw5118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5118Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![3, 0, -3]]
def raw5118step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5118step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw5118step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5118step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw5118step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5118 raw5118Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw5118 raw5118Labels = mixedMoment B raw5118step0 raw5118step0Labels := by
      have hz : ∀ j, raw5118 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5118step0 = (fun i j => raw5118 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5118step0 raw5118; decide +kernel
      have hl : raw5118step0Labels = raw5118Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5118 raw5118Labels permutation265 hz
    mixedMoment B raw5118step0 raw5118step0Labels = mixedMoment B raw5118step1 raw5118step1Labels := by
      have ha : raw5118step1 = (fun i j => raw5118step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5118step1 raw5118step0; decide +kernel
      have hl : raw5118step1Labels = raw5118step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5118step0 raw5118step0Labels permutation145 permutation2
    mixedMoment B raw5118step1 raw5118step1Labels = mixedMoment B raw5118step2 raw5118step2Labels := by
      have ha : raw5118step2 = -raw5118step1 := by apply Matrix.ext; change ∀ i j, raw5118step2 i j = -(raw5118step1 i j); unfold raw5118step2 raw5118step1; decide +kernel
      have hl : raw5118step2Labels = raw5118step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4804 node4804Labels := by rfl

def raw5119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5119Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5119step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5119step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![-1, 0, 1], ![3, 0, -3]]
def raw5119step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5119step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw5119step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5119step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw5119step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5119 raw5119Labels = mixedMoment B node4841 node4841Labels := by
  calc
    mixedMoment B raw5119 raw5119Labels = mixedMoment B raw5119step0 raw5119step0Labels := by
      have hz : ∀ j, raw5119 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5119step0 = (fun i j => raw5119 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5119step0 raw5119; decide +kernel
      have hl : raw5119step0Labels = raw5119Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5119 raw5119Labels permutation346 hz
    mixedMoment B raw5119step0 raw5119step0Labels = mixedMoment B raw5119step1 raw5119step1Labels := by
      have hz : ∀ j, raw5119step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5119step1 = (fun i j => raw5119step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5119step1 raw5119step0; decide +kernel
      have hl : raw5119step1Labels = raw5119step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5119step0 raw5119step0Labels permutation56 hz
    mixedMoment B raw5119step1 raw5119step1Labels = mixedMoment B raw5119step2 raw5119step2Labels := by
      have ha : raw5119step2 = (fun i j => raw5119step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5119step2 raw5119step1; decide +kernel
      have hl : raw5119step2Labels = raw5119step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5119step1 raw5119step1Labels permutation29 permutation2
    mixedMoment B raw5119step2 raw5119step2Labels = mixedMoment B raw5119step3 raw5119step3Labels := by
      have ha : raw5119step3 = -raw5119step2 := by apply Matrix.ext; change ∀ i j, raw5119step3 i j = -(raw5119step2 i j); unfold raw5119step3 raw5119step2; decide +kernel
      have hl : raw5119step3Labels = raw5119step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4841 node4841Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
