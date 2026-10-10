import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw20992 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -4, 3]]
def raw20992Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -4, 3]]
def raw20992step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20992step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw20992step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20992step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw20992step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20992 raw20992Labels = mixedMoment B node1252 node1252Labels := by
  calc
    mixedMoment B raw20992 raw20992Labels = mixedMoment B raw20992step0 raw20992step0Labels := by
      have hz : ∀ j, raw20992 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20992step0 = (fun i j => raw20992 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20992step0 raw20992; decide +kernel
      have hl : raw20992step0Labels = raw20992Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20992 raw20992Labels permutation265 hz
    mixedMoment B raw20992step0 raw20992step0Labels = mixedMoment B raw20992step1 raw20992step1Labels := by
      have ha : raw20992step1 = (fun i j => raw20992step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20992step1 raw20992step0; decide +kernel
      have hl : raw20992step1Labels = raw20992step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20992step0 raw20992step0Labels permutation32 permutation7
    mixedMoment B raw20992step1 raw20992step1Labels = mixedMoment B raw20992step2 raw20992step2Labels := by
      have ha : raw20992step2 = raw20992step1 := by apply Matrix.ext; unfold raw20992step2 raw20992step1; decide +kernel
      have hl : raw20992step1Labels = labelEmbedding1 ∘ raw20992step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20992step1 raw20992step1Labels raw20992step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1252 node1252Labels := by rfl

def raw20993 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![-1, 0, 1], ![1, -4, 3]]
def raw20993Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 2, 0], ![-1, 0, 1], ![1, -4, 3]]
def raw20993step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20993step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![-1, 0, 1], ![1, -4, 3]]
def raw20993step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20993step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, 0, -1], ![3, -4, 1]]
def raw20993step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20993step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, 0, -1], ![3, -4, 1]]
def raw20993step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20993 raw20993Labels = mixedMoment B node1282 node1282Labels := by
  calc
    mixedMoment B raw20993 raw20993Labels = mixedMoment B raw20993step0 raw20993step0Labels := by
      have hz : ∀ j, raw20993 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20993step0 = (fun i j => raw20993 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20993step0 raw20993; decide +kernel
      have hl : raw20993step0Labels = raw20993Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20993 raw20993Labels permutation346 hz
    mixedMoment B raw20993step0 raw20993step0Labels = mixedMoment B raw20993step1 raw20993step1Labels := by
      have hz : ∀ j, raw20993step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20993step1 = (fun i j => raw20993step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20993step1 raw20993step0; decide +kernel
      have hl : raw20993step1Labels = raw20993step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20993step0 raw20993step0Labels permutation56 hz
    mixedMoment B raw20993step1 raw20993step1Labels = mixedMoment B raw20993step2 raw20993step2Labels := by
      have ha : raw20993step2 = (fun i j => raw20993step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20993step2 raw20993step1; decide +kernel
      have hl : raw20993step2Labels = raw20993step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20993step1 raw20993step1Labels permutation8 permutation7
    mixedMoment B raw20993step2 raw20993step2Labels = mixedMoment B raw20993step3 raw20993step3Labels := by
      have ha : raw20993step3 = raw20993step2 := by apply Matrix.ext; unfold raw20993step3 raw20993step2; decide +kernel
      have hl : raw20993step2Labels = labelEmbedding1 ∘ raw20993step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20993step2 raw20993step2Labels raw20993step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1282 node1282Labels := by rfl

def raw20994 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20994Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20994step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20994step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20994step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20994step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw20994step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20994 raw20994Labels = mixedMoment B node2226 node2226Labels := by
  calc
    mixedMoment B raw20994 raw20994Labels = mixedMoment B raw20994step0 raw20994step0Labels := by
      have hz : ∀ j, raw20994 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20994step0 = (fun i j => raw20994 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20994step0 raw20994; decide +kernel
      have hl : raw20994step0Labels = raw20994Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20994 raw20994Labels permutation346 hz
    mixedMoment B raw20994step0 raw20994step0Labels = mixedMoment B raw20994step1 raw20994step1Labels := by
      have hz : ∀ j, raw20994step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20994step1 = (fun i j => raw20994step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20994step1 raw20994step0; decide +kernel
      have hl : raw20994step1Labels = raw20994step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20994step0 raw20994step0Labels permutation56 hz
    mixedMoment B raw20994step1 raw20994step1Labels = mixedMoment B raw20994step2 raw20994step2Labels := by
      have ha : raw20994step2 = (fun i j => raw20994step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20994step2 raw20994step1; decide +kernel
      have hl : raw20994step2Labels = raw20994step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20994step1 raw20994step1Labels permutation31 permutation4
    _ = mixedMoment B node2226 node2226Labels := by rfl

def raw20995 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20995Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20995step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20995step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw20995step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20995step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw20995step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20995 raw20995Labels = mixedMoment B node1599 node1599Labels := by
  calc
    mixedMoment B raw20995 raw20995Labels = mixedMoment B raw20995step0 raw20995step0Labels := by
      have hz : ∀ j, raw20995 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20995step0 = (fun i j => raw20995 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20995step0 raw20995; decide +kernel
      have hl : raw20995step0Labels = raw20995Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20995 raw20995Labels permutation346 hz
    mixedMoment B raw20995step0 raw20995step0Labels = mixedMoment B raw20995step1 raw20995step1Labels := by
      have ha : raw20995step1 = (fun i j => raw20995step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20995step1 raw20995step0; decide +kernel
      have hl : raw20995step1Labels = raw20995step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20995step0 raw20995step0Labels permutation40 permutation4
    mixedMoment B raw20995step1 raw20995step1Labels = mixedMoment B raw20995step2 raw20995step2Labels := by
      have ha : raw20995step2 = -raw20995step1 := by apply Matrix.ext; change ∀ i j, raw20995step2 i j = -(raw20995step1 i j); unfold raw20995step2 raw20995step1; decide +kernel
      have hl : raw20995step2Labels = raw20995step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1599 node1599Labels := by rfl

def raw20996 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20996Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20996step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20996step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw20996step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20996step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw20996step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20996 raw20996Labels = mixedMoment B node1599 node1599Labels := by
  calc
    mixedMoment B raw20996 raw20996Labels = mixedMoment B raw20996step0 raw20996step0Labels := by
      have hz : ∀ j, raw20996 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20996step0 = (fun i j => raw20996 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20996step0 raw20996; decide +kernel
      have hl : raw20996step0Labels = raw20996Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20996 raw20996Labels permutation265 hz
    mixedMoment B raw20996step0 raw20996step0Labels = mixedMoment B raw20996step1 raw20996step1Labels := by
      have ha : raw20996step1 = (fun i j => raw20996step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20996step1 raw20996step0; decide +kernel
      have hl : raw20996step1Labels = raw20996step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20996step0 raw20996step0Labels permutation40 permutation4
    mixedMoment B raw20996step1 raw20996step1Labels = mixedMoment B raw20996step2 raw20996step2Labels := by
      have ha : raw20996step2 = -raw20996step1 := by apply Matrix.ext; change ∀ i j, raw20996step2 i j = -(raw20996step1 i j); unfold raw20996step2 raw20996step1; decide +kernel
      have hl : raw20996step2Labels = raw20996step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1599 node1599Labels := by rfl

def raw20997 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -4, 3]]
def raw20997Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -4, 3]]
def raw20997step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20997step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 0, 1], ![1, -4, 3]]
def raw20997step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20997step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw20997step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20997 raw20997Labels = mixedMoment B node1002 node1002Labels := by
  calc
    mixedMoment B raw20997 raw20997Labels = mixedMoment B raw20997step0 raw20997step0Labels := by
      have hz : ∀ j, raw20997 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20997step0 = (fun i j => raw20997 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20997step0 raw20997; decide +kernel
      have hl : raw20997step0Labels = raw20997Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20997 raw20997Labels permutation346 hz
    mixedMoment B raw20997step0 raw20997step0Labels = mixedMoment B raw20997step1 raw20997step1Labels := by
      have hz : ∀ j, raw20997step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20997step1 = (fun i j => raw20997step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20997step1 raw20997step0; decide +kernel
      have hl : raw20997step1Labels = raw20997step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20997step0 raw20997step0Labels permutation56 hz
    mixedMoment B raw20997step1 raw20997step1Labels = mixedMoment B raw20997step2 raw20997step2Labels := by
      have ha : raw20997step2 = (fun i j => raw20997step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20997step2 raw20997step1; decide +kernel
      have hl : raw20997step2Labels = raw20997step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20997step1 raw20997step1Labels permutation31 permutation4
    _ = mixedMoment B node1002 node1002Labels := by rfl

def raw20998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, 1, -4]]
def raw20998Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![3, 1, -4]]
def raw20998step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20998step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw20998step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20998step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20998step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20998 raw20998Labels = mixedMoment B node1637 node1637Labels := by
  calc
    mixedMoment B raw20998 raw20998Labels = mixedMoment B raw20998step0 raw20998step0Labels := by
      have hz : ∀ j, raw20998 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20998step0 = (fun i j => raw20998 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20998step0 raw20998; decide +kernel
      have hl : raw20998step0Labels = raw20998Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20998 raw20998Labels permutation346 hz
    mixedMoment B raw20998step0 raw20998step0Labels = mixedMoment B raw20998step1 raw20998step1Labels := by
      have ha : raw20998step1 = (fun i j => raw20998step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20998step1 raw20998step0; decide +kernel
      have hl : raw20998step1Labels = raw20998step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20998step0 raw20998step0Labels permutation151 permutation2
    mixedMoment B raw20998step1 raw20998step1Labels = mixedMoment B raw20998step2 raw20998step2Labels := by
      have ha : raw20998step2 = -raw20998step1 := by apply Matrix.ext; change ∀ i j, raw20998step2 i j = -(raw20998step1 i j); unfold raw20998step2 raw20998step1; decide +kernel
      have hl : raw20998step2Labels = raw20998step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1637 node1637Labels := by rfl

def raw20999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![3, 1, -4]]
def raw20999Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![3, 1, -4]]
def raw20999step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20999step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw20999step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20999step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20999step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20999 raw20999Labels = mixedMoment B node1637 node1637Labels := by
  calc
    mixedMoment B raw20999 raw20999Labels = mixedMoment B raw20999step0 raw20999step0Labels := by
      have hz : ∀ j, raw20999 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20999step0 = (fun i j => raw20999 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20999step0 raw20999; decide +kernel
      have hl : raw20999step0Labels = raw20999Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20999 raw20999Labels permutation265 hz
    mixedMoment B raw20999step0 raw20999step0Labels = mixedMoment B raw20999step1 raw20999step1Labels := by
      have ha : raw20999step1 = (fun i j => raw20999step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20999step1 raw20999step0; decide +kernel
      have hl : raw20999step1Labels = raw20999step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20999step0 raw20999step0Labels permutation151 permutation2
    mixedMoment B raw20999step1 raw20999step1Labels = mixedMoment B raw20999step2 raw20999step2Labels := by
      have ha : raw20999step2 = -raw20999step1 := by apply Matrix.ext; change ∀ i j, raw20999step2 i j = -(raw20999step1 i j); unfold raw20999step2 raw20999step1; decide +kernel
      have hl : raw20999step2Labels = raw20999step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1637 node1637Labels := by rfl

def raw21000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![3, 1, -4]]
def raw21000Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![3, 1, -4]]
def raw21000step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21000step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![3, 1, -4]]
def raw21000step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21000step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw21000step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21000step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21000step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21000 raw21000Labels = mixedMoment B node1650 node1650Labels := by
  calc
    mixedMoment B raw21000 raw21000Labels = mixedMoment B raw21000step0 raw21000step0Labels := by
      have hz : ∀ j, raw21000 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21000step0 = (fun i j => raw21000 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21000step0 raw21000; decide +kernel
      have hl : raw21000step0Labels = raw21000Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21000 raw21000Labels permutation346 hz
    mixedMoment B raw21000step0 raw21000step0Labels = mixedMoment B raw21000step1 raw21000step1Labels := by
      have hz : ∀ j, raw21000step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21000step1 = (fun i j => raw21000step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21000step1 raw21000step0; decide +kernel
      have hl : raw21000step1Labels = raw21000step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21000step0 raw21000step0Labels permutation56 hz
    mixedMoment B raw21000step1 raw21000step1Labels = mixedMoment B raw21000step2 raw21000step2Labels := by
      have ha : raw21000step2 = (fun i j => raw21000step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21000step2 raw21000step1; decide +kernel
      have hl : raw21000step2Labels = raw21000step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21000step1 raw21000step1Labels permutation31 permutation2
    mixedMoment B raw21000step2 raw21000step2Labels = mixedMoment B raw21000step3 raw21000step3Labels := by
      have ha : raw21000step3 = -raw21000step2 := by apply Matrix.ext; change ∀ i j, raw21000step3 i j = -(raw21000step2 i j); unfold raw21000step3 raw21000step2; decide +kernel
      have hl : raw21000step3Labels = raw21000step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1650 node1650Labels := by rfl

def raw21001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw21001Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw21001step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21001step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw21001step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21001 raw21001Labels = mixedMoment B node2737 node2737Labels := by
  calc
    mixedMoment B raw21001 raw21001Labels = mixedMoment B raw21001step0 raw21001step0Labels := by
      have hz : ∀ j, raw21001 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21001step0 = (fun i j => raw21001 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21001step0 raw21001; decide +kernel
      have hl : raw21001step0Labels = raw21001Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21001 raw21001Labels permutation346 hz
    mixedMoment B raw21001step0 raw21001step0Labels = mixedMoment B raw21001step1 raw21001step1Labels := by
      have hz : ∀ j, raw21001step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21001step1 = (fun i j => raw21001step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21001step1 raw21001step0; decide +kernel
      have hl : raw21001step1Labels = raw21001step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21001step0 raw21001step0Labels permutation56 hz
    _ = mixedMoment B node2737 node2737Labels := by rfl

def raw21002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![3, -1, -2]]
def raw21002Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![3, -1, -2]]
def raw21002step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21002step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 1, -2], ![3, -1, -2]]
def raw21002step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21002 raw21002Labels = mixedMoment B node1191 node1191Labels := by
  calc
    mixedMoment B raw21002 raw21002Labels = mixedMoment B raw21002step0 raw21002step0Labels := by
      have hz : ∀ j, raw21002 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21002step0 = (fun i j => raw21002 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21002step0 raw21002; decide +kernel
      have hl : raw21002step0Labels = raw21002Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21002 raw21002Labels permutation346 hz
    mixedMoment B raw21002step0 raw21002step0Labels = mixedMoment B raw21002step1 raw21002step1Labels := by
      have hz : ∀ j, raw21002step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21002step1 = (fun i j => raw21002step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21002step1 raw21002step0; decide +kernel
      have hl : raw21002step1Labels = raw21002step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21002step0 raw21002step0Labels permutation56 hz
    _ = mixedMoment B node1191 node1191Labels := by rfl

def raw21003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![3, -1, -2]]
def raw21003Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![3, -1, -2]]
def raw21003step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21003step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw21003step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21003step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw21003step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21003 raw21003Labels = mixedMoment B node2391 node2391Labels := by
  calc
    mixedMoment B raw21003 raw21003Labels = mixedMoment B raw21003step0 raw21003step0Labels := by
      have hz : ∀ j, raw21003 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21003step0 = (fun i j => raw21003 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21003step0 raw21003; decide +kernel
      have hl : raw21003step0Labels = raw21003Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21003 raw21003Labels permutation346 hz
    mixedMoment B raw21003step0 raw21003step0Labels = mixedMoment B raw21003step1 raw21003step1Labels := by
      have ha : raw21003step1 = (fun i j => raw21003step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21003step1 raw21003step0; decide +kernel
      have hl : raw21003step1Labels = raw21003step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21003step0 raw21003step0Labels permutation151 permutation2
    mixedMoment B raw21003step1 raw21003step1Labels = mixedMoment B raw21003step2 raw21003step2Labels := by
      have ha : raw21003step2 = -raw21003step1 := by apply Matrix.ext; change ∀ i j, raw21003step2 i j = -(raw21003step1 i j); unfold raw21003step2 raw21003step1; decide +kernel
      have hl : raw21003step2Labels = raw21003step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2391 node2391Labels := by rfl

def raw21004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![3, -1, -2]]
def raw21004Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![3, -1, -2]]
def raw21004step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21004step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw21004step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21004step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw21004step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21004 raw21004Labels = mixedMoment B node2391 node2391Labels := by
  calc
    mixedMoment B raw21004 raw21004Labels = mixedMoment B raw21004step0 raw21004step0Labels := by
      have hz : ∀ j, raw21004 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21004step0 = (fun i j => raw21004 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21004step0 raw21004; decide +kernel
      have hl : raw21004step0Labels = raw21004Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21004 raw21004Labels permutation265 hz
    mixedMoment B raw21004step0 raw21004step0Labels = mixedMoment B raw21004step1 raw21004step1Labels := by
      have ha : raw21004step1 = (fun i j => raw21004step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21004step1 raw21004step0; decide +kernel
      have hl : raw21004step1Labels = raw21004step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21004step0 raw21004step0Labels permutation151 permutation2
    mixedMoment B raw21004step1 raw21004step1Labels = mixedMoment B raw21004step2 raw21004step2Labels := by
      have ha : raw21004step2 = -raw21004step1 := by apply Matrix.ext; change ∀ i j, raw21004step2 i j = -(raw21004step1 i j); unfold raw21004step2 raw21004step1; decide +kernel
      have hl : raw21004step2Labels = raw21004step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2391 node2391Labels := by rfl

def raw21005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw21005Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21005step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw21005step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21005step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw21005step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21005 raw21005Labels = mixedMoment B node2407 node2407Labels := by
  calc
    mixedMoment B raw21005 raw21005Labels = mixedMoment B raw21005step0 raw21005step0Labels := by
      have hz : ∀ j, raw21005 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21005step0 = (fun i j => raw21005 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21005step0 raw21005; decide +kernel
      have hl : raw21005step0Labels = raw21005Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21005 raw21005Labels permutation346 hz
    mixedMoment B raw21005step0 raw21005step0Labels = mixedMoment B raw21005step1 raw21005step1Labels := by
      have hz : ∀ j, raw21005step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21005step1 = (fun i j => raw21005step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21005step1 raw21005step0; decide +kernel
      have hl : raw21005step1Labels = raw21005step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21005step0 raw21005step0Labels permutation56 hz
    _ = mixedMoment B node2407 node2407Labels := by rfl

def raw21006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw21006Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw21006step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21006step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![3, -1, -2]]
def raw21006step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21006 raw21006Labels = mixedMoment B node2680 node2680Labels := by
  calc
    mixedMoment B raw21006 raw21006Labels = mixedMoment B raw21006step0 raw21006step0Labels := by
      have hz : ∀ j, raw21006 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21006step0 = (fun i j => raw21006 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21006step0 raw21006; decide +kernel
      have hl : raw21006step0Labels = raw21006Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21006 raw21006Labels permutation346 hz
    mixedMoment B raw21006step0 raw21006step0Labels = mixedMoment B raw21006step1 raw21006step1Labels := by
      have hz : ∀ j, raw21006step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21006step1 = (fun i j => raw21006step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21006step1 raw21006step0; decide +kernel
      have hl : raw21006step1Labels = raw21006step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21006step0 raw21006step0Labels permutation56 hz
    _ = mixedMoment B node2680 node2680Labels := by rfl

def raw21007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw21007Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw21007step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21007step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw21007step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21007 raw21007Labels = mixedMoment B node2686 node2686Labels := by
  calc
    mixedMoment B raw21007 raw21007Labels = mixedMoment B raw21007step0 raw21007step0Labels := by
      have hz : ∀ j, raw21007 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21007step0 = (fun i j => raw21007 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21007step0 raw21007; decide +kernel
      have hl : raw21007step0Labels = raw21007Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21007 raw21007Labels permutation346 hz
    mixedMoment B raw21007step0 raw21007step0Labels = mixedMoment B raw21007step1 raw21007step1Labels := by
      have hz : ∀ j, raw21007step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21007step1 = (fun i j => raw21007step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21007step1 raw21007step0; decide +kernel
      have hl : raw21007step1Labels = raw21007step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21007step0 raw21007step0Labels permutation56 hz
    _ = mixedMoment B node2686 node2686Labels := by rfl

def raw21008 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![-2, 2], ![2, -2], ![2, -2]]
def raw21008Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21008step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-2, 2], ![2, -2], ![2, -2]]
def raw21008step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21008step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![2, -2]]
def raw21008step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical21008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21008 raw21008Labels = mixedMoment B node4089 node4089Labels := by
  calc
    mixedMoment B raw21008 raw21008Labels = mixedMoment B raw21008step0 raw21008step0Labels := by
      have hz : ∀ j, raw21008 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21008step0 = (fun i j => raw21008 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21008step0 raw21008; decide +kernel
      have hl : raw21008step0Labels = raw21008Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21008 raw21008Labels permutation346 hz
    mixedMoment B raw21008step0 raw21008step0Labels = mixedMoment B raw21008step1 raw21008step1Labels := by
      have hz : ∀ j, raw21008step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21008step1 = (fun i j => raw21008step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21008step1 raw21008step0; decide +kernel
      have hl : raw21008step1Labels = raw21008step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21008step0 raw21008step0Labels permutation56 hz
    _ = mixedMoment B node4089 node4089Labels := by rfl

def raw21009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw21009Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw21009step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21009step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw21009step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21009 raw21009Labels = mixedMoment B node1185 node1185Labels := by
  calc
    mixedMoment B raw21009 raw21009Labels = mixedMoment B raw21009step0 raw21009step0Labels := by
      have hz : ∀ j, raw21009 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21009step0 = (fun i j => raw21009 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21009step0 raw21009; decide +kernel
      have hl : raw21009step0Labels = raw21009Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21009 raw21009Labels permutation346 hz
    mixedMoment B raw21009step0 raw21009step0Labels = mixedMoment B raw21009step1 raw21009step1Labels := by
      have ha : raw21009step1 = (fun i j => raw21009step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21009step1 raw21009step0; decide +kernel
      have hl : raw21009step1Labels = raw21009step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21009step0 raw21009step0Labels permutation38 permutation2
    _ = mixedMoment B node1185 node1185Labels := by rfl

def raw21010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw21010Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21010step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw21010step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21010step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw21010step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21010 raw21010Labels = mixedMoment B node1185 node1185Labels := by
  calc
    mixedMoment B raw21010 raw21010Labels = mixedMoment B raw21010step0 raw21010step0Labels := by
      have hz : ∀ j, raw21010 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21010step0 = (fun i j => raw21010 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21010step0 raw21010; decide +kernel
      have hl : raw21010step0Labels = raw21010Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21010 raw21010Labels permutation265 hz
    mixedMoment B raw21010step0 raw21010step0Labels = mixedMoment B raw21010step1 raw21010step1Labels := by
      have ha : raw21010step1 = (fun i j => raw21010step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21010step1 raw21010step0; decide +kernel
      have hl : raw21010step1Labels = raw21010step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21010step0 raw21010step0Labels permutation38 permutation2
    _ = mixedMoment B node1185 node1185Labels := by rfl

def raw21011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![2, 0, -2]]
def raw21011Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21011step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2], ![2, 0, -2]]
def raw21011step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21011step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 1, -2], ![2, 0, -2]]
def raw21011step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21011 raw21011Labels = mixedMoment B node1288 node1288Labels := by
  calc
    mixedMoment B raw21011 raw21011Labels = mixedMoment B raw21011step0 raw21011step0Labels := by
      have hz : ∀ j, raw21011 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21011step0 = (fun i j => raw21011 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21011step0 raw21011; decide +kernel
      have hl : raw21011step0Labels = raw21011Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21011 raw21011Labels permutation346 hz
    mixedMoment B raw21011step0 raw21011step0Labels = mixedMoment B raw21011step1 raw21011step1Labels := by
      have hz : ∀ j, raw21011step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21011step1 = (fun i j => raw21011step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21011step1 raw21011step0; decide +kernel
      have hl : raw21011step1Labels = raw21011step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21011step0 raw21011step0Labels permutation56 hz
    _ = mixedMoment B node1288 node1288Labels := by rfl

def raw21012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw21012Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw21012step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21012step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw21012step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21012 raw21012Labels = mixedMoment B node1193 node1193Labels := by
  calc
    mixedMoment B raw21012 raw21012Labels = mixedMoment B raw21012step0 raw21012step0Labels := by
      have hz : ∀ j, raw21012 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21012step0 = (fun i j => raw21012 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21012step0 raw21012; decide +kernel
      have hl : raw21012step0Labels = raw21012Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21012 raw21012Labels permutation346 hz
    mixedMoment B raw21012step0 raw21012step0Labels = mixedMoment B raw21012step1 raw21012step1Labels := by
      have hz : ∀ j, raw21012step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21012step1 = (fun i j => raw21012step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21012step1 raw21012step0; decide +kernel
      have hl : raw21012step1Labels = raw21012step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21012step0 raw21012step0Labels permutation56 hz
    _ = mixedMoment B node1193 node1193Labels := by rfl

def raw21013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw21013Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw21013step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21013step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw21013step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21013 raw21013Labels = mixedMoment B node1190 node1190Labels := by
  calc
    mixedMoment B raw21013 raw21013Labels = mixedMoment B raw21013step0 raw21013step0Labels := by
      have hz : ∀ j, raw21013 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21013step0 = (fun i j => raw21013 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21013step0 raw21013; decide +kernel
      have hl : raw21013step0Labels = raw21013Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21013 raw21013Labels permutation346 hz
    mixedMoment B raw21013step0 raw21013step0Labels = mixedMoment B raw21013step1 raw21013step1Labels := by
      have hz : ∀ j, raw21013step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21013step1 = (fun i j => raw21013step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21013step1 raw21013step0; decide +kernel
      have hl : raw21013step1Labels = raw21013step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21013step0 raw21013step0Labels permutation56 hz
    _ = mixedMoment B node1190 node1190Labels := by rfl

def raw21014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw21014Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw21014step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21014step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw21014step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21014step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw21014step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21014 raw21014Labels = mixedMoment B node1924 node1924Labels := by
  calc
    mixedMoment B raw21014 raw21014Labels = mixedMoment B raw21014step0 raw21014step0Labels := by
      have hz : ∀ j, raw21014 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21014step0 = (fun i j => raw21014 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21014step0 raw21014; decide +kernel
      have hl : raw21014step0Labels = raw21014Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21014 raw21014Labels permutation346 hz
    mixedMoment B raw21014step0 raw21014step0Labels = mixedMoment B raw21014step1 raw21014step1Labels := by
      have ha : raw21014step1 = (fun i j => raw21014step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21014step1 raw21014step0; decide +kernel
      have hl : raw21014step1Labels = raw21014step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21014step0 raw21014step0Labels permutation151 permutation2
    mixedMoment B raw21014step1 raw21014step1Labels = mixedMoment B raw21014step2 raw21014step2Labels := by
      have ha : raw21014step2 = -raw21014step1 := by apply Matrix.ext; change ∀ i j, raw21014step2 i j = -(raw21014step1 i j); unfold raw21014step2 raw21014step1; decide +kernel
      have hl : raw21014step2Labels = raw21014step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1924 node1924Labels := by rfl

def raw21015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw21015Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw21015step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21015step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw21015step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21015step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw21015step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21015 raw21015Labels = mixedMoment B node1924 node1924Labels := by
  calc
    mixedMoment B raw21015 raw21015Labels = mixedMoment B raw21015step0 raw21015step0Labels := by
      have hz : ∀ j, raw21015 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21015step0 = (fun i j => raw21015 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21015step0 raw21015; decide +kernel
      have hl : raw21015step0Labels = raw21015Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21015 raw21015Labels permutation265 hz
    mixedMoment B raw21015step0 raw21015step0Labels = mixedMoment B raw21015step1 raw21015step1Labels := by
      have ha : raw21015step1 = (fun i j => raw21015step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21015step1 raw21015step0; decide +kernel
      have hl : raw21015step1Labels = raw21015step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21015step0 raw21015step0Labels permutation151 permutation2
    mixedMoment B raw21015step1 raw21015step1Labels = mixedMoment B raw21015step2 raw21015step2Labels := by
      have ha : raw21015step2 = -raw21015step1 := by apply Matrix.ext; change ∀ i j, raw21015step2 i j = -(raw21015step1 i j); unfold raw21015step2 raw21015step1; decide +kernel
      have hl : raw21015step2Labels = raw21015step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1924 node1924Labels := by rfl

def raw21016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![3, 0, -3]]
def raw21016Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![3, 0, -3]]
def raw21016step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21016step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![3, 0, -3]]
def raw21016step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21016step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, -1, 2], ![-3, 1, 2]]
def raw21016step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21016step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21016step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21016 raw21016Labels = mixedMoment B node1950 node1950Labels := by
  calc
    mixedMoment B raw21016 raw21016Labels = mixedMoment B raw21016step0 raw21016step0Labels := by
      have hz : ∀ j, raw21016 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21016step0 = (fun i j => raw21016 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21016step0 raw21016; decide +kernel
      have hl : raw21016step0Labels = raw21016Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21016 raw21016Labels permutation346 hz
    mixedMoment B raw21016step0 raw21016step0Labels = mixedMoment B raw21016step1 raw21016step1Labels := by
      have hz : ∀ j, raw21016step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21016step1 = (fun i j => raw21016step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21016step1 raw21016step0; decide +kernel
      have hl : raw21016step1Labels = raw21016step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21016step0 raw21016step0Labels permutation56 hz
    mixedMoment B raw21016step1 raw21016step1Labels = mixedMoment B raw21016step2 raw21016step2Labels := by
      have ha : raw21016step2 = (fun i j => raw21016step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21016step2 raw21016step1; decide +kernel
      have hl : raw21016step2Labels = raw21016step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21016step1 raw21016step1Labels permutation31 permutation2
    mixedMoment B raw21016step2 raw21016step2Labels = mixedMoment B raw21016step3 raw21016step3Labels := by
      have ha : raw21016step3 = -raw21016step2 := by apply Matrix.ext; change ∀ i j, raw21016step3 i j = -(raw21016step2 i j); unfold raw21016step3 raw21016step2; decide +kernel
      have hl : raw21016step3Labels = raw21016step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1950 node1950Labels := by rfl

def raw21017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![3, 0, -3]]
def raw21017Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![3, 0, -3]]
def raw21017step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21017step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![3, 0, -3]]
def raw21017step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21017step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-3, 1, 2]]
def raw21017step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21017step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw21017step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21017 raw21017Labels = mixedMoment B node2218 node2218Labels := by
  calc
    mixedMoment B raw21017 raw21017Labels = mixedMoment B raw21017step0 raw21017step0Labels := by
      have hz : ∀ j, raw21017 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21017step0 = (fun i j => raw21017 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21017step0 raw21017; decide +kernel
      have hl : raw21017step0Labels = raw21017Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21017 raw21017Labels permutation346 hz
    mixedMoment B raw21017step0 raw21017step0Labels = mixedMoment B raw21017step1 raw21017step1Labels := by
      have hz : ∀ j, raw21017step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21017step1 = (fun i j => raw21017step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21017step1 raw21017step0; decide +kernel
      have hl : raw21017step1Labels = raw21017step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21017step0 raw21017step0Labels permutation56 hz
    mixedMoment B raw21017step1 raw21017step1Labels = mixedMoment B raw21017step2 raw21017step2Labels := by
      have ha : raw21017step2 = (fun i j => raw21017step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21017step2 raw21017step1; decide +kernel
      have hl : raw21017step2Labels = raw21017step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21017step1 raw21017step1Labels permutation31 permutation2
    mixedMoment B raw21017step2 raw21017step2Labels = mixedMoment B raw21017step3 raw21017step3Labels := by
      have ha : raw21017step3 = -raw21017step2 := by apply Matrix.ext; change ∀ i j, raw21017step3 i j = -(raw21017step2 i j); unfold raw21017step3 raw21017step2; decide +kernel
      have hl : raw21017step3Labels = raw21017step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2218 node2218Labels := by rfl

def raw21018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw21018Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw21018step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21018step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw21018step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21018 raw21018Labels = mixedMoment B node2685 node2685Labels := by
  calc
    mixedMoment B raw21018 raw21018Labels = mixedMoment B raw21018step0 raw21018step0Labels := by
      have hz : ∀ j, raw21018 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21018step0 = (fun i j => raw21018 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21018step0 raw21018; decide +kernel
      have hl : raw21018step0Labels = raw21018Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21018 raw21018Labels permutation346 hz
    mixedMoment B raw21018step0 raw21018step0Labels = mixedMoment B raw21018step1 raw21018step1Labels := by
      have hz : ∀ j, raw21018step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21018step1 = (fun i j => raw21018step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21018step1 raw21018step0; decide +kernel
      have hl : raw21018step1Labels = raw21018step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21018step0 raw21018step0Labels permutation56 hz
    _ = mixedMoment B node2685 node2685Labels := by rfl

def raw21019 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![-2, 2], ![1, -1], ![3, -3]]
def raw21019Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21019step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-2, 2], ![1, -1], ![3, -3]]
def raw21019step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21019step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![3, -3]]
def raw21019step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21019step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-2, 2], ![-2, 2]]
def raw21019step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21019step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw21019step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical21019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21019 raw21019Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw21019 raw21019Labels = mixedMoment B raw21019step0 raw21019step0Labels := by
      have hz : ∀ j, raw21019 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21019step0 = (fun i j => raw21019 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21019step0 raw21019; decide +kernel
      have hl : raw21019step0Labels = raw21019Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21019 raw21019Labels permutation346 hz
    mixedMoment B raw21019step0 raw21019step0Labels = mixedMoment B raw21019step1 raw21019step1Labels := by
      have hz : ∀ j, raw21019step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21019step1 = (fun i j => raw21019step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21019step1 raw21019step0; decide +kernel
      have hl : raw21019step1Labels = raw21019step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21019step0 raw21019step0Labels permutation56 hz
    mixedMoment B raw21019step1 raw21019step1Labels = mixedMoment B raw21019step2 raw21019step2Labels := by
      have ha : raw21019step2 = (fun i j => raw21019step1 (permutation30 i) (permutation0 j)) := by apply Matrix.ext; unfold raw21019step2 raw21019step1; decide +kernel
      have hl : raw21019step2Labels = raw21019step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21019step1 raw21019step1Labels permutation30 permutation0
    mixedMoment B raw21019step2 raw21019step2Labels = mixedMoment B raw21019step3 raw21019step3Labels := by
      have ha : raw21019step3 = -raw21019step2 := by apply Matrix.ext; change ∀ i j, raw21019step3 i j = -(raw21019step2 i j); unfold raw21019step3 raw21019step2; decide +kernel
      have hl : raw21019step3Labels = raw21019step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4082 node4082Labels := by rfl

def raw21020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![3, 0, -3]]
def raw21020Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![3, 0, -3]]
def raw21020step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21020step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw21020step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21020 raw21020Labels = mixedMoment B node1098 node1098Labels := by
  calc
    mixedMoment B raw21020 raw21020Labels = mixedMoment B raw21020step0 raw21020step0Labels := by
      have hz : ∀ j, raw21020 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21020step0 = (fun i j => raw21020 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21020step0 raw21020; decide +kernel
      have hl : raw21020step0Labels = raw21020Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21020 raw21020Labels permutation346 hz
    mixedMoment B raw21020step0 raw21020step0Labels = mixedMoment B raw21020step1 raw21020step1Labels := by
      have ha : raw21020step1 = (fun i j => raw21020step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21020step1 raw21020step0; decide +kernel
      have hl : raw21020step1Labels = raw21020step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21020step0 raw21020step0Labels permutation38 permutation2
    _ = mixedMoment B node1098 node1098Labels := by rfl

def raw21021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![3, 0, -3]]
def raw21021Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, -1, 2], ![1, 0, -1], ![3, 0, -3]]
def raw21021step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21021step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw21021step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21021 raw21021Labels = mixedMoment B node1098 node1098Labels := by
  calc
    mixedMoment B raw21021 raw21021Labels = mixedMoment B raw21021step0 raw21021step0Labels := by
      have hz : ∀ j, raw21021 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21021step0 = (fun i j => raw21021 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21021step0 raw21021; decide +kernel
      have hl : raw21021step0Labels = raw21021Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21021 raw21021Labels permutation265 hz
    mixedMoment B raw21021step0 raw21021step0Labels = mixedMoment B raw21021step1 raw21021step1Labels := by
      have ha : raw21021step1 = (fun i j => raw21021step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21021step1 raw21021step0; decide +kernel
      have hl : raw21021step1Labels = raw21021step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21021step0 raw21021step0Labels permutation38 permutation2
    _ = mixedMoment B node1098 node1098Labels := by rfl

def raw21022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![2, -1, -1], ![3, 0, -3]]
def raw21022Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, -1, 2], ![2, -1, -1], ![3, 0, -3]]
def raw21022step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21022step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![2, -1, -1], ![3, 0, -3]]
def raw21022step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21022 raw21022Labels = mixedMoment B node1103 node1103Labels := by
  calc
    mixedMoment B raw21022 raw21022Labels = mixedMoment B raw21022step0 raw21022step0Labels := by
      have hz : ∀ j, raw21022 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21022step0 = (fun i j => raw21022 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21022step0 raw21022; decide +kernel
      have hl : raw21022step0Labels = raw21022Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21022 raw21022Labels permutation346 hz
    mixedMoment B raw21022step0 raw21022step0Labels = mixedMoment B raw21022step1 raw21022step1Labels := by
      have hz : ∀ j, raw21022step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21022step1 = (fun i j => raw21022step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21022step1 raw21022step0; decide +kernel
      have hl : raw21022step1Labels = raw21022step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21022step0 raw21022step0Labels permutation56 hz
    _ = mixedMoment B node1103 node1103Labels := by rfl

def raw21023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![4, -1, -3]]
def raw21023Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21023step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![4, -1, -3]]
def raw21023step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21023step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![4, -1, -3]]
def raw21023step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21023step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, -1, 2], ![-4, 2, 2]]
def raw21023step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21023step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw21023step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21023 raw21023Labels = mixedMoment B node893 node893Labels := by
  calc
    mixedMoment B raw21023 raw21023Labels = mixedMoment B raw21023step0 raw21023step0Labels := by
      have hz : ∀ j, raw21023 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21023step0 = (fun i j => raw21023 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21023step0 raw21023; decide +kernel
      have hl : raw21023step0Labels = raw21023Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21023 raw21023Labels permutation346 hz
    mixedMoment B raw21023step0 raw21023step0Labels = mixedMoment B raw21023step1 raw21023step1Labels := by
      have hz : ∀ j, raw21023step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21023step1 = (fun i j => raw21023step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21023step1 raw21023step0; decide +kernel
      have hl : raw21023step1Labels = raw21023step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21023step0 raw21023step0Labels permutation56 hz
    mixedMoment B raw21023step1 raw21023step1Labels = mixedMoment B raw21023step2 raw21023step2Labels := by
      have ha : raw21023step2 = (fun i j => raw21023step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21023step2 raw21023step1; decide +kernel
      have hl : raw21023step2Labels = raw21023step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21023step1 raw21023step1Labels permutation31 permutation2
    mixedMoment B raw21023step2 raw21023step2Labels = mixedMoment B raw21023step3 raw21023step3Labels := by
      have ha : raw21023step3 = -raw21023step2 := by apply Matrix.ext; change ∀ i j, raw21023step3 i j = -(raw21023step2 i j); unfold raw21023step3 raw21023step2; decide +kernel
      have hl : raw21023step3Labels = raw21023step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node893 node893Labels := by rfl

def raw21024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw21024Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw21024step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21024step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw21024step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21024 raw21024Labels = mixedMoment B node1184 node1184Labels := by
  calc
    mixedMoment B raw21024 raw21024Labels = mixedMoment B raw21024step0 raw21024step0Labels := by
      have hz : ∀ j, raw21024 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21024step0 = (fun i j => raw21024 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21024step0 raw21024; decide +kernel
      have hl : raw21024step0Labels = raw21024Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21024 raw21024Labels permutation346 hz
    mixedMoment B raw21024step0 raw21024step0Labels = mixedMoment B raw21024step1 raw21024step1Labels := by
      have ha : raw21024step1 = (fun i j => raw21024step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21024step1 raw21024step0; decide +kernel
      have hl : raw21024step1Labels = raw21024step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21024step0 raw21024step0Labels permutation38 permutation2
    _ = mixedMoment B node1184 node1184Labels := by rfl

def raw21025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw21025Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw21025step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21025step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw21025step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21025 raw21025Labels = mixedMoment B node1184 node1184Labels := by
  calc
    mixedMoment B raw21025 raw21025Labels = mixedMoment B raw21025step0 raw21025step0Labels := by
      have hz : ∀ j, raw21025 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21025step0 = (fun i j => raw21025 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21025step0 raw21025; decide +kernel
      have hl : raw21025step0Labels = raw21025Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21025 raw21025Labels permutation265 hz
    mixedMoment B raw21025step0 raw21025step0Labels = mixedMoment B raw21025step1 raw21025step1Labels := by
      have ha : raw21025step1 = (fun i j => raw21025step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21025step1 raw21025step0; decide +kernel
      have hl : raw21025step1Labels = raw21025step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21025step0 raw21025step0Labels permutation38 permutation2
    _ = mixedMoment B node1184 node1184Labels := by rfl

def raw21026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def raw21026Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def raw21026step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21026step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def raw21026step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21026 raw21026Labels = mixedMoment B node1287 node1287Labels := by
  calc
    mixedMoment B raw21026 raw21026Labels = mixedMoment B raw21026step0 raw21026step0Labels := by
      have hz : ∀ j, raw21026 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21026step0 = (fun i j => raw21026 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21026step0 raw21026; decide +kernel
      have hl : raw21026step0Labels = raw21026Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21026 raw21026Labels permutation346 hz
    mixedMoment B raw21026step0 raw21026step0Labels = mixedMoment B raw21026step1 raw21026step1Labels := by
      have hz : ∀ j, raw21026step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21026step1 = (fun i j => raw21026step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21026step1 raw21026step0; decide +kernel
      have hl : raw21026step1Labels = raw21026step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21026step0 raw21026step0Labels permutation56 hz
    _ = mixedMoment B node1287 node1287Labels := by rfl

def raw21027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw21027Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw21027step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21027step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw21027step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21027 raw21027Labels = mixedMoment B node1192 node1192Labels := by
  calc
    mixedMoment B raw21027 raw21027Labels = mixedMoment B raw21027step0 raw21027step0Labels := by
      have hz : ∀ j, raw21027 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21027step0 = (fun i j => raw21027 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21027step0 raw21027; decide +kernel
      have hl : raw21027step0Labels = raw21027Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21027 raw21027Labels permutation346 hz
    mixedMoment B raw21027step0 raw21027step0Labels = mixedMoment B raw21027step1 raw21027step1Labels := by
      have hz : ∀ j, raw21027step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21027step1 = (fun i j => raw21027step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21027step1 raw21027step0; decide +kernel
      have hl : raw21027step1Labels = raw21027step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21027step0 raw21027step0Labels permutation56 hz
    _ = mixedMoment B node1192 node1192Labels := by rfl

def raw21028 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -3, 3]]
def raw21028Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -3, 3]]
def raw21028step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21028step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, -1, 1], ![0, -3, 3]]
def raw21028step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21028step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![2, -2, 0], ![2, 2, -4]]
def raw21028step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21028 raw21028Labels = mixedMoment B node1952 node1952Labels := by
  calc
    mixedMoment B raw21028 raw21028Labels = mixedMoment B raw21028step0 raw21028step0Labels := by
      have hz : ∀ j, raw21028 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21028step0 = (fun i j => raw21028 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21028step0 raw21028; decide +kernel
      have hl : raw21028step0Labels = raw21028Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21028 raw21028Labels permutation346 hz
    mixedMoment B raw21028step0 raw21028step0Labels = mixedMoment B raw21028step1 raw21028step1Labels := by
      have hz : ∀ j, raw21028step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21028step1 = (fun i j => raw21028step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21028step1 raw21028step0; decide +kernel
      have hl : raw21028step1Labels = raw21028step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21028step0 raw21028step0Labels permutation56 hz
    mixedMoment B raw21028step1 raw21028step1Labels = mixedMoment B raw21028step2 raw21028step2Labels := by
      have ha : raw21028step2 = (fun i j => raw21028step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21028step2 raw21028step1; decide +kernel
      have hl : raw21028step2Labels = raw21028step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21028step1 raw21028step1Labels permutation31 permutation4
    _ = mixedMoment B node1952 node1952Labels := by rfl

def raw21029 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -3, 3]]
def raw21029Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -3, 3]]
def raw21029step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21029step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw21029step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21029step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw21029step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21029 raw21029Labels = mixedMoment B node1543 node1543Labels := by
  calc
    mixedMoment B raw21029 raw21029Labels = mixedMoment B raw21029step0 raw21029step0Labels := by
      have hz : ∀ j, raw21029 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21029step0 = (fun i j => raw21029 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21029step0 raw21029; decide +kernel
      have hl : raw21029step0Labels = raw21029Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21029 raw21029Labels permutation346 hz
    mixedMoment B raw21029step0 raw21029step0Labels = mixedMoment B raw21029step1 raw21029step1Labels := by
      have ha : raw21029step1 = (fun i j => raw21029step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21029step1 raw21029step0; decide +kernel
      have hl : raw21029step1Labels = raw21029step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21029step0 raw21029step0Labels permutation38 permutation4
    mixedMoment B raw21029step1 raw21029step1Labels = mixedMoment B raw21029step2 raw21029step2Labels := by
      have ha : raw21029step2 = -raw21029step1 := by apply Matrix.ext; change ∀ i j, raw21029step2 i j = -(raw21029step1 i j); unfold raw21029step2 raw21029step1; decide +kernel
      have hl : raw21029step2Labels = raw21029step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1543 node1543Labels := by rfl

def raw21030 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -3, 3]]
def raw21030Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21030step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -3, 3]]
def raw21030step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21030step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw21030step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21030step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw21030step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21030 raw21030Labels = mixedMoment B node1543 node1543Labels := by
  calc
    mixedMoment B raw21030 raw21030Labels = mixedMoment B raw21030step0 raw21030step0Labels := by
      have hz : ∀ j, raw21030 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21030step0 = (fun i j => raw21030 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21030step0 raw21030; decide +kernel
      have hl : raw21030step0Labels = raw21030Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21030 raw21030Labels permutation265 hz
    mixedMoment B raw21030step0 raw21030step0Labels = mixedMoment B raw21030step1 raw21030step1Labels := by
      have ha : raw21030step1 = (fun i j => raw21030step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21030step1 raw21030step0; decide +kernel
      have hl : raw21030step1Labels = raw21030step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21030step0 raw21030step0Labels permutation38 permutation4
    mixedMoment B raw21030step1 raw21030step1Labels = mixedMoment B raw21030step2 raw21030step2Labels := by
      have ha : raw21030step2 = -raw21030step1 := by apply Matrix.ext; change ∀ i j, raw21030step2 i j = -(raw21030step1 i j); unfold raw21030step2 raw21030step1; decide +kernel
      have hl : raw21030step2Labels = raw21030step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1543 node1543Labels := by rfl

def raw21031 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![0, -3, 3]]
def raw21031Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![0, -3, 3]]
def raw21031step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21031step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 2, 0], ![1, -2, 1], ![0, -3, 3]]
def raw21031step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21031step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![2, -2, 0], ![-2, 1, 1], ![-3, 0, 3]]
def raw21031step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21031step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-2, 2, 0], ![2, -1, -1], ![3, 0, -3]]
def raw21031step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21031 raw21031Labels = mixedMoment B node1548 node1548Labels := by
  calc
    mixedMoment B raw21031 raw21031Labels = mixedMoment B raw21031step0 raw21031step0Labels := by
      have hz : ∀ j, raw21031 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21031step0 = (fun i j => raw21031 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21031step0 raw21031; decide +kernel
      have hl : raw21031step0Labels = raw21031Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21031 raw21031Labels permutation346 hz
    mixedMoment B raw21031step0 raw21031step0Labels = mixedMoment B raw21031step1 raw21031step1Labels := by
      have hz : ∀ j, raw21031step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21031step1 = (fun i j => raw21031step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21031step1 raw21031step0; decide +kernel
      have hl : raw21031step1Labels = raw21031step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21031step0 raw21031step0Labels permutation56 hz
    mixedMoment B raw21031step1 raw21031step1Labels = mixedMoment B raw21031step2 raw21031step2Labels := by
      have ha : raw21031step2 = (fun i j => raw21031step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21031step2 raw21031step1; decide +kernel
      have hl : raw21031step2Labels = raw21031step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21031step1 raw21031step1Labels permutation8 permutation4
    mixedMoment B raw21031step2 raw21031step2Labels = mixedMoment B raw21031step3 raw21031step3Labels := by
      have ha : raw21031step3 = -raw21031step2 := by apply Matrix.ext; change ∀ i j, raw21031step3 i j = -(raw21031step2 i j); unfold raw21031step3 raw21031step2; decide +kernel
      have hl : raw21031step3Labels = raw21031step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1548 node1548Labels := by rfl

def raw21032 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![1, -4, 3]]
def raw21032Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![1, -4, 3]]
def raw21032step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21032step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 2, 0], ![0, -1, 1], ![1, -4, 3]]
def raw21032step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21032step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, -2, 0], ![3, 1, -4]]
def raw21032step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21032 raw21032Labels = mixedMoment B node894 node894Labels := by
  calc
    mixedMoment B raw21032 raw21032Labels = mixedMoment B raw21032step0 raw21032step0Labels := by
      have hz : ∀ j, raw21032 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21032step0 = (fun i j => raw21032 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21032step0 raw21032; decide +kernel
      have hl : raw21032step0Labels = raw21032Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21032 raw21032Labels permutation346 hz
    mixedMoment B raw21032step0 raw21032step0Labels = mixedMoment B raw21032step1 raw21032step1Labels := by
      have hz : ∀ j, raw21032step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21032step1 = (fun i j => raw21032step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21032step1 raw21032step0; decide +kernel
      have hl : raw21032step1Labels = raw21032step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21032step0 raw21032step0Labels permutation56 hz
    mixedMoment B raw21032step1 raw21032step1Labels = mixedMoment B raw21032step2 raw21032step2Labels := by
      have ha : raw21032step2 = (fun i j => raw21032step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21032step2 raw21032step1; decide +kernel
      have hl : raw21032step2Labels = raw21032step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21032step1 raw21032step1Labels permutation31 permutation4
    _ = mixedMoment B node894 node894Labels := by rfl

def raw21033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![3, 1, -4]]
def raw21033Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![3, 1, -4]]
def raw21033step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21033step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![3, 1, -4]]
def raw21033step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21033 raw21033Labels = mixedMoment B node1186 node1186Labels := by
  calc
    mixedMoment B raw21033 raw21033Labels = mixedMoment B raw21033step0 raw21033step0Labels := by
      have hz : ∀ j, raw21033 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21033step0 = (fun i j => raw21033 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21033step0 raw21033; decide +kernel
      have hl : raw21033step0Labels = raw21033Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21033 raw21033Labels permutation346 hz
    mixedMoment B raw21033step0 raw21033step0Labels = mixedMoment B raw21033step1 raw21033step1Labels := by
      have hz : ∀ j, raw21033step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21033step1 = (fun i j => raw21033step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21033step1 raw21033step0; decide +kernel
      have hl : raw21033step1Labels = raw21033step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21033step0 raw21033step0Labels permutation56 hz
    _ = mixedMoment B node1186 node1186Labels := by rfl

def raw21034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![3, 1, -4]]
def raw21034Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21034step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![3, 1, -4]]
def raw21034step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21034step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw21034step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21034step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw21034step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21034 raw21034Labels = mixedMoment B node1608 node1608Labels := by
  calc
    mixedMoment B raw21034 raw21034Labels = mixedMoment B raw21034step0 raw21034step0Labels := by
      have hz : ∀ j, raw21034 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21034step0 = (fun i j => raw21034 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21034step0 raw21034; decide +kernel
      have hl : raw21034step0Labels = raw21034Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21034 raw21034Labels permutation346 hz
    mixedMoment B raw21034step0 raw21034step0Labels = mixedMoment B raw21034step1 raw21034step1Labels := by
      have ha : raw21034step1 = (fun i j => raw21034step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21034step1 raw21034step0; decide +kernel
      have hl : raw21034step1Labels = raw21034step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21034step0 raw21034step0Labels permutation151 permutation2
    mixedMoment B raw21034step1 raw21034step1Labels = mixedMoment B raw21034step2 raw21034step2Labels := by
      have ha : raw21034step2 = -raw21034step1 := by apply Matrix.ext; change ∀ i j, raw21034step2 i j = -(raw21034step1 i j); unfold raw21034step2 raw21034step1; decide +kernel
      have hl : raw21034step2Labels = raw21034step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1608 node1608Labels := by rfl

def raw21035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![3, 1, -4]]
def raw21035Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21035step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![3, 1, -4]]
def raw21035step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21035step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw21035step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21035step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw21035step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21035 raw21035Labels = mixedMoment B node1608 node1608Labels := by
  calc
    mixedMoment B raw21035 raw21035Labels = mixedMoment B raw21035step0 raw21035step0Labels := by
      have hz : ∀ j, raw21035 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21035step0 = (fun i j => raw21035 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21035step0 raw21035; decide +kernel
      have hl : raw21035step0Labels = raw21035Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21035 raw21035Labels permutation265 hz
    mixedMoment B raw21035step0 raw21035step0Labels = mixedMoment B raw21035step1 raw21035step1Labels := by
      have ha : raw21035step1 = (fun i j => raw21035step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21035step1 raw21035step0; decide +kernel
      have hl : raw21035step1Labels = raw21035step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21035step0 raw21035step0Labels permutation151 permutation2
    mixedMoment B raw21035step1 raw21035step1Labels = mixedMoment B raw21035step2 raw21035step2Labels := by
      have ha : raw21035step2 = -raw21035step1 := by apply Matrix.ext; change ∀ i j, raw21035step2 i j = -(raw21035step1 i j); unfold raw21035step2 raw21035step1; decide +kernel
      have hl : raw21035step2Labels = raw21035step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1608 node1608Labels := by rfl

def raw21036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![1, -1, 0], ![3, 1, -4]]
def raw21036Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21036step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, -1, 2], ![1, -1, 0], ![3, 1, -4]]
def raw21036step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21036step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![3, 1, -4]]
def raw21036step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21036step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw21036step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21036step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw21036step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21036 raw21036Labels = mixedMoment B node1627 node1627Labels := by
  calc
    mixedMoment B raw21036 raw21036Labels = mixedMoment B raw21036step0 raw21036step0Labels := by
      have hz : ∀ j, raw21036 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21036step0 = (fun i j => raw21036 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21036step0 raw21036; decide +kernel
      have hl : raw21036step0Labels = raw21036Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21036 raw21036Labels permutation346 hz
    mixedMoment B raw21036step0 raw21036step0Labels = mixedMoment B raw21036step1 raw21036step1Labels := by
      have hz : ∀ j, raw21036step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21036step1 = (fun i j => raw21036step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21036step1 raw21036step0; decide +kernel
      have hl : raw21036step1Labels = raw21036step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21036step0 raw21036step0Labels permutation56 hz
    mixedMoment B raw21036step1 raw21036step1Labels = mixedMoment B raw21036step2 raw21036step2Labels := by
      have ha : raw21036step2 = (fun i j => raw21036step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21036step2 raw21036step1; decide +kernel
      have hl : raw21036step2Labels = raw21036step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21036step1 raw21036step1Labels permutation31 permutation2
    mixedMoment B raw21036step2 raw21036step2Labels = mixedMoment B raw21036step3 raw21036step3Labels := by
      have ha : raw21036step3 = -raw21036step2 := by apply Matrix.ext; change ∀ i j, raw21036step3 i j = -(raw21036step2 i j); unfold raw21036step3 raw21036step2; decide +kernel
      have hl : raw21036step3Labels = raw21036step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1627 node1627Labels := by rfl

def raw21037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![0, 0, 0], ![3, 1, -4]]
def raw21037Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21037step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, 1, -4]]
def raw21037step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21037step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![3, 1, -4]]
def raw21037step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21037step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![3, 1, -4]]
def raw21037step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21037step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-3, 1, 2]]
def raw21037step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21037step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![3, -1, -2]]
def raw21037step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21037 raw21037Labels = mixedMoment B node1741 node1741Labels := by
  calc
    mixedMoment B raw21037 raw21037Labels = mixedMoment B raw21037step0 raw21037step0Labels := by
      have hz : ∀ j, raw21037 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21037step0 = (fun i j => raw21037 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21037step0 raw21037; decide +kernel
      have hl : raw21037step0Labels = raw21037Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21037 raw21037Labels permutation520 hz
    mixedMoment B raw21037step0 raw21037step0Labels = mixedMoment B raw21037step1 raw21037step1Labels := by
      have hz : ∀ j, raw21037step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21037step1 = (fun i j => raw21037step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21037step1 raw21037step0; decide +kernel
      have hl : raw21037step1Labels = raw21037step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21037step0 raw21037step0Labels permutation80 hz
    mixedMoment B raw21037step1 raw21037step1Labels = mixedMoment B raw21037step2 raw21037step2Labels := by
      have hz : ∀ j, raw21037step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21037step2 = (fun i j => raw21037step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21037step2 raw21037step1; decide +kernel
      have hl : raw21037step2Labels = raw21037step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21037step1 raw21037step1Labels permutation14 hz
    mixedMoment B raw21037step2 raw21037step2Labels = mixedMoment B raw21037step3 raw21037step3Labels := by
      have ha : raw21037step3 = (fun i j => raw21037step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21037step3 raw21037step2; decide +kernel
      have hl : raw21037step3Labels = raw21037step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21037step2 raw21037step2Labels permutation7 permutation2
    mixedMoment B raw21037step3 raw21037step3Labels = mixedMoment B raw21037step4 raw21037step4Labels := by
      have ha : raw21037step4 = -raw21037step3 := by apply Matrix.ext; change ∀ i j, raw21037step4 i j = -(raw21037step3 i j); unfold raw21037step4 raw21037step3; decide +kernel
      have hl : raw21037step4Labels = raw21037step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1741 node1741Labels := by rfl

def raw21038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw21038Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21038step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw21038step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21038step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw21038step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21038 raw21038Labels = mixedMoment B node2683 node2683Labels := by
  calc
    mixedMoment B raw21038 raw21038Labels = mixedMoment B raw21038step0 raw21038step0Labels := by
      have hz : ∀ j, raw21038 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21038step0 = (fun i j => raw21038 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21038step0 raw21038; decide +kernel
      have hl : raw21038step0Labels = raw21038Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21038 raw21038Labels permutation346 hz
    mixedMoment B raw21038step0 raw21038step0Labels = mixedMoment B raw21038step1 raw21038step1Labels := by
      have hz : ∀ j, raw21038step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21038step1 = (fun i j => raw21038step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21038step1 raw21038step0; decide +kernel
      have hl : raw21038step1Labels = raw21038step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21038step0 raw21038step0Labels permutation56 hz
    _ = mixedMoment B node2683 node2683Labels := by rfl

def raw21039 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![-2, 2], ![0, 0], ![4, -4]]
def raw21039Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21039step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![-2, 2], ![4, -4]]
def raw21039step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21039step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-2, 2], ![4, -4]]
def raw21039step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21039step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![4, -4]]
def raw21039step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21039step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![4, -4], ![-2, 2], ![-2, 2]]
def raw21039step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21039step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![2, -2]]
def raw21039step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical21039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21039 raw21039Labels = mixedMoment B node4071 node4071Labels := by
  calc
    mixedMoment B raw21039 raw21039Labels = mixedMoment B raw21039step0 raw21039step0Labels := by
      have hz : ∀ j, raw21039 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21039step0 = (fun i j => raw21039 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21039step0 raw21039; decide +kernel
      have hl : raw21039step0Labels = raw21039Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21039 raw21039Labels permutation520 hz
    mixedMoment B raw21039step0 raw21039step0Labels = mixedMoment B raw21039step1 raw21039step1Labels := by
      have hz : ∀ j, raw21039step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21039step1 = (fun i j => raw21039step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21039step1 raw21039step0; decide +kernel
      have hl : raw21039step1Labels = raw21039step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21039step0 raw21039step0Labels permutation80 hz
    mixedMoment B raw21039step1 raw21039step1Labels = mixedMoment B raw21039step2 raw21039step2Labels := by
      have hz : ∀ j, raw21039step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21039step2 = (fun i j => raw21039step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21039step2 raw21039step1; decide +kernel
      have hl : raw21039step2Labels = raw21039step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21039step1 raw21039step1Labels permutation14 hz
    mixedMoment B raw21039step2 raw21039step2Labels = mixedMoment B raw21039step3 raw21039step3Labels := by
      have ha : raw21039step3 = (fun i j => raw21039step2 (permutation6 i) (permutation0 j)) := by apply Matrix.ext; unfold raw21039step3 raw21039step2; decide +kernel
      have hl : raw21039step3Labels = raw21039step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21039step2 raw21039step2Labels permutation6 permutation0
    mixedMoment B raw21039step3 raw21039step3Labels = mixedMoment B raw21039step4 raw21039step4Labels := by
      have ha : raw21039step4 = -raw21039step3 := by apply Matrix.ext; change ∀ i j, raw21039step4 i j = -(raw21039step3 i j); unfold raw21039step4 raw21039step3; decide +kernel
      have hl : raw21039step4Labels = raw21039step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4071 node4071Labels := by rfl

def raw21040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21040Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21040step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21040 raw21040Labels = mixedMoment B node1203 node1203Labels := by
  calc
    mixedMoment B raw21040 raw21040Labels = mixedMoment B raw21040step0 raw21040step0Labels := by
      have hz : ∀ j, raw21040 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21040step0 = (fun i j => raw21040 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21040step0 raw21040; decide +kernel
      have hl : raw21040step0Labels = raw21040Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21040 raw21040Labels permutation265 hz
    _ = mixedMoment B node1203 node1203Labels := by rfl

def raw21041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21041Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21041step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw21041step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21041step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21041step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21041 raw21041Labels = mixedMoment B node2377 node2377Labels := by
  calc
    mixedMoment B raw21041 raw21041Labels = mixedMoment B raw21041step0 raw21041step0Labels := by
      have ha : raw21041step0 = (fun i j => raw21041 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21041step0 raw21041; decide +kernel
      have hl : raw21041step0Labels = raw21041Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21041 raw21041Labels permutation682 permutation2
    mixedMoment B raw21041step0 raw21041step0Labels = mixedMoment B raw21041step1 raw21041step1Labels := by
      have ha : raw21041step1 = -raw21041step0 := by apply Matrix.ext; change ∀ i j, raw21041step1 i j = -(raw21041step0 i j); unfold raw21041step1 raw21041step0; decide +kernel
      have hl : raw21041step1Labels = raw21041step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2377 node2377Labels := by rfl

def raw21042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21042Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21042step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21042step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw21042step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21042step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21042step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21042 raw21042Labels = mixedMoment B node2385 node2385Labels := by
  calc
    mixedMoment B raw21042 raw21042Labels = mixedMoment B raw21042step0 raw21042step0Labels := by
      have hz : ∀ j, raw21042 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21042step0 = (fun i j => raw21042 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21042step0 raw21042; decide +kernel
      have hl : raw21042step0Labels = raw21042Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21042 raw21042Labels permutation265 hz
    mixedMoment B raw21042step0 raw21042step0Labels = mixedMoment B raw21042step1 raw21042step1Labels := by
      have ha : raw21042step1 = (fun i j => raw21042step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21042step1 raw21042step0; decide +kernel
      have hl : raw21042step1Labels = raw21042step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21042step0 raw21042step0Labels permutation151 permutation2
    mixedMoment B raw21042step1 raw21042step1Labels = mixedMoment B raw21042step2 raw21042step2Labels := by
      have ha : raw21042step2 = -raw21042step1 := by apply Matrix.ext; change ∀ i j, raw21042step2 i j = -(raw21042step1 i j); unfold raw21042step2 raw21042step1; decide +kernel
      have hl : raw21042step2Labels = raw21042step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2385 node2385Labels := by rfl

def raw21043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21043Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21043step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21043step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21043step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw21043step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21043step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21043step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21043 raw21043Labels = mixedMoment B node2385 node2385Labels := by
  calc
    mixedMoment B raw21043 raw21043Labels = mixedMoment B raw21043step0 raw21043step0Labels := by
      have hz : ∀ j, raw21043 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21043step0 = (fun i j => raw21043 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21043step0 raw21043; decide +kernel
      have hl : raw21043step0Labels = raw21043Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21043 raw21043Labels permutation265 hz
    mixedMoment B raw21043step0 raw21043step0Labels = mixedMoment B raw21043step1 raw21043step1Labels := by
      have ha : raw21043step1 = (fun i j => raw21043step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21043step1 raw21043step0; decide +kernel
      have hl : raw21043step1Labels = raw21043step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21043step0 raw21043step0Labels permutation149 permutation2
    mixedMoment B raw21043step1 raw21043step1Labels = mixedMoment B raw21043step2 raw21043step2Labels := by
      have ha : raw21043step2 = -raw21043step1 := by apply Matrix.ext; change ∀ i j, raw21043step2 i j = -(raw21043step1 i j); unfold raw21043step2 raw21043step1; decide +kernel
      have hl : raw21043step2Labels = raw21043step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2385 node2385Labels := by rfl

def raw21044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw21044Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21044step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw21044step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21044step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw21044step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21044step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw21044step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21044 raw21044Labels = mixedMoment B node2664 node2664Labels := by
  calc
    mixedMoment B raw21044 raw21044Labels = mixedMoment B raw21044step0 raw21044step0Labels := by
      have hz : ∀ j, raw21044 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21044step0 = (fun i j => raw21044 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21044step0 raw21044; decide +kernel
      have hl : raw21044step0Labels = raw21044Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21044 raw21044Labels permutation265 hz
    mixedMoment B raw21044step0 raw21044step0Labels = mixedMoment B raw21044step1 raw21044step1Labels := by
      have ha : raw21044step1 = (fun i j => raw21044step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21044step1 raw21044step0; decide +kernel
      have hl : raw21044step1Labels = raw21044step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21044step0 raw21044step0Labels permutation149 permutation2
    mixedMoment B raw21044step1 raw21044step1Labels = mixedMoment B raw21044step2 raw21044step2Labels := by
      have ha : raw21044step2 = -raw21044step1 := by apply Matrix.ext; change ∀ i j, raw21044step2 i j = -(raw21044step1 i j); unfold raw21044step2 raw21044step1; decide +kernel
      have hl : raw21044step2Labels = raw21044step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2664 node2664Labels := by rfl

def raw21045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw21045Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21045step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw21045step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21045 raw21045Labels = mixedMoment B node2705 node2705Labels := by
  calc
    mixedMoment B raw21045 raw21045Labels = mixedMoment B raw21045step0 raw21045step0Labels := by
      have hz : ∀ j, raw21045 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21045step0 = (fun i j => raw21045 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21045step0 raw21045; decide +kernel
      have hl : raw21045step0Labels = raw21045Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21045 raw21045Labels permutation265 hz
    _ = mixedMoment B node2705 node2705Labels := by rfl

def raw21046 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![-1, 1], ![2, -2], ![2, -2]]
def raw21046Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21046step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![2, -2], ![2, -2]]
def raw21046step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21046step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![2, -2], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw21046step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21046step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw21046step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical21046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21046 raw21046Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw21046 raw21046Labels = mixedMoment B raw21046step0 raw21046step0Labels := by
      have hz : ∀ j, raw21046 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21046step0 = (fun i j => raw21046 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21046step0 raw21046; decide +kernel
      have hl : raw21046step0Labels = raw21046Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21046 raw21046Labels permutation265 hz
    mixedMoment B raw21046step0 raw21046step0Labels = mixedMoment B raw21046step1 raw21046step1Labels := by
      have ha : raw21046step1 = (fun i j => raw21046step0 (permutation125 i) (permutation0 j)) := by apply Matrix.ext; unfold raw21046step1 raw21046step0; decide +kernel
      have hl : raw21046step1Labels = raw21046step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21046step0 raw21046step0Labels permutation125 permutation0
    mixedMoment B raw21046step1 raw21046step1Labels = mixedMoment B raw21046step2 raw21046step2Labels := by
      have ha : raw21046step2 = -raw21046step1 := by apply Matrix.ext; change ∀ i j, raw21046step2 i j = -(raw21046step1 i j); unfold raw21046step2 raw21046step1; decide +kernel
      have hl : raw21046step2Labels = raw21046step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4088 node4088Labels := by rfl

def raw21047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw21047Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21047step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw21047step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21047 raw21047Labels = mixedMoment B node1198 node1198Labels := by
  calc
    mixedMoment B raw21047 raw21047Labels = mixedMoment B raw21047step0 raw21047step0Labels := by
      have ha : raw21047step0 = (fun i j => raw21047 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21047step0 raw21047; decide +kernel
      have hl : raw21047step0Labels = raw21047Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21047 raw21047Labels permutation182 permutation2
    _ = mixedMoment B node1198 node1198Labels := by rfl

def raw21048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw21048Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21048step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw21048step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21048step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw21048step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21048 raw21048Labels = mixedMoment B node1230 node1230Labels := by
  calc
    mixedMoment B raw21048 raw21048Labels = mixedMoment B raw21048step0 raw21048step0Labels := by
      have hz : ∀ j, raw21048 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21048step0 = (fun i j => raw21048 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21048step0 raw21048; decide +kernel
      have hl : raw21048step0Labels = raw21048Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21048 raw21048Labels permutation265 hz
    mixedMoment B raw21048step0 raw21048step0Labels = mixedMoment B raw21048step1 raw21048step1Labels := by
      have ha : raw21048step1 = (fun i j => raw21048step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21048step1 raw21048step0; decide +kernel
      have hl : raw21048step1Labels = raw21048step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21048step0 raw21048step0Labels permutation38 permutation2
    _ = mixedMoment B node1230 node1230Labels := by rfl

def raw21049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw21049Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw21049step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21049 raw21049Labels = mixedMoment B node1230 node1230Labels := by
  calc
    mixedMoment B raw21049 raw21049Labels = mixedMoment B raw21049step0 raw21049step0Labels := by
      have hz : ∀ j, raw21049 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21049step0 = (fun i j => raw21049 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21049step0 raw21049; decide +kernel
      have hl : raw21049step0Labels = raw21049Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21049 raw21049Labels permutation265 hz
    _ = mixedMoment B node1230 node1230Labels := by rfl

def raw21050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw21050Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw21050step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21050 raw21050Labels = mixedMoment B node1205 node1205Labels := by
  calc
    mixedMoment B raw21050 raw21050Labels = mixedMoment B raw21050step0 raw21050step0Labels := by
      have hz : ∀ j, raw21050 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21050step0 = (fun i j => raw21050 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21050step0 raw21050; decide +kernel
      have hl : raw21050step0Labels = raw21050Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21050 raw21050Labels permutation265 hz
    _ = mixedMoment B node1205 node1205Labels := by rfl

def raw21051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21051Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21051step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21051 raw21051Labels = mixedMoment B node1202 node1202Labels := by
  calc
    mixedMoment B raw21051 raw21051Labels = mixedMoment B raw21051step0 raw21051step0Labels := by
      have hz : ∀ j, raw21051 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21051step0 = (fun i j => raw21051 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21051step0 raw21051; decide +kernel
      have hl : raw21051step0Labels = raw21051Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21051 raw21051Labels permutation265 hz
    _ = mixedMoment B node1202 node1202Labels := by rfl

def raw21052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21052Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21052step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw21052step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21052step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21052step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21052 raw21052Labels = mixedMoment B node1897 node1897Labels := by
  calc
    mixedMoment B raw21052 raw21052Labels = mixedMoment B raw21052step0 raw21052step0Labels := by
      have ha : raw21052step0 = (fun i j => raw21052 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21052step0 raw21052; decide +kernel
      have hl : raw21052step0Labels = raw21052Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21052 raw21052Labels permutation682 permutation2
    mixedMoment B raw21052step0 raw21052step0Labels = mixedMoment B raw21052step1 raw21052step1Labels := by
      have ha : raw21052step1 = -raw21052step0 := by apply Matrix.ext; change ∀ i j, raw21052step1 i j = -(raw21052step0 i j); unfold raw21052step1 raw21052step0; decide +kernel
      have hl : raw21052step1Labels = raw21052step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1897 node1897Labels := by rfl

def raw21053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21053Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21053step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21053step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21053step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw21053step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21053step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21053step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21053 raw21053Labels = mixedMoment B node1914 node1914Labels := by
  calc
    mixedMoment B raw21053 raw21053Labels = mixedMoment B raw21053step0 raw21053step0Labels := by
      have hz : ∀ j, raw21053 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21053step0 = (fun i j => raw21053 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21053step0 raw21053; decide +kernel
      have hl : raw21053step0Labels = raw21053Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21053 raw21053Labels permutation265 hz
    mixedMoment B raw21053step0 raw21053step0Labels = mixedMoment B raw21053step1 raw21053step1Labels := by
      have ha : raw21053step1 = (fun i j => raw21053step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21053step1 raw21053step0; decide +kernel
      have hl : raw21053step1Labels = raw21053step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21053step0 raw21053step0Labels permutation151 permutation2
    mixedMoment B raw21053step1 raw21053step1Labels = mixedMoment B raw21053step2 raw21053step2Labels := by
      have ha : raw21053step2 = -raw21053step1 := by apply Matrix.ext; change ∀ i j, raw21053step2 i j = -(raw21053step1 i j); unfold raw21053step2 raw21053step1; decide +kernel
      have hl : raw21053step2Labels = raw21053step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1914 node1914Labels := by rfl

def raw21054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21054Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21054step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21054step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21054step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw21054step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21054step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21054step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21054 raw21054Labels = mixedMoment B node1914 node1914Labels := by
  calc
    mixedMoment B raw21054 raw21054Labels = mixedMoment B raw21054step0 raw21054step0Labels := by
      have hz : ∀ j, raw21054 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21054step0 = (fun i j => raw21054 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21054step0 raw21054; decide +kernel
      have hl : raw21054step0Labels = raw21054Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21054 raw21054Labels permutation265 hz
    mixedMoment B raw21054step0 raw21054step0Labels = mixedMoment B raw21054step1 raw21054step1Labels := by
      have ha : raw21054step1 = (fun i j => raw21054step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21054step1 raw21054step0; decide +kernel
      have hl : raw21054step1Labels = raw21054step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21054step0 raw21054step0Labels permutation149 permutation2
    mixedMoment B raw21054step1 raw21054step1Labels = mixedMoment B raw21054step2 raw21054step2Labels := by
      have ha : raw21054step2 = -raw21054step1 := by apply Matrix.ext; change ∀ i j, raw21054step2 i j = -(raw21054step1 i j); unfold raw21054step2 raw21054step1; decide +kernel
      have hl : raw21054step2Labels = raw21054step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1914 node1914Labels := by rfl

def raw21055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21055Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21055step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21055step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw21055step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21055step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw21055step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21055 raw21055Labels = mixedMoment B node2193 node2193Labels := by
  calc
    mixedMoment B raw21055 raw21055Labels = mixedMoment B raw21055step0 raw21055step0Labels := by
      have hz : ∀ j, raw21055 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21055step0 = (fun i j => raw21055 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21055step0 raw21055; decide +kernel
      have hl : raw21055step0Labels = raw21055Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21055 raw21055Labels permutation265 hz
    mixedMoment B raw21055step0 raw21055step0Labels = mixedMoment B raw21055step1 raw21055step1Labels := by
      have ha : raw21055step1 = (fun i j => raw21055step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21055step1 raw21055step0; decide +kernel
      have hl : raw21055step1Labels = raw21055step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21055step0 raw21055step0Labels permutation149 permutation2
    mixedMoment B raw21055step1 raw21055step1Labels = mixedMoment B raw21055step2 raw21055step2Labels := by
      have ha : raw21055step2 = -raw21055step1 := by apply Matrix.ext; change ∀ i j, raw21055step2 i j = -(raw21055step1 i j); unfold raw21055step2 raw21055step1; decide +kernel
      have hl : raw21055step2Labels = raw21055step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2193 node2193Labels := by rfl

def raw21056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21056Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21056step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21056step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21056 raw21056Labels = mixedMoment B node2704 node2704Labels := by
  calc
    mixedMoment B raw21056 raw21056Labels = mixedMoment B raw21056step0 raw21056step0Labels := by
      have hz : ∀ j, raw21056 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21056step0 = (fun i j => raw21056 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21056step0 raw21056; decide +kernel
      have hl : raw21056step0Labels = raw21056Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21056 raw21056Labels permutation265 hz
    _ = mixedMoment B node2704 node2704Labels := by rfl

def raw21057 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![-1, 1], ![1, -1], ![3, -3]]
def raw21057Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21057step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![3, -3]]
def raw21057step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21057step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw21057step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21057step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw21057step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical21057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21057 raw21057Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw21057 raw21057Labels = mixedMoment B raw21057step0 raw21057step0Labels := by
      have hz : ∀ j, raw21057 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21057step0 = (fun i j => raw21057 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21057step0 raw21057; decide +kernel
      have hl : raw21057step0Labels = raw21057Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21057 raw21057Labels permutation265 hz
    mixedMoment B raw21057step0 raw21057step0Labels = mixedMoment B raw21057step1 raw21057step1Labels := by
      have ha : raw21057step1 = (fun i j => raw21057step0 (permutation149 i) (permutation0 j)) := by apply Matrix.ext; unfold raw21057step1 raw21057step0; decide +kernel
      have hl : raw21057step1Labels = raw21057step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21057step0 raw21057step0Labels permutation149 permutation0
    mixedMoment B raw21057step1 raw21057step1Labels = mixedMoment B raw21057step2 raw21057step2Labels := by
      have ha : raw21057step2 = -raw21057step1 := by apply Matrix.ext; change ∀ i j, raw21057step2 i j = -(raw21057step1 i j); unfold raw21057step2 raw21057step1; decide +kernel
      have hl : raw21057step2Labels = raw21057step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw21058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21058Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21058step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw21058step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21058 raw21058Labels = mixedMoment B node1105 node1105Labels := by
  calc
    mixedMoment B raw21058 raw21058Labels = mixedMoment B raw21058step0 raw21058step0Labels := by
      have ha : raw21058step0 = (fun i j => raw21058 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21058step0 raw21058; decide +kernel
      have hl : raw21058step0Labels = raw21058Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21058 raw21058Labels permutation182 permutation2
    _ = mixedMoment B node1105 node1105Labels := by rfl

def raw21059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21059Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21059step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21059 raw21059Labels = mixedMoment B node1123 node1123Labels := by
  calc
    mixedMoment B raw21059 raw21059Labels = mixedMoment B raw21059step0 raw21059step0Labels := by
      have hz : ∀ j, raw21059 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21059step0 = (fun i j => raw21059 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21059step0 raw21059; decide +kernel
      have hl : raw21059step0Labels = raw21059Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21059 raw21059Labels permutation265 hz
    _ = mixedMoment B node1123 node1123Labels := by rfl

def raw21060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21060Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21060step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21060step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21060 raw21060Labels = mixedMoment B node1109 node1109Labels := by
  calc
    mixedMoment B raw21060 raw21060Labels = mixedMoment B raw21060step0 raw21060step0Labels := by
      have hz : ∀ j, raw21060 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21060step0 = (fun i j => raw21060 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21060step0 raw21060; decide +kernel
      have hl : raw21060step0Labels = raw21060Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21060 raw21060Labels permutation265 hz
    _ = mixedMoment B node1109 node1109Labels := by rfl

def raw21061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21061Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21061step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21061step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21061step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-4, 2, 2]]
def raw21061step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21061step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -2, -2]]
def raw21061step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21061 raw21061Labels = mixedMoment B node871 node871Labels := by
  calc
    mixedMoment B raw21061 raw21061Labels = mixedMoment B raw21061step0 raw21061step0Labels := by
      have hz : ∀ j, raw21061 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21061step0 = (fun i j => raw21061 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21061step0 raw21061; decide +kernel
      have hl : raw21061step0Labels = raw21061Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21061 raw21061Labels permutation265 hz
    mixedMoment B raw21061step0 raw21061step0Labels = mixedMoment B raw21061step1 raw21061step1Labels := by
      have ha : raw21061step1 = (fun i j => raw21061step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21061step1 raw21061step0; decide +kernel
      have hl : raw21061step1Labels = raw21061step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21061step0 raw21061step0Labels permutation151 permutation2
    mixedMoment B raw21061step1 raw21061step1Labels = mixedMoment B raw21061step2 raw21061step2Labels := by
      have ha : raw21061step2 = -raw21061step1 := by apply Matrix.ext; change ∀ i j, raw21061step2 i j = -(raw21061step1 i j); unfold raw21061step2 raw21061step1; decide +kernel
      have hl : raw21061step2Labels = raw21061step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node871 node871Labels := by rfl

def raw21062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21062Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21062step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw21062step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21062 raw21062Labels = mixedMoment B node1197 node1197Labels := by
  calc
    mixedMoment B raw21062 raw21062Labels = mixedMoment B raw21062step0 raw21062step0Labels := by
      have ha : raw21062step0 = (fun i j => raw21062 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21062step0 raw21062; decide +kernel
      have hl : raw21062step0Labels = raw21062Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21062 raw21062Labels permutation182 permutation2
    _ = mixedMoment B node1197 node1197Labels := by rfl

def raw21063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21063Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21063step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21063step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21063step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21063 raw21063Labels = mixedMoment B node1229 node1229Labels := by
  calc
    mixedMoment B raw21063 raw21063Labels = mixedMoment B raw21063step0 raw21063step0Labels := by
      have hz : ∀ j, raw21063 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21063step0 = (fun i j => raw21063 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21063step0 raw21063; decide +kernel
      have hl : raw21063step0Labels = raw21063Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21063 raw21063Labels permutation265 hz
    mixedMoment B raw21063step0 raw21063step0Labels = mixedMoment B raw21063step1 raw21063step1Labels := by
      have ha : raw21063step1 = (fun i j => raw21063step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21063step1 raw21063step0; decide +kernel
      have hl : raw21063step1Labels = raw21063step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21063step0 raw21063step0Labels permutation38 permutation2
    _ = mixedMoment B node1229 node1229Labels := by rfl

def raw21064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21064Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21064step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21064 raw21064Labels = mixedMoment B node1229 node1229Labels := by
  calc
    mixedMoment B raw21064 raw21064Labels = mixedMoment B raw21064step0 raw21064step0Labels := by
      have hz : ∀ j, raw21064 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21064step0 = (fun i j => raw21064 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21064step0 raw21064; decide +kernel
      have hl : raw21064step0Labels = raw21064Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21064 raw21064Labels permutation265 hz
    _ = mixedMoment B node1229 node1229Labels := by rfl

def raw21065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw21065Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21065step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw21065step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21065 raw21065Labels = mixedMoment B node1204 node1204Labels := by
  calc
    mixedMoment B raw21065 raw21065Labels = mixedMoment B raw21065step0 raw21065step0Labels := by
      have hz : ∀ j, raw21065 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21065step0 = (fun i j => raw21065 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21065step0 raw21065; decide +kernel
      have hl : raw21065step0Labels = raw21065Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21065 raw21065Labels permutation265 hz
    _ = mixedMoment B node1204 node1204Labels := by rfl

def raw21066 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw21066Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21066step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw21066step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21066step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw21066step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21066 raw21066Labels = mixedMoment B node1942 node1942Labels := by
  calc
    mixedMoment B raw21066 raw21066Labels = mixedMoment B raw21066step0 raw21066step0Labels := by
      have hz : ∀ j, raw21066 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21066step0 = (fun i j => raw21066 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21066step0 raw21066; decide +kernel
      have hl : raw21066step0Labels = raw21066Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21066 raw21066Labels permutation265 hz
    mixedMoment B raw21066step0 raw21066step0Labels = mixedMoment B raw21066step1 raw21066step1Labels := by
      have ha : raw21066step1 = (fun i j => raw21066step0 (permutation149 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21066step1 raw21066step0; decide +kernel
      have hl : raw21066step1Labels = raw21066step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21066step0 raw21066step0Labels permutation149 permutation4
    _ = mixedMoment B node1942 node1942Labels := by rfl

def raw21067 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw21067Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21067step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw21067step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21067step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw21067step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21067 raw21067Labels = mixedMoment B node1580 node1580Labels := by
  calc
    mixedMoment B raw21067 raw21067Labels = mixedMoment B raw21067step0 raw21067step0Labels := by
      have ha : raw21067step0 = (fun i j => raw21067 (permutation182 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21067step0 raw21067; decide +kernel
      have hl : raw21067step0Labels = raw21067Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21067 raw21067Labels permutation182 permutation4
    mixedMoment B raw21067step0 raw21067step0Labels = mixedMoment B raw21067step1 raw21067step1Labels := by
      have ha : raw21067step1 = -raw21067step0 := by apply Matrix.ext; change ∀ i j, raw21067step1 i j = -(raw21067step0 i j); unfold raw21067step1 raw21067step0; decide +kernel
      have hl : raw21067step1Labels = raw21067step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1580 node1580Labels := by rfl

def raw21068 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -3, 3]]
def raw21068Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21068step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw21068step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21068step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw21068step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21068step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw21068step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21068step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw21068step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21068 raw21068Labels = mixedMoment B node1625 node1625Labels := by
  calc
    mixedMoment B raw21068 raw21068Labels = mixedMoment B raw21068step0 raw21068step0Labels := by
      have hz : ∀ j, raw21068 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21068step0 = (fun i j => raw21068 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21068step0 raw21068; decide +kernel
      have hl : raw21068step0Labels = raw21068Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21068 raw21068Labels permutation434 hz
    mixedMoment B raw21068step0 raw21068step0Labels = mixedMoment B raw21068step1 raw21068step1Labels := by
      have hz : ∀ j, raw21068step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21068step1 = (fun i j => raw21068step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21068step1 raw21068step0; decide +kernel
      have hl : raw21068step1Labels = raw21068step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21068step0 raw21068step0Labels permutation56 hz
    mixedMoment B raw21068step1 raw21068step1Labels = mixedMoment B raw21068step2 raw21068step2Labels := by
      have ha : raw21068step2 = (fun i j => raw21068step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21068step2 raw21068step1; decide +kernel
      have hl : raw21068step2Labels = raw21068step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21068step1 raw21068step1Labels permutation8 permutation4
    mixedMoment B raw21068step2 raw21068step2Labels = mixedMoment B raw21068step3 raw21068step3Labels := by
      have ha : raw21068step3 = -raw21068step2 := by apply Matrix.ext; change ∀ i j, raw21068step3 i j = -(raw21068step2 i j); unfold raw21068step3 raw21068step2; decide +kernel
      have hl : raw21068step3Labels = raw21068step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1625 node1625Labels := by rfl

def raw21069 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -3, 3]]
def raw21069Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21069step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -3, 3]]
def raw21069step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21069step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-3, 0, 3]]
def raw21069step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21069step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, 0, -3]]
def raw21069step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21069 raw21069Labels = mixedMoment B node1584 node1584Labels := by
  calc
    mixedMoment B raw21069 raw21069Labels = mixedMoment B raw21069step0 raw21069step0Labels := by
      have hz : ∀ j, raw21069 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21069step0 = (fun i j => raw21069 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21069step0 raw21069; decide +kernel
      have hl : raw21069step0Labels = raw21069Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21069 raw21069Labels permutation265 hz
    mixedMoment B raw21069step0 raw21069step0Labels = mixedMoment B raw21069step1 raw21069step1Labels := by
      have ha : raw21069step1 = (fun i j => raw21069step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21069step1 raw21069step0; decide +kernel
      have hl : raw21069step1Labels = raw21069step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21069step0 raw21069step0Labels permutation32 permutation4
    mixedMoment B raw21069step1 raw21069step1Labels = mixedMoment B raw21069step2 raw21069step2Labels := by
      have ha : raw21069step2 = -raw21069step1 := by apply Matrix.ext; change ∀ i j, raw21069step2 i j = -(raw21069step1 i j); unfold raw21069step2 raw21069step1; decide +kernel
      have hl : raw21069step2Labels = raw21069step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1584 node1584Labels := by rfl

def raw21070 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -4, 3]]
def raw21070Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21070step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -4, 3]]
def raw21070step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21070step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw21070step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21070 raw21070Labels = mixedMoment B node877 node877Labels := by
  calc
    mixedMoment B raw21070 raw21070Labels = mixedMoment B raw21070step0 raw21070step0Labels := by
      have hz : ∀ j, raw21070 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21070step0 = (fun i j => raw21070 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21070step0 raw21070; decide +kernel
      have hl : raw21070step0Labels = raw21070Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21070 raw21070Labels permutation265 hz
    mixedMoment B raw21070step0 raw21070step0Labels = mixedMoment B raw21070step1 raw21070step1Labels := by
      have ha : raw21070step1 = (fun i j => raw21070step0 (permutation149 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21070step1 raw21070step0; decide +kernel
      have hl : raw21070step1Labels = raw21070step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21070step0 raw21070step0Labels permutation149 permutation4
    _ = mixedMoment B node877 node877Labels := by rfl

def raw21071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw21071Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21071step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw21071step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21071 raw21071Labels = mixedMoment B node1199 node1199Labels := by
  calc
    mixedMoment B raw21071 raw21071Labels = mixedMoment B raw21071step0 raw21071step0Labels := by
      have hz : ∀ j, raw21071 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21071step0 = (fun i j => raw21071 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21071step0 raw21071; decide +kernel
      have hl : raw21071step0Labels = raw21071Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21071 raw21071Labels permutation265 hz
    _ = mixedMoment B node1199 node1199Labels := by rfl

def raw21072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw21072Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21072step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw21072step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21072step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw21072step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21072 raw21072Labels = mixedMoment B node1592 node1592Labels := by
  calc
    mixedMoment B raw21072 raw21072Labels = mixedMoment B raw21072step0 raw21072step0Labels := by
      have ha : raw21072step0 = (fun i j => raw21072 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21072step0 raw21072; decide +kernel
      have hl : raw21072step0Labels = raw21072Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21072 raw21072Labels permutation682 permutation2
    mixedMoment B raw21072step0 raw21072step0Labels = mixedMoment B raw21072step1 raw21072step1Labels := by
      have ha : raw21072step1 = -raw21072step0 := by apply Matrix.ext; change ∀ i j, raw21072step1 i j = -(raw21072step0 i j); unfold raw21072step1 raw21072step0; decide +kernel
      have hl : raw21072step1Labels = raw21072step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1592 node1592Labels := by rfl

def raw21073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw21073Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21073step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![3, 1, -4]]
def raw21073step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21073step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw21073step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21073step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21073step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21073 raw21073Labels = mixedMoment B node1602 node1602Labels := by
  calc
    mixedMoment B raw21073 raw21073Labels = mixedMoment B raw21073step0 raw21073step0Labels := by
      have hz : ∀ j, raw21073 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21073step0 = (fun i j => raw21073 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21073step0 raw21073; decide +kernel
      have hl : raw21073step0Labels = raw21073Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21073 raw21073Labels permutation265 hz
    mixedMoment B raw21073step0 raw21073step0Labels = mixedMoment B raw21073step1 raw21073step1Labels := by
      have ha : raw21073step1 = (fun i j => raw21073step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21073step1 raw21073step0; decide +kernel
      have hl : raw21073step1Labels = raw21073step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21073step0 raw21073step0Labels permutation151 permutation2
    mixedMoment B raw21073step1 raw21073step1Labels = mixedMoment B raw21073step2 raw21073step2Labels := by
      have ha : raw21073step2 = -raw21073step1 := by apply Matrix.ext; change ∀ i j, raw21073step2 i j = -(raw21073step1 i j); unfold raw21073step2 raw21073step1; decide +kernel
      have hl : raw21073step2Labels = raw21073step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1602 node1602Labels := by rfl

def raw21074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![3, 1, -4]]
def raw21074Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![3, 1, -4]]
def raw21074step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21074step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw21074step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21074step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21074step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21074 raw21074Labels = mixedMoment B node1602 node1602Labels := by
  calc
    mixedMoment B raw21074 raw21074Labels = mixedMoment B raw21074step0 raw21074step0Labels := by
      have hz : ∀ j, raw21074 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21074step0 = (fun i j => raw21074 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21074step0 raw21074; decide +kernel
      have hl : raw21074step0Labels = raw21074Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21074 raw21074Labels permutation265 hz
    mixedMoment B raw21074step0 raw21074step0Labels = mixedMoment B raw21074step1 raw21074step1Labels := by
      have ha : raw21074step1 = (fun i j => raw21074step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21074step1 raw21074step0; decide +kernel
      have hl : raw21074step1Labels = raw21074step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21074step0 raw21074step0Labels permutation149 permutation2
    mixedMoment B raw21074step1 raw21074step1Labels = mixedMoment B raw21074step2 raw21074step2Labels := by
      have ha : raw21074step2 = -raw21074step1 := by apply Matrix.ext; change ∀ i j, raw21074step2 i j = -(raw21074step1 i j); unfold raw21074step2 raw21074step1; decide +kernel
      have hl : raw21074step2Labels = raw21074step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1602 node1602Labels := by rfl

def raw21075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![3, 1, -4]]
def raw21075Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21075step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![3, 1, -4]]
def raw21075step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21075step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![3, 1, -4]]
def raw21075step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21075step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw21075step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21075step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw21075step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21075 raw21075Labels = mixedMoment B node1710 node1710Labels := by
  calc
    mixedMoment B raw21075 raw21075Labels = mixedMoment B raw21075step0 raw21075step0Labels := by
      have hz : ∀ j, raw21075 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21075step0 = (fun i j => raw21075 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21075step0 raw21075; decide +kernel
      have hl : raw21075step0Labels = raw21075Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21075 raw21075Labels permutation520 hz
    mixedMoment B raw21075step0 raw21075step0Labels = mixedMoment B raw21075step1 raw21075step1Labels := by
      have hz : ∀ j, raw21075step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21075step1 = (fun i j => raw21075step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21075step1 raw21075step0; decide +kernel
      have hl : raw21075step1Labels = raw21075step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21075step0 raw21075step0Labels permutation56 hz
    mixedMoment B raw21075step1 raw21075step1Labels = mixedMoment B raw21075step2 raw21075step2Labels := by
      have ha : raw21075step2 = (fun i j => raw21075step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21075step2 raw21075step1; decide +kernel
      have hl : raw21075step2Labels = raw21075step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21075step1 raw21075step1Labels permutation29 permutation2
    mixedMoment B raw21075step2 raw21075step2Labels = mixedMoment B raw21075step3 raw21075step3Labels := by
      have ha : raw21075step3 = -raw21075step2 := by apply Matrix.ext; change ∀ i j, raw21075step3 i j = -(raw21075step2 i j); unfold raw21075step3 raw21075step2; decide +kernel
      have hl : raw21075step3Labels = raw21075step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1710 node1710Labels := by rfl

def raw21076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw21076Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw21076step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21076 raw21076Labels = mixedMoment B node2702 node2702Labels := by
  calc
    mixedMoment B raw21076 raw21076Labels = mixedMoment B raw21076step0 raw21076step0Labels := by
      have hz : ∀ j, raw21076 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21076step0 = (fun i j => raw21076 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21076step0 raw21076; decide +kernel
      have hl : raw21076step0Labels = raw21076Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21076 raw21076Labels permutation265 hz
    _ = mixedMoment B node2702 node2702Labels := by rfl

def raw21077 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![-1, 1], ![0, 0], ![4, -4]]
def raw21077Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21077step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![-1, 1], ![-1, 1], ![4, -4]]
def raw21077step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21077step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![4, -4]]
def raw21077step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21077step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![4, -4], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw21077step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21077step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw21077step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical21077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21077 raw21077Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw21077 raw21077Labels = mixedMoment B raw21077step0 raw21077step0Labels := by
      have hz : ∀ j, raw21077 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21077step0 = (fun i j => raw21077 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21077step0 raw21077; decide +kernel
      have hl : raw21077step0Labels = raw21077Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21077 raw21077Labels permutation520 hz
    mixedMoment B raw21077step0 raw21077step0Labels = mixedMoment B raw21077step1 raw21077step1Labels := by
      have hz : ∀ j, raw21077step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21077step1 = (fun i j => raw21077step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21077step1 raw21077step0; decide +kernel
      have hl : raw21077step1Labels = raw21077step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21077step0 raw21077step0Labels permutation56 hz
    mixedMoment B raw21077step1 raw21077step1Labels = mixedMoment B raw21077step2 raw21077step2Labels := by
      have ha : raw21077step2 = (fun i j => raw21077step1 (permutation29 i) (permutation0 j)) := by apply Matrix.ext; unfold raw21077step2 raw21077step1; decide +kernel
      have hl : raw21077step2Labels = raw21077step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21077step1 raw21077step1Labels permutation29 permutation0
    mixedMoment B raw21077step2 raw21077step2Labels = mixedMoment B raw21077step3 raw21077step3Labels := by
      have ha : raw21077step3 = -raw21077step2 := by apply Matrix.ext; change ∀ i j, raw21077step3 i j = -(raw21077step2 i j); unfold raw21077step3 raw21077step2; decide +kernel
      have hl : raw21077step3Labels = raw21077step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4069 node4069Labels := by rfl

def raw21078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21078Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21078step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21078step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def raw21078step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21078 raw21078Labels = mixedMoment B node1055 node1055Labels := by
  calc
    mixedMoment B raw21078 raw21078Labels = mixedMoment B raw21078step0 raw21078step0Labels := by
      have hz : ∀ j, raw21078 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21078step0 = (fun i j => raw21078 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21078step0 raw21078; decide +kernel
      have hl : raw21078step0Labels = raw21078Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21078 raw21078Labels permutation434 hz
    mixedMoment B raw21078step0 raw21078step0Labels = mixedMoment B raw21078step1 raw21078step1Labels := by
      have hz : ∀ j, raw21078step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21078step1 = (fun i j => raw21078step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21078step1 raw21078step0; decide +kernel
      have hl : raw21078step1Labels = raw21078step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21078step0 raw21078step0Labels permutation80 hz
    _ = mixedMoment B node1055 node1055Labels := by rfl

def raw21079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21079Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21079step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21079step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -2, 1], ![3, -1, -2]]
def raw21079step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21079 raw21079Labels = mixedMoment B node2130 node2130Labels := by
  calc
    mixedMoment B raw21079 raw21079Labels = mixedMoment B raw21079step0 raw21079step0Labels := by
      have hz : ∀ j, raw21079 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21079step0 = (fun i j => raw21079 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21079step0 raw21079; decide +kernel
      have hl : raw21079step0Labels = raw21079Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21079 raw21079Labels permutation434 hz
    mixedMoment B raw21079step0 raw21079step0Labels = mixedMoment B raw21079step1 raw21079step1Labels := by
      have hz : ∀ j, raw21079step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21079step1 = (fun i j => raw21079step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21079step1 raw21079step0; decide +kernel
      have hl : raw21079step1Labels = raw21079step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21079step0 raw21079step0Labels permutation80 hz
    _ = mixedMoment B node2130 node2130Labels := by rfl

def raw21080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21080Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21080step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21080step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21080step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def raw21080step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21080 raw21080Labels = mixedMoment B node2032 node2032Labels := by
  calc
    mixedMoment B raw21080 raw21080Labels = mixedMoment B raw21080step0 raw21080step0Labels := by
      have hz : ∀ j, raw21080 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21080step0 = (fun i j => raw21080 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21080step0 raw21080; decide +kernel
      have hl : raw21080step0Labels = raw21080Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21080 raw21080Labels permutation434 hz
    mixedMoment B raw21080step0 raw21080step0Labels = mixedMoment B raw21080step1 raw21080step1Labels := by
      have ha : raw21080step1 = (fun i j => raw21080step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21080step1 raw21080step0; decide +kernel
      have hl : raw21080step1Labels = raw21080step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21080step0 raw21080step0Labels permutation38 permutation2
    _ = mixedMoment B node2032 node2032Labels := by rfl

def raw21081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21081Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21081step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21081step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21081step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def raw21081step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21081 raw21081Labels = mixedMoment B node2032 node2032Labels := by
  calc
    mixedMoment B raw21081 raw21081Labels = mixedMoment B raw21081step0 raw21081step0Labels := by
      have hz : ∀ j, raw21081 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21081step0 = (fun i j => raw21081 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21081step0 raw21081; decide +kernel
      have hl : raw21081step0Labels = raw21081Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21081 raw21081Labels permutation346 hz
    mixedMoment B raw21081step0 raw21081step0Labels = mixedMoment B raw21081step1 raw21081step1Labels := by
      have ha : raw21081step1 = (fun i j => raw21081step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21081step1 raw21081step0; decide +kernel
      have hl : raw21081step1Labels = raw21081step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21081step0 raw21081step0Labels permutation38 permutation2
    _ = mixedMoment B node2032 node2032Labels := by rfl

def raw21082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw21082Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw21082step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21082step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![3, -1, -2]]
def raw21082step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21082step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw21082step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21082 raw21082Labels = mixedMoment B node2218 node2218Labels := by
  calc
    mixedMoment B raw21082 raw21082Labels = mixedMoment B raw21082step0 raw21082step0Labels := by
      have hz : ∀ j, raw21082 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21082step0 = (fun i j => raw21082 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21082step0 raw21082; decide +kernel
      have hl : raw21082step0Labels = raw21082Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21082 raw21082Labels permutation434 hz
    mixedMoment B raw21082step0 raw21082step0Labels = mixedMoment B raw21082step1 raw21082step1Labels := by
      have hz : ∀ j, raw21082step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21082step1 = (fun i j => raw21082step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21082step1 raw21082step0; decide +kernel
      have hl : raw21082step1Labels = raw21082step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21082step0 raw21082step0Labels permutation80 hz
    mixedMoment B raw21082step1 raw21082step1Labels = mixedMoment B raw21082step2 raw21082step2Labels := by
      have ha : raw21082step2 = (fun i j => raw21082step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21082step2 raw21082step1; decide +kernel
      have hl : raw21082step2Labels = raw21082step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21082step1 raw21082step1Labels permutation10 permutation2
    _ = mixedMoment B node2218 node2218Labels := by rfl

def raw21083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw21083Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw21083step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21083step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw21083step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21083 raw21083Labels = mixedMoment B node2276 node2276Labels := by
  calc
    mixedMoment B raw21083 raw21083Labels = mixedMoment B raw21083step0 raw21083step0Labels := by
      have hz : ∀ j, raw21083 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21083step0 = (fun i j => raw21083 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21083step0 raw21083; decide +kernel
      have hl : raw21083step0Labels = raw21083Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21083 raw21083Labels permutation434 hz
    mixedMoment B raw21083step0 raw21083step0Labels = mixedMoment B raw21083step1 raw21083step1Labels := by
      have hz : ∀ j, raw21083step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21083step1 = (fun i j => raw21083step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21083step1 raw21083step0; decide +kernel
      have hl : raw21083step1Labels = raw21083step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21083step0 raw21083step0Labels permutation80 hz
    _ = mixedMoment B node2276 node2276Labels := by rfl

def raw21084 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![0, 0], ![-1, 1], ![2, -2]]
def raw21084Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21084step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![-1, 1], ![2, -2]]
def raw21084step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21084step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![-1, 1], ![2, -2]]
def raw21084step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21084step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw21084step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical21084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21084 raw21084Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw21084 raw21084Labels = mixedMoment B raw21084step0 raw21084step0Labels := by
      have hz : ∀ j, raw21084 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21084step0 = (fun i j => raw21084 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21084step0 raw21084; decide +kernel
      have hl : raw21084step0Labels = raw21084Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21084 raw21084Labels permutation434 hz
    mixedMoment B raw21084step0 raw21084step0Labels = mixedMoment B raw21084step1 raw21084step1Labels := by
      have hz : ∀ j, raw21084step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21084step1 = (fun i j => raw21084step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21084step1 raw21084step0; decide +kernel
      have hl : raw21084step1Labels = raw21084step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21084step0 raw21084step0Labels permutation80 hz
    mixedMoment B raw21084step1 raw21084step1Labels = mixedMoment B raw21084step2 raw21084step2Labels := by
      have ha : raw21084step2 = (fun i j => raw21084step1 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw21084step2 raw21084step1; decide +kernel
      have hl : raw21084step2Labels = raw21084step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21084step1 raw21084step1Labels permutation10 permutation0
    _ = mixedMoment B node4082 node4082Labels := by rfl

def raw21085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw21085Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw21085step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21085step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![1, -2, 1], ![2, 0, -2]]
def raw21085step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21085step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw21085step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21085 raw21085Labels = mixedMoment B node1075 node1075Labels := by
  calc
    mixedMoment B raw21085 raw21085Labels = mixedMoment B raw21085step0 raw21085step0Labels := by
      have hz : ∀ j, raw21085 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21085step0 = (fun i j => raw21085 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21085step0 raw21085; decide +kernel
      have hl : raw21085step0Labels = raw21085Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21085 raw21085Labels permutation434 hz
    mixedMoment B raw21085step0 raw21085step0Labels = mixedMoment B raw21085step1 raw21085step1Labels := by
      have hz : ∀ j, raw21085step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21085step1 = (fun i j => raw21085step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21085step1 raw21085step0; decide +kernel
      have hl : raw21085step1Labels = raw21085step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21085step0 raw21085step0Labels permutation80 hz
    mixedMoment B raw21085step1 raw21085step1Labels = mixedMoment B raw21085step2 raw21085step2Labels := by
      have ha : raw21085step2 = (fun i j => raw21085step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21085step2 raw21085step1; decide +kernel
      have hl : raw21085step2Labels = raw21085step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21085step1 raw21085step1Labels permutation10 permutation2
    _ = mixedMoment B node1075 node1075Labels := by rfl

def raw21086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw21086Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21086step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw21086step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21086step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw21086step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21086 raw21086Labels = mixedMoment B node1053 node1053Labels := by
  calc
    mixedMoment B raw21086 raw21086Labels = mixedMoment B raw21086step0 raw21086step0Labels := by
      have hz : ∀ j, raw21086 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21086step0 = (fun i j => raw21086 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21086step0 raw21086; decide +kernel
      have hl : raw21086step0Labels = raw21086Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21086 raw21086Labels permutation434 hz
    mixedMoment B raw21086step0 raw21086step0Labels = mixedMoment B raw21086step1 raw21086step1Labels := by
      have ha : raw21086step1 = (fun i j => raw21086step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21086step1 raw21086step0; decide +kernel
      have hl : raw21086step1Labels = raw21086step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21086step0 raw21086step0Labels permutation34 permutation2
    _ = mixedMoment B node1053 node1053Labels := by rfl

def raw21087 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw21087Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw21087step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21087step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw21087step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21087 raw21087Labels = mixedMoment B node1053 node1053Labels := by
  calc
    mixedMoment B raw21087 raw21087Labels = mixedMoment B raw21087step0 raw21087step0Labels := by
      have hz : ∀ j, raw21087 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21087step0 = (fun i j => raw21087 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21087step0 raw21087; decide +kernel
      have hl : raw21087step0Labels = raw21087Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21087 raw21087Labels permutation346 hz
    mixedMoment B raw21087step0 raw21087step0Labels = mixedMoment B raw21087step1 raw21087step1Labels := by
      have ha : raw21087step1 = (fun i j => raw21087step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21087step1 raw21087step0; decide +kernel
      have hl : raw21087step1Labels = raw21087step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21087step0 raw21087step0Labels permutation34 permutation2
    _ = mixedMoment B node1053 node1053Labels := by rfl

def raw21088 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw21088Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw21088step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21088step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw21088step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21088 raw21088Labels = mixedMoment B node1062 node1062Labels := by
  calc
    mixedMoment B raw21088 raw21088Labels = mixedMoment B raw21088step0 raw21088step0Labels := by
      have hz : ∀ j, raw21088 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21088step0 = (fun i j => raw21088 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21088step0 raw21088; decide +kernel
      have hl : raw21088step0Labels = raw21088Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21088 raw21088Labels permutation434 hz
    mixedMoment B raw21088step0 raw21088step0Labels = mixedMoment B raw21088step1 raw21088step1Labels := by
      have hz : ∀ j, raw21088step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21088step1 = (fun i j => raw21088step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21088step1 raw21088step0; decide +kernel
      have hl : raw21088step1Labels = raw21088step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21088step0 raw21088step0Labels permutation80 hz
    _ = mixedMoment B node1062 node1062Labels := by rfl

def raw21089 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw21089Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw21089step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21089step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw21089step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21089 raw21089Labels = mixedMoment B node991 node991Labels := by
  calc
    mixedMoment B raw21089 raw21089Labels = mixedMoment B raw21089step0 raw21089step0Labels := by
      have hz : ∀ j, raw21089 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21089step0 = (fun i j => raw21089 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21089step0 raw21089; decide +kernel
      have hl : raw21089step0Labels = raw21089Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21089 raw21089Labels permutation346 hz
    mixedMoment B raw21089step0 raw21089step0Labels = mixedMoment B raw21089step1 raw21089step1Labels := by
      have ha : raw21089step1 = (fun i j => raw21089step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21089step1 raw21089step0; decide +kernel
      have hl : raw21089step1Labels = raw21089step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21089step0 raw21089step0Labels permutation38 permutation2
    _ = mixedMoment B node991 node991Labels := by rfl

def raw21090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw21090Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw21090step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21090 raw21090Labels = mixedMoment B node2121 node2121Labels := by
  calc
    mixedMoment B raw21090 raw21090Labels = mixedMoment B raw21090step0 raw21090step0Labels := by
      have hz : ∀ j, raw21090 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21090step0 = (fun i j => raw21090 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21090step0 raw21090; decide +kernel
      have hl : raw21090step0Labels = raw21090Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21090 raw21090Labels permutation346 hz
    _ = mixedMoment B node2121 node2121Labels := by rfl

def raw21091 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw21091Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21091step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw21091step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21091 raw21091Labels = mixedMoment B node1992 node1992Labels := by
  calc
    mixedMoment B raw21091 raw21091Labels = mixedMoment B raw21091step0 raw21091step0Labels := by
      have ha : raw21091step0 = (fun i j => raw21091 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21091step0 raw21091; decide +kernel
      have hl : raw21091step0Labels = raw21091Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21091 raw21091Labels permutation182 permutation2
    _ = mixedMoment B node1992 node1992Labels := by rfl

def raw21092 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw21092Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw21092step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21092step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw21092step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21092 raw21092Labels = mixedMoment B node1926 node1926Labels := by
  calc
    mixedMoment B raw21092 raw21092Labels = mixedMoment B raw21092step0 raw21092step0Labels := by
      have hz : ∀ j, raw21092 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21092step0 = (fun i j => raw21092 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21092step0 raw21092; decide +kernel
      have hl : raw21092step0Labels = raw21092Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21092 raw21092Labels permutation346 hz
    mixedMoment B raw21092step0 raw21092step0Labels = mixedMoment B raw21092step1 raw21092step1Labels := by
      have ha : raw21092step1 = (fun i j => raw21092step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21092step1 raw21092step0; decide +kernel
      have hl : raw21092step1Labels = raw21092step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21092step0 raw21092step0Labels permutation38 permutation2
    _ = mixedMoment B node1926 node1926Labels := by rfl

def raw21093 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw21093Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw21093step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21093step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw21093step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21093 raw21093Labels = mixedMoment B node2197 node2197Labels := by
  calc
    mixedMoment B raw21093 raw21093Labels = mixedMoment B raw21093step0 raw21093step0Labels := by
      have hz : ∀ j, raw21093 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21093step0 = (fun i j => raw21093 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21093step0 raw21093; decide +kernel
      have hl : raw21093step0Labels = raw21093Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21093 raw21093Labels permutation346 hz
    mixedMoment B raw21093step0 raw21093step0Labels = mixedMoment B raw21093step1 raw21093step1Labels := by
      have ha : raw21093step1 = (fun i j => raw21093step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21093step1 raw21093step0; decide +kernel
      have hl : raw21093step1Labels = raw21093step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21093step0 raw21093step0Labels permutation40 permutation2
    _ = mixedMoment B node2197 node2197Labels := by rfl

def raw21094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw21094Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21094step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw21094step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21094step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw21094step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21094 raw21094Labels = mixedMoment B node2216 node2216Labels := by
  calc
    mixedMoment B raw21094 raw21094Labels = mixedMoment B raw21094step0 raw21094step0Labels := by
      have hz : ∀ j, raw21094 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21094step0 = (fun i j => raw21094 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21094step0 raw21094; decide +kernel
      have hl : raw21094step0Labels = raw21094Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21094 raw21094Labels permutation346 hz
    mixedMoment B raw21094step0 raw21094step0Labels = mixedMoment B raw21094step1 raw21094step1Labels := by
      have ha : raw21094step1 = (fun i j => raw21094step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21094step1 raw21094step0; decide +kernel
      have hl : raw21094step1Labels = raw21094step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21094step0 raw21094step0Labels permutation38 permutation2
    _ = mixedMoment B node2216 node2216Labels := by rfl

def raw21095 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![-1, 1], ![1, -1], ![1, -1]]
def raw21095Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21095step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![-1, 1], ![1, -1], ![1, -1]]
def raw21095step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21095step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw21095step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical21095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21095 raw21095Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw21095 raw21095Labels = mixedMoment B raw21095step0 raw21095step0Labels := by
      have hz : ∀ j, raw21095 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21095step0 = (fun i j => raw21095 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21095step0 raw21095; decide +kernel
      have hl : raw21095step0Labels = raw21095Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21095 raw21095Labels permutation346 hz
    mixedMoment B raw21095step0 raw21095step0Labels = mixedMoment B raw21095step1 raw21095step1Labels := by
      have ha : raw21095step1 = (fun i j => raw21095step0 (permutation41 i) (permutation0 j)) := by apply Matrix.ext; unfold raw21095step1 raw21095step0; decide +kernel
      have hl : raw21095step1Labels = raw21095step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21095step0 raw21095step0Labels permutation41 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw21096 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw21096Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw21096step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21096step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw21096step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21096 raw21096Labels = mixedMoment B node1005 node1005Labels := by
  calc
    mixedMoment B raw21096 raw21096Labels = mixedMoment B raw21096step0 raw21096step0Labels := by
      have hz : ∀ j, raw21096 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21096step0 = (fun i j => raw21096 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21096step0 raw21096; decide +kernel
      have hl : raw21096step0Labels = raw21096Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21096 raw21096Labels permutation346 hz
    mixedMoment B raw21096step0 raw21096step0Labels = mixedMoment B raw21096step1 raw21096step1Labels := by
      have ha : raw21096step1 = (fun i j => raw21096step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21096step1 raw21096step0; decide +kernel
      have hl : raw21096step1Labels = raw21096step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21096step0 raw21096step0Labels permutation40 permutation2
    _ = mixedMoment B node1005 node1005Labels := by rfl

def raw21097 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw21097Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21097step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw21097step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21097 raw21097Labels = mixedMoment B node988 node988Labels := by
  calc
    mixedMoment B raw21097 raw21097Labels = mixedMoment B raw21097step0 raw21097step0Labels := by
      have ha : raw21097step0 = (fun i j => raw21097 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21097step0 raw21097; decide +kernel
      have hl : raw21097step0Labels = raw21097Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21097 raw21097Labels permutation200 permutation2
    _ = mixedMoment B node988 node988Labels := by rfl

def raw21098 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw21098Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21098step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw21098step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21098 raw21098Labels = mixedMoment B node1054 node1054Labels := by
  calc
    mixedMoment B raw21098 raw21098Labels = mixedMoment B raw21098step0 raw21098step0Labels := by
      have hz : ∀ j, raw21098 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21098step0 = (fun i j => raw21098 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21098step0 raw21098; decide +kernel
      have hl : raw21098step0Labels = raw21098Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21098 raw21098Labels permutation346 hz
    _ = mixedMoment B node1054 node1054Labels := by rfl

def raw21099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw21099Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw21099step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21099step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw21099step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21099 raw21099Labels = mixedMoment B node993 node993Labels := by
  calc
    mixedMoment B raw21099 raw21099Labels = mixedMoment B raw21099step0 raw21099step0Labels := by
      have hz : ∀ j, raw21099 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21099step0 = (fun i j => raw21099 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21099step0 raw21099; decide +kernel
      have hl : raw21099step0Labels = raw21099Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21099 raw21099Labels permutation346 hz
    mixedMoment B raw21099step0 raw21099step0Labels = mixedMoment B raw21099step1 raw21099step1Labels := by
      have ha : raw21099step1 = (fun i j => raw21099step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21099step1 raw21099step0; decide +kernel
      have hl : raw21099step1Labels = raw21099step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21099step0 raw21099step0Labels permutation38 permutation2
    _ = mixedMoment B node993 node993Labels := by rfl

def raw21100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw21100Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw21100step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21100step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw21100step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21100 raw21100Labels = mixedMoment B node989 node989Labels := by
  calc
    mixedMoment B raw21100 raw21100Labels = mixedMoment B raw21100step0 raw21100step0Labels := by
      have hz : ∀ j, raw21100 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21100step0 = (fun i j => raw21100 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21100step0 raw21100; decide +kernel
      have hl : raw21100step0Labels = raw21100Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21100 raw21100Labels permutation346 hz
    mixedMoment B raw21100step0 raw21100step0Labels = mixedMoment B raw21100step1 raw21100step1Labels := by
      have ha : raw21100step1 = (fun i j => raw21100step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21100step1 raw21100step0; decide +kernel
      have hl : raw21100step1Labels = raw21100step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21100step0 raw21100step0Labels permutation38 permutation2
    _ = mixedMoment B node989 node989Labels := by rfl

def raw21101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw21101Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw21101step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21101 raw21101Labels = mixedMoment B node2119 node2119Labels := by
  calc
    mixedMoment B raw21101 raw21101Labels = mixedMoment B raw21101step0 raw21101step0Labels := by
      have hz : ∀ j, raw21101 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21101step0 = (fun i j => raw21101 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21101step0 raw21101; decide +kernel
      have hl : raw21101step0Labels = raw21101Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21101 raw21101Labels permutation346 hz
    _ = mixedMoment B node2119 node2119Labels := by rfl

def raw21102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw21102Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21102step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw21102step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21102 raw21102Labels = mixedMoment B node1991 node1991Labels := by
  calc
    mixedMoment B raw21102 raw21102Labels = mixedMoment B raw21102step0 raw21102step0Labels := by
      have ha : raw21102step0 = (fun i j => raw21102 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21102step0 raw21102; decide +kernel
      have hl : raw21102step0Labels = raw21102Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21102 raw21102Labels permutation182 permutation2
    _ = mixedMoment B node1991 node1991Labels := by rfl

def raw21103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw21103Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw21103step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21103step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw21103step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21103 raw21103Labels = mixedMoment B node1924 node1924Labels := by
  calc
    mixedMoment B raw21103 raw21103Labels = mixedMoment B raw21103step0 raw21103step0Labels := by
      have hz : ∀ j, raw21103 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21103step0 = (fun i j => raw21103 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21103step0 raw21103; decide +kernel
      have hl : raw21103step0Labels = raw21103Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21103 raw21103Labels permutation346 hz
    mixedMoment B raw21103step0 raw21103step0Labels = mixedMoment B raw21103step1 raw21103step1Labels := by
      have ha : raw21103step1 = (fun i j => raw21103step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21103step1 raw21103step0; decide +kernel
      have hl : raw21103step1Labels = raw21103step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21103step0 raw21103step0Labels permutation38 permutation2
    _ = mixedMoment B node1924 node1924Labels := by rfl

def raw21104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, -1, -2]]
def raw21104Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21104step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw21104step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21104step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![3, -1, -2]]
def raw21104step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21104step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw21104step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21104 raw21104Labels = mixedMoment B node2218 node2218Labels := by
  calc
    mixedMoment B raw21104 raw21104Labels = mixedMoment B raw21104step0 raw21104step0Labels := by
      have hz : ∀ j, raw21104 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21104step0 = (fun i j => raw21104 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21104step0 raw21104; decide +kernel
      have hl : raw21104step0Labels = raw21104Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21104 raw21104Labels permutation520 hz
    mixedMoment B raw21104step0 raw21104step0Labels = mixedMoment B raw21104step1 raw21104step1Labels := by
      have hz : ∀ j, raw21104step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21104step1 = (fun i j => raw21104step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21104step1 raw21104step0; decide +kernel
      have hl : raw21104step1Labels = raw21104step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21104step0 raw21104step0Labels permutation80 hz
    mixedMoment B raw21104step1 raw21104step1Labels = mixedMoment B raw21104step2 raw21104step2Labels := by
      have ha : raw21104step2 = (fun i j => raw21104step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21104step2 raw21104step1; decide +kernel
      have hl : raw21104step2Labels = raw21104step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21104step1 raw21104step1Labels permutation10 permutation2
    _ = mixedMoment B node2218 node2218Labels := by rfl

def raw21105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw21105Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21105step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw21105step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21105step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw21105step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21105 raw21105Labels = mixedMoment B node2215 node2215Labels := by
  calc
    mixedMoment B raw21105 raw21105Labels = mixedMoment B raw21105step0 raw21105step0Labels := by
      have hz : ∀ j, raw21105 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21105step0 = (fun i j => raw21105 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21105step0 raw21105; decide +kernel
      have hl : raw21105step0Labels = raw21105Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21105 raw21105Labels permutation346 hz
    mixedMoment B raw21105step0 raw21105step0Labels = mixedMoment B raw21105step1 raw21105step1Labels := by
      have ha : raw21105step1 = (fun i j => raw21105step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21105step1 raw21105step0; decide +kernel
      have hl : raw21105step1Labels = raw21105step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21105step0 raw21105step0Labels permutation38 permutation2
    _ = mixedMoment B node2215 node2215Labels := by rfl

def raw21106 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![-1, 1], ![0, 0], ![2, -2]]
def raw21106Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21106step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![0, 0], ![-1, 1], ![2, -2]]
def raw21106step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21106step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![-1, 1], ![2, -2]]
def raw21106step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21106step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw21106step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical21106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21106 raw21106Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw21106 raw21106Labels = mixedMoment B raw21106step0 raw21106step0Labels := by
      have hz : ∀ j, raw21106 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw21106step0 = (fun i j => raw21106 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw21106step0 raw21106; decide +kernel
      have hl : raw21106step0Labels = raw21106Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21106 raw21106Labels permutation520 hz
    mixedMoment B raw21106step0 raw21106step0Labels = mixedMoment B raw21106step1 raw21106step1Labels := by
      have hz : ∀ j, raw21106step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21106step1 = (fun i j => raw21106step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21106step1 raw21106step0; decide +kernel
      have hl : raw21106step1Labels = raw21106step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21106step0 raw21106step0Labels permutation80 hz
    mixedMoment B raw21106step1 raw21106step1Labels = mixedMoment B raw21106step2 raw21106step2Labels := by
      have ha : raw21106step2 = (fun i j => raw21106step1 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw21106step2 raw21106step1; decide +kernel
      have hl : raw21106step2Labels = raw21106step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21106step1 raw21106step1Labels permutation10 permutation0
    _ = mixedMoment B node4082 node4082Labels := by rfl

def raw21107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw21107Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw21107step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21107step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw21107step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21107 raw21107Labels = mixedMoment B node1000 node1000Labels := by
  calc
    mixedMoment B raw21107 raw21107Labels = mixedMoment B raw21107step0 raw21107step0Labels := by
      have hz : ∀ j, raw21107 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21107step0 = (fun i j => raw21107 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21107step0 raw21107; decide +kernel
      have hl : raw21107step0Labels = raw21107Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21107 raw21107Labels permutation346 hz
    mixedMoment B raw21107step0 raw21107step0Labels = mixedMoment B raw21107step1 raw21107step1Labels := by
      have ha : raw21107step1 = (fun i j => raw21107step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21107step1 raw21107step0; decide +kernel
      have hl : raw21107step1Labels = raw21107step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21107step0 raw21107step0Labels permutation40 permutation2
    _ = mixedMoment B node1000 node1000Labels := by rfl

def raw21108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw21108Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21108step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw21108step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21108 raw21108Labels = mixedMoment B node987 node987Labels := by
  calc
    mixedMoment B raw21108 raw21108Labels = mixedMoment B raw21108step0 raw21108step0Labels := by
      have ha : raw21108step0 = (fun i j => raw21108 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21108step0 raw21108; decide +kernel
      have hl : raw21108step0Labels = raw21108Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21108 raw21108Labels permutation200 permutation2
    _ = mixedMoment B node987 node987Labels := by rfl

def raw21109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw21109Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21109step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw21109step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21109 raw21109Labels = mixedMoment B node1053 node1053Labels := by
  calc
    mixedMoment B raw21109 raw21109Labels = mixedMoment B raw21109step0 raw21109step0Labels := by
      have hz : ∀ j, raw21109 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21109step0 = (fun i j => raw21109 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21109step0 raw21109; decide +kernel
      have hl : raw21109step0Labels = raw21109Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21109 raw21109Labels permutation346 hz
    _ = mixedMoment B node1053 node1053Labels := by rfl

def raw21110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw21110Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21110step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw21110step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21110step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw21110step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21110 raw21110Labels = mixedMoment B node992 node992Labels := by
  calc
    mixedMoment B raw21110 raw21110Labels = mixedMoment B raw21110step0 raw21110step0Labels := by
      have hz : ∀ j, raw21110 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21110step0 = (fun i j => raw21110 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21110step0 raw21110; decide +kernel
      have hl : raw21110step0Labels = raw21110Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21110 raw21110Labels permutation346 hz
    mixedMoment B raw21110step0 raw21110step0Labels = mixedMoment B raw21110step1 raw21110step1Labels := by
      have ha : raw21110step1 = (fun i j => raw21110step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21110step1 raw21110step0; decide +kernel
      have hl : raw21110step1Labels = raw21110step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21110step0 raw21110step0Labels permutation38 permutation2
    _ = mixedMoment B node992 node992Labels := by rfl

def raw21111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21111Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21111step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw21111step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21111 raw21111Labels = mixedMoment B node1019 node1019Labels := by
  calc
    mixedMoment B raw21111 raw21111Labels = mixedMoment B raw21111step0 raw21111step0Labels := by
      have hz : ∀ j, raw21111 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21111step0 = (fun i j => raw21111 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21111step0 raw21111; decide +kernel
      have hl : raw21111step0Labels = raw21111Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21111 raw21111Labels permutation434 hz
    _ = mixedMoment B node1019 node1019Labels := by rfl

def raw21112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21112Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw21112step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21112 raw21112Labels = mixedMoment B node2087 node2087Labels := by
  calc
    mixedMoment B raw21112 raw21112Labels = mixedMoment B raw21112step0 raw21112step0Labels := by
      have hz : ∀ j, raw21112 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21112step0 = (fun i j => raw21112 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21112step0 raw21112; decide +kernel
      have hl : raw21112step0Labels = raw21112Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21112 raw21112Labels permutation434 hz
    _ = mixedMoment B node2087 node2087Labels := by rfl

def raw21113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21113Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![3, -1, -2]]
def raw21113step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21113step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw21113step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21113 raw21113Labels = mixedMoment B node2087 node2087Labels := by
  calc
    mixedMoment B raw21113 raw21113Labels = mixedMoment B raw21113step0 raw21113step0Labels := by
      have hz : ∀ j, raw21113 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21113step0 = (fun i j => raw21113 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21113step0 raw21113; decide +kernel
      have hl : raw21113step0Labels = raw21113Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21113 raw21113Labels permutation434 hz
    mixedMoment B raw21113step0 raw21113step0Labels = mixedMoment B raw21113step1 raw21113step1Labels := by
      have ha : raw21113step1 = (fun i j => raw21113step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21113step1 raw21113step0; decide +kernel
      have hl : raw21113step1Labels = raw21113step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21113step0 raw21113step0Labels permutation38 permutation2
    _ = mixedMoment B node2087 node2087Labels := by rfl

def raw21114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw21114Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21114step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw21114step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21114 raw21114Labels = mixedMoment B node2008 node2008Labels := by
  calc
    mixedMoment B raw21114 raw21114Labels = mixedMoment B raw21114step0 raw21114step0Labels := by
      have ha : raw21114step0 = (fun i j => raw21114 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21114step0 raw21114; decide +kernel
      have hl : raw21114step0Labels = raw21114Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21114 raw21114Labels permutation200 permutation2
    _ = mixedMoment B node2008 node2008Labels := by rfl

def raw21115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw21115Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![3, -1, -2]]
def raw21115step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21115step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw21115step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21115 raw21115Labels = mixedMoment B node2193 node2193Labels := by
  calc
    mixedMoment B raw21115 raw21115Labels = mixedMoment B raw21115step0 raw21115step0Labels := by
      have hz : ∀ j, raw21115 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21115step0 = (fun i j => raw21115 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21115step0 raw21115; decide +kernel
      have hl : raw21115step0Labels = raw21115Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21115 raw21115Labels permutation434 hz
    mixedMoment B raw21115step0 raw21115step0Labels = mixedMoment B raw21115step1 raw21115step1Labels := by
      have ha : raw21115step1 = (fun i j => raw21115step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21115step1 raw21115step0; decide +kernel
      have hl : raw21115step1Labels = raw21115step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21115step0 raw21115step0Labels permutation44 permutation2
    _ = mixedMoment B node2193 node2193Labels := by rfl

def raw21116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw21116Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw21116step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21116 raw21116Labels = mixedMoment B node2242 node2242Labels := by
  calc
    mixedMoment B raw21116 raw21116Labels = mixedMoment B raw21116step0 raw21116step0Labels := by
      have hz : ∀ j, raw21116 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21116step0 = (fun i j => raw21116 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21116step0 raw21116; decide +kernel
      have hl : raw21116step0Labels = raw21116Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21116 raw21116Labels permutation434 hz
    _ = mixedMoment B node2242 node2242Labels := by rfl

def raw21117 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![0, 0], ![-1, 1], ![2, -2]]
def raw21117Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21117step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![-1, 1], ![2, -2]]
def raw21117step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21117step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw21117step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical21117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21117 raw21117Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw21117 raw21117Labels = mixedMoment B raw21117step0 raw21117step0Labels := by
      have hz : ∀ j, raw21117 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21117step0 = (fun i j => raw21117 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21117step0 raw21117; decide +kernel
      have hl : raw21117step0Labels = raw21117Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21117 raw21117Labels permutation434 hz
    mixedMoment B raw21117step0 raw21117step0Labels = mixedMoment B raw21117step1 raw21117step1Labels := by
      have ha : raw21117step1 = (fun i j => raw21117step0 (permutation44 i) (permutation0 j)) := by apply Matrix.ext; unfold raw21117step1 raw21117step0; decide +kernel
      have hl : raw21117step1Labels = raw21117step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21117step0 raw21117step0Labels permutation44 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw21118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw21118Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw21118step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21118step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw21118step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21118 raw21118Labels = mixedMoment B node1035 node1035Labels := by
  calc
    mixedMoment B raw21118 raw21118Labels = mixedMoment B raw21118step0 raw21118step0Labels := by
      have hz : ∀ j, raw21118 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21118step0 = (fun i j => raw21118 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21118step0 raw21118; decide +kernel
      have hl : raw21118step0Labels = raw21118Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21118 raw21118Labels permutation434 hz
    mixedMoment B raw21118step0 raw21118step0Labels = mixedMoment B raw21118step1 raw21118step1Labels := by
      have ha : raw21118step1 = (fun i j => raw21118step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21118step1 raw21118step0; decide +kernel
      have hl : raw21118step1Labels = raw21118step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21118step0 raw21118step0Labels permutation40 permutation2
    _ = mixedMoment B node1035 node1035Labels := by rfl

def raw21119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw21119Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw21119step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21119step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw21119step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21119 raw21119Labels = mixedMoment B node1035 node1035Labels := by
  calc
    mixedMoment B raw21119 raw21119Labels = mixedMoment B raw21119step0 raw21119step0Labels := by
      have hz : ∀ j, raw21119 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21119step0 = (fun i j => raw21119 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21119step0 raw21119; decide +kernel
      have hl : raw21119step0Labels = raw21119Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21119 raw21119Labels permutation434 hz
    mixedMoment B raw21119step0 raw21119step0Labels = mixedMoment B raw21119step1 raw21119step1Labels := by
      have ha : raw21119step1 = (fun i j => raw21119step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21119step1 raw21119step0; decide +kernel
      have hl : raw21119step1Labels = raw21119step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21119step0 raw21119step0Labels permutation34 permutation2
    _ = mixedMoment B node1035 node1035Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
