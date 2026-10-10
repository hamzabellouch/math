import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw5888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw5888Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![2, 1, -3], ![1, -1, 0]]
def raw5888step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5888step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![2, 1, -3], ![1, -1, 0]]
def raw5888step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5888step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw5888step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5888 raw5888Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw5888 raw5888Labels = mixedMoment B raw5888step0 raw5888step0Labels := by
      have hz : ∀ j, raw5888 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5888step0 = (fun i j => raw5888 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5888step0 raw5888; decide +kernel
      have hl : raw5888step0Labels = raw5888Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5888 raw5888Labels permutation434 hz
    mixedMoment B raw5888step0 raw5888step0Labels = mixedMoment B raw5888step1 raw5888step1Labels := by
      have hz : ∀ j, raw5888step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5888step1 = (fun i j => raw5888step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5888step1 raw5888step0; decide +kernel
      have hl : raw5888step1Labels = raw5888step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5888step0 raw5888step0Labels permutation80 hz
    mixedMoment B raw5888step1 raw5888step1Labels = mixedMoment B raw5888step2 raw5888step2Labels := by
      have ha : raw5888step2 = (fun i j => raw5888step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5888step2 raw5888step1; decide +kernel
      have hl : raw5888step2Labels = raw5888step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5888step1 raw5888step1Labels permutation9 permutation2
    _ = mixedMoment B node2740 node2740Labels := by rfl

def raw5889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 3, -3], ![2, -2, 0]]
def raw5889Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![0, 3, -3], ![2, -2, 0]]
def raw5889step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5889step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw5889step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5889step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5889step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5889 raw5889Labels = mixedMoment B node2133 node2133Labels := by
  calc
    mixedMoment B raw5889 raw5889Labels = mixedMoment B raw5889step0 raw5889step0Labels := by
      have hz : ∀ j, raw5889 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5889step0 = (fun i j => raw5889 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5889step0 raw5889; decide +kernel
      have hl : raw5889step0Labels = raw5889Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5889 raw5889Labels permutation346 hz
    mixedMoment B raw5889step0 raw5889step0Labels = mixedMoment B raw5889step1 raw5889step1Labels := by
      have ha : raw5889step1 = (fun i j => raw5889step0 (permutation106 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5889step1 raw5889step0; decide +kernel
      have hl : raw5889step1Labels = raw5889step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5889step0 raw5889step0Labels permutation106 permutation4
    mixedMoment B raw5889step1 raw5889step1Labels = mixedMoment B raw5889step2 raw5889step2Labels := by
      have ha : raw5889step2 = -raw5889step1 := by apply Matrix.ext; change ∀ i j, raw5889step2 i j = -(raw5889step1 i j); unfold raw5889step2 raw5889step1; decide +kernel
      have hl : raw5889step2Labels = raw5889step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2133 node2133Labels := by rfl

def raw5890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![3, -3, 0]]
def raw5890Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5890step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![0, 3, -3], ![3, -3, 0]]
def raw5890step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5890step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 3, -3], ![3, -3, 0]]
def raw5890step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5890step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw5890step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5890step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, 0, -1], ![3, -3, 0]]
def raw5890step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5890 raw5890Labels = mixedMoment B node2136 node2136Labels := by
  calc
    mixedMoment B raw5890 raw5890Labels = mixedMoment B raw5890step0 raw5890step0Labels := by
      have hz : ∀ j, raw5890 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5890step0 = (fun i j => raw5890 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5890step0 raw5890; decide +kernel
      have hl : raw5890step0Labels = raw5890Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5890 raw5890Labels permutation434 hz
    mixedMoment B raw5890step0 raw5890step0Labels = mixedMoment B raw5890step1 raw5890step1Labels := by
      have hz : ∀ j, raw5890step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5890step1 = (fun i j => raw5890step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5890step1 raw5890step0; decide +kernel
      have hl : raw5890step1Labels = raw5890step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5890step0 raw5890step0Labels permutation80 hz
    mixedMoment B raw5890step1 raw5890step1Labels = mixedMoment B raw5890step2 raw5890step2Labels := by
      have ha : raw5890step2 = (fun i j => raw5890step1 (permutation20 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5890step2 raw5890step1; decide +kernel
      have hl : raw5890step2Labels = raw5890step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5890step1 raw5890step1Labels permutation20 permutation4
    mixedMoment B raw5890step2 raw5890step2Labels = mixedMoment B raw5890step3 raw5890step3Labels := by
      have ha : raw5890step3 = -raw5890step2 := by apply Matrix.ext; change ∀ i j, raw5890step3 i j = -(raw5890step2 i j); unfold raw5890step3 raw5890step2; decide +kernel
      have hl : raw5890step3Labels = raw5890step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2136 node2136Labels := by rfl

def raw5891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5891Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw5891step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5891step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![3, -3, 0]]
def raw5891step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5891 raw5891Labels = mixedMoment B node2559 node2559Labels := by
  calc
    mixedMoment B raw5891 raw5891Labels = mixedMoment B raw5891step0 raw5891step0Labels := by
      have hz : ∀ j, raw5891 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5891step0 = (fun i j => raw5891 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5891step0 raw5891; decide +kernel
      have hl : raw5891step0Labels = raw5891Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5891 raw5891Labels permutation346 hz
    mixedMoment B raw5891step0 raw5891step0Labels = mixedMoment B raw5891step1 raw5891step1Labels := by
      have ha : raw5891step1 = (fun i j => raw5891step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5891step1 raw5891step0; decide +kernel
      have hl : raw5891step1Labels = raw5891step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5891step0 raw5891step0Labels permutation38 permutation2
    _ = mixedMoment B node2559 node2559Labels := by rfl

def raw5892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5892Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5892step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5892step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -3, 2], ![2, 0, -2]]
def raw5892step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5892step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw5892step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5892step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw5892step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5892 raw5892Labels = mixedMoment B node5300 node5300Labels := by
  calc
    mixedMoment B raw5892 raw5892Labels = mixedMoment B raw5892step0 raw5892step0Labels := by
      have hz : ∀ j, raw5892 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5892step0 = (fun i j => raw5892 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5892step0 raw5892; decide +kernel
      have hl : raw5892step0Labels = raw5892Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5892 raw5892Labels permutation434 hz
    mixedMoment B raw5892step0 raw5892step0Labels = mixedMoment B raw5892step1 raw5892step1Labels := by
      have hz : ∀ j, raw5892step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5892step1 = (fun i j => raw5892step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5892step1 raw5892step0; decide +kernel
      have hl : raw5892step1Labels = raw5892step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5892step0 raw5892step0Labels permutation80 hz
    mixedMoment B raw5892step1 raw5892step1Labels = mixedMoment B raw5892step2 raw5892step2Labels := by
      have ha : raw5892step2 = (fun i j => raw5892step1 (permutation24 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5892step2 raw5892step1; decide +kernel
      have hl : raw5892step2Labels = raw5892step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5892step1 raw5892step1Labels permutation24 permutation4
    mixedMoment B raw5892step2 raw5892step2Labels = mixedMoment B raw5892step3 raw5892step3Labels := by
      have ha : raw5892step3 = raw5892step2 := by apply Matrix.ext; unfold raw5892step3 raw5892step2; decide +kernel
      have hl : raw5892step2Labels = labelEmbedding7 ∘ raw5892step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5892step2 raw5892step2Labels raw5892step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5300 node5300Labels := by rfl

def raw5893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5893Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5893step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5893step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw5893step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5893step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw5893step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5893 raw5893Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw5893 raw5893Labels = mixedMoment B raw5893step0 raw5893step0Labels := by
      have hz : ∀ j, raw5893 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5893step0 = (fun i j => raw5893 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5893step0 raw5893; decide +kernel
      have hl : raw5893step0Labels = raw5893Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5893 raw5893Labels permutation434 hz
    mixedMoment B raw5893step0 raw5893step0Labels = mixedMoment B raw5893step1 raw5893step1Labels := by
      have ha : raw5893step1 = (fun i j => raw5893step0 (permutation123 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5893step1 raw5893step0; decide +kernel
      have hl : raw5893step1Labels = raw5893step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5893step0 raw5893step0Labels permutation123 permutation4
    mixedMoment B raw5893step1 raw5893step1Labels = mixedMoment B raw5893step2 raw5893step2Labels := by
      have ha : raw5893step2 = raw5893step1 := by apply Matrix.ext; unfold raw5893step2 raw5893step1; decide +kernel
      have hl : raw5893step1Labels = labelEmbedding7 ∘ raw5893step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5893step1 raw5893step1Labels raw5893step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw5894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5894Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5894step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5894step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw5894step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5894step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw5894step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5894 raw5894Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw5894 raw5894Labels = mixedMoment B raw5894step0 raw5894step0Labels := by
      have hz : ∀ j, raw5894 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5894step0 = (fun i j => raw5894 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5894step0 raw5894; decide +kernel
      have hl : raw5894step0Labels = raw5894Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5894 raw5894Labels permutation346 hz
    mixedMoment B raw5894step0 raw5894step0Labels = mixedMoment B raw5894step1 raw5894step1Labels := by
      have ha : raw5894step1 = (fun i j => raw5894step0 (permutation123 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5894step1 raw5894step0; decide +kernel
      have hl : raw5894step1Labels = raw5894step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5894step0 raw5894step0Labels permutation123 permutation4
    mixedMoment B raw5894step1 raw5894step1Labels = mixedMoment B raw5894step2 raw5894step2Labels := by
      have ha : raw5894step2 = raw5894step1 := by apply Matrix.ext; unfold raw5894step2 raw5894step1; decide +kernel
      have hl : raw5894step1Labels = labelEmbedding7 ∘ raw5894step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5894step1 raw5894step1Labels raw5894step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw5895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw5895Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw5895step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5895step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2]]
def raw5895step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5895step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5895step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw5895step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5895step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5895 raw5895Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw5895 raw5895Labels = mixedMoment B raw5895step0 raw5895step0Labels := by
      have hz : ∀ j, raw5895 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5895step0 = (fun i j => raw5895 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5895step0 raw5895; decide +kernel
      have hl : raw5895step0Labels = raw5895Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5895 raw5895Labels permutation434 hz
    mixedMoment B raw5895step0 raw5895step0Labels = mixedMoment B raw5895step1 raw5895step1Labels := by
      have hz : ∀ j, raw5895step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5895step1 = (fun i j => raw5895step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5895step1 raw5895step0; decide +kernel
      have hl : raw5895step1Labels = raw5895step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5895step0 raw5895step0Labels permutation80 hz
    mixedMoment B raw5895step1 raw5895step1Labels = mixedMoment B raw5895step2 raw5895step2Labels := by
      have ha : raw5895step2 = (fun i j => raw5895step1 (permutation28 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5895step2 raw5895step1; decide +kernel
      have hl : raw5895step2Labels = raw5895step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5895step1 raw5895step1Labels permutation28 permutation7
    mixedMoment B raw5895step2 raw5895step2Labels = mixedMoment B raw5895step3 raw5895step3Labels := by
      have ha : raw5895step3 = raw5895step2 := by apply Matrix.ext; unfold raw5895step3 raw5895step2; decide +kernel
      have hl : raw5895step2Labels = labelEmbedding10 ∘ raw5895step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5895step2 raw5895step2Labels raw5895step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw5896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2]]
def raw5896Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2]]
def raw5896step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5896step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2]]
def raw5896step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5896step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw5896step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5896step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw5896step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5896 raw5896Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw5896 raw5896Labels = mixedMoment B raw5896step0 raw5896step0Labels := by
      have hz : ∀ j, raw5896 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5896step0 = (fun i j => raw5896 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5896step0 raw5896; decide +kernel
      have hl : raw5896step0Labels = raw5896Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5896 raw5896Labels permutation434 hz
    mixedMoment B raw5896step0 raw5896step0Labels = mixedMoment B raw5896step1 raw5896step1Labels := by
      have hz : ∀ j, raw5896step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5896step1 = (fun i j => raw5896step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5896step1 raw5896step0; decide +kernel
      have hl : raw5896step1Labels = raw5896step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5896step0 raw5896step0Labels permutation80 hz
    mixedMoment B raw5896step1 raw5896step1Labels = mixedMoment B raw5896step2 raw5896step2Labels := by
      have ha : raw5896step2 = (fun i j => raw5896step1 (permutation20 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5896step2 raw5896step1; decide +kernel
      have hl : raw5896step2Labels = raw5896step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5896step1 raw5896step1Labels permutation20 permutation4
    mixedMoment B raw5896step2 raw5896step2Labels = mixedMoment B raw5896step3 raw5896step3Labels := by
      have ha : raw5896step3 = raw5896step2 := by apply Matrix.ext; unfold raw5896step3 raw5896step2; decide +kernel
      have hl : raw5896step2Labels = labelEmbedding7 ∘ raw5896step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5896step2 raw5896step2Labels raw5896step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

def raw5897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5897Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5897step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5897step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, -3, 2], ![2, 0, -2]]
def raw5897step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5897step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5897step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5897step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5897step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5897 raw5897Labels = mixedMoment B node4500 node4500Labels := by
  calc
    mixedMoment B raw5897 raw5897Labels = mixedMoment B raw5897step0 raw5897step0Labels := by
      have hz : ∀ j, raw5897 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5897step0 = (fun i j => raw5897 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5897step0 raw5897; decide +kernel
      have hl : raw5897step0Labels = raw5897Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5897 raw5897Labels permutation434 hz
    mixedMoment B raw5897step0 raw5897step0Labels = mixedMoment B raw5897step1 raw5897step1Labels := by
      have hz : ∀ j, raw5897step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5897step1 = (fun i j => raw5897step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5897step1 raw5897step0; decide +kernel
      have hl : raw5897step1Labels = raw5897step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5897step0 raw5897step0Labels permutation80 hz
    mixedMoment B raw5897step1 raw5897step1Labels = mixedMoment B raw5897step2 raw5897step2Labels := by
      have ha : raw5897step2 = (fun i j => raw5897step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5897step2 raw5897step1; decide +kernel
      have hl : raw5897step2Labels = raw5897step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5897step1 raw5897step1Labels permutation8 permutation3
    mixedMoment B raw5897step2 raw5897step2Labels = mixedMoment B raw5897step3 raw5897step3Labels := by
      have ha : raw5897step3 = raw5897step2 := by apply Matrix.ext; unfold raw5897step3 raw5897step2; decide +kernel
      have hl : raw5897step2Labels = labelEmbedding6 ∘ raw5897step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5897step2 raw5897step2Labels raw5897step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4500 node4500Labels := by rfl

def raw5898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5898Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5898step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5898step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5898step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5898step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5898step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5898 raw5898Labels = mixedMoment B node5103 node5103Labels := by
  calc
    mixedMoment B raw5898 raw5898Labels = mixedMoment B raw5898step0 raw5898step0Labels := by
      have hz : ∀ j, raw5898 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5898step0 = (fun i j => raw5898 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5898step0 raw5898; decide +kernel
      have hl : raw5898step0Labels = raw5898Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5898 raw5898Labels permutation434 hz
    mixedMoment B raw5898step0 raw5898step0Labels = mixedMoment B raw5898step1 raw5898step1Labels := by
      have ha : raw5898step1 = (fun i j => raw5898step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5898step1 raw5898step0; decide +kernel
      have hl : raw5898step1Labels = raw5898step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5898step0 raw5898step0Labels permutation38 permutation3
    mixedMoment B raw5898step1 raw5898step1Labels = mixedMoment B raw5898step2 raw5898step2Labels := by
      have ha : raw5898step2 = raw5898step1 := by apply Matrix.ext; unfold raw5898step2 raw5898step1; decide +kernel
      have hl : raw5898step1Labels = labelEmbedding6 ∘ raw5898step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5898step1 raw5898step1Labels raw5898step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5103 node5103Labels := by rfl

def raw5899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5899Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5899step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5899step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5899step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5899step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5899step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5899 raw5899Labels = mixedMoment B node5103 node5103Labels := by
  calc
    mixedMoment B raw5899 raw5899Labels = mixedMoment B raw5899step0 raw5899step0Labels := by
      have hz : ∀ j, raw5899 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5899step0 = (fun i j => raw5899 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5899step0 raw5899; decide +kernel
      have hl : raw5899step0Labels = raw5899Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5899 raw5899Labels permutation346 hz
    mixedMoment B raw5899step0 raw5899step0Labels = mixedMoment B raw5899step1 raw5899step1Labels := by
      have ha : raw5899step1 = (fun i j => raw5899step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5899step1 raw5899step0; decide +kernel
      have hl : raw5899step1Labels = raw5899step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5899step0 raw5899step0Labels permutation38 permutation3
    mixedMoment B raw5899step1 raw5899step1Labels = mixedMoment B raw5899step2 raw5899step2Labels := by
      have ha : raw5899step2 = raw5899step1 := by apply Matrix.ext; unfold raw5899step2 raw5899step1; decide +kernel
      have hl : raw5899step1Labels = labelEmbedding6 ∘ raw5899step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5899step1 raw5899step1Labels raw5899step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5103 node5103Labels := by rfl

def raw5900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw5900Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw5900step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5900step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![2, 0, -2]]
def raw5900step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5900step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5900step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5900step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5900step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5900 raw5900Labels = mixedMoment B node5302 node5302Labels := by
  calc
    mixedMoment B raw5900 raw5900Labels = mixedMoment B raw5900step0 raw5900step0Labels := by
      have hz : ∀ j, raw5900 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5900step0 = (fun i j => raw5900 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5900step0 raw5900; decide +kernel
      have hl : raw5900step0Labels = raw5900Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5900 raw5900Labels permutation434 hz
    mixedMoment B raw5900step0 raw5900step0Labels = mixedMoment B raw5900step1 raw5900step1Labels := by
      have hz : ∀ j, raw5900step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5900step1 = (fun i j => raw5900step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5900step1 raw5900step0; decide +kernel
      have hl : raw5900step1Labels = raw5900step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5900step0 raw5900step0Labels permutation80 hz
    mixedMoment B raw5900step1 raw5900step1Labels = mixedMoment B raw5900step2 raw5900step2Labels := by
      have ha : raw5900step2 = (fun i j => raw5900step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5900step2 raw5900step1; decide +kernel
      have hl : raw5900step2Labels = raw5900step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5900step1 raw5900step1Labels permutation10 permutation3
    mixedMoment B raw5900step2 raw5900step2Labels = mixedMoment B raw5900step3 raw5900step3Labels := by
      have ha : raw5900step3 = raw5900step2 := by apply Matrix.ext; unfold raw5900step3 raw5900step2; decide +kernel
      have hl : raw5900step2Labels = labelEmbedding6 ∘ raw5900step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5900step2 raw5900step2Labels raw5900step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5302 node5302Labels := by rfl

def raw5901 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2]]
def raw5901Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5901step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2]]
def raw5901step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5901step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![1, -3, 2], ![1, 1, -2]]
def raw5901step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5901step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw5901step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5901step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw5901step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5901 raw5901Labels = mixedMoment B node5295 node5295Labels := by
  calc
    mixedMoment B raw5901 raw5901Labels = mixedMoment B raw5901step0 raw5901step0Labels := by
      have hz : ∀ j, raw5901 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5901step0 = (fun i j => raw5901 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5901step0 raw5901; decide +kernel
      have hl : raw5901step0Labels = raw5901Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5901 raw5901Labels permutation434 hz
    mixedMoment B raw5901step0 raw5901step0Labels = mixedMoment B raw5901step1 raw5901step1Labels := by
      have hz : ∀ j, raw5901step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5901step1 = (fun i j => raw5901step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5901step1 raw5901step0; decide +kernel
      have hl : raw5901step1Labels = raw5901step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5901step0 raw5901step0Labels permutation80 hz
    mixedMoment B raw5901step1 raw5901step1Labels = mixedMoment B raw5901step2 raw5901step2Labels := by
      have ha : raw5901step2 = (fun i j => raw5901step1 (permutation23 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5901step2 raw5901step1; decide +kernel
      have hl : raw5901step2Labels = raw5901step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5901step1 raw5901step1Labels permutation23 permutation4
    mixedMoment B raw5901step2 raw5901step2Labels = mixedMoment B raw5901step3 raw5901step3Labels := by
      have ha : raw5901step3 = raw5901step2 := by apply Matrix.ext; unfold raw5901step3 raw5901step2; decide +kernel
      have hl : raw5901step2Labels = labelEmbedding7 ∘ raw5901step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5901step2 raw5901step2Labels raw5901step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5295 node5295Labels := by rfl

def raw5902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5902Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5902step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5902step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw5902step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5902step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw5902step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5902 raw5902Labels = mixedMoment B node4425 node4425Labels := by
  calc
    mixedMoment B raw5902 raw5902Labels = mixedMoment B raw5902step0 raw5902step0Labels := by
      have hz : ∀ j, raw5902 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5902step0 = (fun i j => raw5902 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5902step0 raw5902; decide +kernel
      have hl : raw5902step0Labels = raw5902Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5902 raw5902Labels permutation434 hz
    mixedMoment B raw5902step0 raw5902step0Labels = mixedMoment B raw5902step1 raw5902step1Labels := by
      have ha : raw5902step1 = (fun i j => raw5902step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5902step1 raw5902step0; decide +kernel
      have hl : raw5902step1Labels = raw5902step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5902step0 raw5902step0Labels permutation32 permutation3
    mixedMoment B raw5902step1 raw5902step1Labels = mixedMoment B raw5902step2 raw5902step2Labels := by
      have ha : raw5902step2 = raw5902step1 := by apply Matrix.ext; unfold raw5902step2 raw5902step1; decide +kernel
      have hl : raw5902step1Labels = labelEmbedding6 ∘ raw5902step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5902step1 raw5902step1Labels raw5902step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4425 node4425Labels := by rfl

def raw5903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5903Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5903step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5903step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw5903step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5903step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw5903step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5903 raw5903Labels = mixedMoment B node5019 node5019Labels := by
  calc
    mixedMoment B raw5903 raw5903Labels = mixedMoment B raw5903step0 raw5903step0Labels := by
      have hz : ∀ j, raw5903 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5903step0 = (fun i j => raw5903 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5903step0 raw5903; decide +kernel
      have hl : raw5903step0Labels = raw5903Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5903 raw5903Labels permutation434 hz
    mixedMoment B raw5903step0 raw5903step0Labels = mixedMoment B raw5903step1 raw5903step1Labels := by
      have ha : raw5903step1 = (fun i j => raw5903step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5903step1 raw5903step0; decide +kernel
      have hl : raw5903step1Labels = raw5903step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5903step0 raw5903step0Labels permutation32 permutation3
    mixedMoment B raw5903step1 raw5903step1Labels = mixedMoment B raw5903step2 raw5903step2Labels := by
      have ha : raw5903step2 = raw5903step1 := by apply Matrix.ext; unfold raw5903step2 raw5903step1; decide +kernel
      have hl : raw5903step1Labels = labelEmbedding6 ∘ raw5903step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5903step1 raw5903step1Labels raw5903step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5019 node5019Labels := by rfl

def raw5904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5904Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5904step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw5904step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5904step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw5904step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5904 raw5904Labels = mixedMoment B node5060 node5060Labels := by
  calc
    mixedMoment B raw5904 raw5904Labels = mixedMoment B raw5904step0 raw5904step0Labels := by
      have ha : raw5904step0 = (fun i j => raw5904 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5904step0 raw5904; decide +kernel
      have hl : raw5904step0Labels = raw5904Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5904 raw5904Labels permutation200 permutation3
    mixedMoment B raw5904step0 raw5904step0Labels = mixedMoment B raw5904step1 raw5904step1Labels := by
      have ha : raw5904step1 = raw5904step0 := by apply Matrix.ext; unfold raw5904step1 raw5904step0; decide +kernel
      have hl : raw5904step0Labels = labelEmbedding6 ∘ raw5904step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5904step0 raw5904step0Labels raw5904step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5060 node5060Labels := by rfl

def raw5905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw5905Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5905step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![2, 0, -2]]
def raw5905step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5905step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw5905step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5905step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw5905step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5905 raw5905Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw5905 raw5905Labels = mixedMoment B raw5905step0 raw5905step0Labels := by
      have hz : ∀ j, raw5905 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5905step0 = (fun i j => raw5905 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5905step0 raw5905; decide +kernel
      have hl : raw5905step0Labels = raw5905Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5905 raw5905Labels permutation434 hz
    mixedMoment B raw5905step0 raw5905step0Labels = mixedMoment B raw5905step1 raw5905step1Labels := by
      have ha : raw5905step1 = (fun i j => raw5905step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5905step1 raw5905step0; decide +kernel
      have hl : raw5905step1Labels = raw5905step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5905step0 raw5905step0Labels permutation34 permutation3
    mixedMoment B raw5905step1 raw5905step1Labels = mixedMoment B raw5905step2 raw5905step2Labels := by
      have ha : raw5905step2 = raw5905step1 := by apply Matrix.ext; unfold raw5905step2 raw5905step1; decide +kernel
      have hl : raw5905step1Labels = labelEmbedding6 ∘ raw5905step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5905step1 raw5905step1Labels raw5905step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5267 node5267Labels := by rfl

def raw5906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2]]
def raw5906Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -3, 2], ![1, 1, -2]]
def raw5906step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5906step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw5906step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5906step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw5906step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5906 raw5906Labels = mixedMoment B node5173 node5173Labels := by
  calc
    mixedMoment B raw5906 raw5906Labels = mixedMoment B raw5906step0 raw5906step0Labels := by
      have hz : ∀ j, raw5906 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5906step0 = (fun i j => raw5906 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5906step0 raw5906; decide +kernel
      have hl : raw5906step0Labels = raw5906Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5906 raw5906Labels permutation434 hz
    mixedMoment B raw5906step0 raw5906step0Labels = mixedMoment B raw5906step1 raw5906step1Labels := by
      have ha : raw5906step1 = (fun i j => raw5906step0 (permutation119 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5906step1 raw5906step0; decide +kernel
      have hl : raw5906step1Labels = raw5906step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5906step0 raw5906step0Labels permutation119 permutation4
    mixedMoment B raw5906step1 raw5906step1Labels = mixedMoment B raw5906step2 raw5906step2Labels := by
      have ha : raw5906step2 = raw5906step1 := by apply Matrix.ext; unfold raw5906step2 raw5906step1; decide +kernel
      have hl : raw5906step1Labels = labelEmbedding7 ∘ raw5906step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5906step1 raw5906step1Labels raw5906step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5173 node5173Labels := by rfl

def raw5907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5907Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5907step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5907step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5907step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw5907step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5907step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw5907step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5907 raw5907Labels = mixedMoment B node4425 node4425Labels := by
  calc
    mixedMoment B raw5907 raw5907Labels = mixedMoment B raw5907step0 raw5907step0Labels := by
      have hz : ∀ j, raw5907 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5907step0 = (fun i j => raw5907 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5907step0 raw5907; decide +kernel
      have hl : raw5907step0Labels = raw5907Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5907 raw5907Labels permutation346 hz
    mixedMoment B raw5907step0 raw5907step0Labels = mixedMoment B raw5907step1 raw5907step1Labels := by
      have ha : raw5907step1 = (fun i j => raw5907step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5907step1 raw5907step0; decide +kernel
      have hl : raw5907step1Labels = raw5907step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5907step0 raw5907step0Labels permutation32 permutation3
    mixedMoment B raw5907step1 raw5907step1Labels = mixedMoment B raw5907step2 raw5907step2Labels := by
      have ha : raw5907step2 = raw5907step1 := by apply Matrix.ext; unfold raw5907step2 raw5907step1; decide +kernel
      have hl : raw5907step1Labels = labelEmbedding6 ∘ raw5907step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5907step1 raw5907step1Labels raw5907step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4425 node4425Labels := by rfl

def raw5908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5908Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5908step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5908step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw5908step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5908step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw5908step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5908 raw5908Labels = mixedMoment B node5019 node5019Labels := by
  calc
    mixedMoment B raw5908 raw5908Labels = mixedMoment B raw5908step0 raw5908step0Labels := by
      have hz : ∀ j, raw5908 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5908step0 = (fun i j => raw5908 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5908step0 raw5908; decide +kernel
      have hl : raw5908step0Labels = raw5908Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5908 raw5908Labels permutation346 hz
    mixedMoment B raw5908step0 raw5908step0Labels = mixedMoment B raw5908step1 raw5908step1Labels := by
      have ha : raw5908step1 = (fun i j => raw5908step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5908step1 raw5908step0; decide +kernel
      have hl : raw5908step1Labels = raw5908step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5908step0 raw5908step0Labels permutation32 permutation3
    mixedMoment B raw5908step1 raw5908step1Labels = mixedMoment B raw5908step2 raw5908step2Labels := by
      have ha : raw5908step2 = raw5908step1 := by apply Matrix.ext; unfold raw5908step2 raw5908step1; decide +kernel
      have hl : raw5908step1Labels = labelEmbedding6 ∘ raw5908step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5908step1 raw5908step1Labels raw5908step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5019 node5019Labels := by rfl

def raw5909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5909Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5909step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw5909step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5909step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw5909step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5909 raw5909Labels = mixedMoment B node5060 node5060Labels := by
  calc
    mixedMoment B raw5909 raw5909Labels = mixedMoment B raw5909step0 raw5909step0Labels := by
      have ha : raw5909step0 = (fun i j => raw5909 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5909step0 raw5909; decide +kernel
      have hl : raw5909step0Labels = raw5909Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5909 raw5909Labels permutation176 permutation3
    mixedMoment B raw5909step0 raw5909step0Labels = mixedMoment B raw5909step1 raw5909step1Labels := by
      have ha : raw5909step1 = raw5909step0 := by apply Matrix.ext; unfold raw5909step1 raw5909step0; decide +kernel
      have hl : raw5909step0Labels = labelEmbedding6 ∘ raw5909step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5909step0 raw5909step0Labels raw5909step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5060 node5060Labels := by rfl

def raw5910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![2, 0, -2]]
def raw5910Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![2, 0, -2]]
def raw5910step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5910step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw5910step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5910step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw5910step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5910 raw5910Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw5910 raw5910Labels = mixedMoment B raw5910step0 raw5910step0Labels := by
      have hz : ∀ j, raw5910 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5910step0 = (fun i j => raw5910 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5910step0 raw5910; decide +kernel
      have hl : raw5910step0Labels = raw5910Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5910 raw5910Labels permutation346 hz
    mixedMoment B raw5910step0 raw5910step0Labels = mixedMoment B raw5910step1 raw5910step1Labels := by
      have ha : raw5910step1 = (fun i j => raw5910step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5910step1 raw5910step0; decide +kernel
      have hl : raw5910step1Labels = raw5910step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5910step0 raw5910step0Labels permutation34 permutation3
    mixedMoment B raw5910step1 raw5910step1Labels = mixedMoment B raw5910step2 raw5910step2Labels := by
      have ha : raw5910step2 = raw5910step1 := by apply Matrix.ext; unfold raw5910step2 raw5910step1; decide +kernel
      have hl : raw5910step1Labels = labelEmbedding6 ∘ raw5910step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5910step1 raw5910step1Labels raw5910step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5267 node5267Labels := by rfl

def raw5911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -3, 2], ![1, 1, -2]]
def raw5911Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -3, 2], ![1, 1, -2]]
def raw5911step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5911step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw5911step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5911step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw5911step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5911 raw5911Labels = mixedMoment B node5173 node5173Labels := by
  calc
    mixedMoment B raw5911 raw5911Labels = mixedMoment B raw5911step0 raw5911step0Labels := by
      have hz : ∀ j, raw5911 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5911step0 = (fun i j => raw5911 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5911step0 raw5911; decide +kernel
      have hl : raw5911step0Labels = raw5911Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5911 raw5911Labels permutation346 hz
    mixedMoment B raw5911step0 raw5911step0Labels = mixedMoment B raw5911step1 raw5911step1Labels := by
      have ha : raw5911step1 = (fun i j => raw5911step0 (permutation119 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5911step1 raw5911step0; decide +kernel
      have hl : raw5911step1Labels = raw5911step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5911step0 raw5911step0Labels permutation119 permutation4
    mixedMoment B raw5911step1 raw5911step1Labels = mixedMoment B raw5911step2 raw5911step2Labels := by
      have ha : raw5911step2 = raw5911step1 := by apply Matrix.ext; unfold raw5911step2 raw5911step1; decide +kernel
      have hl : raw5911step1Labels = labelEmbedding7 ∘ raw5911step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5911step1 raw5911step1Labels raw5911step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5173 node5173Labels := by rfl

def raw5912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -4, 2], ![2, 0, -2]]
def raw5912Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![2, -4, 2], ![2, 0, -2]]
def raw5912step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5912step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![2, -4, 2], ![2, 0, -2]]
def raw5912step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5912step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -2, 0], ![2, 2, -4]]
def raw5912step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5912step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -2, 0], ![2, 2, -4]]
def raw5912step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5912 raw5912Labels = mixedMoment B node4430 node4430Labels := by
  calc
    mixedMoment B raw5912 raw5912Labels = mixedMoment B raw5912step0 raw5912step0Labels := by
      have hz : ∀ j, raw5912 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5912step0 = (fun i j => raw5912 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5912step0 raw5912; decide +kernel
      have hl : raw5912step0Labels = raw5912Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5912 raw5912Labels permutation434 hz
    mixedMoment B raw5912step0 raw5912step0Labels = mixedMoment B raw5912step1 raw5912step1Labels := by
      have hz : ∀ j, raw5912step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5912step1 = (fun i j => raw5912step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5912step1 raw5912step0; decide +kernel
      have hl : raw5912step1Labels = raw5912step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5912step0 raw5912step0Labels permutation80 hz
    mixedMoment B raw5912step1 raw5912step1Labels = mixedMoment B raw5912step2 raw5912step2Labels := by
      have ha : raw5912step2 = (fun i j => raw5912step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5912step2 raw5912step1; decide +kernel
      have hl : raw5912step2Labels = raw5912step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5912step1 raw5912step1Labels permutation9 permutation3
    mixedMoment B raw5912step2 raw5912step2Labels = mixedMoment B raw5912step3 raw5912step3Labels := by
      have ha : raw5912step3 = raw5912step2 := by apply Matrix.ext; unfold raw5912step3 raw5912step2; decide +kernel
      have hl : raw5912step2Labels = labelEmbedding6 ∘ raw5912step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5912step2 raw5912step2Labels raw5912step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4430 node4430Labels := by rfl

def raw5913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -4, 2], ![2, 0, -2]]
def raw5913Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![2, -4, 2], ![2, 0, -2]]
def raw5913step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5913step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![2, -4, 2], ![2, 0, -2]]
def raw5913step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5913step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw5913step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5913step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw5913step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5913 raw5913Labels = mixedMoment B node4574 node4574Labels := by
  calc
    mixedMoment B raw5913 raw5913Labels = mixedMoment B raw5913step0 raw5913step0Labels := by
      have hz : ∀ j, raw5913 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5913step0 = (fun i j => raw5913 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5913step0 raw5913; decide +kernel
      have hl : raw5913step0Labels = raw5913Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5913 raw5913Labels permutation434 hz
    mixedMoment B raw5913step0 raw5913step0Labels = mixedMoment B raw5913step1 raw5913step1Labels := by
      have hz : ∀ j, raw5913step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5913step1 = (fun i j => raw5913step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5913step1 raw5913step0; decide +kernel
      have hl : raw5913step1Labels = raw5913step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5913step0 raw5913step0Labels permutation80 hz
    mixedMoment B raw5913step1 raw5913step1Labels = mixedMoment B raw5913step2 raw5913step2Labels := by
      have ha : raw5913step2 = (fun i j => raw5913step1 (permutation25 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5913step2 raw5913step1; decide +kernel
      have hl : raw5913step2Labels = raw5913step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5913step1 raw5913step1Labels permutation25 permutation5
    mixedMoment B raw5913step2 raw5913step2Labels = mixedMoment B raw5913step3 raw5913step3Labels := by
      have ha : raw5913step3 = raw5913step2 := by apply Matrix.ext; unfold raw5913step3 raw5913step2; decide +kernel
      have hl : raw5913step2Labels = labelEmbedding8 ∘ raw5913step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5913step2 raw5913step2Labels raw5913step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4574 node4574Labels := by rfl

def raw5914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -4, 2], ![2, 0, -2]]
def raw5914Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![2, -4, 2], ![2, 0, -2]]
def raw5914step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5914step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw5914step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5914step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw5914step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5914 raw5914Labels = mixedMoment B node4567 node4567Labels := by
  calc
    mixedMoment B raw5914 raw5914Labels = mixedMoment B raw5914step0 raw5914step0Labels := by
      have hz : ∀ j, raw5914 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5914step0 = (fun i j => raw5914 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5914step0 raw5914; decide +kernel
      have hl : raw5914step0Labels = raw5914Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5914 raw5914Labels permutation434 hz
    mixedMoment B raw5914step0 raw5914step0Labels = mixedMoment B raw5914step1 raw5914step1Labels := by
      have ha : raw5914step1 = (fun i j => raw5914step0 (permutation125 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5914step1 raw5914step0; decide +kernel
      have hl : raw5914step1Labels = raw5914step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5914step0 raw5914step0Labels permutation125 permutation5
    mixedMoment B raw5914step1 raw5914step1Labels = mixedMoment B raw5914step2 raw5914step2Labels := by
      have ha : raw5914step2 = raw5914step1 := by apply Matrix.ext; unfold raw5914step2 raw5914step1; decide +kernel
      have hl : raw5914step1Labels = labelEmbedding8 ∘ raw5914step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5914step1 raw5914step1Labels raw5914step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4567 node4567Labels := by rfl

def raw5915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -4, 2], ![2, 0, -2]]
def raw5915Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5915step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![2, -4, 2], ![2, 0, -2]]
def raw5915step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5915step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw5915step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5915step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw5915step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5915 raw5915Labels = mixedMoment B node4567 node4567Labels := by
  calc
    mixedMoment B raw5915 raw5915Labels = mixedMoment B raw5915step0 raw5915step0Labels := by
      have hz : ∀ j, raw5915 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5915step0 = (fun i j => raw5915 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5915step0 raw5915; decide +kernel
      have hl : raw5915step0Labels = raw5915Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5915 raw5915Labels permutation346 hz
    mixedMoment B raw5915step0 raw5915step0Labels = mixedMoment B raw5915step1 raw5915step1Labels := by
      have ha : raw5915step1 = (fun i j => raw5915step0 (permutation125 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5915step1 raw5915step0; decide +kernel
      have hl : raw5915step1Labels = raw5915step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5915step0 raw5915step0Labels permutation125 permutation5
    mixedMoment B raw5915step1 raw5915step1Labels = mixedMoment B raw5915step2 raw5915step2Labels := by
      have ha : raw5915step2 = raw5915step1 := by apply Matrix.ext; unfold raw5915step2 raw5915step1; decide +kernel
      have hl : raw5915step1Labels = labelEmbedding8 ∘ raw5915step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5915step1 raw5915step1Labels raw5915step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4567 node4567Labels := by rfl

def raw5916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -4, 2], ![1, 1, -2]]
def raw5916Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5916step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![2, -4, 2], ![1, 1, -2]]
def raw5916step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5916step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![2, -4, 2], ![1, 1, -2]]
def raw5916step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5916step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw5916step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5916step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw5916step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5916 raw5916Labels = mixedMoment B node4617 node4617Labels := by
  calc
    mixedMoment B raw5916 raw5916Labels = mixedMoment B raw5916step0 raw5916step0Labels := by
      have hz : ∀ j, raw5916 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5916step0 = (fun i j => raw5916 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5916step0 raw5916; decide +kernel
      have hl : raw5916step0Labels = raw5916Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5916 raw5916Labels permutation434 hz
    mixedMoment B raw5916step0 raw5916step0Labels = mixedMoment B raw5916step1 raw5916step1Labels := by
      have hz : ∀ j, raw5916step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5916step1 = (fun i j => raw5916step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5916step1 raw5916step0; decide +kernel
      have hl : raw5916step1Labels = raw5916step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5916step0 raw5916step0Labels permutation80 hz
    mixedMoment B raw5916step1 raw5916step1Labels = mixedMoment B raw5916step2 raw5916step2Labels := by
      have ha : raw5916step2 = (fun i j => raw5916step1 (permutation25 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5916step2 raw5916step1; decide +kernel
      have hl : raw5916step2Labels = raw5916step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5916step1 raw5916step1Labels permutation25 permutation5
    mixedMoment B raw5916step2 raw5916step2Labels = mixedMoment B raw5916step3 raw5916step3Labels := by
      have ha : raw5916step3 = raw5916step2 := by apply Matrix.ext; unfold raw5916step3 raw5916step2; decide +kernel
      have hl : raw5916step2Labels = labelEmbedding8 ∘ raw5916step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5916step2 raw5916step2Labels raw5916step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4617 node4617Labels := by rfl

def raw5917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![3, -1, -2]]
def raw5917Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![3, -1, -2]]
def raw5917step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5917step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -3, 2], ![3, -1, -2]]
def raw5917step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5917step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw5917step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5917step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw5917step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5917 raw5917Labels = mixedMoment B node4429 node4429Labels := by
  calc
    mixedMoment B raw5917 raw5917Labels = mixedMoment B raw5917step0 raw5917step0Labels := by
      have hz : ∀ j, raw5917 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5917step0 = (fun i j => raw5917 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5917step0 raw5917; decide +kernel
      have hl : raw5917step0Labels = raw5917Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5917 raw5917Labels permutation434 hz
    mixedMoment B raw5917step0 raw5917step0Labels = mixedMoment B raw5917step1 raw5917step1Labels := by
      have hz : ∀ j, raw5917step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5917step1 = (fun i j => raw5917step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5917step1 raw5917step0; decide +kernel
      have hl : raw5917step1Labels = raw5917step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5917step0 raw5917step0Labels permutation80 hz
    mixedMoment B raw5917step1 raw5917step1Labels = mixedMoment B raw5917step2 raw5917step2Labels := by
      have ha : raw5917step2 = (fun i j => raw5917step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5917step2 raw5917step1; decide +kernel
      have hl : raw5917step2Labels = raw5917step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5917step1 raw5917step1Labels permutation8 permutation3
    mixedMoment B raw5917step2 raw5917step2Labels = mixedMoment B raw5917step3 raw5917step3Labels := by
      have ha : raw5917step3 = raw5917step2 := by apply Matrix.ext; unfold raw5917step3 raw5917step2; decide +kernel
      have hl : raw5917step2Labels = labelEmbedding6 ∘ raw5917step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5917step2 raw5917step2Labels raw5917step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4429 node4429Labels := by rfl

def raw5918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![3, -1, -2]]
def raw5918Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![3, -1, -2]]
def raw5918step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5918step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -3, 2], ![3, -1, -2]]
def raw5918step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5918step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 2, -3], ![3, -2, -1]]
def raw5918step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5918step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 2, -3], ![3, -2, -1]]
def raw5918step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5918 raw5918Labels = mixedMoment B node5022 node5022Labels := by
  calc
    mixedMoment B raw5918 raw5918Labels = mixedMoment B raw5918step0 raw5918step0Labels := by
      have hz : ∀ j, raw5918 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5918step0 = (fun i j => raw5918 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5918step0 raw5918; decide +kernel
      have hl : raw5918step0Labels = raw5918Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5918 raw5918Labels permutation434 hz
    mixedMoment B raw5918step0 raw5918step0Labels = mixedMoment B raw5918step1 raw5918step1Labels := by
      have hz : ∀ j, raw5918step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5918step1 = (fun i j => raw5918step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5918step1 raw5918step0; decide +kernel
      have hl : raw5918step1Labels = raw5918step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5918step0 raw5918step0Labels permutation80 hz
    mixedMoment B raw5918step1 raw5918step1Labels = mixedMoment B raw5918step2 raw5918step2Labels := by
      have ha : raw5918step2 = (fun i j => raw5918step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5918step2 raw5918step1; decide +kernel
      have hl : raw5918step2Labels = raw5918step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5918step1 raw5918step1Labels permutation8 permutation3
    mixedMoment B raw5918step2 raw5918step2Labels = mixedMoment B raw5918step3 raw5918step3Labels := by
      have ha : raw5918step3 = raw5918step2 := by apply Matrix.ext; unfold raw5918step3 raw5918step2; decide +kernel
      have hl : raw5918step2Labels = labelEmbedding6 ∘ raw5918step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5918step2 raw5918step2Labels raw5918step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5022 node5022Labels := by rfl

def raw5919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![3, -1, -2]]
def raw5919Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -3, 2], ![3, -1, -2]]
def raw5919step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5919step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw5919step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5919step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw5919step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5919 raw5919Labels = mixedMoment B node5062 node5062Labels := by
  calc
    mixedMoment B raw5919 raw5919Labels = mixedMoment B raw5919step0 raw5919step0Labels := by
      have hz : ∀ j, raw5919 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5919step0 = (fun i j => raw5919 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5919step0 raw5919; decide +kernel
      have hl : raw5919step0Labels = raw5919Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5919 raw5919Labels permutation434 hz
    mixedMoment B raw5919step0 raw5919step0Labels = mixedMoment B raw5919step1 raw5919step1Labels := by
      have ha : raw5919step1 = (fun i j => raw5919step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5919step1 raw5919step0; decide +kernel
      have hl : raw5919step1Labels = raw5919step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5919step0 raw5919step0Labels permutation38 permutation3
    mixedMoment B raw5919step1 raw5919step1Labels = mixedMoment B raw5919step2 raw5919step2Labels := by
      have ha : raw5919step2 = raw5919step1 := by apply Matrix.ext; unfold raw5919step2 raw5919step1; decide +kernel
      have hl : raw5919step1Labels = labelEmbedding6 ∘ raw5919step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5919step1 raw5919step1Labels raw5919step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5062 node5062Labels := by rfl

def raw5920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![3, -1, -2]]
def raw5920Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -3, 2], ![3, -1, -2]]
def raw5920step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5920step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw5920step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5920step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw5920step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5920 raw5920Labels = mixedMoment B node5062 node5062Labels := by
  calc
    mixedMoment B raw5920 raw5920Labels = mixedMoment B raw5920step0 raw5920step0Labels := by
      have hz : ∀ j, raw5920 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5920step0 = (fun i j => raw5920 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5920step0 raw5920; decide +kernel
      have hl : raw5920step0Labels = raw5920Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5920 raw5920Labels permutation346 hz
    mixedMoment B raw5920step0 raw5920step0Labels = mixedMoment B raw5920step1 raw5920step1Labels := by
      have ha : raw5920step1 = (fun i j => raw5920step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5920step1 raw5920step0; decide +kernel
      have hl : raw5920step1Labels = raw5920step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5920step0 raw5920step0Labels permutation38 permutation3
    mixedMoment B raw5920step1 raw5920step1Labels = mixedMoment B raw5920step2 raw5920step2Labels := by
      have ha : raw5920step2 = raw5920step1 := by apply Matrix.ext; unfold raw5920step2 raw5920step1; decide +kernel
      have hl : raw5920step1Labels = labelEmbedding6 ∘ raw5920step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5920step1 raw5920step1Labels raw5920step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5062 node5062Labels := by rfl

def raw5921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw5921Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw5921step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5921step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![3, -1, -2]]
def raw5921step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5921step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-3, 2, 1]]
def raw5921step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5921step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw5921step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5921 raw5921Labels = mixedMoment B node5268 node5268Labels := by
  calc
    mixedMoment B raw5921 raw5921Labels = mixedMoment B raw5921step0 raw5921step0Labels := by
      have hz : ∀ j, raw5921 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5921step0 = (fun i j => raw5921 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5921step0 raw5921; decide +kernel
      have hl : raw5921step0Labels = raw5921Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5921 raw5921Labels permutation434 hz
    mixedMoment B raw5921step0 raw5921step0Labels = mixedMoment B raw5921step1 raw5921step1Labels := by
      have hz : ∀ j, raw5921step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5921step1 = (fun i j => raw5921step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5921step1 raw5921step0; decide +kernel
      have hl : raw5921step1Labels = raw5921step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5921step0 raw5921step0Labels permutation80 hz
    mixedMoment B raw5921step1 raw5921step1Labels = mixedMoment B raw5921step2 raw5921step2Labels := by
      have ha : raw5921step2 = (fun i j => raw5921step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5921step2 raw5921step1; decide +kernel
      have hl : raw5921step2Labels = raw5921step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5921step1 raw5921step1Labels permutation29 permutation2
    mixedMoment B raw5921step2 raw5921step2Labels = mixedMoment B raw5921step3 raw5921step3Labels := by
      have ha : raw5921step3 = -raw5921step2 := by apply Matrix.ext; change ∀ i j, raw5921step3 i j = -(raw5921step2 i j); unfold raw5921step3 raw5921step2; decide +kernel
      have hl : raw5921step3Labels = raw5921step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5268 node5268Labels := by rfl

def raw5922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5922Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5922step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5922step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -3, 2], ![2, 0, -2]]
def raw5922step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5922step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw5922step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5922step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw5922step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5922 raw5922Labels = mixedMoment B node3584 node3584Labels := by
  calc
    mixedMoment B raw5922 raw5922Labels = mixedMoment B raw5922step0 raw5922step0Labels := by
      have hz : ∀ j, raw5922 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5922step0 = (fun i j => raw5922 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5922step0 raw5922; decide +kernel
      have hl : raw5922step0Labels = raw5922Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5922 raw5922Labels permutation434 hz
    mixedMoment B raw5922step0 raw5922step0Labels = mixedMoment B raw5922step1 raw5922step1Labels := by
      have hz : ∀ j, raw5922step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5922step1 = (fun i j => raw5922step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5922step1 raw5922step0; decide +kernel
      have hl : raw5922step1Labels = raw5922step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5922step0 raw5922step0Labels permutation80 hz
    mixedMoment B raw5922step1 raw5922step1Labels = mixedMoment B raw5922step2 raw5922step2Labels := by
      have ha : raw5922step2 = (fun i j => raw5922step1 (permutation20 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5922step2 raw5922step1; decide +kernel
      have hl : raw5922step2Labels = raw5922step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5922step1 raw5922step1Labels permutation20 permutation6
    mixedMoment B raw5922step2 raw5922step2Labels = mixedMoment B raw5922step3 raw5922step3Labels := by
      have ha : raw5922step3 = -raw5922step2 := by apply Matrix.ext; change ∀ i j, raw5922step3 i j = -(raw5922step2 i j); unfold raw5922step3 raw5922step2; decide +kernel
      have hl : raw5922step3Labels = raw5922step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3584 node3584Labels := by rfl

def raw5923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5923Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5923step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5923step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw5923step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5923step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5923step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5923 raw5923Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw5923 raw5923Labels = mixedMoment B raw5923step0 raw5923step0Labels := by
      have hz : ∀ j, raw5923 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5923step0 = (fun i j => raw5923 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5923step0 raw5923; decide +kernel
      have hl : raw5923step0Labels = raw5923Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5923 raw5923Labels permutation434 hz
    mixedMoment B raw5923step0 raw5923step0Labels = mixedMoment B raw5923step1 raw5923step1Labels := by
      have ha : raw5923step1 = (fun i j => raw5923step0 (permutation106 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5923step1 raw5923step0; decide +kernel
      have hl : raw5923step1Labels = raw5923step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5923step0 raw5923step0Labels permutation106 permutation6
    mixedMoment B raw5923step1 raw5923step1Labels = mixedMoment B raw5923step2 raw5923step2Labels := by
      have ha : raw5923step2 = -raw5923step1 := by apply Matrix.ext; change ∀ i j, raw5923step2 i j = -(raw5923step1 i j); unfold raw5923step2 raw5923step1; decide +kernel
      have hl : raw5923step2Labels = raw5923step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3573 node3573Labels := by rfl

def raw5924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5924Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5924step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5924step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5924step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw5924step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5924step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5924step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5924 raw5924Labels = mixedMoment B node3573 node3573Labels := by
  calc
    mixedMoment B raw5924 raw5924Labels = mixedMoment B raw5924step0 raw5924step0Labels := by
      have hz : ∀ j, raw5924 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5924step0 = (fun i j => raw5924 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5924step0 raw5924; decide +kernel
      have hl : raw5924step0Labels = raw5924Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5924 raw5924Labels permutation346 hz
    mixedMoment B raw5924step0 raw5924step0Labels = mixedMoment B raw5924step1 raw5924step1Labels := by
      have ha : raw5924step1 = (fun i j => raw5924step0 (permutation106 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5924step1 raw5924step0; decide +kernel
      have hl : raw5924step1Labels = raw5924step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5924step0 raw5924step0Labels permutation106 permutation6
    mixedMoment B raw5924step1 raw5924step1Labels = mixedMoment B raw5924step2 raw5924step2Labels := by
      have ha : raw5924step2 = -raw5924step1 := by apply Matrix.ext; change ∀ i j, raw5924step2 i j = -(raw5924step1 i j); unfold raw5924step2 raw5924step1; decide +kernel
      have hl : raw5924step2Labels = raw5924step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3573 node3573Labels := by rfl

def raw5925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw5925Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5925step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw5925step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5925step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2]]
def raw5925step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5925step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw5925step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5925step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5925step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5925 raw5925Labels = mixedMoment B node3889 node3889Labels := by
  calc
    mixedMoment B raw5925 raw5925Labels = mixedMoment B raw5925step0 raw5925step0Labels := by
      have hz : ∀ j, raw5925 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5925step0 = (fun i j => raw5925 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5925step0 raw5925; decide +kernel
      have hl : raw5925step0Labels = raw5925Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5925 raw5925Labels permutation434 hz
    mixedMoment B raw5925step0 raw5925step0Labels = mixedMoment B raw5925step1 raw5925step1Labels := by
      have hz : ∀ j, raw5925step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5925step1 = (fun i j => raw5925step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5925step1 raw5925step0; decide +kernel
      have hl : raw5925step1Labels = raw5925step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5925step0 raw5925step0Labels permutation80 hz
    mixedMoment B raw5925step1 raw5925step1Labels = mixedMoment B raw5925step2 raw5925step2Labels := by
      have ha : raw5925step2 = (fun i j => raw5925step1 (permutation20 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5925step2 raw5925step1; decide +kernel
      have hl : raw5925step2Labels = raw5925step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5925step1 raw5925step1Labels permutation20 permutation6
    mixedMoment B raw5925step2 raw5925step2Labels = mixedMoment B raw5925step3 raw5925step3Labels := by
      have ha : raw5925step3 = -raw5925step2 := by apply Matrix.ext; change ∀ i j, raw5925step3 i j = -(raw5925step2 i j); unfold raw5925step3 raw5925step2; decide +kernel
      have hl : raw5925step3Labels = raw5925step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3889 node3889Labels := by rfl

def raw5926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2]]
def raw5926Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2]]
def raw5926step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5926step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2]]
def raw5926step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5926step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw5926step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5926step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw5926step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5926 raw5926Labels = mixedMoment B node3583 node3583Labels := by
  calc
    mixedMoment B raw5926 raw5926Labels = mixedMoment B raw5926step0 raw5926step0Labels := by
      have hz : ∀ j, raw5926 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5926step0 = (fun i j => raw5926 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5926step0 raw5926; decide +kernel
      have hl : raw5926step0Labels = raw5926Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5926 raw5926Labels permutation434 hz
    mixedMoment B raw5926step0 raw5926step0Labels = mixedMoment B raw5926step1 raw5926step1Labels := by
      have hz : ∀ j, raw5926step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5926step1 = (fun i j => raw5926step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5926step1 raw5926step0; decide +kernel
      have hl : raw5926step1Labels = raw5926step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5926step0 raw5926step0Labels permutation80 hz
    mixedMoment B raw5926step1 raw5926step1Labels = mixedMoment B raw5926step2 raw5926step2Labels := by
      have ha : raw5926step2 = (fun i j => raw5926step1 (permutation20 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5926step2 raw5926step1; decide +kernel
      have hl : raw5926step2Labels = raw5926step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5926step1 raw5926step1Labels permutation20 permutation6
    mixedMoment B raw5926step2 raw5926step2Labels = mixedMoment B raw5926step3 raw5926step3Labels := by
      have ha : raw5926step3 = -raw5926step2 := by apply Matrix.ext; change ∀ i j, raw5926step3 i j = -(raw5926step2 i j); unfold raw5926step3 raw5926step2; decide +kernel
      have hl : raw5926step3Labels = raw5926step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3583 node3583Labels := by rfl

def raw5927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5927Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5927step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5927step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, -3, 2], ![2, 0, -2]]
def raw5927step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5927step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5927step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5927 raw5927Labels = mixedMoment B node1084 node1084Labels := by
  calc
    mixedMoment B raw5927 raw5927Labels = mixedMoment B raw5927step0 raw5927step0Labels := by
      have hz : ∀ j, raw5927 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5927step0 = (fun i j => raw5927 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5927step0 raw5927; decide +kernel
      have hl : raw5927step0Labels = raw5927Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5927 raw5927Labels permutation434 hz
    mixedMoment B raw5927step0 raw5927step0Labels = mixedMoment B raw5927step1 raw5927step1Labels := by
      have hz : ∀ j, raw5927step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5927step1 = (fun i j => raw5927step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5927step1 raw5927step0; decide +kernel
      have hl : raw5927step1Labels = raw5927step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5927step0 raw5927step0Labels permutation80 hz
    mixedMoment B raw5927step1 raw5927step1Labels = mixedMoment B raw5927step2 raw5927step2Labels := by
      have ha : raw5927step2 = (fun i j => raw5927step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5927step2 raw5927step1; decide +kernel
      have hl : raw5927step2Labels = raw5927step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5927step1 raw5927step1Labels permutation8 permutation3
    _ = mixedMoment B node1084 node1084Labels := by rfl

def raw5928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5928Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5928step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5928step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5928step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5928 raw5928Labels = mixedMoment B node2513 node2513Labels := by
  calc
    mixedMoment B raw5928 raw5928Labels = mixedMoment B raw5928step0 raw5928step0Labels := by
      have hz : ∀ j, raw5928 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5928step0 = (fun i j => raw5928 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5928step0 raw5928; decide +kernel
      have hl : raw5928step0Labels = raw5928Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5928 raw5928Labels permutation434 hz
    mixedMoment B raw5928step0 raw5928step0Labels = mixedMoment B raw5928step1 raw5928step1Labels := by
      have ha : raw5928step1 = (fun i j => raw5928step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5928step1 raw5928step0; decide +kernel
      have hl : raw5928step1Labels = raw5928step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5928step0 raw5928step0Labels permutation38 permutation3
    _ = mixedMoment B node2513 node2513Labels := by rfl

def raw5929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5929Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5929step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5929step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5929step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5929step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5929 raw5929Labels = mixedMoment B node2513 node2513Labels := by
  calc
    mixedMoment B raw5929 raw5929Labels = mixedMoment B raw5929step0 raw5929step0Labels := by
      have hz : ∀ j, raw5929 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5929step0 = (fun i j => raw5929 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5929step0 raw5929; decide +kernel
      have hl : raw5929step0Labels = raw5929Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5929 raw5929Labels permutation346 hz
    mixedMoment B raw5929step0 raw5929step0Labels = mixedMoment B raw5929step1 raw5929step1Labels := by
      have ha : raw5929step1 = (fun i j => raw5929step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5929step1 raw5929step0; decide +kernel
      have hl : raw5929step1Labels = raw5929step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5929step0 raw5929step0Labels permutation38 permutation3
    _ = mixedMoment B node2513 node2513Labels := by rfl

def raw5930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw5930Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw5930step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5930step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![2, 0, -2]]
def raw5930step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5930step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5930step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5930 raw5930Labels = mixedMoment B node2776 node2776Labels := by
  calc
    mixedMoment B raw5930 raw5930Labels = mixedMoment B raw5930step0 raw5930step0Labels := by
      have hz : ∀ j, raw5930 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5930step0 = (fun i j => raw5930 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5930step0 raw5930; decide +kernel
      have hl : raw5930step0Labels = raw5930Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5930 raw5930Labels permutation434 hz
    mixedMoment B raw5930step0 raw5930step0Labels = mixedMoment B raw5930step1 raw5930step1Labels := by
      have hz : ∀ j, raw5930step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5930step1 = (fun i j => raw5930step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5930step1 raw5930step0; decide +kernel
      have hl : raw5930step1Labels = raw5930step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5930step0 raw5930step0Labels permutation80 hz
    mixedMoment B raw5930step1 raw5930step1Labels = mixedMoment B raw5930step2 raw5930step2Labels := by
      have ha : raw5930step2 = (fun i j => raw5930step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5930step2 raw5930step1; decide +kernel
      have hl : raw5930step2Labels = raw5930step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5930step1 raw5930step1Labels permutation10 permutation3
    _ = mixedMoment B node2776 node2776Labels := by rfl

def raw5931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2]]
def raw5931Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2]]
def raw5931step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5931step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![1, -3, 2], ![1, 1, -2]]
def raw5931step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5931step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw5931step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5931 raw5931Labels = mixedMoment B node2781 node2781Labels := by
  calc
    mixedMoment B raw5931 raw5931Labels = mixedMoment B raw5931step0 raw5931step0Labels := by
      have hz : ∀ j, raw5931 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5931step0 = (fun i j => raw5931 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5931step0 raw5931; decide +kernel
      have hl : raw5931step0Labels = raw5931Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5931 raw5931Labels permutation434 hz
    mixedMoment B raw5931step0 raw5931step0Labels = mixedMoment B raw5931step1 raw5931step1Labels := by
      have hz : ∀ j, raw5931step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5931step1 = (fun i j => raw5931step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5931step1 raw5931step0; decide +kernel
      have hl : raw5931step1Labels = raw5931step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5931step0 raw5931step0Labels permutation80 hz
    mixedMoment B raw5931step1 raw5931step1Labels = mixedMoment B raw5931step2 raw5931step2Labels := by
      have ha : raw5931step2 = (fun i j => raw5931step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5931step2 raw5931step1; decide +kernel
      have hl : raw5931step2Labels = raw5931step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5931step1 raw5931step1Labels permutation12 permutation3
    _ = mixedMoment B node2781 node2781Labels := by rfl

def raw5932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5932Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5932step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5932step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw5932step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5932 raw5932Labels = mixedMoment B node1006 node1006Labels := by
  calc
    mixedMoment B raw5932 raw5932Labels = mixedMoment B raw5932step0 raw5932step0Labels := by
      have hz : ∀ j, raw5932 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5932step0 = (fun i j => raw5932 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5932step0 raw5932; decide +kernel
      have hl : raw5932step0Labels = raw5932Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5932 raw5932Labels permutation434 hz
    mixedMoment B raw5932step0 raw5932step0Labels = mixedMoment B raw5932step1 raw5932step1Labels := by
      have ha : raw5932step1 = (fun i j => raw5932step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5932step1 raw5932step0; decide +kernel
      have hl : raw5932step1Labels = raw5932step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5932step0 raw5932step0Labels permutation32 permutation3
    _ = mixedMoment B node1006 node1006Labels := by rfl

def raw5933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5933Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5933step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5933step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw5933step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5933 raw5933Labels = mixedMoment B node2405 node2405Labels := by
  calc
    mixedMoment B raw5933 raw5933Labels = mixedMoment B raw5933step0 raw5933step0Labels := by
      have hz : ∀ j, raw5933 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5933step0 = (fun i j => raw5933 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5933step0 raw5933; decide +kernel
      have hl : raw5933step0Labels = raw5933Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5933 raw5933Labels permutation434 hz
    mixedMoment B raw5933step0 raw5933step0Labels = mixedMoment B raw5933step1 raw5933step1Labels := by
      have ha : raw5933step1 = (fun i j => raw5933step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5933step1 raw5933step0; decide +kernel
      have hl : raw5933step1Labels = raw5933step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5933step0 raw5933step0Labels permutation32 permutation3
    _ = mixedMoment B node2405 node2405Labels := by rfl

def raw5934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5934Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5934step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw5934step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5934 raw5934Labels = mixedMoment B node2463 node2463Labels := by
  calc
    mixedMoment B raw5934 raw5934Labels = mixedMoment B raw5934step0 raw5934step0Labels := by
      have ha : raw5934step0 = (fun i j => raw5934 (permutation200 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5934step0 raw5934; decide +kernel
      have hl : raw5934step0Labels = raw5934Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5934 raw5934Labels permutation200 permutation3
    _ = mixedMoment B node2463 node2463Labels := by rfl

def raw5935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw5935Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![2, 0, -2]]
def raw5935step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5935step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw5935step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5935 raw5935Labels = mixedMoment B node2732 node2732Labels := by
  calc
    mixedMoment B raw5935 raw5935Labels = mixedMoment B raw5935step0 raw5935step0Labels := by
      have hz : ∀ j, raw5935 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5935step0 = (fun i j => raw5935 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5935step0 raw5935; decide +kernel
      have hl : raw5935step0Labels = raw5935Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5935 raw5935Labels permutation434 hz
    mixedMoment B raw5935step0 raw5935step0Labels = mixedMoment B raw5935step1 raw5935step1Labels := by
      have ha : raw5935step1 = (fun i j => raw5935step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5935step1 raw5935step0; decide +kernel
      have hl : raw5935step1Labels = raw5935step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5935step0 raw5935step0Labels permutation34 permutation3
    _ = mixedMoment B node2732 node2732Labels := by rfl

def raw5936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2]]
def raw5936Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -3, 2], ![1, 1, -2]]
def raw5936step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5936step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw5936step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5936 raw5936Labels = mixedMoment B node2735 node2735Labels := by
  calc
    mixedMoment B raw5936 raw5936Labels = mixedMoment B raw5936step0 raw5936step0Labels := by
      have hz : ∀ j, raw5936 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5936step0 = (fun i j => raw5936 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5936step0 raw5936; decide +kernel
      have hl : raw5936step0Labels = raw5936Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5936 raw5936Labels permutation434 hz
    mixedMoment B raw5936step0 raw5936step0Labels = mixedMoment B raw5936step1 raw5936step1Labels := by
      have ha : raw5936step1 = (fun i j => raw5936step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5936step1 raw5936step0; decide +kernel
      have hl : raw5936step1Labels = raw5936step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5936step0 raw5936step0Labels permutation36 permutation3
    _ = mixedMoment B node2735 node2735Labels := by rfl

def raw5937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5937Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5937step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5937step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw5937step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5937 raw5937Labels = mixedMoment B node1006 node1006Labels := by
  calc
    mixedMoment B raw5937 raw5937Labels = mixedMoment B raw5937step0 raw5937step0Labels := by
      have hz : ∀ j, raw5937 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5937step0 = (fun i j => raw5937 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5937step0 raw5937; decide +kernel
      have hl : raw5937step0Labels = raw5937Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5937 raw5937Labels permutation346 hz
    mixedMoment B raw5937step0 raw5937step0Labels = mixedMoment B raw5937step1 raw5937step1Labels := by
      have ha : raw5937step1 = (fun i j => raw5937step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5937step1 raw5937step0; decide +kernel
      have hl : raw5937step1Labels = raw5937step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5937step0 raw5937step0Labels permutation32 permutation3
    _ = mixedMoment B node1006 node1006Labels := by rfl

def raw5938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5938Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5938step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5938step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw5938step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5938 raw5938Labels = mixedMoment B node2405 node2405Labels := by
  calc
    mixedMoment B raw5938 raw5938Labels = mixedMoment B raw5938step0 raw5938step0Labels := by
      have hz : ∀ j, raw5938 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5938step0 = (fun i j => raw5938 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5938step0 raw5938; decide +kernel
      have hl : raw5938step0Labels = raw5938Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5938 raw5938Labels permutation346 hz
    mixedMoment B raw5938step0 raw5938step0Labels = mixedMoment B raw5938step1 raw5938step1Labels := by
      have ha : raw5938step1 = (fun i j => raw5938step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5938step1 raw5938step0; decide +kernel
      have hl : raw5938step1Labels = raw5938step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5938step0 raw5938step0Labels permutation32 permutation3
    _ = mixedMoment B node2405 node2405Labels := by rfl

def raw5939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5939Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5939step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw5939step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5939 raw5939Labels = mixedMoment B node2463 node2463Labels := by
  calc
    mixedMoment B raw5939 raw5939Labels = mixedMoment B raw5939step0 raw5939step0Labels := by
      have ha : raw5939step0 = (fun i j => raw5939 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5939step0 raw5939; decide +kernel
      have hl : raw5939step0Labels = raw5939Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5939 raw5939Labels permutation176 permutation3
    _ = mixedMoment B node2463 node2463Labels := by rfl

def raw5940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![2, 0, -2]]
def raw5940Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![2, 0, -2]]
def raw5940step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5940step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw5940step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5940 raw5940Labels = mixedMoment B node2732 node2732Labels := by
  calc
    mixedMoment B raw5940 raw5940Labels = mixedMoment B raw5940step0 raw5940step0Labels := by
      have hz : ∀ j, raw5940 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5940step0 = (fun i j => raw5940 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5940step0 raw5940; decide +kernel
      have hl : raw5940step0Labels = raw5940Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5940 raw5940Labels permutation346 hz
    mixedMoment B raw5940step0 raw5940step0Labels = mixedMoment B raw5940step1 raw5940step1Labels := by
      have ha : raw5940step1 = (fun i j => raw5940step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5940step1 raw5940step0; decide +kernel
      have hl : raw5940step1Labels = raw5940step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5940step0 raw5940step0Labels permutation34 permutation3
    _ = mixedMoment B node2732 node2732Labels := by rfl

def raw5941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -3, 2], ![1, 1, -2]]
def raw5941Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -3, 2], ![1, 1, -2]]
def raw5941step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5941step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw5941step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5941 raw5941Labels = mixedMoment B node2735 node2735Labels := by
  calc
    mixedMoment B raw5941 raw5941Labels = mixedMoment B raw5941step0 raw5941step0Labels := by
      have hz : ∀ j, raw5941 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5941step0 = (fun i j => raw5941 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5941step0 raw5941; decide +kernel
      have hl : raw5941step0Labels = raw5941Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5941 raw5941Labels permutation346 hz
    mixedMoment B raw5941step0 raw5941step0Labels = mixedMoment B raw5941step1 raw5941step1Labels := by
      have ha : raw5941step1 = (fun i j => raw5941step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5941step1 raw5941step0; decide +kernel
      have hl : raw5941step1Labels = raw5941step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5941step0 raw5941step0Labels permutation36 permutation3
    _ = mixedMoment B node2735 node2735Labels := by rfl

def raw5942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -4, 2], ![2, 0, -2]]
def raw5942Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![2, -4, 2], ![2, 0, -2]]
def raw5942step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5942step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![2, -4, 2], ![2, 0, -2]]
def raw5942step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5942step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -2, 0], ![2, 2, -4]]
def raw5942step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5942 raw5942Labels = mixedMoment B node1011 node1011Labels := by
  calc
    mixedMoment B raw5942 raw5942Labels = mixedMoment B raw5942step0 raw5942step0Labels := by
      have hz : ∀ j, raw5942 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5942step0 = (fun i j => raw5942 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5942step0 raw5942; decide +kernel
      have hl : raw5942step0Labels = raw5942Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5942 raw5942Labels permutation434 hz
    mixedMoment B raw5942step0 raw5942step0Labels = mixedMoment B raw5942step1 raw5942step1Labels := by
      have hz : ∀ j, raw5942step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5942step1 = (fun i j => raw5942step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5942step1 raw5942step0; decide +kernel
      have hl : raw5942step1Labels = raw5942step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5942step0 raw5942step0Labels permutation80 hz
    mixedMoment B raw5942step1 raw5942step1Labels = mixedMoment B raw5942step2 raw5942step2Labels := by
      have ha : raw5942step2 = (fun i j => raw5942step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5942step2 raw5942step1; decide +kernel
      have hl : raw5942step2Labels = raw5942step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5942step1 raw5942step1Labels permutation9 permutation3
    _ = mixedMoment B node1011 node1011Labels := by rfl

def raw5943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -4, 2], ![2, 0, -2]]
def raw5943Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![2, -4, 2], ![2, 0, -2]]
def raw5943step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5943step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![2, -4, 2], ![2, 0, -2]]
def raw5943step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5943step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![2, -2, 0], ![2, 2, -4]]
def raw5943step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5943 raw5943Labels = mixedMoment B node2409 node2409Labels := by
  calc
    mixedMoment B raw5943 raw5943Labels = mixedMoment B raw5943step0 raw5943step0Labels := by
      have hz : ∀ j, raw5943 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5943step0 = (fun i j => raw5943 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5943step0 raw5943; decide +kernel
      have hl : raw5943step0Labels = raw5943Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5943 raw5943Labels permutation434 hz
    mixedMoment B raw5943step0 raw5943step0Labels = mixedMoment B raw5943step1 raw5943step1Labels := by
      have hz : ∀ j, raw5943step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5943step1 = (fun i j => raw5943step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5943step1 raw5943step0; decide +kernel
      have hl : raw5943step1Labels = raw5943step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5943step0 raw5943step0Labels permutation80 hz
    mixedMoment B raw5943step1 raw5943step1Labels = mixedMoment B raw5943step2 raw5943step2Labels := by
      have ha : raw5943step2 = (fun i j => raw5943step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5943step2 raw5943step1; decide +kernel
      have hl : raw5943step2Labels = raw5943step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5943step1 raw5943step1Labels permutation9 permutation3
    _ = mixedMoment B node2409 node2409Labels := by rfl

def raw5944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -4, 2], ![2, 0, -2]]
def raw5944Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![2, -4, 2], ![2, 0, -2]]
def raw5944step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5944step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 2, -4]]
def raw5944step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5944 raw5944Labels = mixedMoment B node2466 node2466Labels := by
  calc
    mixedMoment B raw5944 raw5944Labels = mixedMoment B raw5944step0 raw5944step0Labels := by
      have hz : ∀ j, raw5944 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5944step0 = (fun i j => raw5944 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5944step0 raw5944; decide +kernel
      have hl : raw5944step0Labels = raw5944Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5944 raw5944Labels permutation434 hz
    mixedMoment B raw5944step0 raw5944step0Labels = mixedMoment B raw5944step1 raw5944step1Labels := by
      have ha : raw5944step1 = (fun i j => raw5944step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5944step1 raw5944step0; decide +kernel
      have hl : raw5944step1Labels = raw5944step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5944step0 raw5944step0Labels permutation39 permutation3
    _ = mixedMoment B node2466 node2466Labels := by rfl

def raw5945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -4, 2], ![2, 0, -2]]
def raw5945Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![2, -4, 2], ![2, 0, -2]]
def raw5945step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5945step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -2, 0], ![2, 2, -4]]
def raw5945step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5945 raw5945Labels = mixedMoment B node2466 node2466Labels := by
  calc
    mixedMoment B raw5945 raw5945Labels = mixedMoment B raw5945step0 raw5945step0Labels := by
      have hz : ∀ j, raw5945 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5945step0 = (fun i j => raw5945 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5945step0 raw5945; decide +kernel
      have hl : raw5945step0Labels = raw5945Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5945 raw5945Labels permutation346 hz
    mixedMoment B raw5945step0 raw5945step0Labels = mixedMoment B raw5945step1 raw5945step1Labels := by
      have ha : raw5945step1 = (fun i j => raw5945step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5945step1 raw5945step0; decide +kernel
      have hl : raw5945step1Labels = raw5945step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5945step0 raw5945step0Labels permutation39 permutation3
    _ = mixedMoment B node2466 node2466Labels := by rfl

def raw5946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -4, 2], ![1, 1, -2]]
def raw5946Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![2, -4, 2], ![1, 1, -2]]
def raw5946step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5946step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![2, -4, 2], ![1, 1, -2]]
def raw5946step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5946step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw5946step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5946 raw5946Labels = mixedMoment B node2737 node2737Labels := by
  calc
    mixedMoment B raw5946 raw5946Labels = mixedMoment B raw5946step0 raw5946step0Labels := by
      have hz : ∀ j, raw5946 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5946step0 = (fun i j => raw5946 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5946step0 raw5946; decide +kernel
      have hl : raw5946step0Labels = raw5946Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5946 raw5946Labels permutation434 hz
    mixedMoment B raw5946step0 raw5946step0Labels = mixedMoment B raw5946step1 raw5946step1Labels := by
      have hz : ∀ j, raw5946step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5946step1 = (fun i j => raw5946step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5946step1 raw5946step0; decide +kernel
      have hl : raw5946step1Labels = raw5946step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5946step0 raw5946step0Labels permutation80 hz
    mixedMoment B raw5946step1 raw5946step1Labels = mixedMoment B raw5946step2 raw5946step2Labels := by
      have ha : raw5946step2 = (fun i j => raw5946step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5946step2 raw5946step1; decide +kernel
      have hl : raw5946step2Labels = raw5946step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5946step1 raw5946step1Labels permutation9 permutation3
    _ = mixedMoment B node2737 node2737Labels := by rfl

def raw5947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![3, -1, -2]]
def raw5947Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![3, -1, -2]]
def raw5947step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5947step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -3, 2], ![3, -1, -2]]
def raw5947step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5947step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw5947step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5947 raw5947Labels = mixedMoment B node1010 node1010Labels := by
  calc
    mixedMoment B raw5947 raw5947Labels = mixedMoment B raw5947step0 raw5947step0Labels := by
      have hz : ∀ j, raw5947 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5947step0 = (fun i j => raw5947 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5947step0 raw5947; decide +kernel
      have hl : raw5947step0Labels = raw5947Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5947 raw5947Labels permutation434 hz
    mixedMoment B raw5947step0 raw5947step0Labels = mixedMoment B raw5947step1 raw5947step1Labels := by
      have hz : ∀ j, raw5947step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5947step1 = (fun i j => raw5947step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5947step1 raw5947step0; decide +kernel
      have hl : raw5947step1Labels = raw5947step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5947step0 raw5947step0Labels permutation80 hz
    mixedMoment B raw5947step1 raw5947step1Labels = mixedMoment B raw5947step2 raw5947step2Labels := by
      have ha : raw5947step2 = (fun i j => raw5947step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5947step2 raw5947step1; decide +kernel
      have hl : raw5947step2Labels = raw5947step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5947step1 raw5947step1Labels permutation8 permutation3
    _ = mixedMoment B node1010 node1010Labels := by rfl

def raw5948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![3, -1, -2]]
def raw5948Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![3, -1, -2]]
def raw5948step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5948step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -3, 2], ![3, -1, -2]]
def raw5948step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5948step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 2, -3], ![3, -2, -1]]
def raw5948step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5948 raw5948Labels = mixedMoment B node2408 node2408Labels := by
  calc
    mixedMoment B raw5948 raw5948Labels = mixedMoment B raw5948step0 raw5948step0Labels := by
      have hz : ∀ j, raw5948 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5948step0 = (fun i j => raw5948 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5948step0 raw5948; decide +kernel
      have hl : raw5948step0Labels = raw5948Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5948 raw5948Labels permutation434 hz
    mixedMoment B raw5948step0 raw5948step0Labels = mixedMoment B raw5948step1 raw5948step1Labels := by
      have hz : ∀ j, raw5948step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5948step1 = (fun i j => raw5948step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5948step1 raw5948step0; decide +kernel
      have hl : raw5948step1Labels = raw5948step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5948step0 raw5948step0Labels permutation80 hz
    mixedMoment B raw5948step1 raw5948step1Labels = mixedMoment B raw5948step2 raw5948step2Labels := by
      have ha : raw5948step2 = (fun i j => raw5948step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5948step2 raw5948step1; decide +kernel
      have hl : raw5948step2Labels = raw5948step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5948step1 raw5948step1Labels permutation8 permutation3
    _ = mixedMoment B node2408 node2408Labels := by rfl

def raw5949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![3, -1, -2]]
def raw5949Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -3, 2], ![3, -1, -2]]
def raw5949step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5949step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw5949step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5949 raw5949Labels = mixedMoment B node2465 node2465Labels := by
  calc
    mixedMoment B raw5949 raw5949Labels = mixedMoment B raw5949step0 raw5949step0Labels := by
      have hz : ∀ j, raw5949 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5949step0 = (fun i j => raw5949 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5949step0 raw5949; decide +kernel
      have hl : raw5949step0Labels = raw5949Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5949 raw5949Labels permutation434 hz
    mixedMoment B raw5949step0 raw5949step0Labels = mixedMoment B raw5949step1 raw5949step1Labels := by
      have ha : raw5949step1 = (fun i j => raw5949step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5949step1 raw5949step0; decide +kernel
      have hl : raw5949step1Labels = raw5949step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5949step0 raw5949step0Labels permutation38 permutation3
    _ = mixedMoment B node2465 node2465Labels := by rfl

def raw5950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![3, -1, -2]]
def raw5950Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -3, 2], ![3, -1, -2]]
def raw5950step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5950step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 2, -3], ![3, -2, -1]]
def raw5950step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5950 raw5950Labels = mixedMoment B node2465 node2465Labels := by
  calc
    mixedMoment B raw5950 raw5950Labels = mixedMoment B raw5950step0 raw5950step0Labels := by
      have hz : ∀ j, raw5950 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5950step0 = (fun i j => raw5950 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5950step0 raw5950; decide +kernel
      have hl : raw5950step0Labels = raw5950Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5950 raw5950Labels permutation346 hz
    mixedMoment B raw5950step0 raw5950step0Labels = mixedMoment B raw5950step1 raw5950step1Labels := by
      have ha : raw5950step1 = (fun i j => raw5950step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5950step1 raw5950step0; decide +kernel
      have hl : raw5950step1Labels = raw5950step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5950step0 raw5950step0Labels permutation38 permutation3
    _ = mixedMoment B node2465 node2465Labels := by rfl

def raw5951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw5951Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw5951step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5951step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![3, -1, -2]]
def raw5951step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5951step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw5951step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5951 raw5951Labels = mixedMoment B node2734 node2734Labels := by
  calc
    mixedMoment B raw5951 raw5951Labels = mixedMoment B raw5951step0 raw5951step0Labels := by
      have hz : ∀ j, raw5951 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5951step0 = (fun i j => raw5951 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5951step0 raw5951; decide +kernel
      have hl : raw5951step0Labels = raw5951Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5951 raw5951Labels permutation434 hz
    mixedMoment B raw5951step0 raw5951step0Labels = mixedMoment B raw5951step1 raw5951step1Labels := by
      have hz : ∀ j, raw5951step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5951step1 = (fun i j => raw5951step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5951step1 raw5951step0; decide +kernel
      have hl : raw5951step1Labels = raw5951step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5951step0 raw5951step0Labels permutation80 hz
    mixedMoment B raw5951step1 raw5951step1Labels = mixedMoment B raw5951step2 raw5951step2Labels := by
      have ha : raw5951step2 = (fun i j => raw5951step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5951step2 raw5951step1; decide +kernel
      have hl : raw5951step2Labels = raw5951step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5951step1 raw5951step1Labels permutation8 permutation3
    _ = mixedMoment B node2734 node2734Labels := by rfl

def raw5952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5952Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5952step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5952step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -3, 2], ![2, 0, -2]]
def raw5952step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5952step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw5952step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5952step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw5952step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5952 raw5952Labels = mixedMoment B node3055 node3055Labels := by
  calc
    mixedMoment B raw5952 raw5952Labels = mixedMoment B raw5952step0 raw5952step0Labels := by
      have hz : ∀ j, raw5952 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5952step0 = (fun i j => raw5952 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5952step0 raw5952; decide +kernel
      have hl : raw5952step0Labels = raw5952Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5952 raw5952Labels permutation434 hz
    mixedMoment B raw5952step0 raw5952step0Labels = mixedMoment B raw5952step1 raw5952step1Labels := by
      have hz : ∀ j, raw5952step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5952step1 = (fun i j => raw5952step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5952step1 raw5952step0; decide +kernel
      have hl : raw5952step1Labels = raw5952step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5952step0 raw5952step0Labels permutation80 hz
    mixedMoment B raw5952step1 raw5952step1Labels = mixedMoment B raw5952step2 raw5952step2Labels := by
      have ha : raw5952step2 = (fun i j => raw5952step1 (permutation24 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5952step2 raw5952step1; decide +kernel
      have hl : raw5952step2Labels = raw5952step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5952step1 raw5952step1Labels permutation24 permutation5
    mixedMoment B raw5952step2 raw5952step2Labels = mixedMoment B raw5952step3 raw5952step3Labels := by
      have ha : raw5952step3 = raw5952step2 := by apply Matrix.ext; unfold raw5952step3 raw5952step2; decide +kernel
      have hl : raw5952step2Labels = labelEmbedding1 ∘ raw5952step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5952step2 raw5952step2Labels raw5952step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3055 node3055Labels := by rfl

def raw5953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5953Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5953step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5953step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw5953step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5953step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw5953step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5953 raw5953Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw5953 raw5953Labels = mixedMoment B raw5953step0 raw5953step0Labels := by
      have hz : ∀ j, raw5953 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5953step0 = (fun i j => raw5953 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5953step0 raw5953; decide +kernel
      have hl : raw5953step0Labels = raw5953Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5953 raw5953Labels permutation434 hz
    mixedMoment B raw5953step0 raw5953step0Labels = mixedMoment B raw5953step1 raw5953step1Labels := by
      have ha : raw5953step1 = (fun i j => raw5953step0 (permutation125 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5953step1 raw5953step0; decide +kernel
      have hl : raw5953step1Labels = raw5953step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5953step0 raw5953step0Labels permutation125 permutation5
    mixedMoment B raw5953step1 raw5953step1Labels = mixedMoment B raw5953step2 raw5953step2Labels := by
      have ha : raw5953step2 = raw5953step1 := by apply Matrix.ext; unfold raw5953step2 raw5953step1; decide +kernel
      have hl : raw5953step1Labels = labelEmbedding1 ∘ raw5953step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5953step1 raw5953step1Labels raw5953step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3051 node3051Labels := by rfl

def raw5954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5954Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5954step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5954step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5954step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw5954step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5954step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw5954step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5954 raw5954Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw5954 raw5954Labels = mixedMoment B raw5954step0 raw5954step0Labels := by
      have hz : ∀ j, raw5954 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5954step0 = (fun i j => raw5954 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5954step0 raw5954; decide +kernel
      have hl : raw5954step0Labels = raw5954Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5954 raw5954Labels permutation346 hz
    mixedMoment B raw5954step0 raw5954step0Labels = mixedMoment B raw5954step1 raw5954step1Labels := by
      have ha : raw5954step1 = (fun i j => raw5954step0 (permutation125 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5954step1 raw5954step0; decide +kernel
      have hl : raw5954step1Labels = raw5954step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5954step0 raw5954step0Labels permutation125 permutation5
    mixedMoment B raw5954step1 raw5954step1Labels = mixedMoment B raw5954step2 raw5954step2Labels := by
      have ha : raw5954step2 = raw5954step1 := by apply Matrix.ext; unfold raw5954step2 raw5954step1; decide +kernel
      have hl : raw5954step1Labels = labelEmbedding1 ∘ raw5954step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5954step1 raw5954step1Labels raw5954step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3051 node3051Labels := by rfl

def raw5955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw5955Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5955step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw5955step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5955step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2]]
def raw5955step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5955step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5955step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5955step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5955step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5955 raw5955Labels = mixedMoment B node3862 node3862Labels := by
  calc
    mixedMoment B raw5955 raw5955Labels = mixedMoment B raw5955step0 raw5955step0Labels := by
      have hz : ∀ j, raw5955 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5955step0 = (fun i j => raw5955 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5955step0 raw5955; decide +kernel
      have hl : raw5955step0Labels = raw5955Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5955 raw5955Labels permutation434 hz
    mixedMoment B raw5955step0 raw5955step0Labels = mixedMoment B raw5955step1 raw5955step1Labels := by
      have hz : ∀ j, raw5955step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5955step1 = (fun i j => raw5955step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5955step1 raw5955step0; decide +kernel
      have hl : raw5955step1Labels = raw5955step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5955step0 raw5955step0Labels permutation80 hz
    mixedMoment B raw5955step1 raw5955step1Labels = mixedMoment B raw5955step2 raw5955step2Labels := by
      have ha : raw5955step2 = (fun i j => raw5955step1 (permutation28 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5955step2 raw5955step1; decide +kernel
      have hl : raw5955step2Labels = raw5955step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5955step1 raw5955step1Labels permutation28 permutation7
    mixedMoment B raw5955step2 raw5955step2Labels = mixedMoment B raw5955step3 raw5955step3Labels := by
      have ha : raw5955step3 = raw5955step2 := by apply Matrix.ext; unfold raw5955step3 raw5955step2; decide +kernel
      have hl : raw5955step2Labels = labelEmbedding1 ∘ raw5955step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5955step2 raw5955step2Labels raw5955step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3862 node3862Labels := by rfl

def raw5956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2]]
def raw5956Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2]]
def raw5956step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5956step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2]]
def raw5956step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5956step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw5956step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5956step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw5956step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5956 raw5956Labels = mixedMoment B node3119 node3119Labels := by
  calc
    mixedMoment B raw5956 raw5956Labels = mixedMoment B raw5956step0 raw5956step0Labels := by
      have hz : ∀ j, raw5956 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5956step0 = (fun i j => raw5956 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5956step0 raw5956; decide +kernel
      have hl : raw5956step0Labels = raw5956Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5956 raw5956Labels permutation434 hz
    mixedMoment B raw5956step0 raw5956step0Labels = mixedMoment B raw5956step1 raw5956step1Labels := by
      have hz : ∀ j, raw5956step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5956step1 = (fun i j => raw5956step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5956step1 raw5956step0; decide +kernel
      have hl : raw5956step1Labels = raw5956step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5956step0 raw5956step0Labels permutation80 hz
    mixedMoment B raw5956step1 raw5956step1Labels = mixedMoment B raw5956step2 raw5956step2Labels := by
      have ha : raw5956step2 = (fun i j => raw5956step1 (permutation25 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5956step2 raw5956step1; decide +kernel
      have hl : raw5956step2Labels = raw5956step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5956step1 raw5956step1Labels permutation25 permutation5
    mixedMoment B raw5956step2 raw5956step2Labels = mixedMoment B raw5956step3 raw5956step3Labels := by
      have ha : raw5956step3 = raw5956step2 := by apply Matrix.ext; unfold raw5956step3 raw5956step2; decide +kernel
      have hl : raw5956step2Labels = labelEmbedding1 ∘ raw5956step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5956step2 raw5956step2Labels raw5956step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3119 node3119Labels := by rfl

def raw5957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5957Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5957step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5957step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, -3, 2], ![2, 0, -2]]
def raw5957step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5957step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw5957step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5957step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw5957step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5957step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw5957step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5957 raw5957Labels = mixedMoment B node1716 node1716Labels := by
  calc
    mixedMoment B raw5957 raw5957Labels = mixedMoment B raw5957step0 raw5957step0Labels := by
      have hz : ∀ j, raw5957 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5957step0 = (fun i j => raw5957 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5957step0 raw5957; decide +kernel
      have hl : raw5957step0Labels = raw5957Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5957 raw5957Labels permutation434 hz
    mixedMoment B raw5957step0 raw5957step0Labels = mixedMoment B raw5957step1 raw5957step1Labels := by
      have hz : ∀ j, raw5957step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5957step1 = (fun i j => raw5957step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5957step1 raw5957step0; decide +kernel
      have hl : raw5957step1Labels = raw5957step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5957step0 raw5957step0Labels permutation80 hz
    mixedMoment B raw5957step1 raw5957step1Labels = mixedMoment B raw5957step2 raw5957step2Labels := by
      have ha : raw5957step2 = (fun i j => raw5957step1 (permutation9 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5957step2 raw5957step1; decide +kernel
      have hl : raw5957step2Labels = raw5957step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5957step1 raw5957step1Labels permutation9 permutation5
    mixedMoment B raw5957step2 raw5957step2Labels = mixedMoment B raw5957step3 raw5957step3Labels := by
      have ha : raw5957step3 = -raw5957step2 := by apply Matrix.ext; change ∀ i j, raw5957step3 i j = -(raw5957step2 i j); unfold raw5957step3 raw5957step2; decide +kernel
      have hl : raw5957step3Labels = raw5957step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5957step3 raw5957step3Labels = mixedMoment B raw5957step4 raw5957step4Labels := by
      have ha : raw5957step4 = raw5957step3 := by apply Matrix.ext; unfold raw5957step4 raw5957step3; decide +kernel
      have hl : raw5957step3Labels = labelEmbedding1 ∘ raw5957step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5957step3 raw5957step3Labels raw5957step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1716 node1716Labels := by rfl

def raw5958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5958Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5958step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5958step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw5958step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5958step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw5958step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5958 raw5958Labels = mixedMoment B node3024 node3024Labels := by
  calc
    mixedMoment B raw5958 raw5958Labels = mixedMoment B raw5958step0 raw5958step0Labels := by
      have hz : ∀ j, raw5958 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5958step0 = (fun i j => raw5958 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5958step0 raw5958; decide +kernel
      have hl : raw5958step0Labels = raw5958Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5958 raw5958Labels permutation434 hz
    mixedMoment B raw5958step0 raw5958step0Labels = mixedMoment B raw5958step1 raw5958step1Labels := by
      have ha : raw5958step1 = (fun i j => raw5958step0 (permutation125 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5958step1 raw5958step0; decide +kernel
      have hl : raw5958step1Labels = raw5958step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5958step0 raw5958step0Labels permutation125 permutation5
    mixedMoment B raw5958step1 raw5958step1Labels = mixedMoment B raw5958step2 raw5958step2Labels := by
      have ha : raw5958step2 = raw5958step1 := by apply Matrix.ext; unfold raw5958step2 raw5958step1; decide +kernel
      have hl : raw5958step1Labels = labelEmbedding1 ∘ raw5958step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5958step1 raw5958step1Labels raw5958step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3024 node3024Labels := by rfl

def raw5959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5959Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5959step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5959step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5959step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw5959step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5959step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw5959step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5959 raw5959Labels = mixedMoment B node3024 node3024Labels := by
  calc
    mixedMoment B raw5959 raw5959Labels = mixedMoment B raw5959step0 raw5959step0Labels := by
      have hz : ∀ j, raw5959 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5959step0 = (fun i j => raw5959 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5959step0 raw5959; decide +kernel
      have hl : raw5959step0Labels = raw5959Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5959 raw5959Labels permutation346 hz
    mixedMoment B raw5959step0 raw5959step0Labels = mixedMoment B raw5959step1 raw5959step1Labels := by
      have ha : raw5959step1 = (fun i j => raw5959step0 (permutation125 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5959step1 raw5959step0; decide +kernel
      have hl : raw5959step1Labels = raw5959step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5959step0 raw5959step0Labels permutation125 permutation5
    mixedMoment B raw5959step1 raw5959step1Labels = mixedMoment B raw5959step2 raw5959step2Labels := by
      have ha : raw5959step2 = raw5959step1 := by apply Matrix.ext; unfold raw5959step2 raw5959step1; decide +kernel
      have hl : raw5959step1Labels = labelEmbedding1 ∘ raw5959step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5959step1 raw5959step1Labels raw5959step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3024 node3024Labels := by rfl

def raw5960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw5960Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw5960step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5960step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![2, 0, -2]]
def raw5960step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5960step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0]]
def raw5960step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5960step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw5960step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5960step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw5960step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5960 raw5960Labels = mixedMoment B node3626 node3626Labels := by
  calc
    mixedMoment B raw5960 raw5960Labels = mixedMoment B raw5960step0 raw5960step0Labels := by
      have hz : ∀ j, raw5960 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5960step0 = (fun i j => raw5960 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5960step0 raw5960; decide +kernel
      have hl : raw5960step0Labels = raw5960Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5960 raw5960Labels permutation434 hz
    mixedMoment B raw5960step0 raw5960step0Labels = mixedMoment B raw5960step1 raw5960step1Labels := by
      have hz : ∀ j, raw5960step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5960step1 = (fun i j => raw5960step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5960step1 raw5960step0; decide +kernel
      have hl : raw5960step1Labels = raw5960step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5960step0 raw5960step0Labels permutation80 hz
    mixedMoment B raw5960step1 raw5960step1Labels = mixedMoment B raw5960step2 raw5960step2Labels := by
      have ha : raw5960step2 = (fun i j => raw5960step1 (permutation9 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5960step2 raw5960step1; decide +kernel
      have hl : raw5960step2Labels = raw5960step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5960step1 raw5960step1Labels permutation9 permutation5
    mixedMoment B raw5960step2 raw5960step2Labels = mixedMoment B raw5960step3 raw5960step3Labels := by
      have ha : raw5960step3 = -raw5960step2 := by apply Matrix.ext; change ∀ i j, raw5960step3 i j = -(raw5960step2 i j); unfold raw5960step3 raw5960step2; decide +kernel
      have hl : raw5960step3Labels = raw5960step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5960step3 raw5960step3Labels = mixedMoment B raw5960step4 raw5960step4Labels := by
      have ha : raw5960step4 = raw5960step3 := by apply Matrix.ext; unfold raw5960step4 raw5960step3; decide +kernel
      have hl : raw5960step3Labels = labelEmbedding1 ∘ raw5960step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5960step3 raw5960step3Labels raw5960step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3626 node3626Labels := by rfl

def raw5961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2]]
def raw5961Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2]]
def raw5961step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5961step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![1, -3, 2], ![1, 1, -2]]
def raw5961step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5961step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw5961step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5961step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw5961step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5961 raw5961Labels = mixedMoment B node3098 node3098Labels := by
  calc
    mixedMoment B raw5961 raw5961Labels = mixedMoment B raw5961step0 raw5961step0Labels := by
      have hz : ∀ j, raw5961 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5961step0 = (fun i j => raw5961 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5961step0 raw5961; decide +kernel
      have hl : raw5961step0Labels = raw5961Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5961 raw5961Labels permutation434 hz
    mixedMoment B raw5961step0 raw5961step0Labels = mixedMoment B raw5961step1 raw5961step1Labels := by
      have hz : ∀ j, raw5961step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5961step1 = (fun i j => raw5961step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5961step1 raw5961step0; decide +kernel
      have hl : raw5961step1Labels = raw5961step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5961step0 raw5961step0Labels permutation80 hz
    mixedMoment B raw5961step1 raw5961step1Labels = mixedMoment B raw5961step2 raw5961step2Labels := by
      have ha : raw5961step2 = (fun i j => raw5961step1 (permutation23 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5961step2 raw5961step1; decide +kernel
      have hl : raw5961step2Labels = raw5961step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5961step1 raw5961step1Labels permutation23 permutation5
    mixedMoment B raw5961step2 raw5961step2Labels = mixedMoment B raw5961step3 raw5961step3Labels := by
      have ha : raw5961step3 = raw5961step2 := by apply Matrix.ext; unfold raw5961step3 raw5961step2; decide +kernel
      have hl : raw5961step2Labels = labelEmbedding1 ∘ raw5961step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5961step2 raw5961step2Labels raw5961step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3098 node3098Labels := by rfl

def raw5962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5962Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5962step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5962step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw5962step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5962step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw5962step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5962step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw5962step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5962 raw5962Labels = mixedMoment B node1610 node1610Labels := by
  calc
    mixedMoment B raw5962 raw5962Labels = mixedMoment B raw5962step0 raw5962step0Labels := by
      have hz : ∀ j, raw5962 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5962step0 = (fun i j => raw5962 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5962step0 raw5962; decide +kernel
      have hl : raw5962step0Labels = raw5962Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5962 raw5962Labels permutation434 hz
    mixedMoment B raw5962step0 raw5962step0Labels = mixedMoment B raw5962step1 raw5962step1Labels := by
      have ha : raw5962step1 = (fun i j => raw5962step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5962step1 raw5962step0; decide +kernel
      have hl : raw5962step1Labels = raw5962step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5962step0 raw5962step0Labels permutation36 permutation5
    mixedMoment B raw5962step1 raw5962step1Labels = mixedMoment B raw5962step2 raw5962step2Labels := by
      have ha : raw5962step2 = -raw5962step1 := by apply Matrix.ext; change ∀ i j, raw5962step2 i j = -(raw5962step1 i j); unfold raw5962step2 raw5962step1; decide +kernel
      have hl : raw5962step2Labels = raw5962step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5962step2 raw5962step2Labels = mixedMoment B raw5962step3 raw5962step3Labels := by
      have ha : raw5962step3 = raw5962step2 := by apply Matrix.ext; unfold raw5962step3 raw5962step2; decide +kernel
      have hl : raw5962step2Labels = labelEmbedding1 ∘ raw5962step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5962step2 raw5962step2Labels raw5962step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1610 node1610Labels := by rfl

def raw5963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5963Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5963step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5963step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw5963step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5963step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw5963step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5963 raw5963Labels = mixedMoment B node2910 node2910Labels := by
  calc
    mixedMoment B raw5963 raw5963Labels = mixedMoment B raw5963step0 raw5963step0Labels := by
      have hz : ∀ j, raw5963 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5963step0 = (fun i j => raw5963 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5963step0 raw5963; decide +kernel
      have hl : raw5963step0Labels = raw5963Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5963 raw5963Labels permutation434 hz
    mixedMoment B raw5963step0 raw5963step0Labels = mixedMoment B raw5963step1 raw5963step1Labels := by
      have ha : raw5963step1 = (fun i j => raw5963step0 (permutation121 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5963step1 raw5963step0; decide +kernel
      have hl : raw5963step1Labels = raw5963step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5963step0 raw5963step0Labels permutation121 permutation5
    mixedMoment B raw5963step1 raw5963step1Labels = mixedMoment B raw5963step2 raw5963step2Labels := by
      have ha : raw5963step2 = raw5963step1 := by apply Matrix.ext; unfold raw5963step2 raw5963step1; decide +kernel
      have hl : raw5963step1Labels = labelEmbedding1 ∘ raw5963step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5963step1 raw5963step1Labels raw5963step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2910 node2910Labels := by rfl

def raw5964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5964Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5964step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw5964step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5964step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw5964step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5964 raw5964Labels = mixedMoment B node2906 node2906Labels := by
  calc
    mixedMoment B raw5964 raw5964Labels = mixedMoment B raw5964step0 raw5964step0Labels := by
      have ha : raw5964step0 = (fun i j => raw5964 (permutation550 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5964step0 raw5964; decide +kernel
      have hl : raw5964step0Labels = raw5964Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5964 raw5964Labels permutation550 permutation5
    mixedMoment B raw5964step0 raw5964step0Labels = mixedMoment B raw5964step1 raw5964step1Labels := by
      have ha : raw5964step1 = raw5964step0 := by apply Matrix.ext; unfold raw5964step1 raw5964step0; decide +kernel
      have hl : raw5964step0Labels = labelEmbedding1 ∘ raw5964step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5964step0 raw5964step0Labels raw5964step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2906 node2906Labels := by rfl

def raw5965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw5965Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![2, 0, -2]]
def raw5965step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5965step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw5965step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5965step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw5965step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5965step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw5965step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5965 raw5965Labels = mixedMoment B node3541 node3541Labels := by
  calc
    mixedMoment B raw5965 raw5965Labels = mixedMoment B raw5965step0 raw5965step0Labels := by
      have hz : ∀ j, raw5965 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5965step0 = (fun i j => raw5965 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5965step0 raw5965; decide +kernel
      have hl : raw5965step0Labels = raw5965Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5965 raw5965Labels permutation434 hz
    mixedMoment B raw5965step0 raw5965step0Labels = mixedMoment B raw5965step1 raw5965step1Labels := by
      have ha : raw5965step1 = (fun i j => raw5965step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5965step1 raw5965step0; decide +kernel
      have hl : raw5965step1Labels = raw5965step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5965step0 raw5965step0Labels permutation36 permutation5
    mixedMoment B raw5965step1 raw5965step1Labels = mixedMoment B raw5965step2 raw5965step2Labels := by
      have ha : raw5965step2 = -raw5965step1 := by apply Matrix.ext; change ∀ i j, raw5965step2 i j = -(raw5965step1 i j); unfold raw5965step2 raw5965step1; decide +kernel
      have hl : raw5965step2Labels = raw5965step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5965step2 raw5965step2Labels = mixedMoment B raw5965step3 raw5965step3Labels := by
      have ha : raw5965step3 = raw5965step2 := by apply Matrix.ext; unfold raw5965step3 raw5965step2; decide +kernel
      have hl : raw5965step2Labels = labelEmbedding1 ∘ raw5965step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5965step2 raw5965step2Labels raw5965step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3541 node3541Labels := by rfl

def raw5966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2]]
def raw5966Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -3, 2], ![1, 1, -2]]
def raw5966step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5966step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw5966step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5966step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw5966step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5966 raw5966Labels = mixedMoment B node2952 node2952Labels := by
  calc
    mixedMoment B raw5966 raw5966Labels = mixedMoment B raw5966step0 raw5966step0Labels := by
      have hz : ∀ j, raw5966 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5966step0 = (fun i j => raw5966 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5966step0 raw5966; decide +kernel
      have hl : raw5966step0Labels = raw5966Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5966 raw5966Labels permutation434 hz
    mixedMoment B raw5966step0 raw5966step0Labels = mixedMoment B raw5966step1 raw5966step1Labels := by
      have ha : raw5966step1 = (fun i j => raw5966step0 (permutation121 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5966step1 raw5966step0; decide +kernel
      have hl : raw5966step1Labels = raw5966step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5966step0 raw5966step0Labels permutation121 permutation5
    mixedMoment B raw5966step1 raw5966step1Labels = mixedMoment B raw5966step2 raw5966step2Labels := by
      have ha : raw5966step2 = raw5966step1 := by apply Matrix.ext; unfold raw5966step2 raw5966step1; decide +kernel
      have hl : raw5966step1Labels = labelEmbedding1 ∘ raw5966step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5966step1 raw5966step1Labels raw5966step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2952 node2952Labels := by rfl

def raw5967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5967Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5967step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5967step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw5967step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5967step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw5967step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5967step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw5967step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5967 raw5967Labels = mixedMoment B node1610 node1610Labels := by
  calc
    mixedMoment B raw5967 raw5967Labels = mixedMoment B raw5967step0 raw5967step0Labels := by
      have hz : ∀ j, raw5967 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5967step0 = (fun i j => raw5967 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5967step0 raw5967; decide +kernel
      have hl : raw5967step0Labels = raw5967Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5967 raw5967Labels permutation346 hz
    mixedMoment B raw5967step0 raw5967step0Labels = mixedMoment B raw5967step1 raw5967step1Labels := by
      have ha : raw5967step1 = (fun i j => raw5967step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5967step1 raw5967step0; decide +kernel
      have hl : raw5967step1Labels = raw5967step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5967step0 raw5967step0Labels permutation36 permutation5
    mixedMoment B raw5967step1 raw5967step1Labels = mixedMoment B raw5967step2 raw5967step2Labels := by
      have ha : raw5967step2 = -raw5967step1 := by apply Matrix.ext; change ∀ i j, raw5967step2 i j = -(raw5967step1 i j); unfold raw5967step2 raw5967step1; decide +kernel
      have hl : raw5967step2Labels = raw5967step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5967step2 raw5967step2Labels = mixedMoment B raw5967step3 raw5967step3Labels := by
      have ha : raw5967step3 = raw5967step2 := by apply Matrix.ext; unfold raw5967step3 raw5967step2; decide +kernel
      have hl : raw5967step2Labels = labelEmbedding1 ∘ raw5967step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5967step2 raw5967step2Labels raw5967step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1610 node1610Labels := by rfl

def raw5968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5968Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5968step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5968step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5968step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw5968step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5968step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw5968step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5968 raw5968Labels = mixedMoment B node2910 node2910Labels := by
  calc
    mixedMoment B raw5968 raw5968Labels = mixedMoment B raw5968step0 raw5968step0Labels := by
      have hz : ∀ j, raw5968 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5968step0 = (fun i j => raw5968 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5968step0 raw5968; decide +kernel
      have hl : raw5968step0Labels = raw5968Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5968 raw5968Labels permutation346 hz
    mixedMoment B raw5968step0 raw5968step0Labels = mixedMoment B raw5968step1 raw5968step1Labels := by
      have ha : raw5968step1 = (fun i j => raw5968step0 (permutation121 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5968step1 raw5968step0; decide +kernel
      have hl : raw5968step1Labels = raw5968step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5968step0 raw5968step0Labels permutation121 permutation5
    mixedMoment B raw5968step1 raw5968step1Labels = mixedMoment B raw5968step2 raw5968step2Labels := by
      have ha : raw5968step2 = raw5968step1 := by apply Matrix.ext; unfold raw5968step2 raw5968step1; decide +kernel
      have hl : raw5968step1Labels = labelEmbedding1 ∘ raw5968step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5968step1 raw5968step1Labels raw5968step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2910 node2910Labels := by rfl

def raw5969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5969Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5969step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw5969step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5969step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw5969step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5969 raw5969Labels = mixedMoment B node2906 node2906Labels := by
  calc
    mixedMoment B raw5969 raw5969Labels = mixedMoment B raw5969step0 raw5969step0Labels := by
      have ha : raw5969step0 = (fun i j => raw5969 (permutation566 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5969step0 raw5969; decide +kernel
      have hl : raw5969step0Labels = raw5969Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5969 raw5969Labels permutation566 permutation5
    mixedMoment B raw5969step0 raw5969step0Labels = mixedMoment B raw5969step1 raw5969step1Labels := by
      have ha : raw5969step1 = raw5969step0 := by apply Matrix.ext; unfold raw5969step1 raw5969step0; decide +kernel
      have hl : raw5969step0Labels = labelEmbedding1 ∘ raw5969step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5969step0 raw5969step0Labels raw5969step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2906 node2906Labels := by rfl

def raw5970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![2, 0, -2]]
def raw5970Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![2, 0, -2]]
def raw5970step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw5970step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5970step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw5970step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5970step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw5970step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5970 raw5970Labels = mixedMoment B node3541 node3541Labels := by
  calc
    mixedMoment B raw5970 raw5970Labels = mixedMoment B raw5970step0 raw5970step0Labels := by
      have hz : ∀ j, raw5970 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5970step0 = (fun i j => raw5970 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5970step0 raw5970; decide +kernel
      have hl : raw5970step0Labels = raw5970Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5970 raw5970Labels permutation346 hz
    mixedMoment B raw5970step0 raw5970step0Labels = mixedMoment B raw5970step1 raw5970step1Labels := by
      have ha : raw5970step1 = (fun i j => raw5970step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5970step1 raw5970step0; decide +kernel
      have hl : raw5970step1Labels = raw5970step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5970step0 raw5970step0Labels permutation36 permutation5
    mixedMoment B raw5970step1 raw5970step1Labels = mixedMoment B raw5970step2 raw5970step2Labels := by
      have ha : raw5970step2 = -raw5970step1 := by apply Matrix.ext; change ∀ i j, raw5970step2 i j = -(raw5970step1 i j); unfold raw5970step2 raw5970step1; decide +kernel
      have hl : raw5970step2Labels = raw5970step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5970step2 raw5970step2Labels = mixedMoment B raw5970step3 raw5970step3Labels := by
      have ha : raw5970step3 = raw5970step2 := by apply Matrix.ext; unfold raw5970step3 raw5970step2; decide +kernel
      have hl : raw5970step2Labels = labelEmbedding1 ∘ raw5970step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5970step2 raw5970step2Labels raw5970step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3541 node3541Labels := by rfl

def raw5971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -3, 2], ![1, 1, -2]]
def raw5971Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -3, 2], ![1, 1, -2]]
def raw5971step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5971step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw5971step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5971step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw5971step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5971 raw5971Labels = mixedMoment B node2952 node2952Labels := by
  calc
    mixedMoment B raw5971 raw5971Labels = mixedMoment B raw5971step0 raw5971step0Labels := by
      have hz : ∀ j, raw5971 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5971step0 = (fun i j => raw5971 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5971step0 raw5971; decide +kernel
      have hl : raw5971step0Labels = raw5971Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5971 raw5971Labels permutation346 hz
    mixedMoment B raw5971step0 raw5971step0Labels = mixedMoment B raw5971step1 raw5971step1Labels := by
      have ha : raw5971step1 = (fun i j => raw5971step0 (permutation121 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5971step1 raw5971step0; decide +kernel
      have hl : raw5971step1Labels = raw5971step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5971step0 raw5971step0Labels permutation121 permutation5
    mixedMoment B raw5971step1 raw5971step1Labels = mixedMoment B raw5971step2 raw5971step2Labels := by
      have ha : raw5971step2 = raw5971step1 := by apply Matrix.ext; unfold raw5971step2 raw5971step1; decide +kernel
      have hl : raw5971step1Labels = labelEmbedding1 ∘ raw5971step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5971step1 raw5971step1Labels raw5971step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2952 node2952Labels := by rfl

def raw5972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -4, 2], ![2, 0, -2]]
def raw5972Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![2, -4, 2], ![2, 0, -2]]
def raw5972step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5972step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![2, -4, 2], ![2, 0, -2]]
def raw5972step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5972step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![3, 1, -4]]
def raw5972step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5972step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![3, 1, -4]]
def raw5972step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5972 raw5972Labels = mixedMoment B node1186 node1186Labels := by
  calc
    mixedMoment B raw5972 raw5972Labels = mixedMoment B raw5972step0 raw5972step0Labels := by
      have hz : ∀ j, raw5972 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5972step0 = (fun i j => raw5972 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5972step0 raw5972; decide +kernel
      have hl : raw5972step0Labels = raw5972Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5972 raw5972Labels permutation434 hz
    mixedMoment B raw5972step0 raw5972step0Labels = mixedMoment B raw5972step1 raw5972step1Labels := by
      have hz : ∀ j, raw5972step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5972step1 = (fun i j => raw5972step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5972step1 raw5972step0; decide +kernel
      have hl : raw5972step1Labels = raw5972step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5972step0 raw5972step0Labels permutation80 hz
    mixedMoment B raw5972step1 raw5972step1Labels = mixedMoment B raw5972step2 raw5972step2Labels := by
      have ha : raw5972step2 = (fun i j => raw5972step1 (permutation25 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5972step2 raw5972step1; decide +kernel
      have hl : raw5972step2Labels = raw5972step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5972step1 raw5972step1Labels permutation25 permutation5
    mixedMoment B raw5972step2 raw5972step2Labels = mixedMoment B raw5972step3 raw5972step3Labels := by
      have ha : raw5972step3 = raw5972step2 := by apply Matrix.ext; unfold raw5972step3 raw5972step2; decide +kernel
      have hl : raw5972step2Labels = labelEmbedding1 ∘ raw5972step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5972step2 raw5972step2Labels raw5972step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1186 node1186Labels := by rfl

def raw5973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -4, 2], ![2, 0, -2]]
def raw5973Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![2, -4, 2], ![2, 0, -2]]
def raw5973step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5973step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![2, -4, 2], ![2, 0, -2]]
def raw5973step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5973step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw5973step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5973step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![2, -1, -1], ![2, 1, -3]]
def raw5973step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5973 raw5973Labels = mixedMoment B node1192 node1192Labels := by
  calc
    mixedMoment B raw5973 raw5973Labels = mixedMoment B raw5973step0 raw5973step0Labels := by
      have hz : ∀ j, raw5973 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5973step0 = (fun i j => raw5973 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5973step0 raw5973; decide +kernel
      have hl : raw5973step0Labels = raw5973Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5973 raw5973Labels permutation434 hz
    mixedMoment B raw5973step0 raw5973step0Labels = mixedMoment B raw5973step1 raw5973step1Labels := by
      have hz : ∀ j, raw5973step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5973step1 = (fun i j => raw5973step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5973step1 raw5973step0; decide +kernel
      have hl : raw5973step1Labels = raw5973step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5973step0 raw5973step0Labels permutation80 hz
    mixedMoment B raw5973step1 raw5973step1Labels = mixedMoment B raw5973step2 raw5973step2Labels := by
      have ha : raw5973step2 = (fun i j => raw5973step1 (permutation25 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5973step2 raw5973step1; decide +kernel
      have hl : raw5973step2Labels = raw5973step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5973step1 raw5973step1Labels permutation25 permutation5
    mixedMoment B raw5973step2 raw5973step2Labels = mixedMoment B raw5973step3 raw5973step3Labels := by
      have ha : raw5973step3 = raw5973step2 := by apply Matrix.ext; unfold raw5973step3 raw5973step2; decide +kernel
      have hl : raw5973step2Labels = labelEmbedding1 ∘ raw5973step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5973step2 raw5973step2Labels raw5973step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1192 node1192Labels := by rfl

def raw5974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -4, 2], ![2, 0, -2]]
def raw5974Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![2, -4, 2], ![2, 0, -2]]
def raw5974step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5974step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw5974step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5974step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw5974step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5974 raw5974Labels = mixedMoment B node1184 node1184Labels := by
  calc
    mixedMoment B raw5974 raw5974Labels = mixedMoment B raw5974step0 raw5974step0Labels := by
      have hz : ∀ j, raw5974 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5974step0 = (fun i j => raw5974 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5974step0 raw5974; decide +kernel
      have hl : raw5974step0Labels = raw5974Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5974 raw5974Labels permutation434 hz
    mixedMoment B raw5974step0 raw5974step0Labels = mixedMoment B raw5974step1 raw5974step1Labels := by
      have ha : raw5974step1 = (fun i j => raw5974step0 (permutation125 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5974step1 raw5974step0; decide +kernel
      have hl : raw5974step1Labels = raw5974step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5974step0 raw5974step0Labels permutation125 permutation5
    mixedMoment B raw5974step1 raw5974step1Labels = mixedMoment B raw5974step2 raw5974step2Labels := by
      have ha : raw5974step2 = raw5974step1 := by apply Matrix.ext; unfold raw5974step2 raw5974step1; decide +kernel
      have hl : raw5974step1Labels = labelEmbedding1 ∘ raw5974step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5974step1 raw5974step1Labels raw5974step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1184 node1184Labels := by rfl

def raw5975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -4, 2], ![2, 0, -2]]
def raw5975Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![2, -4, 2], ![2, 0, -2]]
def raw5975step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5975step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw5975step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5975step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw5975step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5975 raw5975Labels = mixedMoment B node1184 node1184Labels := by
  calc
    mixedMoment B raw5975 raw5975Labels = mixedMoment B raw5975step0 raw5975step0Labels := by
      have hz : ∀ j, raw5975 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5975step0 = (fun i j => raw5975 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5975step0 raw5975; decide +kernel
      have hl : raw5975step0Labels = raw5975Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5975 raw5975Labels permutation346 hz
    mixedMoment B raw5975step0 raw5975step0Labels = mixedMoment B raw5975step1 raw5975step1Labels := by
      have ha : raw5975step1 = (fun i j => raw5975step0 (permutation125 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5975step1 raw5975step0; decide +kernel
      have hl : raw5975step1Labels = raw5975step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5975step0 raw5975step0Labels permutation125 permutation5
    mixedMoment B raw5975step1 raw5975step1Labels = mixedMoment B raw5975step2 raw5975step2Labels := by
      have ha : raw5975step2 = raw5975step1 := by apply Matrix.ext; unfold raw5975step2 raw5975step1; decide +kernel
      have hl : raw5975step1Labels = labelEmbedding1 ∘ raw5975step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5975step1 raw5975step1Labels raw5975step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1184 node1184Labels := by rfl

def raw5976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -4, 2], ![1, 1, -2]]
def raw5976Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![2, -4, 2], ![1, 1, -2]]
def raw5976step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5976step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![2, -4, 2], ![1, 1, -2]]
def raw5976step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5976step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw5976step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5976step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw5976step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5976 raw5976Labels = mixedMoment B node1292 node1292Labels := by
  calc
    mixedMoment B raw5976 raw5976Labels = mixedMoment B raw5976step0 raw5976step0Labels := by
      have hz : ∀ j, raw5976 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5976step0 = (fun i j => raw5976 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5976step0 raw5976; decide +kernel
      have hl : raw5976step0Labels = raw5976Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5976 raw5976Labels permutation434 hz
    mixedMoment B raw5976step0 raw5976step0Labels = mixedMoment B raw5976step1 raw5976step1Labels := by
      have hz : ∀ j, raw5976step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5976step1 = (fun i j => raw5976step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5976step1 raw5976step0; decide +kernel
      have hl : raw5976step1Labels = raw5976step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5976step0 raw5976step0Labels permutation80 hz
    mixedMoment B raw5976step1 raw5976step1Labels = mixedMoment B raw5976step2 raw5976step2Labels := by
      have ha : raw5976step2 = (fun i j => raw5976step1 (permutation25 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5976step2 raw5976step1; decide +kernel
      have hl : raw5976step2Labels = raw5976step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5976step1 raw5976step1Labels permutation25 permutation5
    mixedMoment B raw5976step2 raw5976step2Labels = mixedMoment B raw5976step3 raw5976step3Labels := by
      have ha : raw5976step3 = raw5976step2 := by apply Matrix.ext; unfold raw5976step3 raw5976step2; decide +kernel
      have hl : raw5976step2Labels = labelEmbedding1 ∘ raw5976step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5976step2 raw5976step2Labels raw5976step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1292 node1292Labels := by rfl

def raw5977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![3, -1, -2]]
def raw5977Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![3, -1, -2]]
def raw5977step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5977step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -3, 2], ![3, -1, -2]]
def raw5977step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5977step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, -2, 3], ![-3, 2, 1]]
def raw5977step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5977step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 2, -3], ![3, -2, -1]]
def raw5977step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5977step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 2, -3], ![3, -2, -1]]
def raw5977step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5977 raw5977Labels = mixedMoment B node1628 node1628Labels := by
  calc
    mixedMoment B raw5977 raw5977Labels = mixedMoment B raw5977step0 raw5977step0Labels := by
      have hz : ∀ j, raw5977 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5977step0 = (fun i j => raw5977 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5977step0 raw5977; decide +kernel
      have hl : raw5977step0Labels = raw5977Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5977 raw5977Labels permutation434 hz
    mixedMoment B raw5977step0 raw5977step0Labels = mixedMoment B raw5977step1 raw5977step1Labels := by
      have hz : ∀ j, raw5977step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5977step1 = (fun i j => raw5977step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5977step1 raw5977step0; decide +kernel
      have hl : raw5977step1Labels = raw5977step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5977step0 raw5977step0Labels permutation80 hz
    mixedMoment B raw5977step1 raw5977step1Labels = mixedMoment B raw5977step2 raw5977step2Labels := by
      have ha : raw5977step2 = (fun i j => raw5977step1 (permutation9 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5977step2 raw5977step1; decide +kernel
      have hl : raw5977step2Labels = raw5977step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5977step1 raw5977step1Labels permutation9 permutation5
    mixedMoment B raw5977step2 raw5977step2Labels = mixedMoment B raw5977step3 raw5977step3Labels := by
      have ha : raw5977step3 = -raw5977step2 := by apply Matrix.ext; change ∀ i j, raw5977step3 i j = -(raw5977step2 i j); unfold raw5977step3 raw5977step2; decide +kernel
      have hl : raw5977step3Labels = raw5977step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5977step3 raw5977step3Labels = mixedMoment B raw5977step4 raw5977step4Labels := by
      have ha : raw5977step4 = raw5977step3 := by apply Matrix.ext; unfold raw5977step4 raw5977step3; decide +kernel
      have hl : raw5977step3Labels = labelEmbedding1 ∘ raw5977step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5977step3 raw5977step3Labels raw5977step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1628 node1628Labels := by rfl

def raw5978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![3, -1, -2]]
def raw5978Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![3, -1, -2]]
def raw5978step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5978step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -3, 2], ![3, -1, -2]]
def raw5978step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5978step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![2, -1, -1], ![2, 1, -3]]
def raw5978step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5978step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![2, -1, -1], ![2, 1, -3]]
def raw5978step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5978 raw5978Labels = mixedMoment B node2842 node2842Labels := by
  calc
    mixedMoment B raw5978 raw5978Labels = mixedMoment B raw5978step0 raw5978step0Labels := by
      have hz : ∀ j, raw5978 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5978step0 = (fun i j => raw5978 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5978step0 raw5978; decide +kernel
      have hl : raw5978step0Labels = raw5978Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5978 raw5978Labels permutation434 hz
    mixedMoment B raw5978step0 raw5978step0Labels = mixedMoment B raw5978step1 raw5978step1Labels := by
      have hz : ∀ j, raw5978step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5978step1 = (fun i j => raw5978step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5978step1 raw5978step0; decide +kernel
      have hl : raw5978step1Labels = raw5978step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5978step0 raw5978step0Labels permutation80 hz
    mixedMoment B raw5978step1 raw5978step1Labels = mixedMoment B raw5978step2 raw5978step2Labels := by
      have ha : raw5978step2 = (fun i j => raw5978step1 (permutation25 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5978step2 raw5978step1; decide +kernel
      have hl : raw5978step2Labels = raw5978step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5978step1 raw5978step1Labels permutation25 permutation5
    mixedMoment B raw5978step2 raw5978step2Labels = mixedMoment B raw5978step3 raw5978step3Labels := by
      have ha : raw5978step3 = raw5978step2 := by apply Matrix.ext; unfold raw5978step3 raw5978step2; decide +kernel
      have hl : raw5978step2Labels = labelEmbedding1 ∘ raw5978step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5978step2 raw5978step2Labels raw5978step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2842 node2842Labels := by rfl

def raw5979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![3, -1, -2]]
def raw5979Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -3, 2], ![3, -1, -2]]
def raw5979step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5979step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw5979step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5979step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw5979step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5979 raw5979Labels = mixedMoment B node2837 node2837Labels := by
  calc
    mixedMoment B raw5979 raw5979Labels = mixedMoment B raw5979step0 raw5979step0Labels := by
      have hz : ∀ j, raw5979 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5979step0 = (fun i j => raw5979 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5979step0 raw5979; decide +kernel
      have hl : raw5979step0Labels = raw5979Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5979 raw5979Labels permutation434 hz
    mixedMoment B raw5979step0 raw5979step0Labels = mixedMoment B raw5979step1 raw5979step1Labels := by
      have ha : raw5979step1 = (fun i j => raw5979step0 (permutation125 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5979step1 raw5979step0; decide +kernel
      have hl : raw5979step1Labels = raw5979step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5979step0 raw5979step0Labels permutation125 permutation5
    mixedMoment B raw5979step1 raw5979step1Labels = mixedMoment B raw5979step2 raw5979step2Labels := by
      have ha : raw5979step2 = raw5979step1 := by apply Matrix.ext; unfold raw5979step2 raw5979step1; decide +kernel
      have hl : raw5979step1Labels = labelEmbedding1 ∘ raw5979step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5979step1 raw5979step1Labels raw5979step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2837 node2837Labels := by rfl

def raw5980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![3, -1, -2]]
def raw5980Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -3, 2], ![3, -1, -2]]
def raw5980step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5980step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw5980step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5980step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw5980step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5980 raw5980Labels = mixedMoment B node2837 node2837Labels := by
  calc
    mixedMoment B raw5980 raw5980Labels = mixedMoment B raw5980step0 raw5980step0Labels := by
      have hz : ∀ j, raw5980 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5980step0 = (fun i j => raw5980 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5980step0 raw5980; decide +kernel
      have hl : raw5980step0Labels = raw5980Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5980 raw5980Labels permutation346 hz
    mixedMoment B raw5980step0 raw5980step0Labels = mixedMoment B raw5980step1 raw5980step1Labels := by
      have ha : raw5980step1 = (fun i j => raw5980step0 (permutation125 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5980step1 raw5980step0; decide +kernel
      have hl : raw5980step1Labels = raw5980step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5980step0 raw5980step0Labels permutation125 permutation5
    mixedMoment B raw5980step1 raw5980step1Labels = mixedMoment B raw5980step2 raw5980step2Labels := by
      have ha : raw5980step2 = raw5980step1 := by apply Matrix.ext; unfold raw5980step2 raw5980step1; decide +kernel
      have hl : raw5980step1Labels = labelEmbedding1 ∘ raw5980step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5980step1 raw5980step1Labels raw5980step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2837 node2837Labels := by rfl

def raw5981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw5981Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![3, -1, -2]]
def raw5981step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5981step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![3, -1, -2]]
def raw5981step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5981step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, -2, 3], ![-2, 2, 0]]
def raw5981step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5981step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5981step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5981step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5981step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5981 raw5981Labels = mixedMoment B node3549 node3549Labels := by
  calc
    mixedMoment B raw5981 raw5981Labels = mixedMoment B raw5981step0 raw5981step0Labels := by
      have hz : ∀ j, raw5981 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5981step0 = (fun i j => raw5981 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5981step0 raw5981; decide +kernel
      have hl : raw5981step0Labels = raw5981Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5981 raw5981Labels permutation434 hz
    mixedMoment B raw5981step0 raw5981step0Labels = mixedMoment B raw5981step1 raw5981step1Labels := by
      have hz : ∀ j, raw5981step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5981step1 = (fun i j => raw5981step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5981step1 raw5981step0; decide +kernel
      have hl : raw5981step1Labels = raw5981step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5981step0 raw5981step0Labels permutation80 hz
    mixedMoment B raw5981step1 raw5981step1Labels = mixedMoment B raw5981step2 raw5981step2Labels := by
      have ha : raw5981step2 = (fun i j => raw5981step1 (permutation9 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5981step2 raw5981step1; decide +kernel
      have hl : raw5981step2Labels = raw5981step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5981step1 raw5981step1Labels permutation9 permutation5
    mixedMoment B raw5981step2 raw5981step2Labels = mixedMoment B raw5981step3 raw5981step3Labels := by
      have ha : raw5981step3 = -raw5981step2 := by apply Matrix.ext; change ∀ i j, raw5981step3 i j = -(raw5981step2 i j); unfold raw5981step3 raw5981step2; decide +kernel
      have hl : raw5981step3Labels = raw5981step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5981step3 raw5981step3Labels = mixedMoment B raw5981step4 raw5981step4Labels := by
      have ha : raw5981step4 = raw5981step3 := by apply Matrix.ext; unfold raw5981step4 raw5981step3; decide +kernel
      have hl : raw5981step3Labels = labelEmbedding1 ∘ raw5981step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5981step3 raw5981step3Labels raw5981step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3549 node3549Labels := by rfl

def raw5982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5982Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5982step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5982step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw5982step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5982step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw5982step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5982 raw5982Labels = mixedMoment B node2777 node2777Labels := by
  calc
    mixedMoment B raw5982 raw5982Labels = mixedMoment B raw5982step0 raw5982step0Labels := by
      have hz : ∀ j, raw5982 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5982step0 = (fun i j => raw5982 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5982step0 raw5982; decide +kernel
      have hl : raw5982step0Labels = raw5982Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5982 raw5982Labels permutation434 hz
    mixedMoment B raw5982step0 raw5982step0Labels = mixedMoment B raw5982step1 raw5982step1Labels := by
      have hz : ∀ j, raw5982step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5982step1 = (fun i j => raw5982step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5982step1 raw5982step0; decide +kernel
      have hl : raw5982step1Labels = raw5982step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5982step0 raw5982step0Labels permutation80 hz
    mixedMoment B raw5982step1 raw5982step1Labels = mixedMoment B raw5982step2 raw5982step2Labels := by
      have ha : raw5982step2 = (fun i j => raw5982step1 (permutation25 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5982step2 raw5982step1; decide +kernel
      have hl : raw5982step2Labels = raw5982step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5982step1 raw5982step1Labels permutation25 permutation4
    _ = mixedMoment B node2777 node2777Labels := by rfl

def raw5983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5983Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5983step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5983step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5983step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -3, 2], ![2, 0, -2]]
def raw5983step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5983step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw5983step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5983 raw5983Labels = mixedMoment B node2774 node2774Labels := by
  calc
    mixedMoment B raw5983 raw5983Labels = mixedMoment B raw5983step0 raw5983step0Labels := by
      have hz : ∀ j, raw5983 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5983step0 = (fun i j => raw5983 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5983step0 raw5983; decide +kernel
      have hl : raw5983step0Labels = raw5983Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5983 raw5983Labels permutation434 hz
    mixedMoment B raw5983step0 raw5983step0Labels = mixedMoment B raw5983step1 raw5983step1Labels := by
      have hz : ∀ j, raw5983step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5983step1 = (fun i j => raw5983step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5983step1 raw5983step0; decide +kernel
      have hl : raw5983step1Labels = raw5983step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5983step0 raw5983step0Labels permutation80 hz
    mixedMoment B raw5983step1 raw5983step1Labels = mixedMoment B raw5983step2 raw5983step2Labels := by
      have ha : raw5983step2 = (fun i j => raw5983step1 (permutation24 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5983step2 raw5983step1; decide +kernel
      have hl : raw5983step2Labels = raw5983step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5983step1 raw5983step1Labels permutation24 permutation4
    _ = mixedMoment B node2774 node2774Labels := by rfl

def raw5984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5984Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5984step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5984step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw5984step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5984 raw5984Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw5984 raw5984Labels = mixedMoment B raw5984step0 raw5984step0Labels := by
      have hz : ∀ j, raw5984 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5984step0 = (fun i j => raw5984 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5984step0 raw5984; decide +kernel
      have hl : raw5984step0Labels = raw5984Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5984 raw5984Labels permutation434 hz
    mixedMoment B raw5984step0 raw5984step0Labels = mixedMoment B raw5984step1 raw5984step1Labels := by
      have ha : raw5984step1 = (fun i j => raw5984step0 (permutation123 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5984step1 raw5984step0; decide +kernel
      have hl : raw5984step1Labels = raw5984step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5984step0 raw5984step0Labels permutation123 permutation4
    _ = mixedMoment B node2773 node2773Labels := by rfl

def raw5985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5985Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5985step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5985step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw5985step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5985 raw5985Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw5985 raw5985Labels = mixedMoment B raw5985step0 raw5985step0Labels := by
      have hz : ∀ j, raw5985 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5985step0 = (fun i j => raw5985 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5985step0 raw5985; decide +kernel
      have hl : raw5985step0Labels = raw5985Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5985 raw5985Labels permutation346 hz
    mixedMoment B raw5985step0 raw5985step0Labels = mixedMoment B raw5985step1 raw5985step1Labels := by
      have ha : raw5985step1 = (fun i j => raw5985step0 (permutation123 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5985step1 raw5985step0; decide +kernel
      have hl : raw5985step1Labels = raw5985step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5985step0 raw5985step0Labels permutation123 permutation4
    _ = mixedMoment B node2773 node2773Labels := by rfl

def raw5986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw5986Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw5986step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5986step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![2, 0, -2]]
def raw5986step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5986step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1]]
def raw5986step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5986step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw5986step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5986 raw5986Labels = mixedMoment B node3907 node3907Labels := by
  calc
    mixedMoment B raw5986 raw5986Labels = mixedMoment B raw5986step0 raw5986step0Labels := by
      have hz : ∀ j, raw5986 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5986step0 = (fun i j => raw5986 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5986step0 raw5986; decide +kernel
      have hl : raw5986step0Labels = raw5986Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5986 raw5986Labels permutation434 hz
    mixedMoment B raw5986step0 raw5986step0Labels = mixedMoment B raw5986step1 raw5986step1Labels := by
      have hz : ∀ j, raw5986step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5986step1 = (fun i j => raw5986step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5986step1 raw5986step0; decide +kernel
      have hl : raw5986step1Labels = raw5986step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5986step0 raw5986step0Labels permutation80 hz
    mixedMoment B raw5986step1 raw5986step1Labels = mixedMoment B raw5986step2 raw5986step2Labels := by
      have ha : raw5986step2 = (fun i j => raw5986step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5986step2 raw5986step1; decide +kernel
      have hl : raw5986step2Labels = raw5986step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5986step1 raw5986step1Labels permutation29 permutation2
    mixedMoment B raw5986step2 raw5986step2Labels = mixedMoment B raw5986step3 raw5986step3Labels := by
      have ha : raw5986step3 = -raw5986step2 := by apply Matrix.ext; change ∀ i j, raw5986step3 i j = -(raw5986step2 i j); unfold raw5986step3 raw5986step2; decide +kernel
      have hl : raw5986step3Labels = raw5986step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3907 node3907Labels := by rfl

def raw5987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2]]
def raw5987Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2]]
def raw5987step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5987step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -3, 2], ![1, 1, -2]]
def raw5987step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5987step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw5987step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5987 raw5987Labels = mixedMoment B node2782 node2782Labels := by
  calc
    mixedMoment B raw5987 raw5987Labels = mixedMoment B raw5987step0 raw5987step0Labels := by
      have hz : ∀ j, raw5987 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5987step0 = (fun i j => raw5987 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5987step0 raw5987; decide +kernel
      have hl : raw5987step0Labels = raw5987Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5987 raw5987Labels permutation434 hz
    mixedMoment B raw5987step0 raw5987step0Labels = mixedMoment B raw5987step1 raw5987step1Labels := by
      have hz : ∀ j, raw5987step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5987step1 = (fun i j => raw5987step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5987step1 raw5987step0; decide +kernel
      have hl : raw5987step1Labels = raw5987step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5987step0 raw5987step0Labels permutation80 hz
    mixedMoment B raw5987step1 raw5987step1Labels = mixedMoment B raw5987step2 raw5987step2Labels := by
      have ha : raw5987step2 = (fun i j => raw5987step1 (permutation20 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5987step2 raw5987step1; decide +kernel
      have hl : raw5987step2Labels = raw5987step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5987step1 raw5987step1Labels permutation20 permutation4
    _ = mixedMoment B node2782 node2782Labels := by rfl

def raw5988 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![0, 0], ![0, 0], ![-2, 2], ![2, -2]]
def raw5988Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5988step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![0, 0], ![-2, 2], ![2, -2]]
def raw5988step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5988step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-2, 2], ![2, -2]]
def raw5988step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5988step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw5988step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical5988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5988 raw5988Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw5988 raw5988Labels = mixedMoment B raw5988step0 raw5988step0Labels := by
      have hz : ∀ j, raw5988 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5988step0 = (fun i j => raw5988 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5988step0 raw5988; decide +kernel
      have hl : raw5988step0Labels = raw5988Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5988 raw5988Labels permutation434 hz
    mixedMoment B raw5988step0 raw5988step0Labels = mixedMoment B raw5988step1 raw5988step1Labels := by
      have hz : ∀ j, raw5988step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5988step1 = (fun i j => raw5988step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5988step1 raw5988step0; decide +kernel
      have hl : raw5988step1Labels = raw5988step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5988step0 raw5988step0Labels permutation80 hz
    mixedMoment B raw5988step1 raw5988step1Labels = mixedMoment B raw5988step2 raw5988step2Labels := by
      have ha : raw5988step2 = (fun i j => raw5988step1 (permutation20 i) (permutation0 j)) := by apply Matrix.ext; unfold raw5988step2 raw5988step1; decide +kernel
      have hl : raw5988step2Labels = raw5988step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5988step1 raw5988step1Labels permutation20 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw5989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5989Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5989step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5989step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![1, -3, 2], ![2, 0, -2]]
def raw5989step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5989step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5989step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5989 raw5989Labels = mixedMoment B node1436 node1436Labels := by
  calc
    mixedMoment B raw5989 raw5989Labels = mixedMoment B raw5989step0 raw5989step0Labels := by
      have hz : ∀ j, raw5989 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5989step0 = (fun i j => raw5989 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5989step0 raw5989; decide +kernel
      have hl : raw5989step0Labels = raw5989Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5989 raw5989Labels permutation434 hz
    mixedMoment B raw5989step0 raw5989step0Labels = mixedMoment B raw5989step1 raw5989step1Labels := by
      have hz : ∀ j, raw5989step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5989step1 = (fun i j => raw5989step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5989step1 raw5989step0; decide +kernel
      have hl : raw5989step1Labels = raw5989step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5989step0 raw5989step0Labels permutation80 hz
    mixedMoment B raw5989step1 raw5989step1Labels = mixedMoment B raw5989step2 raw5989step2Labels := by
      have ha : raw5989step2 = (fun i j => raw5989step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5989step2 raw5989step1; decide +kernel
      have hl : raw5989step2Labels = raw5989step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5989step1 raw5989step1Labels permutation10 permutation2
    _ = mixedMoment B node1436 node1436Labels := by rfl

def raw5990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5990Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5990step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5990step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -3, 2], ![1, -1, 0], ![2, 0, -2]]
def raw5990step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5990 raw5990Labels = mixedMoment B node1422 node1422Labels := by
  calc
    mixedMoment B raw5990 raw5990Labels = mixedMoment B raw5990step0 raw5990step0Labels := by
      have hz : ∀ j, raw5990 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5990step0 = (fun i j => raw5990 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5990step0 raw5990; decide +kernel
      have hl : raw5990step0Labels = raw5990Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5990 raw5990Labels permutation434 hz
    mixedMoment B raw5990step0 raw5990step0Labels = mixedMoment B raw5990step1 raw5990step1Labels := by
      have ha : raw5990step1 = (fun i j => raw5990step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5990step1 raw5990step0; decide +kernel
      have hl : raw5990step1Labels = raw5990step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5990step0 raw5990step0Labels permutation34 permutation2
    _ = mixedMoment B node1422 node1422Labels := by rfl

def raw5991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5991Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5991step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5991step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -3, 2], ![1, -1, 0], ![2, 0, -2]]
def raw5991step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5991 raw5991Labels = mixedMoment B node1422 node1422Labels := by
  calc
    mixedMoment B raw5991 raw5991Labels = mixedMoment B raw5991step0 raw5991step0Labels := by
      have hz : ∀ j, raw5991 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5991step0 = (fun i j => raw5991 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5991step0 raw5991; decide +kernel
      have hl : raw5991step0Labels = raw5991Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5991 raw5991Labels permutation346 hz
    mixedMoment B raw5991step0 raw5991step0Labels = mixedMoment B raw5991step1 raw5991step1Labels := by
      have ha : raw5991step1 = (fun i j => raw5991step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5991step1 raw5991step0; decide +kernel
      have hl : raw5991step1Labels = raw5991step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5991step0 raw5991step0Labels permutation34 permutation2
    _ = mixedMoment B node1422 node1422Labels := by rfl

def raw5992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -4, 2], ![2, 0, -2]]
def raw5992Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![2, -4, 2], ![2, 0, -2]]
def raw5992step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5992step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![2, -4, 2], ![2, 0, -2]]
def raw5992step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5992step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, 0, -1], ![3, -4, 1]]
def raw5992step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5992 raw5992Labels = mixedMoment B node1282 node1282Labels := by
  calc
    mixedMoment B raw5992 raw5992Labels = mixedMoment B raw5992step0 raw5992step0Labels := by
      have hz : ∀ j, raw5992 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5992step0 = (fun i j => raw5992 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5992step0 raw5992; decide +kernel
      have hl : raw5992step0Labels = raw5992Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5992 raw5992Labels permutation434 hz
    mixedMoment B raw5992step0 raw5992step0Labels = mixedMoment B raw5992step1 raw5992step1Labels := by
      have hz : ∀ j, raw5992step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5992step1 = (fun i j => raw5992step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5992step1 raw5992step0; decide +kernel
      have hl : raw5992step1Labels = raw5992step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5992step0 raw5992step0Labels permutation80 hz
    mixedMoment B raw5992step1 raw5992step1Labels = mixedMoment B raw5992step2 raw5992step2Labels := by
      have ha : raw5992step2 = (fun i j => raw5992step1 (permutation25 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5992step2 raw5992step1; decide +kernel
      have hl : raw5992step2Labels = raw5992step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5992step1 raw5992step1Labels permutation25 permutation4
    _ = mixedMoment B node1282 node1282Labels := by rfl

def raw5993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![3, -1, -2]]
def raw5993Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![3, -1, -2]]
def raw5993step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5993step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -3, 2], ![3, -1, -2]]
def raw5993step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5993 raw5993Labels = mixedMoment B node1424 node1424Labels := by
  calc
    mixedMoment B raw5993 raw5993Labels = mixedMoment B raw5993step0 raw5993step0Labels := by
      have hz : ∀ j, raw5993 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5993step0 = (fun i j => raw5993 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5993step0 raw5993; decide +kernel
      have hl : raw5993step0Labels = raw5993Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5993 raw5993Labels permutation434 hz
    mixedMoment B raw5993step0 raw5993step0Labels = mixedMoment B raw5993step1 raw5993step1Labels := by
      have hz : ∀ j, raw5993step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5993step1 = (fun i j => raw5993step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5993step1 raw5993step0; decide +kernel
      have hl : raw5993step1Labels = raw5993step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5993step0 raw5993step0Labels permutation80 hz
    _ = mixedMoment B node1424 node1424Labels := by rfl

def raw5994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5994Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5994step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5994step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -3, 1]]
def raw5994step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5994 raw5994Labels = mixedMoment B node2759 node2759Labels := by
  calc
    mixedMoment B raw5994 raw5994Labels = mixedMoment B raw5994step0 raw5994step0Labels := by
      have hz : ∀ j, raw5994 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5994step0 = (fun i j => raw5994 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5994step0 raw5994; decide +kernel
      have hl : raw5994step0Labels = raw5994Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5994 raw5994Labels permutation434 hz
    mixedMoment B raw5994step0 raw5994step0Labels = mixedMoment B raw5994step1 raw5994step1Labels := by
      have ha : raw5994step1 = (fun i j => raw5994step0 (permutation115 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5994step1 raw5994step0; decide +kernel
      have hl : raw5994step1Labels = raw5994step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5994step0 raw5994step0Labels permutation115 permutation4
    _ = mixedMoment B node2759 node2759Labels := by rfl

def raw5995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5995Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5995step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5995step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -3, 1]]
def raw5995step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5995 raw5995Labels = mixedMoment B node2759 node2759Labels := by
  calc
    mixedMoment B raw5995 raw5995Labels = mixedMoment B raw5995step0 raw5995step0Labels := by
      have hz : ∀ j, raw5995 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5995step0 = (fun i j => raw5995 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5995step0 raw5995; decide +kernel
      have hl : raw5995step0Labels = raw5995Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5995 raw5995Labels permutation346 hz
    mixedMoment B raw5995step0 raw5995step0Labels = mixedMoment B raw5995step1 raw5995step1Labels := by
      have ha : raw5995step1 = (fun i j => raw5995step0 (permutation115 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5995step1 raw5995step0; decide +kernel
      have hl : raw5995step1Labels = raw5995step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5995step0 raw5995step0Labels permutation115 permutation4
    _ = mixedMoment B node2759 node2759Labels := by rfl

def raw5996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw5996Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw5996step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5996step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![2, 0, -2]]
def raw5996step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5996step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5996step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5996 raw5996Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw5996 raw5996Labels = mixedMoment B raw5996step0 raw5996step0Labels := by
      have hz : ∀ j, raw5996 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5996step0 = (fun i j => raw5996 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5996step0 raw5996; decide +kernel
      have hl : raw5996step0Labels = raw5996Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5996 raw5996Labels permutation434 hz
    mixedMoment B raw5996step0 raw5996step0Labels = mixedMoment B raw5996step1 raw5996step1Labels := by
      have hz : ∀ j, raw5996step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5996step1 = (fun i j => raw5996step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5996step1 raw5996step0; decide +kernel
      have hl : raw5996step1Labels = raw5996step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5996step0 raw5996step0Labels permutation80 hz
    mixedMoment B raw5996step1 raw5996step1Labels = mixedMoment B raw5996step2 raw5996step2Labels := by
      have ha : raw5996step2 = (fun i j => raw5996step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5996step2 raw5996step1; decide +kernel
      have hl : raw5996step2Labels = raw5996step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5996step1 raw5996step1Labels permutation10 permutation2
    _ = mixedMoment B node3054 node3054Labels := by rfl

def raw5997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2]]
def raw5997Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2]]
def raw5997step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5997step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![1, -3, 2], ![1, 1, -2]]
def raw5997step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5997step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw5997step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5997 raw5997Labels = mixedMoment B node2769 node2769Labels := by
  calc
    mixedMoment B raw5997 raw5997Labels = mixedMoment B raw5997step0 raw5997step0Labels := by
      have hz : ∀ j, raw5997 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5997step0 = (fun i j => raw5997 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5997step0 raw5997; decide +kernel
      have hl : raw5997step0Labels = raw5997Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5997 raw5997Labels permutation434 hz
    mixedMoment B raw5997step0 raw5997step0Labels = mixedMoment B raw5997step1 raw5997step1Labels := by
      have hz : ∀ j, raw5997step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw5997step1 = (fun i j => raw5997step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw5997step1 raw5997step0; decide +kernel
      have hl : raw5997step1Labels = raw5997step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5997step0 raw5997step0Labels permutation80 hz
    mixedMoment B raw5997step1 raw5997step1Labels = mixedMoment B raw5997step2 raw5997step2Labels := by
      have ha : raw5997step2 = (fun i j => raw5997step1 (permutation23 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5997step2 raw5997step1; decide +kernel
      have hl : raw5997step2Labels = raw5997step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5997step1 raw5997step1Labels permutation23 permutation4
    _ = mixedMoment B node2769 node2769Labels := by rfl

def raw5998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5998Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5998step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5998step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw5998step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5998 raw5998Labels = mixedMoment B node2582 node2582Labels := by
  calc
    mixedMoment B raw5998 raw5998Labels = mixedMoment B raw5998step0 raw5998step0Labels := by
      have hz : ∀ j, raw5998 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw5998step0 = (fun i j => raw5998 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw5998step0 raw5998; decide +kernel
      have hl : raw5998step0Labels = raw5998Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5998 raw5998Labels permutation434 hz
    mixedMoment B raw5998step0 raw5998step0Labels = mixedMoment B raw5998step1 raw5998step1Labels := by
      have ha : raw5998step1 = (fun i j => raw5998step0 (permutation120 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5998step1 raw5998step0; decide +kernel
      have hl : raw5998step1Labels = raw5998step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5998step0 raw5998step0Labels permutation120 permutation4
    _ = mixedMoment B node2582 node2582Labels := by rfl

def raw5999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5999Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw5999step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5999step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw5999step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5999 raw5999Labels = mixedMoment B node2582 node2582Labels := by
  calc
    mixedMoment B raw5999 raw5999Labels = mixedMoment B raw5999step0 raw5999step0Labels := by
      have hz : ∀ j, raw5999 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw5999step0 = (fun i j => raw5999 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw5999step0 raw5999; decide +kernel
      have hl : raw5999step0Labels = raw5999Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5999 raw5999Labels permutation346 hz
    mixedMoment B raw5999step0 raw5999step0Labels = mixedMoment B raw5999step1 raw5999step1Labels := by
      have ha : raw5999step1 = (fun i j => raw5999step0 (permutation120 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5999step1 raw5999step0; decide +kernel
      have hl : raw5999step1Labels = raw5999step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5999step0 raw5999step0Labels permutation120 permutation4
    _ = mixedMoment B node2582 node2582Labels := by rfl

def raw6000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -4, 2], ![2, 0, -2]]
def raw6000Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![2, -4, 2], ![2, 0, -2]]
def raw6000step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6000step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![2, -4, 2], ![2, 0, -2]]
def raw6000step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6000step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![2, -3, 1], ![2, -1, -1]]
def raw6000step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6000 raw6000Labels = mixedMoment B node1283 node1283Labels := by
  calc
    mixedMoment B raw6000 raw6000Labels = mixedMoment B raw6000step0 raw6000step0Labels := by
      have hz : ∀ j, raw6000 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6000step0 = (fun i j => raw6000 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6000step0 raw6000; decide +kernel
      have hl : raw6000step0Labels = raw6000Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6000 raw6000Labels permutation434 hz
    mixedMoment B raw6000step0 raw6000step0Labels = mixedMoment B raw6000step1 raw6000step1Labels := by
      have hz : ∀ j, raw6000step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6000step1 = (fun i j => raw6000step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6000step1 raw6000step0; decide +kernel
      have hl : raw6000step1Labels = raw6000step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6000step0 raw6000step0Labels permutation80 hz
    mixedMoment B raw6000step1 raw6000step1Labels = mixedMoment B raw6000step2 raw6000step2Labels := by
      have ha : raw6000step2 = (fun i j => raw6000step1 (permutation24 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6000step2 raw6000step1; decide +kernel
      have hl : raw6000step2Labels = raw6000step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6000step1 raw6000step1Labels permutation24 permutation4
    _ = mixedMoment B node1283 node1283Labels := by rfl

def raw6001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![3, -1, -2]]
def raw6001Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![3, -1, -2]]
def raw6001step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6001step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -3, 2], ![3, -1, -2]]
def raw6001step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6001step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, -3, 2], ![-1, 2, -1], ![-3, 2, 1]]
def raw6001step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6001step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![1, -2, 1], ![3, -2, -1]]
def raw6001step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6001 raw6001Labels = mixedMoment B node2651 node2651Labels := by
  calc
    mixedMoment B raw6001 raw6001Labels = mixedMoment B raw6001step0 raw6001step0Labels := by
      have hz : ∀ j, raw6001 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6001step0 = (fun i j => raw6001 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6001step0 raw6001; decide +kernel
      have hl : raw6001step0Labels = raw6001Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6001 raw6001Labels permutation434 hz
    mixedMoment B raw6001step0 raw6001step0Labels = mixedMoment B raw6001step1 raw6001step1Labels := by
      have hz : ∀ j, raw6001step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6001step1 = (fun i j => raw6001step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6001step1 raw6001step0; decide +kernel
      have hl : raw6001step1Labels = raw6001step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6001step0 raw6001step0Labels permutation80 hz
    mixedMoment B raw6001step1 raw6001step1Labels = mixedMoment B raw6001step2 raw6001step2Labels := by
      have ha : raw6001step2 = (fun i j => raw6001step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6001step2 raw6001step1; decide +kernel
      have hl : raw6001step2Labels = raw6001step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6001step1 raw6001step1Labels permutation31 permutation2
    mixedMoment B raw6001step2 raw6001step2Labels = mixedMoment B raw6001step3 raw6001step3Labels := by
      have ha : raw6001step3 = -raw6001step2 := by apply Matrix.ext; change ∀ i j, raw6001step3 i j = -(raw6001step2 i j); unfold raw6001step3 raw6001step2; decide +kernel
      have hl : raw6001step3Labels = raw6001step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2651 node2651Labels := by rfl

def raw6002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw6002Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6002step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw6002step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6002 raw6002Labels = mixedMoment B node2580 node2580Labels := by
  calc
    mixedMoment B raw6002 raw6002Labels = mixedMoment B raw6002step0 raw6002step0Labels := by
      have ha : raw6002step0 = (fun i j => raw6002 (permutation552 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6002step0 raw6002; decide +kernel
      have hl : raw6002step0Labels = raw6002Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6002 raw6002Labels permutation552 permutation4
    _ = mixedMoment B node2580 node2580Labels := by rfl

def raw6003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![2, 0, -2]]
def raw6003Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![2, 0, -2]]
def raw6003step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6003step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw6003step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6003 raw6003Labels = mixedMoment B node3038 node3038Labels := by
  calc
    mixedMoment B raw6003 raw6003Labels = mixedMoment B raw6003step0 raw6003step0Labels := by
      have hz : ∀ j, raw6003 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6003step0 = (fun i j => raw6003 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6003step0 raw6003; decide +kernel
      have hl : raw6003step0Labels = raw6003Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6003 raw6003Labels permutation434 hz
    mixedMoment B raw6003step0 raw6003step0Labels = mixedMoment B raw6003step1 raw6003step1Labels := by
      have ha : raw6003step1 = (fun i j => raw6003step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6003step1 raw6003step0; decide +kernel
      have hl : raw6003step1Labels = raw6003step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6003step0 raw6003step0Labels permutation44 permutation2
    _ = mixedMoment B node3038 node3038Labels := by rfl

def raw6004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![1, 1, -2]]
def raw6004Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![1, -3, 2], ![1, 1, -2]]
def raw6004step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6004step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw6004step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6004 raw6004Labels = mixedMoment B node2600 node2600Labels := by
  calc
    mixedMoment B raw6004 raw6004Labels = mixedMoment B raw6004step0 raw6004step0Labels := by
      have hz : ∀ j, raw6004 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6004step0 = (fun i j => raw6004 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6004step0 raw6004; decide +kernel
      have hl : raw6004step0Labels = raw6004Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6004 raw6004Labels permutation434 hz
    mixedMoment B raw6004step0 raw6004step0Labels = mixedMoment B raw6004step1 raw6004step1Labels := by
      have ha : raw6004step1 = (fun i j => raw6004step0 (permutation119 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6004step1 raw6004step0; decide +kernel
      have hl : raw6004step1Labels = raw6004step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6004step0 raw6004step0Labels permutation119 permutation4
    _ = mixedMoment B node2600 node2600Labels := by rfl

def raw6005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, -3, 2], ![2, 0, -2]]
def raw6005Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6005step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw6005step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6005 raw6005Labels = mixedMoment B node2580 node2580Labels := by
  calc
    mixedMoment B raw6005 raw6005Labels = mixedMoment B raw6005step0 raw6005step0Labels := by
      have ha : raw6005step0 = (fun i j => raw6005 (permutation568 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6005step0 raw6005; decide +kernel
      have hl : raw6005step0Labels = raw6005Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6005 raw6005Labels permutation568 permutation4
    _ = mixedMoment B node2580 node2580Labels := by rfl

def raw6006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -4, 2], ![2, 0, -2]]
def raw6006Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![2, -4, 2], ![2, 0, -2]]
def raw6006step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6006step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw6006step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6006 raw6006Labels = mixedMoment B node1280 node1280Labels := by
  calc
    mixedMoment B raw6006 raw6006Labels = mixedMoment B raw6006step0 raw6006step0Labels := by
      have hz : ∀ j, raw6006 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6006step0 = (fun i j => raw6006 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6006step0 raw6006; decide +kernel
      have hl : raw6006step0Labels = raw6006Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6006 raw6006Labels permutation434 hz
    mixedMoment B raw6006step0 raw6006step0Labels = mixedMoment B raw6006step1 raw6006step1Labels := by
      have ha : raw6006step1 = (fun i j => raw6006step0 (permutation127 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6006step1 raw6006step0; decide +kernel
      have hl : raw6006step1Labels = raw6006step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6006step0 raw6006step0Labels permutation127 permutation4
    _ = mixedMoment B node1280 node1280Labels := by rfl

def raw6007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![3, -1, -2]]
def raw6007Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -3, 2], ![3, -1, -2]]
def raw6007step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6007step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -3, 2], ![0, 1, -1], ![-1, 1, 0], ![-3, 2, 1]]
def raw6007step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6007step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![3, -2, -1]]
def raw6007step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6007 raw6007Labels = mixedMoment B node2647 node2647Labels := by
  calc
    mixedMoment B raw6007 raw6007Labels = mixedMoment B raw6007step0 raw6007step0Labels := by
      have hz : ∀ j, raw6007 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6007step0 = (fun i j => raw6007 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6007step0 raw6007; decide +kernel
      have hl : raw6007step0Labels = raw6007Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6007 raw6007Labels permutation434 hz
    mixedMoment B raw6007step0 raw6007step0Labels = mixedMoment B raw6007step1 raw6007step1Labels := by
      have ha : raw6007step1 = (fun i j => raw6007step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6007step1 raw6007step0; decide +kernel
      have hl : raw6007step1Labels = raw6007step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6007step0 raw6007step0Labels permutation149 permutation2
    mixedMoment B raw6007step1 raw6007step1Labels = mixedMoment B raw6007step2 raw6007step2Labels := by
      have ha : raw6007step2 = -raw6007step1 := by apply Matrix.ext; change ∀ i j, raw6007step2 i j = -(raw6007step1 i j); unfold raw6007step2 raw6007step1; decide +kernel
      have hl : raw6007step2Labels = raw6007step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2647 node2647Labels := by rfl

def raw6008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -4, 2], ![2, 0, -2]]
def raw6008Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6008step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, 1, 0], ![2, -4, 2], ![2, 0, -2]]
def raw6008step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6008step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -3, 1]]
def raw6008step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6008 raw6008Labels = mixedMoment B node1280 node1280Labels := by
  calc
    mixedMoment B raw6008 raw6008Labels = mixedMoment B raw6008step0 raw6008step0Labels := by
      have hz : ∀ j, raw6008 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6008step0 = (fun i j => raw6008 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6008step0 raw6008; decide +kernel
      have hl : raw6008step0Labels = raw6008Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6008 raw6008Labels permutation346 hz
    mixedMoment B raw6008step0 raw6008step0Labels = mixedMoment B raw6008step1 raw6008step1Labels := by
      have ha : raw6008step1 = (fun i j => raw6008step0 (permutation127 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6008step1 raw6008step0; decide +kernel
      have hl : raw6008step1Labels = raw6008step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6008step0 raw6008step0Labels permutation127 permutation4
    _ = mixedMoment B node1280 node1280Labels := by rfl

def raw6009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -4, 2], ![1, 1, -2]]
def raw6009Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, 0, 0], ![2, -4, 2], ![1, 1, -2]]
def raw6009step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6009step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![2, -4, 2], ![1, 1, -2]]
def raw6009step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw6009step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw6009step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical6009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6009 raw6009Labels = mixedMoment B node1306 node1306Labels := by
  calc
    mixedMoment B raw6009 raw6009Labels = mixedMoment B raw6009step0 raw6009step0Labels := by
      have hz : ∀ j, raw6009 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6009step0 = (fun i j => raw6009 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6009step0 raw6009; decide +kernel
      have hl : raw6009step0Labels = raw6009Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6009 raw6009Labels permutation434 hz
    mixedMoment B raw6009step0 raw6009step0Labels = mixedMoment B raw6009step1 raw6009step1Labels := by
      have hz : ∀ j, raw6009step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6009step1 = (fun i j => raw6009step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6009step1 raw6009step0; decide +kernel
      have hl : raw6009step1Labels = raw6009step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6009step0 raw6009step0Labels permutation80 hz
    mixedMoment B raw6009step1 raw6009step1Labels = mixedMoment B raw6009step2 raw6009step2Labels := by
      have ha : raw6009step2 = (fun i j => raw6009step1 (permutation23 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6009step2 raw6009step1; decide +kernel
      have hl : raw6009step2Labels = raw6009step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6009step1 raw6009step1Labels permutation23 permutation4
    _ = mixedMoment B node1306 node1306Labels := by rfl

def raw6010 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6010Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6010step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6010step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6010step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6010step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6010step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw6010step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw6010step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw6010step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6010 raw6010Labels = mixedMoment B node5297 node5297Labels := by
  calc
    mixedMoment B raw6010 raw6010Labels = mixedMoment B raw6010step0 raw6010step0Labels := by
      have hz : ∀ j, raw6010 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6010step0 = (fun i j => raw6010 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6010step0 raw6010; decide +kernel
      have hl : raw6010step0Labels = raw6010Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6010 raw6010Labels permutation434 hz
    mixedMoment B raw6010step0 raw6010step0Labels = mixedMoment B raw6010step1 raw6010step1Labels := by
      have hz : ∀ j, raw6010step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6010step1 = (fun i j => raw6010step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6010step1 raw6010step0; decide +kernel
      have hl : raw6010step1Labels = raw6010step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6010step0 raw6010step0Labels permutation80 hz
    mixedMoment B raw6010step1 raw6010step1Labels = mixedMoment B raw6010step2 raw6010step2Labels := by
      have ha : raw6010step2 = (fun i j => raw6010step1 (permutation24 i) (permutation5 j)) := by apply Matrix.ext; unfold raw6010step2 raw6010step1; decide +kernel
      have hl : raw6010step2Labels = raw6010step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6010step1 raw6010step1Labels permutation24 permutation5
    mixedMoment B raw6010step2 raw6010step2Labels = mixedMoment B raw6010step3 raw6010step3Labels := by
      have ha : raw6010step3 = raw6010step2 := by apply Matrix.ext; unfold raw6010step3 raw6010step2; decide +kernel
      have hl : raw6010step2Labels = labelEmbedding8 ∘ raw6010step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6010step2 raw6010step2Labels raw6010step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5297 node5297Labels := by rfl

def raw6011 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6011Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6011step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6011step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6011step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw6011step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw6011step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw6011step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6011 raw6011Labels = mixedMoment B node5279 node5279Labels := by
  calc
    mixedMoment B raw6011 raw6011Labels = mixedMoment B raw6011step0 raw6011step0Labels := by
      have hz : ∀ j, raw6011 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6011step0 = (fun i j => raw6011 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6011step0 raw6011; decide +kernel
      have hl : raw6011step0Labels = raw6011Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6011 raw6011Labels permutation434 hz
    mixedMoment B raw6011step0 raw6011step0Labels = mixedMoment B raw6011step1 raw6011step1Labels := by
      have ha : raw6011step1 = (fun i j => raw6011step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6011step1 raw6011step0; decide +kernel
      have hl : raw6011step1Labels = raw6011step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6011step0 raw6011step0Labels permutation32 permutation7
    mixedMoment B raw6011step1 raw6011step1Labels = mixedMoment B raw6011step2 raw6011step2Labels := by
      have ha : raw6011step2 = raw6011step1 := by apply Matrix.ext; unfold raw6011step2 raw6011step1; decide +kernel
      have hl : raw6011step1Labels = labelEmbedding10 ∘ raw6011step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6011step1 raw6011step1Labels raw6011step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5279 node5279Labels := by rfl

def raw6012 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6012Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6012step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6012step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw6012step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw6012step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw6012step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6012 raw6012Labels = mixedMoment B node5279 node5279Labels := by
  calc
    mixedMoment B raw6012 raw6012Labels = mixedMoment B raw6012step0 raw6012step0Labels := by
      have hz : ∀ j, raw6012 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw6012step0 = (fun i j => raw6012 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw6012step0 raw6012; decide +kernel
      have hl : raw6012step0Labels = raw6012Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6012 raw6012Labels permutation346 hz
    mixedMoment B raw6012step0 raw6012step0Labels = mixedMoment B raw6012step1 raw6012step1Labels := by
      have ha : raw6012step1 = (fun i j => raw6012step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6012step1 raw6012step0; decide +kernel
      have hl : raw6012step1Labels = raw6012step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6012step0 raw6012step0Labels permutation32 permutation7
    mixedMoment B raw6012step1 raw6012step1Labels = mixedMoment B raw6012step2 raw6012step2Labels := by
      have ha : raw6012step2 = raw6012step1 := by apply Matrix.ext; unfold raw6012step2 raw6012step1; decide +kernel
      have hl : raw6012step1Labels = labelEmbedding10 ∘ raw6012step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6012step1 raw6012step1Labels raw6012step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5279 node5279Labels := by rfl

def raw6013 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6013Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6013step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6013step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw6013step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6013step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw6013step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw6013step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw6013step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6013 raw6013Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw6013 raw6013Labels = mixedMoment B raw6013step0 raw6013step0Labels := by
      have hz : ∀ j, raw6013 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6013step0 = (fun i j => raw6013 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6013step0 raw6013; decide +kernel
      have hl : raw6013step0Labels = raw6013Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6013 raw6013Labels permutation434 hz
    mixedMoment B raw6013step0 raw6013step0Labels = mixedMoment B raw6013step1 raw6013step1Labels := by
      have hz : ∀ j, raw6013step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6013step1 = (fun i j => raw6013step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6013step1 raw6013step0; decide +kernel
      have hl : raw6013step1Labels = raw6013step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6013step0 raw6013step0Labels permutation80 hz
    mixedMoment B raw6013step1 raw6013step1Labels = mixedMoment B raw6013step2 raw6013step2Labels := by
      have ha : raw6013step2 = (fun i j => raw6013step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw6013step2 raw6013step1; decide +kernel
      have hl : raw6013step2Labels = raw6013step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6013step1 raw6013step1Labels permutation8 permutation7
    mixedMoment B raw6013step2 raw6013step2Labels = mixedMoment B raw6013step3 raw6013step3Labels := by
      have ha : raw6013step3 = raw6013step2 := by apply Matrix.ext; unfold raw6013step3 raw6013step2; decide +kernel
      have hl : raw6013step2Labels = labelEmbedding10 ∘ raw6013step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6013step2 raw6013step2Labels raw6013step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5291 node5291Labels := by rfl

def raw6014 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6014Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6014step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6014step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -3, 1], ![-3, 1, 2]]
def raw6014step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6014step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -3, 1], ![2, 1, -3]]
def raw6014step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6014 raw6014Labels = mixedMoment B node5175 node5175Labels := by
  calc
    mixedMoment B raw6014 raw6014Labels = mixedMoment B raw6014step0 raw6014step0Labels := by
      have hz : ∀ j, raw6014 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6014step0 = (fun i j => raw6014 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6014step0 raw6014; decide +kernel
      have hl : raw6014step0Labels = raw6014Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6014 raw6014Labels permutation434 hz
    mixedMoment B raw6014step0 raw6014step0Labels = mixedMoment B raw6014step1 raw6014step1Labels := by
      have hz : ∀ j, raw6014step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6014step1 = (fun i j => raw6014step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6014step1 raw6014step0; decide +kernel
      have hl : raw6014step1Labels = raw6014step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6014step0 raw6014step0Labels permutation80 hz
    mixedMoment B raw6014step1 raw6014step1Labels = mixedMoment B raw6014step2 raw6014step2Labels := by
      have ha : raw6014step2 = (fun i j => raw6014step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw6014step2 raw6014step1; decide +kernel
      have hl : raw6014step2Labels = raw6014step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6014step1 raw6014step1Labels permutation29 permutation2
    _ = mixedMoment B node5175 node5175Labels := by rfl

def raw6015 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6015Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6015step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6015step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -3, 1], ![-2, 0, 2]]
def raw6015step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6015step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 3, -3], ![2, -3, 1], ![-2, 0, 2]]
def raw6015step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw6015step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-3, 2, 1]]
def raw6015step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6015step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw6015step4Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw6015step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw6015step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical6015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw6015 raw6015Labels = mixedMoment B node4899 node4899Labels := by
  calc
    mixedMoment B raw6015 raw6015Labels = mixedMoment B raw6015step0 raw6015step0Labels := by
      have hz : ∀ j, raw6015 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw6015step0 = (fun i j => raw6015 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw6015step0 raw6015; decide +kernel
      have hl : raw6015step0Labels = raw6015Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6015 raw6015Labels permutation434 hz
    mixedMoment B raw6015step0 raw6015step0Labels = mixedMoment B raw6015step1 raw6015step1Labels := by
      have hz : ∀ j, raw6015step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw6015step1 = (fun i j => raw6015step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw6015step1 raw6015step0; decide +kernel
      have hl : raw6015step1Labels = raw6015step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6015step0 raw6015step0Labels permutation80 hz
    mixedMoment B raw6015step1 raw6015step1Labels = mixedMoment B raw6015step2 raw6015step2Labels := by
      have hz : ∀ j, raw6015step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw6015step2 = (fun i j => raw6015step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw6015step2 raw6015step1; decide +kernel
      have hl : raw6015step2Labels = raw6015step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw6015step1 raw6015step1Labels permutation14 hz
    mixedMoment B raw6015step2 raw6015step2Labels = mixedMoment B raw6015step3 raw6015step3Labels := by
      have ha : raw6015step3 = (fun i j => raw6015step2 (permutation3 i) (permutation4 j)) := by apply Matrix.ext; unfold raw6015step3 raw6015step2; decide +kernel
      have hl : raw6015step3Labels = raw6015step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw6015step2 raw6015step2Labels permutation3 permutation4
    mixedMoment B raw6015step3 raw6015step3Labels = mixedMoment B raw6015step4 raw6015step4Labels := by
      have ha : raw6015step4 = -raw6015step3 := by apply Matrix.ext; change ∀ i j, raw6015step4 i j = -(raw6015step3 i j); unfold raw6015step4 raw6015step3; decide +kernel
      have hl : raw6015step4Labels = raw6015step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw6015step4 raw6015step4Labels = mixedMoment B raw6015step5 raw6015step5Labels := by
      have ha : raw6015step5 = raw6015step4 := by apply Matrix.ext; unfold raw6015step5 raw6015step4; decide +kernel
      have hl : raw6015step4Labels = labelEmbedding7 ∘ raw6015step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw6015step4 raw6015step4Labels raw6015step5Labels labelEmbedding7 hl
    _ = mixedMoment B node4899 node4899Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
