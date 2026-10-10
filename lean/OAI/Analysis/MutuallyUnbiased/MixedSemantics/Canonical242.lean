import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw30976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30976Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30976step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30976step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, 0, -2], ![3, -3, 0]]
def raw30976step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30976step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-2, -1, 3], ![-3, 3, 0]]
def raw30976step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30976step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 1, -3], ![3, -3, 0]]
def raw30976step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30976 raw30976Labels = mixedMoment B node1820 node1820Labels := by
  calc
    mixedMoment B raw30976 raw30976Labels = mixedMoment B raw30976step0 raw30976step0Labels := by
      have hz : ∀ j, raw30976 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30976step0 = (fun i j => raw30976 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30976step0 raw30976; decide +kernel
      have hl : raw30976step0Labels = raw30976Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30976 raw30976Labels permutation434 hz
    mixedMoment B raw30976step0 raw30976step0Labels = mixedMoment B raw30976step1 raw30976step1Labels := by
      have hz : ∀ j, raw30976step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30976step1 = (fun i j => raw30976step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30976step1 raw30976step0; decide +kernel
      have hl : raw30976step1Labels = raw30976step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30976step0 raw30976step0Labels permutation80 hz
    mixedMoment B raw30976step1 raw30976step1Labels = mixedMoment B raw30976step2 raw30976step2Labels := by
      have ha : raw30976step2 = (fun i j => raw30976step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30976step2 raw30976step1; decide +kernel
      have hl : raw30976step2Labels = raw30976step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30976step1 raw30976step1Labels permutation31 permutation3
    mixedMoment B raw30976step2 raw30976step2Labels = mixedMoment B raw30976step3 raw30976step3Labels := by
      have ha : raw30976step3 = -raw30976step2 := by apply Matrix.ext; change ∀ i j, raw30976step3 i j = -(raw30976step2 i j); unfold raw30976step3 raw30976step2; decide +kernel
      have hl : raw30976step3Labels = raw30976step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1820 node1820Labels := by rfl

def raw30977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30977Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30977step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30977step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw30977step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30977step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw30977step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30977 raw30977Labels = mixedMoment B node1813 node1813Labels := by
  calc
    mixedMoment B raw30977 raw30977Labels = mixedMoment B raw30977step0 raw30977step0Labels := by
      have hz : ∀ j, raw30977 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30977step0 = (fun i j => raw30977 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30977step0 raw30977; decide +kernel
      have hl : raw30977step0Labels = raw30977Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30977 raw30977Labels permutation434 hz
    mixedMoment B raw30977step0 raw30977step0Labels = mixedMoment B raw30977step1 raw30977step1Labels := by
      have ha : raw30977step1 = (fun i j => raw30977step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30977step1 raw30977step0; decide +kernel
      have hl : raw30977step1Labels = raw30977step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30977step0 raw30977step0Labels permutation151 permutation3
    mixedMoment B raw30977step1 raw30977step1Labels = mixedMoment B raw30977step2 raw30977step2Labels := by
      have ha : raw30977step2 = -raw30977step1 := by apply Matrix.ext; change ∀ i j, raw30977step2 i j = -(raw30977step1 i j); unfold raw30977step2 raw30977step1; decide +kernel
      have hl : raw30977step2Labels = raw30977step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1813 node1813Labels := by rfl

def raw30978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30978Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30978step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30978step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw30978step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30978step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw30978step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30978 raw30978Labels = mixedMoment B node1813 node1813Labels := by
  calc
    mixedMoment B raw30978 raw30978Labels = mixedMoment B raw30978step0 raw30978step0Labels := by
      have hz : ∀ j, raw30978 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30978step0 = (fun i j => raw30978 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30978step0 raw30978; decide +kernel
      have hl : raw30978step0Labels = raw30978Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30978 raw30978Labels permutation346 hz
    mixedMoment B raw30978step0 raw30978step0Labels = mixedMoment B raw30978step1 raw30978step1Labels := by
      have ha : raw30978step1 = (fun i j => raw30978step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30978step1 raw30978step0; decide +kernel
      have hl : raw30978step1Labels = raw30978step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30978step0 raw30978step0Labels permutation151 permutation3
    mixedMoment B raw30978step1 raw30978step1Labels = mixedMoment B raw30978step2 raw30978step2Labels := by
      have ha : raw30978step2 = -raw30978step1 := by apply Matrix.ext; change ∀ i j, raw30978step2 i j = -(raw30978step1 i j); unfold raw30978step2 raw30978step1; decide +kernel
      have hl : raw30978step2Labels = raw30978step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1813 node1813Labels := by rfl

def raw30979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw30979Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw30979step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30979step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw30979step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30979step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw30979step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30979step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw30979step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30979 raw30979Labels = mixedMoment B node2113 node2113Labels := by
  calc
    mixedMoment B raw30979 raw30979Labels = mixedMoment B raw30979step0 raw30979step0Labels := by
      have hz : ∀ j, raw30979 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30979step0 = (fun i j => raw30979 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30979step0 raw30979; decide +kernel
      have hl : raw30979step0Labels = raw30979Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30979 raw30979Labels permutation434 hz
    mixedMoment B raw30979step0 raw30979step0Labels = mixedMoment B raw30979step1 raw30979step1Labels := by
      have hz : ∀ j, raw30979step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30979step1 = (fun i j => raw30979step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30979step1 raw30979step0; decide +kernel
      have hl : raw30979step1Labels = raw30979step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30979step0 raw30979step0Labels permutation80 hz
    mixedMoment B raw30979step1 raw30979step1Labels = mixedMoment B raw30979step2 raw30979step2Labels := by
      have ha : raw30979step2 = (fun i j => raw30979step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30979step2 raw30979step1; decide +kernel
      have hl : raw30979step2Labels = raw30979step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30979step1 raw30979step1Labels permutation31 permutation3
    mixedMoment B raw30979step2 raw30979step2Labels = mixedMoment B raw30979step3 raw30979step3Labels := by
      have ha : raw30979step3 = -raw30979step2 := by apply Matrix.ext; change ∀ i j, raw30979step3 i j = -(raw30979step2 i j); unfold raw30979step3 raw30979step2; decide +kernel
      have hl : raw30979step3Labels = raw30979step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2113 node2113Labels := by rfl

def raw30980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30980Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30980step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30980step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30980step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30980step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30980step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 3, -2], ![-2, 0, 2]]
def raw30980step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30980step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw30980step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30980step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw30980step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30980 raw30980Labels = mixedMoment B node2771 node2771Labels := by
  calc
    mixedMoment B raw30980 raw30980Labels = mixedMoment B raw30980step0 raw30980step0Labels := by
      have hz : ∀ j, raw30980 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30980step0 = (fun i j => raw30980 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30980step0 raw30980; decide +kernel
      have hl : raw30980step0Labels = raw30980Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30980 raw30980Labels permutation434 hz
    mixedMoment B raw30980step0 raw30980step0Labels = mixedMoment B raw30980step1 raw30980step1Labels := by
      have hz : ∀ j, raw30980step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30980step1 = (fun i j => raw30980step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30980step1 raw30980step0; decide +kernel
      have hl : raw30980step1Labels = raw30980step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30980step0 raw30980step0Labels permutation80 hz
    mixedMoment B raw30980step1 raw30980step1Labels = mixedMoment B raw30980step2 raw30980step2Labels := by
      have ha : raw30980step2 = (fun i j => raw30980step1 (permutation16 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30980step2 raw30980step1; decide +kernel
      have hl : raw30980step2Labels = raw30980step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30980step1 raw30980step1Labels permutation16 permutation5
    mixedMoment B raw30980step2 raw30980step2Labels = mixedMoment B raw30980step3 raw30980step3Labels := by
      have ha : raw30980step3 = -raw30980step2 := by apply Matrix.ext; change ∀ i j, raw30980step3 i j = -(raw30980step2 i j); unfold raw30980step3 raw30980step2; decide +kernel
      have hl : raw30980step3Labels = raw30980step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30980step3 raw30980step3Labels = mixedMoment B raw30980step4 raw30980step4Labels := by
      have ha : raw30980step4 = raw30980step3 := by apply Matrix.ext; unfold raw30980step4 raw30980step3; decide +kernel
      have hl : raw30980step3Labels = labelEmbedding1 ∘ raw30980step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30980step3 raw30980step3Labels raw30980step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2771 node2771Labels := by rfl

def raw30981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30981Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30981step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30981step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw30981step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30981step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw30981step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30981step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw30981step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30981 raw30981Labels = mixedMoment B node2729 node2729Labels := by
  calc
    mixedMoment B raw30981 raw30981Labels = mixedMoment B raw30981step0 raw30981step0Labels := by
      have hz : ∀ j, raw30981 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30981step0 = (fun i j => raw30981 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30981step0 raw30981; decide +kernel
      have hl : raw30981step0Labels = raw30981Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30981 raw30981Labels permutation434 hz
    mixedMoment B raw30981step0 raw30981step0Labels = mixedMoment B raw30981step1 raw30981step1Labels := by
      have ha : raw30981step1 = (fun i j => raw30981step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30981step1 raw30981step0; decide +kernel
      have hl : raw30981step1Labels = raw30981step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30981step0 raw30981step0Labels permutation42 permutation7
    mixedMoment B raw30981step1 raw30981step1Labels = mixedMoment B raw30981step2 raw30981step2Labels := by
      have ha : raw30981step2 = -raw30981step1 := by apply Matrix.ext; change ∀ i j, raw30981step2 i j = -(raw30981step1 i j); unfold raw30981step2 raw30981step1; decide +kernel
      have hl : raw30981step2Labels = raw30981step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30981step2 raw30981step2Labels = mixedMoment B raw30981step3 raw30981step3Labels := by
      have ha : raw30981step3 = raw30981step2 := by apply Matrix.ext; unfold raw30981step3 raw30981step2; decide +kernel
      have hl : raw30981step2Labels = labelEmbedding1 ∘ raw30981step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30981step2 raw30981step2Labels raw30981step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2729 node2729Labels := by rfl

def raw30982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30982Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30982step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30982step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw30982step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30982step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw30982step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30982step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw30982step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30982 raw30982Labels = mixedMoment B node2729 node2729Labels := by
  calc
    mixedMoment B raw30982 raw30982Labels = mixedMoment B raw30982step0 raw30982step0Labels := by
      have hz : ∀ j, raw30982 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30982step0 = (fun i j => raw30982 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30982step0 raw30982; decide +kernel
      have hl : raw30982step0Labels = raw30982Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30982 raw30982Labels permutation346 hz
    mixedMoment B raw30982step0 raw30982step0Labels = mixedMoment B raw30982step1 raw30982step1Labels := by
      have ha : raw30982step1 = (fun i j => raw30982step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30982step1 raw30982step0; decide +kernel
      have hl : raw30982step1Labels = raw30982step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30982step0 raw30982step0Labels permutation42 permutation7
    mixedMoment B raw30982step1 raw30982step1Labels = mixedMoment B raw30982step2 raw30982step2Labels := by
      have ha : raw30982step2 = -raw30982step1 := by apply Matrix.ext; change ∀ i j, raw30982step2 i j = -(raw30982step1 i j); unfold raw30982step2 raw30982step1; decide +kernel
      have hl : raw30982step2Labels = raw30982step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30982step2 raw30982step2Labels = mixedMoment B raw30982step3 raw30982step3Labels := by
      have ha : raw30982step3 = raw30982step2 := by apply Matrix.ext; unfold raw30982step3 raw30982step2; decide +kernel
      have hl : raw30982step2Labels = labelEmbedding1 ∘ raw30982step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30982step2 raw30982step2Labels raw30982step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2729 node2729Labels := by rfl

def raw30983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30983Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30983step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30983step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30983step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw30983step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30983step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw30983step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30983step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw30983step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30983step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw30983step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30983 raw30983Labels = mixedMoment B node2774 node2774Labels := by
  calc
    mixedMoment B raw30983 raw30983Labels = mixedMoment B raw30983step0 raw30983step0Labels := by
      have hz : ∀ j, raw30983 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30983step0 = (fun i j => raw30983 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30983step0 raw30983; decide +kernel
      have hl : raw30983step0Labels = raw30983Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30983 raw30983Labels permutation434 hz
    mixedMoment B raw30983step0 raw30983step0Labels = mixedMoment B raw30983step1 raw30983step1Labels := by
      have hz : ∀ j, raw30983step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30983step1 = (fun i j => raw30983step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30983step1 raw30983step0; decide +kernel
      have hl : raw30983step1Labels = raw30983step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30983step0 raw30983step0Labels permutation80 hz
    mixedMoment B raw30983step1 raw30983step1Labels = mixedMoment B raw30983step2 raw30983step2Labels := by
      have ha : raw30983step2 = (fun i j => raw30983step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30983step2 raw30983step1; decide +kernel
      have hl : raw30983step2Labels = raw30983step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30983step1 raw30983step1Labels permutation12 permutation7
    mixedMoment B raw30983step2 raw30983step2Labels = mixedMoment B raw30983step3 raw30983step3Labels := by
      have ha : raw30983step3 = -raw30983step2 := by apply Matrix.ext; change ∀ i j, raw30983step3 i j = -(raw30983step2 i j); unfold raw30983step3 raw30983step2; decide +kernel
      have hl : raw30983step3Labels = raw30983step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30983step3 raw30983step3Labels = mixedMoment B raw30983step4 raw30983step4Labels := by
      have ha : raw30983step4 = raw30983step3 := by apply Matrix.ext; unfold raw30983step4 raw30983step3; decide +kernel
      have hl : raw30983step3Labels = labelEmbedding1 ∘ raw30983step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30983step3 raw30983step3Labels raw30983step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2774 node2774Labels := by rfl

def raw30984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30984Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30984step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30984step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30984step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![2, 0, -2], ![1, -1, 0]]
def raw30984step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30984step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw30984step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30984step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw30984step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30984step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw30984step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30984 raw30984Labels = mixedMoment B node2765 node2765Labels := by
  calc
    mixedMoment B raw30984 raw30984Labels = mixedMoment B raw30984step0 raw30984step0Labels := by
      have hz : ∀ j, raw30984 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30984step0 = (fun i j => raw30984 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30984step0 raw30984; decide +kernel
      have hl : raw30984step0Labels = raw30984Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30984 raw30984Labels permutation434 hz
    mixedMoment B raw30984step0 raw30984step0Labels = mixedMoment B raw30984step1 raw30984step1Labels := by
      have hz : ∀ j, raw30984step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30984step1 = (fun i j => raw30984step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30984step1 raw30984step0; decide +kernel
      have hl : raw30984step1Labels = raw30984step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30984step0 raw30984step0Labels permutation80 hz
    mixedMoment B raw30984step1 raw30984step1Labels = mixedMoment B raw30984step2 raw30984step2Labels := by
      have ha : raw30984step2 = (fun i j => raw30984step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30984step2 raw30984step1; decide +kernel
      have hl : raw30984step2Labels = raw30984step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30984step1 raw30984step1Labels permutation12 permutation7
    mixedMoment B raw30984step2 raw30984step2Labels = mixedMoment B raw30984step3 raw30984step3Labels := by
      have ha : raw30984step3 = -raw30984step2 := by apply Matrix.ext; change ∀ i j, raw30984step3 i j = -(raw30984step2 i j); unfold raw30984step3 raw30984step2; decide +kernel
      have hl : raw30984step3Labels = raw30984step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30984step3 raw30984step3Labels = mixedMoment B raw30984step4 raw30984step4Labels := by
      have ha : raw30984step4 = raw30984step3 := by apply Matrix.ext; unfold raw30984step4 raw30984step3; decide +kernel
      have hl : raw30984step3Labels = labelEmbedding1 ∘ raw30984step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30984step3 raw30984step3Labels raw30984step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2765 node2765Labels := by rfl

def raw30985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30985Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30985step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30985step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, 0, -2], ![2, -2, 0]]
def raw30985step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30985step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw30985step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30985step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw30985step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30985step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw30985step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30985 raw30985Labels = mixedMoment B node1738 node1738Labels := by
  calc
    mixedMoment B raw30985 raw30985Labels = mixedMoment B raw30985step0 raw30985step0Labels := by
      have hz : ∀ j, raw30985 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30985step0 = (fun i j => raw30985 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30985step0 raw30985; decide +kernel
      have hl : raw30985step0Labels = raw30985Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30985 raw30985Labels permutation434 hz
    mixedMoment B raw30985step0 raw30985step0Labels = mixedMoment B raw30985step1 raw30985step1Labels := by
      have hz : ∀ j, raw30985step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30985step1 = (fun i j => raw30985step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30985step1 raw30985step0; decide +kernel
      have hl : raw30985step1Labels = raw30985step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30985step0 raw30985step0Labels permutation80 hz
    mixedMoment B raw30985step1 raw30985step1Labels = mixedMoment B raw30985step2 raw30985step2Labels := by
      have ha : raw30985step2 = (fun i j => raw30985step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30985step2 raw30985step1; decide +kernel
      have hl : raw30985step2Labels = raw30985step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30985step1 raw30985step1Labels permutation12 permutation7
    mixedMoment B raw30985step2 raw30985step2Labels = mixedMoment B raw30985step3 raw30985step3Labels := by
      have ha : raw30985step3 = -raw30985step2 := by apply Matrix.ext; change ∀ i j, raw30985step3 i j = -(raw30985step2 i j); unfold raw30985step3 raw30985step2; decide +kernel
      have hl : raw30985step3Labels = raw30985step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30985step3 raw30985step3Labels = mixedMoment B raw30985step4 raw30985step4Labels := by
      have ha : raw30985step4 = raw30985step3 := by apply Matrix.ext; unfold raw30985step4 raw30985step3; decide +kernel
      have hl : raw30985step3Labels = labelEmbedding1 ∘ raw30985step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30985step3 raw30985step3Labels raw30985step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1738 node1738Labels := by rfl

def raw30986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30986Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30986step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30986step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 3, -2], ![-2, 0, 2]]
def raw30986step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30986step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw30986step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30986step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw30986step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30986 raw30986Labels = mixedMoment B node2249 node2249Labels := by
  calc
    mixedMoment B raw30986 raw30986Labels = mixedMoment B raw30986step0 raw30986step0Labels := by
      have hz : ∀ j, raw30986 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30986step0 = (fun i j => raw30986 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30986step0 raw30986; decide +kernel
      have hl : raw30986step0Labels = raw30986Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30986 raw30986Labels permutation434 hz
    mixedMoment B raw30986step0 raw30986step0Labels = mixedMoment B raw30986step1 raw30986step1Labels := by
      have ha : raw30986step1 = (fun i j => raw30986step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30986step1 raw30986step0; decide +kernel
      have hl : raw30986step1Labels = raw30986step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30986step0 raw30986step0Labels permutation42 permutation7
    mixedMoment B raw30986step1 raw30986step1Labels = mixedMoment B raw30986step2 raw30986step2Labels := by
      have ha : raw30986step2 = -raw30986step1 := by apply Matrix.ext; change ∀ i j, raw30986step2 i j = -(raw30986step1 i j); unfold raw30986step2 raw30986step1; decide +kernel
      have hl : raw30986step2Labels = raw30986step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30986step2 raw30986step2Labels = mixedMoment B raw30986step3 raw30986step3Labels := by
      have ha : raw30986step3 = raw30986step2 := by apply Matrix.ext; unfold raw30986step3 raw30986step2; decide +kernel
      have hl : raw30986step2Labels = labelEmbedding1 ∘ raw30986step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30986step2 raw30986step2Labels raw30986step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2249 node2249Labels := by rfl

def raw30987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30987Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30987step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw30987step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30987step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw30987step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30987step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw30987step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30987 raw30987Labels = mixedMoment B node2194 node2194Labels := by
  calc
    mixedMoment B raw30987 raw30987Labels = mixedMoment B raw30987step0 raw30987step0Labels := by
      have ha : raw30987step0 = (fun i j => raw30987 (permutation210 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30987step0 raw30987; decide +kernel
      have hl : raw30987step0Labels = raw30987Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30987 raw30987Labels permutation210 permutation7
    mixedMoment B raw30987step0 raw30987step0Labels = mixedMoment B raw30987step1 raw30987step1Labels := by
      have ha : raw30987step1 = -raw30987step0 := by apply Matrix.ext; change ∀ i j, raw30987step1 i j = -(raw30987step0 i j); unfold raw30987step1 raw30987step0; decide +kernel
      have hl : raw30987step1Labels = raw30987step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30987step1 raw30987step1Labels = mixedMoment B raw30987step2 raw30987step2Labels := by
      have ha : raw30987step2 = raw30987step1 := by apply Matrix.ext; unfold raw30987step2 raw30987step1; decide +kernel
      have hl : raw30987step1Labels = labelEmbedding1 ∘ raw30987step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30987step1 raw30987step1Labels raw30987step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2194 node2194Labels := by rfl

def raw30988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30988Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30988step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30988step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw30988step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30988step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw30988step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30988step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw30988step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30988 raw30988Labels = mixedMoment B node2251 node2251Labels := by
  calc
    mixedMoment B raw30988 raw30988Labels = mixedMoment B raw30988step0 raw30988step0Labels := by
      have hz : ∀ j, raw30988 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30988step0 = (fun i j => raw30988 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30988step0 raw30988; decide +kernel
      have hl : raw30988step0Labels = raw30988Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30988 raw30988Labels permutation434 hz
    mixedMoment B raw30988step0 raw30988step0Labels = mixedMoment B raw30988step1 raw30988step1Labels := by
      have ha : raw30988step1 = (fun i j => raw30988step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30988step1 raw30988step0; decide +kernel
      have hl : raw30988step1Labels = raw30988step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30988step0 raw30988step0Labels permutation42 permutation7
    mixedMoment B raw30988step1 raw30988step1Labels = mixedMoment B raw30988step2 raw30988step2Labels := by
      have ha : raw30988step2 = -raw30988step1 := by apply Matrix.ext; change ∀ i j, raw30988step2 i j = -(raw30988step1 i j); unfold raw30988step2 raw30988step1; decide +kernel
      have hl : raw30988step2Labels = raw30988step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30988step2 raw30988step2Labels = mixedMoment B raw30988step3 raw30988step3Labels := by
      have ha : raw30988step3 = raw30988step2 := by apply Matrix.ext; unfold raw30988step3 raw30988step2; decide +kernel
      have hl : raw30988step2Labels = labelEmbedding1 ∘ raw30988step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30988step2 raw30988step2Labels raw30988step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2251 node2251Labels := by rfl

def raw30989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30989Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30989step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30989step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw30989step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30989step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw30989step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30989step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw30989step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30989 raw30989Labels = mixedMoment B node2242 node2242Labels := by
  calc
    mixedMoment B raw30989 raw30989Labels = mixedMoment B raw30989step0 raw30989step0Labels := by
      have hz : ∀ j, raw30989 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30989step0 = (fun i j => raw30989 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30989step0 raw30989; decide +kernel
      have hl : raw30989step0Labels = raw30989Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30989 raw30989Labels permutation434 hz
    mixedMoment B raw30989step0 raw30989step0Labels = mixedMoment B raw30989step1 raw30989step1Labels := by
      have ha : raw30989step1 = (fun i j => raw30989step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30989step1 raw30989step0; decide +kernel
      have hl : raw30989step1Labels = raw30989step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30989step0 raw30989step0Labels permutation42 permutation7
    mixedMoment B raw30989step1 raw30989step1Labels = mixedMoment B raw30989step2 raw30989step2Labels := by
      have ha : raw30989step2 = -raw30989step1 := by apply Matrix.ext; change ∀ i j, raw30989step2 i j = -(raw30989step1 i j); unfold raw30989step2 raw30989step1; decide +kernel
      have hl : raw30989step2Labels = raw30989step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30989step2 raw30989step2Labels = mixedMoment B raw30989step3 raw30989step3Labels := by
      have ha : raw30989step3 = raw30989step2 := by apply Matrix.ext; unfold raw30989step3 raw30989step2; decide +kernel
      have hl : raw30989step2Labels = labelEmbedding1 ∘ raw30989step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30989step2 raw30989step2Labels raw30989step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2242 node2242Labels := by rfl

def raw30990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30990Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30990step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30990step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 3, -2], ![-2, 0, 2]]
def raw30990step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30990step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw30990step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30990step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw30990step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30990 raw30990Labels = mixedMoment B node2249 node2249Labels := by
  calc
    mixedMoment B raw30990 raw30990Labels = mixedMoment B raw30990step0 raw30990step0Labels := by
      have hz : ∀ j, raw30990 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30990step0 = (fun i j => raw30990 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30990step0 raw30990; decide +kernel
      have hl : raw30990step0Labels = raw30990Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30990 raw30990Labels permutation346 hz
    mixedMoment B raw30990step0 raw30990step0Labels = mixedMoment B raw30990step1 raw30990step1Labels := by
      have ha : raw30990step1 = (fun i j => raw30990step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30990step1 raw30990step0; decide +kernel
      have hl : raw30990step1Labels = raw30990step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30990step0 raw30990step0Labels permutation42 permutation7
    mixedMoment B raw30990step1 raw30990step1Labels = mixedMoment B raw30990step2 raw30990step2Labels := by
      have ha : raw30990step2 = -raw30990step1 := by apply Matrix.ext; change ∀ i j, raw30990step2 i j = -(raw30990step1 i j); unfold raw30990step2 raw30990step1; decide +kernel
      have hl : raw30990step2Labels = raw30990step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30990step2 raw30990step2Labels = mixedMoment B raw30990step3 raw30990step3Labels := by
      have ha : raw30990step3 = raw30990step2 := by apply Matrix.ext; unfold raw30990step3 raw30990step2; decide +kernel
      have hl : raw30990step2Labels = labelEmbedding1 ∘ raw30990step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30990step2 raw30990step2Labels raw30990step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2249 node2249Labels := by rfl

def raw30991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw30991Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30991step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw30991step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30991step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw30991step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30991step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw30991step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30991 raw30991Labels = mixedMoment B node2194 node2194Labels := by
  calc
    mixedMoment B raw30991 raw30991Labels = mixedMoment B raw30991step0 raw30991step0Labels := by
      have ha : raw30991step0 = (fun i j => raw30991 (permutation186 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30991step0 raw30991; decide +kernel
      have hl : raw30991step0Labels = raw30991Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30991 raw30991Labels permutation186 permutation7
    mixedMoment B raw30991step0 raw30991step0Labels = mixedMoment B raw30991step1 raw30991step1Labels := by
      have ha : raw30991step1 = -raw30991step0 := by apply Matrix.ext; change ∀ i j, raw30991step1 i j = -(raw30991step0 i j); unfold raw30991step1 raw30991step0; decide +kernel
      have hl : raw30991step1Labels = raw30991step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30991step1 raw30991step1Labels = mixedMoment B raw30991step2 raw30991step2Labels := by
      have ha : raw30991step2 = raw30991step1 := by apply Matrix.ext; unfold raw30991step2 raw30991step1; decide +kernel
      have hl : raw30991step1Labels = labelEmbedding1 ∘ raw30991step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30991step1 raw30991step1Labels raw30991step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2194 node2194Labels := by rfl

def raw30992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30992Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw30992step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30992step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw30992step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30992step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw30992step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30992step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw30992step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30992 raw30992Labels = mixedMoment B node2251 node2251Labels := by
  calc
    mixedMoment B raw30992 raw30992Labels = mixedMoment B raw30992step0 raw30992step0Labels := by
      have hz : ∀ j, raw30992 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30992step0 = (fun i j => raw30992 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30992step0 raw30992; decide +kernel
      have hl : raw30992step0Labels = raw30992Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30992 raw30992Labels permutation346 hz
    mixedMoment B raw30992step0 raw30992step0Labels = mixedMoment B raw30992step1 raw30992step1Labels := by
      have ha : raw30992step1 = (fun i j => raw30992step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30992step1 raw30992step0; decide +kernel
      have hl : raw30992step1Labels = raw30992step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30992step0 raw30992step0Labels permutation42 permutation7
    mixedMoment B raw30992step1 raw30992step1Labels = mixedMoment B raw30992step2 raw30992step2Labels := by
      have ha : raw30992step2 = -raw30992step1 := by apply Matrix.ext; change ∀ i j, raw30992step2 i j = -(raw30992step1 i j); unfold raw30992step2 raw30992step1; decide +kernel
      have hl : raw30992step2Labels = raw30992step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30992step2 raw30992step2Labels = mixedMoment B raw30992step3 raw30992step3Labels := by
      have ha : raw30992step3 = raw30992step2 := by apply Matrix.ext; unfold raw30992step3 raw30992step2; decide +kernel
      have hl : raw30992step2Labels = labelEmbedding1 ∘ raw30992step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30992step2 raw30992step2Labels raw30992step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2251 node2251Labels := by rfl

def raw30993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30993Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw30993step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30993step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw30993step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30993step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw30993step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30993step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw30993step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30993 raw30993Labels = mixedMoment B node2242 node2242Labels := by
  calc
    mixedMoment B raw30993 raw30993Labels = mixedMoment B raw30993step0 raw30993step0Labels := by
      have hz : ∀ j, raw30993 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30993step0 = (fun i j => raw30993 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30993step0 raw30993; decide +kernel
      have hl : raw30993step0Labels = raw30993Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30993 raw30993Labels permutation346 hz
    mixedMoment B raw30993step0 raw30993step0Labels = mixedMoment B raw30993step1 raw30993step1Labels := by
      have ha : raw30993step1 = (fun i j => raw30993step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30993step1 raw30993step0; decide +kernel
      have hl : raw30993step1Labels = raw30993step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30993step0 raw30993step0Labels permutation42 permutation7
    mixedMoment B raw30993step1 raw30993step1Labels = mixedMoment B raw30993step2 raw30993step2Labels := by
      have ha : raw30993step2 = -raw30993step1 := by apply Matrix.ext; change ∀ i j, raw30993step2 i j = -(raw30993step1 i j); unfold raw30993step2 raw30993step1; decide +kernel
      have hl : raw30993step2Labels = raw30993step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30993step2 raw30993step2Labels = mixedMoment B raw30993step3 raw30993step3Labels := by
      have ha : raw30993step3 = raw30993step2 := by apply Matrix.ext; unfold raw30993step3 raw30993step2; decide +kernel
      have hl : raw30993step2Labels = labelEmbedding1 ∘ raw30993step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30993step2 raw30993step2Labels raw30993step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2242 node2242Labels := by rfl

def raw30994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30994Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30994step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30994step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![3, -1, -2], ![2, -2, 0]]
def raw30994step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30994step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 3, -2], ![-2, -1, 3]]
def raw30994step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30994step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]
def raw30994step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30994step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -3, 2], ![2, 1, -3]]
def raw30994step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30994 raw30994Labels = mixedMoment B node2273 node2273Labels := by
  calc
    mixedMoment B raw30994 raw30994Labels = mixedMoment B raw30994step0 raw30994step0Labels := by
      have hz : ∀ j, raw30994 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30994step0 = (fun i j => raw30994 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30994step0 raw30994; decide +kernel
      have hl : raw30994step0Labels = raw30994Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30994 raw30994Labels permutation434 hz
    mixedMoment B raw30994step0 raw30994step0Labels = mixedMoment B raw30994step1 raw30994step1Labels := by
      have hz : ∀ j, raw30994step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30994step1 = (fun i j => raw30994step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30994step1 raw30994step0; decide +kernel
      have hl : raw30994step1Labels = raw30994step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30994step0 raw30994step0Labels permutation80 hz
    mixedMoment B raw30994step1 raw30994step1Labels = mixedMoment B raw30994step2 raw30994step2Labels := by
      have ha : raw30994step2 = (fun i j => raw30994step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30994step2 raw30994step1; decide +kernel
      have hl : raw30994step2Labels = raw30994step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30994step1 raw30994step1Labels permutation12 permutation7
    mixedMoment B raw30994step2 raw30994step2Labels = mixedMoment B raw30994step3 raw30994step3Labels := by
      have ha : raw30994step3 = -raw30994step2 := by apply Matrix.ext; change ∀ i j, raw30994step3 i j = -(raw30994step2 i j); unfold raw30994step3 raw30994step2; decide +kernel
      have hl : raw30994step3Labels = raw30994step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30994step3 raw30994step3Labels = mixedMoment B raw30994step4 raw30994step4Labels := by
      have ha : raw30994step4 = raw30994step3 := by apply Matrix.ext; unfold raw30994step4 raw30994step3; decide +kernel
      have hl : raw30994step3Labels = labelEmbedding1 ∘ raw30994step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30994step3 raw30994step3Labels raw30994step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2273 node2273Labels := by rfl

def raw30995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30995Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30995step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30995step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, -1, 3]]
def raw30995step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30995step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw30995step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30995step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw30995step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30995 raw30995Labels = mixedMoment B node2212 node2212Labels := by
  calc
    mixedMoment B raw30995 raw30995Labels = mixedMoment B raw30995step0 raw30995step0Labels := by
      have hz : ∀ j, raw30995 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30995step0 = (fun i j => raw30995 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30995step0 raw30995; decide +kernel
      have hl : raw30995step0Labels = raw30995Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30995 raw30995Labels permutation434 hz
    mixedMoment B raw30995step0 raw30995step0Labels = mixedMoment B raw30995step1 raw30995step1Labels := by
      have ha : raw30995step1 = (fun i j => raw30995step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30995step1 raw30995step0; decide +kernel
      have hl : raw30995step1Labels = raw30995step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30995step0 raw30995step0Labels permutation42 permutation7
    mixedMoment B raw30995step1 raw30995step1Labels = mixedMoment B raw30995step2 raw30995step2Labels := by
      have ha : raw30995step2 = -raw30995step1 := by apply Matrix.ext; change ∀ i j, raw30995step2 i j = -(raw30995step1 i j); unfold raw30995step2 raw30995step1; decide +kernel
      have hl : raw30995step2Labels = raw30995step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30995step2 raw30995step2Labels = mixedMoment B raw30995step3 raw30995step3Labels := by
      have ha : raw30995step3 = raw30995step2 := by apply Matrix.ext; unfold raw30995step3 raw30995step2; decide +kernel
      have hl : raw30995step2Labels = labelEmbedding1 ∘ raw30995step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30995step2 raw30995step2Labels raw30995step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2212 node2212Labels := by rfl

def raw30996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30996Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![3, -1, -2], ![2, -2, 0]]
def raw30996step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30996step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, -1, 3]]
def raw30996step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30996step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw30996step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30996step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw30996step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30996 raw30996Labels = mixedMoment B node2212 node2212Labels := by
  calc
    mixedMoment B raw30996 raw30996Labels = mixedMoment B raw30996step0 raw30996step0Labels := by
      have hz : ∀ j, raw30996 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30996step0 = (fun i j => raw30996 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30996step0 raw30996; decide +kernel
      have hl : raw30996step0Labels = raw30996Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30996 raw30996Labels permutation346 hz
    mixedMoment B raw30996step0 raw30996step0Labels = mixedMoment B raw30996step1 raw30996step1Labels := by
      have ha : raw30996step1 = (fun i j => raw30996step0 (permutation42 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30996step1 raw30996step0; decide +kernel
      have hl : raw30996step1Labels = raw30996step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30996step0 raw30996step0Labels permutation42 permutation7
    mixedMoment B raw30996step1 raw30996step1Labels = mixedMoment B raw30996step2 raw30996step2Labels := by
      have ha : raw30996step2 = -raw30996step1 := by apply Matrix.ext; change ∀ i j, raw30996step2 i j = -(raw30996step1 i j); unfold raw30996step2 raw30996step1; decide +kernel
      have hl : raw30996step2Labels = raw30996step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30996step2 raw30996step2Labels = mixedMoment B raw30996step3 raw30996step3Labels := by
      have ha : raw30996step3 = raw30996step2 := by apply Matrix.ext; unfold raw30996step3 raw30996step2; decide +kernel
      have hl : raw30996step2Labels = labelEmbedding1 ∘ raw30996step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30996step2 raw30996step2Labels raw30996step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2212 node2212Labels := by rfl

def raw30997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw30997Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![3, -1, -2], ![1, -1, 0]]
def raw30997step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30997step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![3, -1, -2], ![1, -1, 0]]
def raw30997step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30997step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 2, -1], ![-2, -1, 3]]
def raw30997step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30997step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw30997step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30997step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw30997step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30997 raw30997Labels = mixedMoment B node2261 node2261Labels := by
  calc
    mixedMoment B raw30997 raw30997Labels = mixedMoment B raw30997step0 raw30997step0Labels := by
      have hz : ∀ j, raw30997 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30997step0 = (fun i j => raw30997 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30997step0 raw30997; decide +kernel
      have hl : raw30997step0Labels = raw30997Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30997 raw30997Labels permutation434 hz
    mixedMoment B raw30997step0 raw30997step0Labels = mixedMoment B raw30997step1 raw30997step1Labels := by
      have hz : ∀ j, raw30997step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30997step1 = (fun i j => raw30997step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30997step1 raw30997step0; decide +kernel
      have hl : raw30997step1Labels = raw30997step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30997step0 raw30997step0Labels permutation80 hz
    mixedMoment B raw30997step1 raw30997step1Labels = mixedMoment B raw30997step2 raw30997step2Labels := by
      have ha : raw30997step2 = (fun i j => raw30997step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30997step2 raw30997step1; decide +kernel
      have hl : raw30997step2Labels = raw30997step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30997step1 raw30997step1Labels permutation12 permutation7
    mixedMoment B raw30997step2 raw30997step2Labels = mixedMoment B raw30997step3 raw30997step3Labels := by
      have ha : raw30997step3 = -raw30997step2 := by apply Matrix.ext; change ∀ i j, raw30997step3 i j = -(raw30997step2 i j); unfold raw30997step3 raw30997step2; decide +kernel
      have hl : raw30997step3Labels = raw30997step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30997step3 raw30997step3Labels = mixedMoment B raw30997step4 raw30997step4Labels := by
      have ha : raw30997step4 = raw30997step3 := by apply Matrix.ext; unfold raw30997step4 raw30997step3; decide +kernel
      have hl : raw30997step3Labels = labelEmbedding1 ∘ raw30997step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30997step3 raw30997step3Labels raw30997step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2261 node2261Labels := by rfl

def raw30998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30998Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30998step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30998step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, 0, -2], ![3, -3, 0]]
def raw30998step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30998step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![3, -1, -2]]
def raw30998step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30998step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![3, -1, -2]]
def raw30998step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30998 raw30998Labels = mixedMoment B node2163 node2163Labels := by
  calc
    mixedMoment B raw30998 raw30998Labels = mixedMoment B raw30998step0 raw30998step0Labels := by
      have hz : ∀ j, raw30998 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30998step0 = (fun i j => raw30998 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30998step0 raw30998; decide +kernel
      have hl : raw30998step0Labels = raw30998Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30998 raw30998Labels permutation434 hz
    mixedMoment B raw30998step0 raw30998step0Labels = mixedMoment B raw30998step1 raw30998step1Labels := by
      have hz : ∀ j, raw30998step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30998step1 = (fun i j => raw30998step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30998step1 raw30998step0; decide +kernel
      have hl : raw30998step1Labels = raw30998step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30998step0 raw30998step0Labels permutation80 hz
    mixedMoment B raw30998step1 raw30998step1Labels = mixedMoment B raw30998step2 raw30998step2Labels := by
      have ha : raw30998step2 = (fun i j => raw30998step1 (permutation30 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30998step2 raw30998step1; decide +kernel
      have hl : raw30998step2Labels = raw30998step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30998step1 raw30998step1Labels permutation30 permutation5
    mixedMoment B raw30998step2 raw30998step2Labels = mixedMoment B raw30998step3 raw30998step3Labels := by
      have ha : raw30998step3 = raw30998step2 := by apply Matrix.ext; unfold raw30998step3 raw30998step2; decide +kernel
      have hl : raw30998step2Labels = labelEmbedding1 ∘ raw30998step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30998step2 raw30998step2Labels raw30998step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2163 node2163Labels := by rfl

def raw30999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30999Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw30999step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30999step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw30999step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30999step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw30999step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30999 raw30999Labels = mixedMoment B node2162 node2162Labels := by
  calc
    mixedMoment B raw30999 raw30999Labels = mixedMoment B raw30999step0 raw30999step0Labels := by
      have hz : ∀ j, raw30999 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30999step0 = (fun i j => raw30999 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30999step0 raw30999; decide +kernel
      have hl : raw30999step0Labels = raw30999Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30999 raw30999Labels permutation434 hz
    mixedMoment B raw30999step0 raw30999step0Labels = mixedMoment B raw30999step1 raw30999step1Labels := by
      have ha : raw30999step1 = (fun i j => raw30999step0 (permutation147 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30999step1 raw30999step0; decide +kernel
      have hl : raw30999step1Labels = raw30999step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30999step0 raw30999step0Labels permutation147 permutation5
    mixedMoment B raw30999step1 raw30999step1Labels = mixedMoment B raw30999step2 raw30999step2Labels := by
      have ha : raw30999step2 = raw30999step1 := by apply Matrix.ext; unfold raw30999step2 raw30999step1; decide +kernel
      have hl : raw30999step1Labels = labelEmbedding1 ∘ raw30999step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30999step1 raw30999step1Labels raw30999step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2162 node2162Labels := by rfl

def raw31000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw31000Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![-1, 1, 0], ![2, 0, -2], ![3, -3, 0]]
def raw31000step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31000step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw31000step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31000step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 3, -3], ![1, 0, -1], ![2, -1, -1]]
def raw31000step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31000 raw31000Labels = mixedMoment B node2162 node2162Labels := by
  calc
    mixedMoment B raw31000 raw31000Labels = mixedMoment B raw31000step0 raw31000step0Labels := by
      have hz : ∀ j, raw31000 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31000step0 = (fun i j => raw31000 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31000step0 raw31000; decide +kernel
      have hl : raw31000step0Labels = raw31000Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31000 raw31000Labels permutation346 hz
    mixedMoment B raw31000step0 raw31000step0Labels = mixedMoment B raw31000step1 raw31000step1Labels := by
      have ha : raw31000step1 = (fun i j => raw31000step0 (permutation147 i) (permutation5 j)) := by apply Matrix.ext; unfold raw31000step1 raw31000step0; decide +kernel
      have hl : raw31000step1Labels = raw31000step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31000step0 raw31000step0Labels permutation147 permutation5
    mixedMoment B raw31000step1 raw31000step1Labels = mixedMoment B raw31000step2 raw31000step2Labels := by
      have ha : raw31000step2 = raw31000step1 := by apply Matrix.ext; unfold raw31000step2 raw31000step1; decide +kernel
      have hl : raw31000step1Labels = labelEmbedding1 ∘ raw31000step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31000step1 raw31000step1Labels raw31000step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2162 node2162Labels := by rfl

def raw31001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw31001Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw31001step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31001step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![3, -3, 0]]
def raw31001step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw31001step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]
def raw31001step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw31001step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -2, 1], ![2, -1, -1]]
def raw31001step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31001 raw31001Labels = mixedMoment B node2282 node2282Labels := by
  calc
    mixedMoment B raw31001 raw31001Labels = mixedMoment B raw31001step0 raw31001step0Labels := by
      have hz : ∀ j, raw31001 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31001step0 = (fun i j => raw31001 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31001step0 raw31001; decide +kernel
      have hl : raw31001step0Labels = raw31001Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31001 raw31001Labels permutation434 hz
    mixedMoment B raw31001step0 raw31001step0Labels = mixedMoment B raw31001step1 raw31001step1Labels := by
      have hz : ∀ j, raw31001step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31001step1 = (fun i j => raw31001step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31001step1 raw31001step0; decide +kernel
      have hl : raw31001step1Labels = raw31001step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31001step0 raw31001step0Labels permutation80 hz
    mixedMoment B raw31001step1 raw31001step1Labels = mixedMoment B raw31001step2 raw31001step2Labels := by
      have ha : raw31001step2 = (fun i j => raw31001step1 (permutation27 i) (permutation5 j)) := by apply Matrix.ext; unfold raw31001step2 raw31001step1; decide +kernel
      have hl : raw31001step2Labels = raw31001step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31001step1 raw31001step1Labels permutation27 permutation5
    mixedMoment B raw31001step2 raw31001step2Labels = mixedMoment B raw31001step3 raw31001step3Labels := by
      have ha : raw31001step3 = raw31001step2 := by apply Matrix.ext; unfold raw31001step3 raw31001step2; decide +kernel
      have hl : raw31001step2Labels = labelEmbedding1 ∘ raw31001step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31001step2 raw31001step2Labels raw31001step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2282 node2282Labels := by rfl

def raw31002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31002Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31002step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31002step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 3, -1], ![2, 0, -2], ![2, -2, 0]]
def raw31002step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31002step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, -2, 3], ![-2, 2, 0]]
def raw31002step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31002step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 2, -3], ![2, -2, 0]]
def raw31002step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31002 raw31002Labels = mixedMoment B node3056 node3056Labels := by
  calc
    mixedMoment B raw31002 raw31002Labels = mixedMoment B raw31002step0 raw31002step0Labels := by
      have hz : ∀ j, raw31002 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31002step0 = (fun i j => raw31002 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31002step0 raw31002; decide +kernel
      have hl : raw31002step0Labels = raw31002Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31002 raw31002Labels permutation434 hz
    mixedMoment B raw31002step0 raw31002step0Labels = mixedMoment B raw31002step1 raw31002step1Labels := by
      have hz : ∀ j, raw31002step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31002step1 = (fun i j => raw31002step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31002step1 raw31002step0; decide +kernel
      have hl : raw31002step1Labels = raw31002step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31002step0 raw31002step0Labels permutation80 hz
    mixedMoment B raw31002step1 raw31002step1Labels = mixedMoment B raw31002step2 raw31002step2Labels := by
      have ha : raw31002step2 = (fun i j => raw31002step1 (permutation16 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31002step2 raw31002step1; decide +kernel
      have hl : raw31002step2Labels = raw31002step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31002step1 raw31002step1Labels permutation16 permutation4
    mixedMoment B raw31002step2 raw31002step2Labels = mixedMoment B raw31002step3 raw31002step3Labels := by
      have ha : raw31002step3 = -raw31002step2 := by apply Matrix.ext; change ∀ i j, raw31002step3 i j = -(raw31002step2 i j); unfold raw31002step3 raw31002step2; decide +kernel
      have hl : raw31002step3Labels = raw31002step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3056 node3056Labels := by rfl

def raw31003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31003Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31003step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31003step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31003step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31003 raw31003Labels = mixedMoment B node1826 node1826Labels := by
  calc
    mixedMoment B raw31003 raw31003Labels = mixedMoment B raw31003step0 raw31003step0Labels := by
      have hz : ∀ j, raw31003 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31003step0 = (fun i j => raw31003 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31003step0 raw31003; decide +kernel
      have hl : raw31003step0Labels = raw31003Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31003 raw31003Labels permutation434 hz
    mixedMoment B raw31003step0 raw31003step0Labels = mixedMoment B raw31003step1 raw31003step1Labels := by
      have ha : raw31003step1 = (fun i j => raw31003step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31003step1 raw31003step0; decide +kernel
      have hl : raw31003step1Labels = raw31003step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31003step0 raw31003step0Labels permutation33 permutation2
    _ = mixedMoment B node1826 node1826Labels := by rfl

def raw31004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31004Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31004step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31004step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31004step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31004 raw31004Labels = mixedMoment B node1826 node1826Labels := by
  calc
    mixedMoment B raw31004 raw31004Labels = mixedMoment B raw31004step0 raw31004step0Labels := by
      have hz : ∀ j, raw31004 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31004step0 = (fun i j => raw31004 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31004step0 raw31004; decide +kernel
      have hl : raw31004step0Labels = raw31004Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31004 raw31004Labels permutation346 hz
    mixedMoment B raw31004step0 raw31004step0Labels = mixedMoment B raw31004step1 raw31004step1Labels := by
      have ha : raw31004step1 = (fun i j => raw31004step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31004step1 raw31004step0; decide +kernel
      have hl : raw31004step1Labels = raw31004step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31004step0 raw31004step0Labels permutation33 permutation2
    _ = mixedMoment B node1826 node1826Labels := by rfl

def raw31005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw31005Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31005step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![0, 0, 0], ![3, -1, -2], ![2, -2, 0]]
def raw31005step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31005step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![3, -1, -2], ![2, -2, 0]]
def raw31005step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31005step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![2, -2, 0], ![3, -1, -2]]
def raw31005step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31005 raw31005Labels = mixedMoment B node1830 node1830Labels := by
  calc
    mixedMoment B raw31005 raw31005Labels = mixedMoment B raw31005step0 raw31005step0Labels := by
      have hz : ∀ j, raw31005 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31005step0 = (fun i j => raw31005 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31005step0 raw31005; decide +kernel
      have hl : raw31005step0Labels = raw31005Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31005 raw31005Labels permutation434 hz
    mixedMoment B raw31005step0 raw31005step0Labels = mixedMoment B raw31005step1 raw31005step1Labels := by
      have hz : ∀ j, raw31005step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31005step1 = (fun i j => raw31005step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31005step1 raw31005step0; decide +kernel
      have hl : raw31005step1Labels = raw31005step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31005step0 raw31005step0Labels permutation80 hz
    mixedMoment B raw31005step1 raw31005step1Labels = mixedMoment B raw31005step2 raw31005step2Labels := by
      have ha : raw31005step2 = (fun i j => raw31005step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31005step2 raw31005step1; decide +kernel
      have hl : raw31005step2Labels = raw31005step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31005step1 raw31005step1Labels permutation9 permutation2
    _ = mixedMoment B node1830 node1830Labels := by rfl

def raw31006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw31006Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31006step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31006step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31006 raw31006Labels = mixedMoment B node1974 node1974Labels := by
  calc
    mixedMoment B raw31006 raw31006Labels = mixedMoment B raw31006step0 raw31006step0Labels := by
      have ha : raw31006step0 = (fun i j => raw31006 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31006step0 raw31006; decide +kernel
      have hl : raw31006step0Labels = raw31006Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31006 raw31006Labels permutation201 permutation2
    _ = mixedMoment B node1974 node1974Labels := by rfl

def raw31007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw31007Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw31007step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31007 raw31007Labels = mixedMoment B node2108 node2108Labels := by
  calc
    mixedMoment B raw31007 raw31007Labels = mixedMoment B raw31007step0 raw31007step0Labels := by
      have hz : ∀ j, raw31007 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31007step0 = (fun i j => raw31007 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31007step0 raw31007; decide +kernel
      have hl : raw31007step0Labels = raw31007Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31007 raw31007Labels permutation434 hz
    _ = mixedMoment B node2108 node2108Labels := by rfl

def raw31008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw31008Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31008step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2], ![1, -1, 0]]
def raw31008step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31008step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw31008step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31008 raw31008Labels = mixedMoment B node2106 node2106Labels := by
  calc
    mixedMoment B raw31008 raw31008Labels = mixedMoment B raw31008step0 raw31008step0Labels := by
      have hz : ∀ j, raw31008 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31008step0 = (fun i j => raw31008 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31008step0 raw31008; decide +kernel
      have hl : raw31008step0Labels = raw31008Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31008 raw31008Labels permutation434 hz
    mixedMoment B raw31008step0 raw31008step0Labels = mixedMoment B raw31008step1 raw31008step1Labels := by
      have ha : raw31008step1 = (fun i j => raw31008step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31008step1 raw31008step0; decide +kernel
      have hl : raw31008step1Labels = raw31008step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31008step0 raw31008step0Labels permutation33 permutation2
    _ = mixedMoment B node2106 node2106Labels := by rfl

def raw31009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31009Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31009step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31009step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![2, -2, 0], ![2, 0, -2]]
def raw31009step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31009step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31009step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31009 raw31009Labels = mixedMoment B node5389 node5389Labels := by
  calc
    mixedMoment B raw31009 raw31009Labels = mixedMoment B raw31009step0 raw31009step0Labels := by
      have hz : ∀ j, raw31009 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31009step0 = (fun i j => raw31009 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31009step0 raw31009; decide +kernel
      have hl : raw31009step0Labels = raw31009Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31009 raw31009Labels permutation434 hz
    mixedMoment B raw31009step0 raw31009step0Labels = mixedMoment B raw31009step1 raw31009step1Labels := by
      have hz : ∀ j, raw31009step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31009step1 = (fun i j => raw31009step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31009step1 raw31009step0; decide +kernel
      have hl : raw31009step1Labels = raw31009step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31009step0 raw31009step0Labels permutation80 hz
    mixedMoment B raw31009step1 raw31009step1Labels = mixedMoment B raw31009step2 raw31009step2Labels := by
      have ha : raw31009step2 = (fun i j => raw31009step1 (permutation14 i) (permutation2 j)) := by apply Matrix.ext; unfold raw31009step2 raw31009step1; decide +kernel
      have hl : raw31009step2Labels = raw31009step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31009step1 raw31009step1Labels permutation14 permutation2
    _ = mixedMoment B node5389 node5389Labels := by rfl

def raw31010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31010Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31010step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31010step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31010step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw31010step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31010step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw31010step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31010step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw31010step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31010 raw31010Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw31010 raw31010Labels = mixedMoment B raw31010step0 raw31010step0Labels := by
      have hz : ∀ j, raw31010 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31010step0 = (fun i j => raw31010 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31010step0 raw31010; decide +kernel
      have hl : raw31010step0Labels = raw31010Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31010 raw31010Labels permutation434 hz
    mixedMoment B raw31010step0 raw31010step0Labels = mixedMoment B raw31010step1 raw31010step1Labels := by
      have ha : raw31010step1 = (fun i j => raw31010step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31010step1 raw31010step0; decide +kernel
      have hl : raw31010step1Labels = raw31010step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31010step0 raw31010step0Labels permutation125 permutation3
    mixedMoment B raw31010step1 raw31010step1Labels = mixedMoment B raw31010step2 raw31010step2Labels := by
      have ha : raw31010step2 = -raw31010step1 := by apply Matrix.ext; change ∀ i j, raw31010step2 i j = -(raw31010step1 i j); unfold raw31010step2 raw31010step1; decide +kernel
      have hl : raw31010step2Labels = raw31010step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31010step2 raw31010step2Labels = mixedMoment B raw31010step3 raw31010step3Labels := by
      have ha : raw31010step3 = raw31010step2 := by apply Matrix.ext; unfold raw31010step3 raw31010step2; decide +kernel
      have hl : raw31010step2Labels = labelEmbedding6 ∘ raw31010step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31010step2 raw31010step2Labels raw31010step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5384 node5384Labels := by rfl

def raw31011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31011Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31011step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31011step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31011step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw31011step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31011step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw31011step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31011step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw31011step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31011 raw31011Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw31011 raw31011Labels = mixedMoment B raw31011step0 raw31011step0Labels := by
      have hz : ∀ j, raw31011 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31011step0 = (fun i j => raw31011 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31011step0 raw31011; decide +kernel
      have hl : raw31011step0Labels = raw31011Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31011 raw31011Labels permutation346 hz
    mixedMoment B raw31011step0 raw31011step0Labels = mixedMoment B raw31011step1 raw31011step1Labels := by
      have ha : raw31011step1 = (fun i j => raw31011step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31011step1 raw31011step0; decide +kernel
      have hl : raw31011step1Labels = raw31011step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31011step0 raw31011step0Labels permutation125 permutation3
    mixedMoment B raw31011step1 raw31011step1Labels = mixedMoment B raw31011step2 raw31011step2Labels := by
      have ha : raw31011step2 = -raw31011step1 := by apply Matrix.ext; change ∀ i j, raw31011step2 i j = -(raw31011step1 i j); unfold raw31011step2 raw31011step1; decide +kernel
      have hl : raw31011step2Labels = raw31011step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31011step2 raw31011step2Labels = mixedMoment B raw31011step3 raw31011step3Labels := by
      have ha : raw31011step3 = raw31011step2 := by apply Matrix.ext; unfold raw31011step3 raw31011step2; decide +kernel
      have hl : raw31011step2Labels = labelEmbedding6 ∘ raw31011step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31011step2 raw31011step2Labels raw31011step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5384 node5384Labels := by rfl

def raw31012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw31012Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw31012step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31012step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw31012step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31012step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw31012step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31012step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw31012step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31012 raw31012Labels = mixedMoment B node4898 node4898Labels := by
  calc
    mixedMoment B raw31012 raw31012Labels = mixedMoment B raw31012step0 raw31012step0Labels := by
      have hz : ∀ j, raw31012 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31012step0 = (fun i j => raw31012 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31012step0 raw31012; decide +kernel
      have hl : raw31012step0Labels = raw31012Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31012 raw31012Labels permutation434 hz
    mixedMoment B raw31012step0 raw31012step0Labels = mixedMoment B raw31012step1 raw31012step1Labels := by
      have hz : ∀ j, raw31012step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31012step1 = (fun i j => raw31012step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31012step1 raw31012step0; decide +kernel
      have hl : raw31012step1Labels = raw31012step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31012step0 raw31012step0Labels permutation80 hz
    mixedMoment B raw31012step1 raw31012step1Labels = mixedMoment B raw31012step2 raw31012step2Labels := by
      have ha : raw31012step2 = (fun i j => raw31012step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31012step2 raw31012step1; decide +kernel
      have hl : raw31012step2Labels = raw31012step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31012step1 raw31012step1Labels permutation8 permutation3
    mixedMoment B raw31012step2 raw31012step2Labels = mixedMoment B raw31012step3 raw31012step3Labels := by
      have ha : raw31012step3 = raw31012step2 := by apply Matrix.ext; unfold raw31012step3 raw31012step2; decide +kernel
      have hl : raw31012step2Labels = labelEmbedding6 ∘ raw31012step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31012step2 raw31012step2Labels raw31012step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4898 node4898Labels := by rfl

def raw31013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31013Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31013step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31013step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31013step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31013step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31013step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31013 raw31013Labels = mixedMoment B node4238 node4238Labels := by
  calc
    mixedMoment B raw31013 raw31013Labels = mixedMoment B raw31013step0 raw31013step0Labels := by
      have hz : ∀ j, raw31013 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31013step0 = (fun i j => raw31013 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31013step0 raw31013; decide +kernel
      have hl : raw31013step0Labels = raw31013Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31013 raw31013Labels permutation434 hz
    mixedMoment B raw31013step0 raw31013step0Labels = mixedMoment B raw31013step1 raw31013step1Labels := by
      have ha : raw31013step1 = (fun i j => raw31013step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31013step1 raw31013step0; decide +kernel
      have hl : raw31013step1Labels = raw31013step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31013step0 raw31013step0Labels permutation33 permutation3
    mixedMoment B raw31013step1 raw31013step1Labels = mixedMoment B raw31013step2 raw31013step2Labels := by
      have ha : raw31013step2 = raw31013step1 := by apply Matrix.ext; unfold raw31013step2 raw31013step1; decide +kernel
      have hl : raw31013step1Labels = labelEmbedding6 ∘ raw31013step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31013step1 raw31013step1Labels raw31013step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4238 node4238Labels := by rfl

def raw31014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31014Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31014step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31014step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31014step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31014step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31014step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31014 raw31014Labels = mixedMoment B node4688 node4688Labels := by
  calc
    mixedMoment B raw31014 raw31014Labels = mixedMoment B raw31014step0 raw31014step0Labels := by
      have hz : ∀ j, raw31014 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31014step0 = (fun i j => raw31014 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31014step0 raw31014; decide +kernel
      have hl : raw31014step0Labels = raw31014Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31014 raw31014Labels permutation434 hz
    mixedMoment B raw31014step0 raw31014step0Labels = mixedMoment B raw31014step1 raw31014step1Labels := by
      have ha : raw31014step1 = (fun i j => raw31014step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31014step1 raw31014step0; decide +kernel
      have hl : raw31014step1Labels = raw31014step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31014step0 raw31014step0Labels permutation33 permutation3
    mixedMoment B raw31014step1 raw31014step1Labels = mixedMoment B raw31014step2 raw31014step2Labels := by
      have ha : raw31014step2 = raw31014step1 := by apply Matrix.ext; unfold raw31014step2 raw31014step1; decide +kernel
      have hl : raw31014step1Labels = labelEmbedding6 ∘ raw31014step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31014step1 raw31014step1Labels raw31014step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4688 node4688Labels := by rfl

def raw31015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31015Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31015step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31015step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31015step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31015step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31015 raw31015Labels = mixedMoment B node4724 node4724Labels := by
  calc
    mixedMoment B raw31015 raw31015Labels = mixedMoment B raw31015step0 raw31015step0Labels := by
      have ha : raw31015step0 = (fun i j => raw31015 (permutation201 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31015step0 raw31015; decide +kernel
      have hl : raw31015step0Labels = raw31015Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31015 raw31015Labels permutation201 permutation3
    mixedMoment B raw31015step0 raw31015step0Labels = mixedMoment B raw31015step1 raw31015step1Labels := by
      have ha : raw31015step1 = raw31015step0 := by apply Matrix.ext; unfold raw31015step1 raw31015step0; decide +kernel
      have hl : raw31015step0Labels = labelEmbedding6 ∘ raw31015step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31015step0 raw31015step0Labels raw31015step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4724 node4724Labels := by rfl

def raw31016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw31016Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw31016step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31016step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw31016step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31016step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw31016step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31016 raw31016Labels = mixedMoment B node4860 node4860Labels := by
  calc
    mixedMoment B raw31016 raw31016Labels = mixedMoment B raw31016step0 raw31016step0Labels := by
      have hz : ∀ j, raw31016 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31016step0 = (fun i j => raw31016 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31016step0 raw31016; decide +kernel
      have hl : raw31016step0Labels = raw31016Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31016 raw31016Labels permutation434 hz
    mixedMoment B raw31016step0 raw31016step0Labels = mixedMoment B raw31016step1 raw31016step1Labels := by
      have ha : raw31016step1 = (fun i j => raw31016step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31016step1 raw31016step0; decide +kernel
      have hl : raw31016step1Labels = raw31016step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31016step0 raw31016step0Labels permutation36 permutation3
    mixedMoment B raw31016step1 raw31016step1Labels = mixedMoment B raw31016step2 raw31016step2Labels := by
      have ha : raw31016step2 = raw31016step1 := by apply Matrix.ext; unfold raw31016step2 raw31016step1; decide +kernel
      have hl : raw31016step1Labels = labelEmbedding6 ∘ raw31016step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31016step1 raw31016step1Labels raw31016step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4860 node4860Labels := by rfl

def raw31017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31017Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31017step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31017step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31017step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31017step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31017step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31017 raw31017Labels = mixedMoment B node4238 node4238Labels := by
  calc
    mixedMoment B raw31017 raw31017Labels = mixedMoment B raw31017step0 raw31017step0Labels := by
      have hz : ∀ j, raw31017 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31017step0 = (fun i j => raw31017 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31017step0 raw31017; decide +kernel
      have hl : raw31017step0Labels = raw31017Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31017 raw31017Labels permutation346 hz
    mixedMoment B raw31017step0 raw31017step0Labels = mixedMoment B raw31017step1 raw31017step1Labels := by
      have ha : raw31017step1 = (fun i j => raw31017step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31017step1 raw31017step0; decide +kernel
      have hl : raw31017step1Labels = raw31017step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31017step0 raw31017step0Labels permutation33 permutation3
    mixedMoment B raw31017step1 raw31017step1Labels = mixedMoment B raw31017step2 raw31017step2Labels := by
      have ha : raw31017step2 = raw31017step1 := by apply Matrix.ext; unfold raw31017step2 raw31017step1; decide +kernel
      have hl : raw31017step1Labels = labelEmbedding6 ∘ raw31017step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31017step1 raw31017step1Labels raw31017step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4238 node4238Labels := by rfl

def raw31018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31018Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31018step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31018step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31018step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31018step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31018step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31018step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31018 raw31018Labels = mixedMoment B node4688 node4688Labels := by
  calc
    mixedMoment B raw31018 raw31018Labels = mixedMoment B raw31018step0 raw31018step0Labels := by
      have hz : ∀ j, raw31018 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31018step0 = (fun i j => raw31018 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31018step0 raw31018; decide +kernel
      have hl : raw31018step0Labels = raw31018Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31018 raw31018Labels permutation346 hz
    mixedMoment B raw31018step0 raw31018step0Labels = mixedMoment B raw31018step1 raw31018step1Labels := by
      have ha : raw31018step1 = (fun i j => raw31018step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31018step1 raw31018step0; decide +kernel
      have hl : raw31018step1Labels = raw31018step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31018step0 raw31018step0Labels permutation33 permutation3
    mixedMoment B raw31018step1 raw31018step1Labels = mixedMoment B raw31018step2 raw31018step2Labels := by
      have ha : raw31018step2 = raw31018step1 := by apply Matrix.ext; unfold raw31018step2 raw31018step1; decide +kernel
      have hl : raw31018step1Labels = labelEmbedding6 ∘ raw31018step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31018step1 raw31018step1Labels raw31018step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4688 node4688Labels := by rfl

def raw31019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31019Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31019step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31019step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31019step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31019step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31019 raw31019Labels = mixedMoment B node4724 node4724Labels := by
  calc
    mixedMoment B raw31019 raw31019Labels = mixedMoment B raw31019step0 raw31019step0Labels := by
      have ha : raw31019step0 = (fun i j => raw31019 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31019step0 raw31019; decide +kernel
      have hl : raw31019step0Labels = raw31019Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31019 raw31019Labels permutation177 permutation3
    mixedMoment B raw31019step0 raw31019step0Labels = mixedMoment B raw31019step1 raw31019step1Labels := by
      have ha : raw31019step1 = raw31019step0 := by apply Matrix.ext; unfold raw31019step1 raw31019step0; decide +kernel
      have hl : raw31019step0Labels = labelEmbedding6 ∘ raw31019step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31019step0 raw31019step0Labels raw31019step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4724 node4724Labels := by rfl

def raw31020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw31020Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw31020step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31020step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![3, -3, 0], ![2, 0, -2]]
def raw31020step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31020step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -2, 0], ![3, 0, -3]]
def raw31020step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31020step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -2, 0], ![3, 0, -3]]
def raw31020step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31020 raw31020Labels = mixedMoment B node4241 node4241Labels := by
  calc
    mixedMoment B raw31020 raw31020Labels = mixedMoment B raw31020step0 raw31020step0Labels := by
      have hz : ∀ j, raw31020 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31020step0 = (fun i j => raw31020 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31020step0 raw31020; decide +kernel
      have hl : raw31020step0Labels = raw31020Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31020 raw31020Labels permutation434 hz
    mixedMoment B raw31020step0 raw31020step0Labels = mixedMoment B raw31020step1 raw31020step1Labels := by
      have hz : ∀ j, raw31020step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31020step1 = (fun i j => raw31020step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31020step1 raw31020step0; decide +kernel
      have hl : raw31020step1Labels = raw31020step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31020step0 raw31020step0Labels permutation80 hz
    mixedMoment B raw31020step1 raw31020step1Labels = mixedMoment B raw31020step2 raw31020step2Labels := by
      have ha : raw31020step2 = (fun i j => raw31020step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31020step2 raw31020step1; decide +kernel
      have hl : raw31020step2Labels = raw31020step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31020step1 raw31020step1Labels permutation9 permutation3
    mixedMoment B raw31020step2 raw31020step2Labels = mixedMoment B raw31020step3 raw31020step3Labels := by
      have ha : raw31020step3 = raw31020step2 := by apply Matrix.ext; unfold raw31020step3 raw31020step2; decide +kernel
      have hl : raw31020step2Labels = labelEmbedding6 ∘ raw31020step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31020step2 raw31020step2Labels raw31020step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4241 node4241Labels := by rfl

def raw31021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw31021Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw31021step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31021step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![3, -3, 0], ![2, 0, -2]]
def raw31021step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31021step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def raw31021step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31021step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def raw31021step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31021 raw31021Labels = mixedMoment B node4691 node4691Labels := by
  calc
    mixedMoment B raw31021 raw31021Labels = mixedMoment B raw31021step0 raw31021step0Labels := by
      have hz : ∀ j, raw31021 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31021step0 = (fun i j => raw31021 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31021step0 raw31021; decide +kernel
      have hl : raw31021step0Labels = raw31021Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31021 raw31021Labels permutation434 hz
    mixedMoment B raw31021step0 raw31021step0Labels = mixedMoment B raw31021step1 raw31021step1Labels := by
      have hz : ∀ j, raw31021step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31021step1 = (fun i j => raw31021step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31021step1 raw31021step0; decide +kernel
      have hl : raw31021step1Labels = raw31021step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31021step0 raw31021step0Labels permutation80 hz
    mixedMoment B raw31021step1 raw31021step1Labels = mixedMoment B raw31021step2 raw31021step2Labels := by
      have ha : raw31021step2 = (fun i j => raw31021step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31021step2 raw31021step1; decide +kernel
      have hl : raw31021step2Labels = raw31021step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31021step1 raw31021step1Labels permutation9 permutation3
    mixedMoment B raw31021step2 raw31021step2Labels = mixedMoment B raw31021step3 raw31021step3Labels := by
      have ha : raw31021step3 = raw31021step2 := by apply Matrix.ext; unfold raw31021step3 raw31021step2; decide +kernel
      have hl : raw31021step2Labels = labelEmbedding6 ∘ raw31021step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31021step2 raw31021step2Labels raw31021step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4691 node4691Labels := by rfl

def raw31022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw31022Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31022step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw31022step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31022step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-3, 0, 3]]
def raw31022step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31022step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw31022step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31022step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw31022step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31022 raw31022Labels = mixedMoment B node4673 node4673Labels := by
  calc
    mixedMoment B raw31022 raw31022Labels = mixedMoment B raw31022step0 raw31022step0Labels := by
      have hz : ∀ j, raw31022 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31022step0 = (fun i j => raw31022 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31022step0 raw31022; decide +kernel
      have hl : raw31022step0Labels = raw31022Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31022 raw31022Labels permutation434 hz
    mixedMoment B raw31022step0 raw31022step0Labels = mixedMoment B raw31022step1 raw31022step1Labels := by
      have ha : raw31022step1 = (fun i j => raw31022step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31022step1 raw31022step0; decide +kernel
      have hl : raw31022step1Labels = raw31022step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31022step0 raw31022step0Labels permutation125 permutation3
    mixedMoment B raw31022step1 raw31022step1Labels = mixedMoment B raw31022step2 raw31022step2Labels := by
      have ha : raw31022step2 = -raw31022step1 := by apply Matrix.ext; change ∀ i j, raw31022step2 i j = -(raw31022step1 i j); unfold raw31022step2 raw31022step1; decide +kernel
      have hl : raw31022step2Labels = raw31022step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31022step2 raw31022step2Labels = mixedMoment B raw31022step3 raw31022step3Labels := by
      have ha : raw31022step3 = raw31022step2 := by apply Matrix.ext; unfold raw31022step3 raw31022step2; decide +kernel
      have hl : raw31022step2Labels = labelEmbedding6 ∘ raw31022step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31022step2 raw31022step2Labels raw31022step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4673 node4673Labels := by rfl

def raw31023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw31023Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31023step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw31023step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31023step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-3, 0, 3]]
def raw31023step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31023step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw31023step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31023step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw31023step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31023 raw31023Labels = mixedMoment B node4673 node4673Labels := by
  calc
    mixedMoment B raw31023 raw31023Labels = mixedMoment B raw31023step0 raw31023step0Labels := by
      have hz : ∀ j, raw31023 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31023step0 = (fun i j => raw31023 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31023step0 raw31023; decide +kernel
      have hl : raw31023step0Labels = raw31023Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31023 raw31023Labels permutation346 hz
    mixedMoment B raw31023step0 raw31023step0Labels = mixedMoment B raw31023step1 raw31023step1Labels := by
      have ha : raw31023step1 = (fun i j => raw31023step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31023step1 raw31023step0; decide +kernel
      have hl : raw31023step1Labels = raw31023step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31023step0 raw31023step0Labels permutation125 permutation3
    mixedMoment B raw31023step1 raw31023step1Labels = mixedMoment B raw31023step2 raw31023step2Labels := by
      have ha : raw31023step2 = -raw31023step1 := by apply Matrix.ext; change ∀ i j, raw31023step2 i j = -(raw31023step1 i j); unfold raw31023step2 raw31023step1; decide +kernel
      have hl : raw31023step2Labels = raw31023step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31023step2 raw31023step2Labels = mixedMoment B raw31023step3 raw31023step3Labels := by
      have ha : raw31023step3 = raw31023step2 := by apply Matrix.ext; unfold raw31023step3 raw31023step2; decide +kernel
      have hl : raw31023step2Labels = labelEmbedding6 ∘ raw31023step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31023step2 raw31023step2Labels raw31023step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4673 node4673Labels := by rfl

def raw31024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw31024Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw31024step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31024step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![3, -3, 0], ![1, 1, -2]]
def raw31024step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31024step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![3, 0, -3]]
def raw31024step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31024step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![3, 0, -3]]
def raw31024step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31024 raw31024Labels = mixedMoment B node4862 node4862Labels := by
  calc
    mixedMoment B raw31024 raw31024Labels = mixedMoment B raw31024step0 raw31024step0Labels := by
      have hz : ∀ j, raw31024 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31024step0 = (fun i j => raw31024 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31024step0 raw31024; decide +kernel
      have hl : raw31024step0Labels = raw31024Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31024 raw31024Labels permutation434 hz
    mixedMoment B raw31024step0 raw31024step0Labels = mixedMoment B raw31024step1 raw31024step1Labels := by
      have hz : ∀ j, raw31024step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31024step1 = (fun i j => raw31024step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31024step1 raw31024step0; decide +kernel
      have hl : raw31024step1Labels = raw31024step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31024step0 raw31024step0Labels permutation80 hz
    mixedMoment B raw31024step1 raw31024step1Labels = mixedMoment B raw31024step2 raw31024step2Labels := by
      have ha : raw31024step2 = (fun i j => raw31024step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31024step2 raw31024step1; decide +kernel
      have hl : raw31024step2Labels = raw31024step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31024step1 raw31024step1Labels permutation9 permutation3
    mixedMoment B raw31024step2 raw31024step2Labels = mixedMoment B raw31024step3 raw31024step3Labels := by
      have ha : raw31024step3 = raw31024step2 := by apply Matrix.ext; unfold raw31024step3 raw31024step2; decide +kernel
      have hl : raw31024step2Labels = labelEmbedding6 ∘ raw31024step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31024step2 raw31024step2Labels raw31024step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4862 node4862Labels := by rfl

def raw31025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw31025Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw31025step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31025step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![2, -2, 0], ![3, -1, -2]]
def raw31025step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31025step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw31025step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31025step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw31025step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31025 raw31025Labels = mixedMoment B node4243 node4243Labels := by
  calc
    mixedMoment B raw31025 raw31025Labels = mixedMoment B raw31025step0 raw31025step0Labels := by
      have hz : ∀ j, raw31025 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31025step0 = (fun i j => raw31025 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31025step0 raw31025; decide +kernel
      have hl : raw31025step0Labels = raw31025Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31025 raw31025Labels permutation434 hz
    mixedMoment B raw31025step0 raw31025step0Labels = mixedMoment B raw31025step1 raw31025step1Labels := by
      have hz : ∀ j, raw31025step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31025step1 = (fun i j => raw31025step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31025step1 raw31025step0; decide +kernel
      have hl : raw31025step1Labels = raw31025step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31025step0 raw31025step0Labels permutation80 hz
    mixedMoment B raw31025step1 raw31025step1Labels = mixedMoment B raw31025step2 raw31025step2Labels := by
      have ha : raw31025step2 = (fun i j => raw31025step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31025step2 raw31025step1; decide +kernel
      have hl : raw31025step2Labels = raw31025step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31025step1 raw31025step1Labels permutation8 permutation3
    mixedMoment B raw31025step2 raw31025step2Labels = mixedMoment B raw31025step3 raw31025step3Labels := by
      have ha : raw31025step3 = raw31025step2 := by apply Matrix.ext; unfold raw31025step3 raw31025step2; decide +kernel
      have hl : raw31025step2Labels = labelEmbedding6 ∘ raw31025step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31025step2 raw31025step2Labels raw31025step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4243 node4243Labels := by rfl

def raw31026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw31026Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw31026step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31026step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![2, -2, 0], ![3, -1, -2]]
def raw31026step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31026step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31026step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31026step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31026step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31026 raw31026Labels = mixedMoment B node4693 node4693Labels := by
  calc
    mixedMoment B raw31026 raw31026Labels = mixedMoment B raw31026step0 raw31026step0Labels := by
      have hz : ∀ j, raw31026 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31026step0 = (fun i j => raw31026 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31026step0 raw31026; decide +kernel
      have hl : raw31026step0Labels = raw31026Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31026 raw31026Labels permutation434 hz
    mixedMoment B raw31026step0 raw31026step0Labels = mixedMoment B raw31026step1 raw31026step1Labels := by
      have hz : ∀ j, raw31026step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31026step1 = (fun i j => raw31026step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31026step1 raw31026step0; decide +kernel
      have hl : raw31026step1Labels = raw31026step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31026step0 raw31026step0Labels permutation80 hz
    mixedMoment B raw31026step1 raw31026step1Labels = mixedMoment B raw31026step2 raw31026step2Labels := by
      have ha : raw31026step2 = (fun i j => raw31026step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31026step2 raw31026step1; decide +kernel
      have hl : raw31026step2Labels = raw31026step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31026step1 raw31026step1Labels permutation8 permutation3
    mixedMoment B raw31026step2 raw31026step2Labels = mixedMoment B raw31026step3 raw31026step3Labels := by
      have ha : raw31026step3 = raw31026step2 := by apply Matrix.ext; unfold raw31026step3 raw31026step2; decide +kernel
      have hl : raw31026step2Labels = labelEmbedding6 ∘ raw31026step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31026step2 raw31026step2Labels raw31026step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4693 node4693Labels := by rfl

def raw31027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw31027Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw31027step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31027step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw31027step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31027step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw31027step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31027 raw31027Labels = mixedMoment B node4727 node4727Labels := by
  calc
    mixedMoment B raw31027 raw31027Labels = mixedMoment B raw31027step0 raw31027step0Labels := by
      have hz : ∀ j, raw31027 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31027step0 = (fun i j => raw31027 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31027step0 raw31027; decide +kernel
      have hl : raw31027step0Labels = raw31027Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31027 raw31027Labels permutation434 hz
    mixedMoment B raw31027step0 raw31027step0Labels = mixedMoment B raw31027step1 raw31027step1Labels := by
      have ha : raw31027step1 = (fun i j => raw31027step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31027step1 raw31027step0; decide +kernel
      have hl : raw31027step1Labels = raw31027step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31027step0 raw31027step0Labels permutation38 permutation3
    mixedMoment B raw31027step1 raw31027step1Labels = mixedMoment B raw31027step2 raw31027step2Labels := by
      have ha : raw31027step2 = raw31027step1 := by apply Matrix.ext; unfold raw31027step2 raw31027step1; decide +kernel
      have hl : raw31027step1Labels = labelEmbedding6 ∘ raw31027step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31027step1 raw31027step1Labels raw31027step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4727 node4727Labels := by rfl

def raw31028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw31028Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw31028step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31028step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw31028step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw31028step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw31028step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31028 raw31028Labels = mixedMoment B node4727 node4727Labels := by
  calc
    mixedMoment B raw31028 raw31028Labels = mixedMoment B raw31028step0 raw31028step0Labels := by
      have hz : ∀ j, raw31028 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31028step0 = (fun i j => raw31028 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31028step0 raw31028; decide +kernel
      have hl : raw31028step0Labels = raw31028Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31028 raw31028Labels permutation346 hz
    mixedMoment B raw31028step0 raw31028step0Labels = mixedMoment B raw31028step1 raw31028step1Labels := by
      have ha : raw31028step1 = (fun i j => raw31028step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31028step1 raw31028step0; decide +kernel
      have hl : raw31028step1Labels = raw31028step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31028step0 raw31028step0Labels permutation38 permutation3
    mixedMoment B raw31028step1 raw31028step1Labels = mixedMoment B raw31028step2 raw31028step2Labels := by
      have ha : raw31028step2 = raw31028step1 := by apply Matrix.ext; unfold raw31028step2 raw31028step1; decide +kernel
      have hl : raw31028step1Labels = labelEmbedding6 ∘ raw31028step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31028step1 raw31028step1Labels raw31028step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4727 node4727Labels := by rfl

def raw31029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31029Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31029step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31029step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![2, -2, 0], ![2, 0, -2]]
def raw31029step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31029step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31029step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31029 raw31029Labels = mixedMoment B node3740 node3740Labels := by
  calc
    mixedMoment B raw31029 raw31029Labels = mixedMoment B raw31029step0 raw31029step0Labels := by
      have hz : ∀ j, raw31029 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31029step0 = (fun i j => raw31029 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31029step0 raw31029; decide +kernel
      have hl : raw31029step0Labels = raw31029Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31029 raw31029Labels permutation434 hz
    mixedMoment B raw31029step0 raw31029step0Labels = mixedMoment B raw31029step1 raw31029step1Labels := by
      have hz : ∀ j, raw31029step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31029step1 = (fun i j => raw31029step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31029step1 raw31029step0; decide +kernel
      have hl : raw31029step1Labels = raw31029step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31029step0 raw31029step0Labels permutation80 hz
    mixedMoment B raw31029step1 raw31029step1Labels = mixedMoment B raw31029step2 raw31029step2Labels := by
      have ha : raw31029step2 = (fun i j => raw31029step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31029step2 raw31029step1; decide +kernel
      have hl : raw31029step2Labels = raw31029step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31029step1 raw31029step1Labels permutation9 permutation3
    _ = mixedMoment B node3740 node3740Labels := by rfl

def raw31030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31030Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31030step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31030step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31030step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw31030step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31030step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw31030step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31030 raw31030Labels = mixedMoment B node3732 node3732Labels := by
  calc
    mixedMoment B raw31030 raw31030Labels = mixedMoment B raw31030step0 raw31030step0Labels := by
      have hz : ∀ j, raw31030 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31030step0 = (fun i j => raw31030 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31030step0 raw31030; decide +kernel
      have hl : raw31030step0Labels = raw31030Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31030 raw31030Labels permutation434 hz
    mixedMoment B raw31030step0 raw31030step0Labels = mixedMoment B raw31030step1 raw31030step1Labels := by
      have ha : raw31030step1 = (fun i j => raw31030step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31030step1 raw31030step0; decide +kernel
      have hl : raw31030step1Labels = raw31030step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31030step0 raw31030step0Labels permutation125 permutation3
    mixedMoment B raw31030step1 raw31030step1Labels = mixedMoment B raw31030step2 raw31030step2Labels := by
      have ha : raw31030step2 = -raw31030step1 := by apply Matrix.ext; change ∀ i j, raw31030step2 i j = -(raw31030step1 i j); unfold raw31030step2 raw31030step1; decide +kernel
      have hl : raw31030step2Labels = raw31030step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3732 node3732Labels := by rfl

def raw31031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31031Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31031step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31031step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31031step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw31031step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31031step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw31031step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31031 raw31031Labels = mixedMoment B node3732 node3732Labels := by
  calc
    mixedMoment B raw31031 raw31031Labels = mixedMoment B raw31031step0 raw31031step0Labels := by
      have hz : ∀ j, raw31031 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31031step0 = (fun i j => raw31031 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31031step0 raw31031; decide +kernel
      have hl : raw31031step0Labels = raw31031Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31031 raw31031Labels permutation346 hz
    mixedMoment B raw31031step0 raw31031step0Labels = mixedMoment B raw31031step1 raw31031step1Labels := by
      have ha : raw31031step1 = (fun i j => raw31031step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31031step1 raw31031step0; decide +kernel
      have hl : raw31031step1Labels = raw31031step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31031step0 raw31031step0Labels permutation125 permutation3
    mixedMoment B raw31031step1 raw31031step1Labels = mixedMoment B raw31031step2 raw31031step2Labels := by
      have ha : raw31031step2 = -raw31031step1 := by apply Matrix.ext; change ∀ i j, raw31031step2 i j = -(raw31031step1 i j); unfold raw31031step2 raw31031step1; decide +kernel
      have hl : raw31031step2Labels = raw31031step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3732 node3732Labels := by rfl

def raw31032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw31032Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw31032step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31032step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![2, 0, -2]]
def raw31032step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31032step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw31032step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31032 raw31032Labels = mixedMoment B node3889 node3889Labels := by
  calc
    mixedMoment B raw31032 raw31032Labels = mixedMoment B raw31032step0 raw31032step0Labels := by
      have hz : ∀ j, raw31032 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31032step0 = (fun i j => raw31032 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31032step0 raw31032; decide +kernel
      have hl : raw31032step0Labels = raw31032Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31032 raw31032Labels permutation434 hz
    mixedMoment B raw31032step0 raw31032step0Labels = mixedMoment B raw31032step1 raw31032step1Labels := by
      have hz : ∀ j, raw31032step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31032step1 = (fun i j => raw31032step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31032step1 raw31032step0; decide +kernel
      have hl : raw31032step1Labels = raw31032step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31032step0 raw31032step0Labels permutation80 hz
    mixedMoment B raw31032step1 raw31032step1Labels = mixedMoment B raw31032step2 raw31032step2Labels := by
      have ha : raw31032step2 = (fun i j => raw31032step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31032step2 raw31032step1; decide +kernel
      have hl : raw31032step2Labels = raw31032step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31032step1 raw31032step1Labels permutation8 permutation3
    _ = mixedMoment B node3889 node3889Labels := by rfl

def raw31033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw31033Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw31033step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31033step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![2, -2, 0], ![1, 1, -2]]
def raw31033step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31033step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw31033step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31033 raw31033Labels = mixedMoment B node3886 node3886Labels := by
  calc
    mixedMoment B raw31033 raw31033Labels = mixedMoment B raw31033step0 raw31033step0Labels := by
      have hz : ∀ j, raw31033 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31033step0 = (fun i j => raw31033 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31033step0 raw31033; decide +kernel
      have hl : raw31033step0Labels = raw31033Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31033 raw31033Labels permutation434 hz
    mixedMoment B raw31033step0 raw31033step0Labels = mixedMoment B raw31033step1 raw31033step1Labels := by
      have hz : ∀ j, raw31033step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31033step1 = (fun i j => raw31033step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31033step1 raw31033step0; decide +kernel
      have hl : raw31033step1Labels = raw31033step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31033step0 raw31033step0Labels permutation80 hz
    mixedMoment B raw31033step1 raw31033step1Labels = mixedMoment B raw31033step2 raw31033step2Labels := by
      have ha : raw31033step2 = (fun i j => raw31033step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31033step2 raw31033step1; decide +kernel
      have hl : raw31033step2Labels = raw31033step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31033step1 raw31033step1Labels permutation9 permutation3
    _ = mixedMoment B node3886 node3886Labels := by rfl

def raw31034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31034Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31034step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31034step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31034step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw31034step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31034step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw31034step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31034 raw31034Labels = mixedMoment B node830 node830Labels := by
  calc
    mixedMoment B raw31034 raw31034Labels = mixedMoment B raw31034step0 raw31034step0Labels := by
      have hz : ∀ j, raw31034 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31034step0 = (fun i j => raw31034 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31034step0 raw31034; decide +kernel
      have hl : raw31034step0Labels = raw31034Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31034 raw31034Labels permutation434 hz
    mixedMoment B raw31034step0 raw31034step0Labels = mixedMoment B raw31034step1 raw31034step1Labels := by
      have hz : ∀ j, raw31034step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31034step1 = (fun i j => raw31034step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31034step1 raw31034step0; decide +kernel
      have hl : raw31034step1Labels = raw31034step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31034step0 raw31034step0Labels permutation80 hz
    mixedMoment B raw31034step1 raw31034step1Labels = mixedMoment B raw31034step2 raw31034step2Labels := by
      have ha : raw31034step2 = (fun i j => raw31034step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31034step2 raw31034step1; decide +kernel
      have hl : raw31034step2Labels = raw31034step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31034step1 raw31034step1Labels permutation9 permutation3
    _ = mixedMoment B node830 node830Labels := by rfl

def raw31035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31035Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31035step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31035step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31035step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw31035step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31035 raw31035Labels = mixedMoment B node1928 node1928Labels := by
  calc
    mixedMoment B raw31035 raw31035Labels = mixedMoment B raw31035step0 raw31035step0Labels := by
      have hz : ∀ j, raw31035 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31035step0 = (fun i j => raw31035 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31035step0 raw31035; decide +kernel
      have hl : raw31035step0Labels = raw31035Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31035 raw31035Labels permutation434 hz
    mixedMoment B raw31035step0 raw31035step0Labels = mixedMoment B raw31035step1 raw31035step1Labels := by
      have ha : raw31035step1 = (fun i j => raw31035step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31035step1 raw31035step0; decide +kernel
      have hl : raw31035step1Labels = raw31035step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31035step0 raw31035step0Labels permutation39 permutation3
    _ = mixedMoment B node1928 node1928Labels := by rfl

def raw31036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31036Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31036step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31036step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31036step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw31036step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31036 raw31036Labels = mixedMoment B node1928 node1928Labels := by
  calc
    mixedMoment B raw31036 raw31036Labels = mixedMoment B raw31036step0 raw31036step0Labels := by
      have hz : ∀ j, raw31036 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31036step0 = (fun i j => raw31036 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31036step0 raw31036; decide +kernel
      have hl : raw31036step0Labels = raw31036Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31036 raw31036Labels permutation346 hz
    mixedMoment B raw31036step0 raw31036step0Labels = mixedMoment B raw31036step1 raw31036step1Labels := by
      have ha : raw31036step1 = (fun i j => raw31036step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31036step1 raw31036step0; decide +kernel
      have hl : raw31036step1Labels = raw31036step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31036step0 raw31036step0Labels permutation39 permutation3
    _ = mixedMoment B node1928 node1928Labels := by rfl

def raw31037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw31037Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31037step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw31037step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31037step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw31037step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31037step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw31037step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31037 raw31037Labels = mixedMoment B node2279 node2279Labels := by
  calc
    mixedMoment B raw31037 raw31037Labels = mixedMoment B raw31037step0 raw31037step0Labels := by
      have hz : ∀ j, raw31037 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31037step0 = (fun i j => raw31037 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31037step0 raw31037; decide +kernel
      have hl : raw31037step0Labels = raw31037Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31037 raw31037Labels permutation434 hz
    mixedMoment B raw31037step0 raw31037step0Labels = mixedMoment B raw31037step1 raw31037step1Labels := by
      have hz : ∀ j, raw31037step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31037step1 = (fun i j => raw31037step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31037step1 raw31037step0; decide +kernel
      have hl : raw31037step1Labels = raw31037step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31037step0 raw31037step0Labels permutation80 hz
    mixedMoment B raw31037step1 raw31037step1Labels = mixedMoment B raw31037step2 raw31037step2Labels := by
      have ha : raw31037step2 = (fun i j => raw31037step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31037step2 raw31037step1; decide +kernel
      have hl : raw31037step2Labels = raw31037step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31037step1 raw31037step1Labels permutation8 permutation3
    _ = mixedMoment B node2279 node2279Labels := by rfl

def raw31038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw31038Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31038step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw31038step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31038step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![2, -2, 0], ![1, 1, -2]]
def raw31038step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31038step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw31038step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31038 raw31038Labels = mixedMoment B node2276 node2276Labels := by
  calc
    mixedMoment B raw31038 raw31038Labels = mixedMoment B raw31038step0 raw31038step0Labels := by
      have hz : ∀ j, raw31038 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31038step0 = (fun i j => raw31038 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31038step0 raw31038; decide +kernel
      have hl : raw31038step0Labels = raw31038Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31038 raw31038Labels permutation434 hz
    mixedMoment B raw31038step0 raw31038step0Labels = mixedMoment B raw31038step1 raw31038step1Labels := by
      have hz : ∀ j, raw31038step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31038step1 = (fun i j => raw31038step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31038step1 raw31038step0; decide +kernel
      have hl : raw31038step1Labels = raw31038step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31038step0 raw31038step0Labels permutation80 hz
    mixedMoment B raw31038step1 raw31038step1Labels = mixedMoment B raw31038step2 raw31038step2Labels := by
      have ha : raw31038step2 = (fun i j => raw31038step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31038step2 raw31038step1; decide +kernel
      have hl : raw31038step2Labels = raw31038step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31038step1 raw31038step1Labels permutation9 permutation3
    _ = mixedMoment B node2276 node2276Labels := by rfl

def raw31039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31039Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31039step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31039step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31039step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31039step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31039 raw31039Labels = mixedMoment B node738 node738Labels := by
  calc
    mixedMoment B raw31039 raw31039Labels = mixedMoment B raw31039step0 raw31039step0Labels := by
      have hz : ∀ j, raw31039 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31039step0 = (fun i j => raw31039 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31039step0 raw31039; decide +kernel
      have hl : raw31039step0Labels = raw31039Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31039 raw31039Labels permutation434 hz
    mixedMoment B raw31039step0 raw31039step0Labels = mixedMoment B raw31039step1 raw31039step1Labels := by
      have ha : raw31039step1 = (fun i j => raw31039step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31039step1 raw31039step0; decide +kernel
      have hl : raw31039step1Labels = raw31039step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31039step0 raw31039step0Labels permutation33 permutation3
    _ = mixedMoment B node738 node738Labels := by rfl

def raw31040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31040Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31040step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31040step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31040step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31040 raw31040Labels = mixedMoment B node1814 node1814Labels := by
  calc
    mixedMoment B raw31040 raw31040Labels = mixedMoment B raw31040step0 raw31040step0Labels := by
      have hz : ∀ j, raw31040 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31040step0 = (fun i j => raw31040 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31040step0 raw31040; decide +kernel
      have hl : raw31040step0Labels = raw31040Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31040 raw31040Labels permutation434 hz
    mixedMoment B raw31040step0 raw31040step0Labels = mixedMoment B raw31040step1 raw31040step1Labels := by
      have ha : raw31040step1 = (fun i j => raw31040step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31040step1 raw31040step0; decide +kernel
      have hl : raw31040step1Labels = raw31040step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31040step0 raw31040step0Labels permutation33 permutation3
    _ = mixedMoment B node1814 node1814Labels := by rfl

def raw31041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31041Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31041step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31041step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31041 raw31041Labels = mixedMoment B node1878 node1878Labels := by
  calc
    mixedMoment B raw31041 raw31041Labels = mixedMoment B raw31041step0 raw31041step0Labels := by
      have ha : raw31041step0 = (fun i j => raw31041 (permutation201 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31041step0 raw31041; decide +kernel
      have hl : raw31041step0Labels = raw31041Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31041 raw31041Labels permutation201 permutation3
    _ = mixedMoment B node1878 node1878Labels := by rfl

def raw31042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw31042Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31042step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw31042step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31042step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw31042step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31042 raw31042Labels = mixedMoment B node2110 node2110Labels := by
  calc
    mixedMoment B raw31042 raw31042Labels = mixedMoment B raw31042step0 raw31042step0Labels := by
      have hz : ∀ j, raw31042 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31042step0 = (fun i j => raw31042 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31042step0 raw31042; decide +kernel
      have hl : raw31042step0Labels = raw31042Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31042 raw31042Labels permutation434 hz
    mixedMoment B raw31042step0 raw31042step0Labels = mixedMoment B raw31042step1 raw31042step1Labels := by
      have ha : raw31042step1 = (fun i j => raw31042step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31042step1 raw31042step0; decide +kernel
      have hl : raw31042step1Labels = raw31042step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31042step0 raw31042step0Labels permutation32 permutation3
    _ = mixedMoment B node2110 node2110Labels := by rfl

def raw31043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw31043Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31043step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw31043step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31043step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw31043step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31043 raw31043Labels = mixedMoment B node2101 node2101Labels := by
  calc
    mixedMoment B raw31043 raw31043Labels = mixedMoment B raw31043step0 raw31043step0Labels := by
      have hz : ∀ j, raw31043 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31043step0 = (fun i j => raw31043 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31043step0 raw31043; decide +kernel
      have hl : raw31043step0Labels = raw31043Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31043 raw31043Labels permutation434 hz
    mixedMoment B raw31043step0 raw31043step0Labels = mixedMoment B raw31043step1 raw31043step1Labels := by
      have ha : raw31043step1 = (fun i j => raw31043step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31043step1 raw31043step0; decide +kernel
      have hl : raw31043step1Labels = raw31043step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31043step0 raw31043step0Labels permutation36 permutation3
    _ = mixedMoment B node2101 node2101Labels := by rfl

def raw31044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31044Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31044step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31044step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31044step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31044step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31044 raw31044Labels = mixedMoment B node738 node738Labels := by
  calc
    mixedMoment B raw31044 raw31044Labels = mixedMoment B raw31044step0 raw31044step0Labels := by
      have hz : ∀ j, raw31044 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31044step0 = (fun i j => raw31044 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31044step0 raw31044; decide +kernel
      have hl : raw31044step0Labels = raw31044Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31044 raw31044Labels permutation346 hz
    mixedMoment B raw31044step0 raw31044step0Labels = mixedMoment B raw31044step1 raw31044step1Labels := by
      have ha : raw31044step1 = (fun i j => raw31044step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31044step1 raw31044step0; decide +kernel
      have hl : raw31044step1Labels = raw31044step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31044step0 raw31044step0Labels permutation33 permutation3
    _ = mixedMoment B node738 node738Labels := by rfl

def raw31045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31045Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31045step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31045step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31045step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31045step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31045 raw31045Labels = mixedMoment B node1814 node1814Labels := by
  calc
    mixedMoment B raw31045 raw31045Labels = mixedMoment B raw31045step0 raw31045step0Labels := by
      have hz : ∀ j, raw31045 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31045step0 = (fun i j => raw31045 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31045step0 raw31045; decide +kernel
      have hl : raw31045step0Labels = raw31045Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31045 raw31045Labels permutation346 hz
    mixedMoment B raw31045step0 raw31045step0Labels = mixedMoment B raw31045step1 raw31045step1Labels := by
      have ha : raw31045step1 = (fun i j => raw31045step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31045step1 raw31045step0; decide +kernel
      have hl : raw31045step1Labels = raw31045step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31045step0 raw31045step0Labels permutation33 permutation3
    _ = mixedMoment B node1814 node1814Labels := by rfl

def raw31046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw31046Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31046step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31046step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31046 raw31046Labels = mixedMoment B node1878 node1878Labels := by
  calc
    mixedMoment B raw31046 raw31046Labels = mixedMoment B raw31046step0 raw31046step0Labels := by
      have ha : raw31046step0 = (fun i j => raw31046 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31046step0 raw31046; decide +kernel
      have hl : raw31046step0Labels = raw31046Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31046 raw31046Labels permutation177 permutation3
    _ = mixedMoment B node1878 node1878Labels := by rfl

def raw31047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw31047Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31047step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw31047step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31047step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw31047step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31047 raw31047Labels = mixedMoment B node2110 node2110Labels := by
  calc
    mixedMoment B raw31047 raw31047Labels = mixedMoment B raw31047step0 raw31047step0Labels := by
      have hz : ∀ j, raw31047 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31047step0 = (fun i j => raw31047 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31047step0 raw31047; decide +kernel
      have hl : raw31047step0Labels = raw31047Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31047 raw31047Labels permutation346 hz
    mixedMoment B raw31047step0 raw31047step0Labels = mixedMoment B raw31047step1 raw31047step1Labels := by
      have ha : raw31047step1 = (fun i j => raw31047step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31047step1 raw31047step0; decide +kernel
      have hl : raw31047step1Labels = raw31047step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31047step0 raw31047step0Labels permutation32 permutation3
    _ = mixedMoment B node2110 node2110Labels := by rfl

def raw31048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw31048Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31048step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw31048step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31048step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw31048step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31048 raw31048Labels = mixedMoment B node2101 node2101Labels := by
  calc
    mixedMoment B raw31048 raw31048Labels = mixedMoment B raw31048step0 raw31048step0Labels := by
      have hz : ∀ j, raw31048 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31048step0 = (fun i j => raw31048 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31048step0 raw31048; decide +kernel
      have hl : raw31048step0Labels = raw31048Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31048 raw31048Labels permutation346 hz
    mixedMoment B raw31048step0 raw31048step0Labels = mixedMoment B raw31048step1 raw31048step1Labels := by
      have ha : raw31048step1 = (fun i j => raw31048step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31048step1 raw31048step0; decide +kernel
      have hl : raw31048step1Labels = raw31048step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31048step0 raw31048step0Labels permutation36 permutation3
    _ = mixedMoment B node2101 node2101Labels := by rfl

def raw31049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw31049Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw31049step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31049step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![3, -3, 0], ![2, 0, -2]]
def raw31049step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31049step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, -2, 0], ![3, 0, -3]]
def raw31049step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31049 raw31049Labels = mixedMoment B node741 node741Labels := by
  calc
    mixedMoment B raw31049 raw31049Labels = mixedMoment B raw31049step0 raw31049step0Labels := by
      have hz : ∀ j, raw31049 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31049step0 = (fun i j => raw31049 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31049step0 raw31049; decide +kernel
      have hl : raw31049step0Labels = raw31049Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31049 raw31049Labels permutation434 hz
    mixedMoment B raw31049step0 raw31049step0Labels = mixedMoment B raw31049step1 raw31049step1Labels := by
      have hz : ∀ j, raw31049step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31049step1 = (fun i j => raw31049step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31049step1 raw31049step0; decide +kernel
      have hl : raw31049step1Labels = raw31049step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31049step0 raw31049step0Labels permutation80 hz
    mixedMoment B raw31049step1 raw31049step1Labels = mixedMoment B raw31049step2 raw31049step2Labels := by
      have ha : raw31049step2 = (fun i j => raw31049step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31049step2 raw31049step1; decide +kernel
      have hl : raw31049step2Labels = raw31049step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31049step1 raw31049step1Labels permutation9 permutation3
    _ = mixedMoment B node741 node741Labels := by rfl

def raw31050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw31050Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw31050step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31050step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![3, -3, 0], ![2, 0, -2]]
def raw31050step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31050step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def raw31050step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31050 raw31050Labels = mixedMoment B node1817 node1817Labels := by
  calc
    mixedMoment B raw31050 raw31050Labels = mixedMoment B raw31050step0 raw31050step0Labels := by
      have hz : ∀ j, raw31050 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31050step0 = (fun i j => raw31050 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31050step0 raw31050; decide +kernel
      have hl : raw31050step0Labels = raw31050Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31050 raw31050Labels permutation434 hz
    mixedMoment B raw31050step0 raw31050step0Labels = mixedMoment B raw31050step1 raw31050step1Labels := by
      have hz : ∀ j, raw31050step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31050step1 = (fun i j => raw31050step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31050step1 raw31050step0; decide +kernel
      have hl : raw31050step1Labels = raw31050step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31050step0 raw31050step0Labels permutation80 hz
    mixedMoment B raw31050step1 raw31050step1Labels = mixedMoment B raw31050step2 raw31050step2Labels := by
      have ha : raw31050step2 = (fun i j => raw31050step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31050step2 raw31050step1; decide +kernel
      have hl : raw31050step2Labels = raw31050step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31050step1 raw31050step1Labels permutation9 permutation3
    _ = mixedMoment B node1817 node1817Labels := by rfl

def raw31051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw31051Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw31051step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31051step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-3, 0, 3]]
def raw31051step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31051step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw31051step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31051 raw31051Labels = mixedMoment B node1799 node1799Labels := by
  calc
    mixedMoment B raw31051 raw31051Labels = mixedMoment B raw31051step0 raw31051step0Labels := by
      have hz : ∀ j, raw31051 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31051step0 = (fun i j => raw31051 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31051step0 raw31051; decide +kernel
      have hl : raw31051step0Labels = raw31051Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31051 raw31051Labels permutation434 hz
    mixedMoment B raw31051step0 raw31051step0Labels = mixedMoment B raw31051step1 raw31051step1Labels := by
      have ha : raw31051step1 = (fun i j => raw31051step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31051step1 raw31051step0; decide +kernel
      have hl : raw31051step1Labels = raw31051step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31051step0 raw31051step0Labels permutation125 permutation3
    mixedMoment B raw31051step1 raw31051step1Labels = mixedMoment B raw31051step2 raw31051step2Labels := by
      have ha : raw31051step2 = -raw31051step1 := by apply Matrix.ext; change ∀ i j, raw31051step2 i j = -(raw31051step1 i j); unfold raw31051step2 raw31051step1; decide +kernel
      have hl : raw31051step2Labels = raw31051step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1799 node1799Labels := by rfl

def raw31052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw31052Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31052step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw31052step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31052step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-3, 0, 3]]
def raw31052step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw31052step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw31052step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31052 raw31052Labels = mixedMoment B node1799 node1799Labels := by
  calc
    mixedMoment B raw31052 raw31052Labels = mixedMoment B raw31052step0 raw31052step0Labels := by
      have hz : ∀ j, raw31052 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31052step0 = (fun i j => raw31052 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31052step0 raw31052; decide +kernel
      have hl : raw31052step0Labels = raw31052Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31052 raw31052Labels permutation346 hz
    mixedMoment B raw31052step0 raw31052step0Labels = mixedMoment B raw31052step1 raw31052step1Labels := by
      have ha : raw31052step1 = (fun i j => raw31052step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31052step1 raw31052step0; decide +kernel
      have hl : raw31052step1Labels = raw31052step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31052step0 raw31052step0Labels permutation125 permutation3
    mixedMoment B raw31052step1 raw31052step1Labels = mixedMoment B raw31052step2 raw31052step2Labels := by
      have ha : raw31052step2 = -raw31052step1 := by apply Matrix.ext; change ∀ i j, raw31052step2 i j = -(raw31052step1 i j); unfold raw31052step2 raw31052step1; decide +kernel
      have hl : raw31052step2Labels = raw31052step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1799 node1799Labels := by rfl

def raw31053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw31053Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31053step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw31053step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31053step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![3, -3, 0], ![1, 1, -2]]
def raw31053step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31053step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![3, 0, -3]]
def raw31053step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31053 raw31053Labels = mixedMoment B node2103 node2103Labels := by
  calc
    mixedMoment B raw31053 raw31053Labels = mixedMoment B raw31053step0 raw31053step0Labels := by
      have hz : ∀ j, raw31053 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31053step0 = (fun i j => raw31053 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31053step0 raw31053; decide +kernel
      have hl : raw31053step0Labels = raw31053Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31053 raw31053Labels permutation434 hz
    mixedMoment B raw31053step0 raw31053step0Labels = mixedMoment B raw31053step1 raw31053step1Labels := by
      have hz : ∀ j, raw31053step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31053step1 = (fun i j => raw31053step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31053step1 raw31053step0; decide +kernel
      have hl : raw31053step1Labels = raw31053step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31053step0 raw31053step0Labels permutation80 hz
    mixedMoment B raw31053step1 raw31053step1Labels = mixedMoment B raw31053step2 raw31053step2Labels := by
      have ha : raw31053step2 = (fun i j => raw31053step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31053step2 raw31053step1; decide +kernel
      have hl : raw31053step2Labels = raw31053step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31053step1 raw31053step1Labels permutation9 permutation3
    _ = mixedMoment B node2103 node2103Labels := by rfl

def raw31054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw31054Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31054step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw31054step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31054step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![-1, -1, 2], ![2, -2, 0], ![3, -1, -2]]
def raw31054step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31054step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw31054step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31054 raw31054Labels = mixedMoment B node743 node743Labels := by
  calc
    mixedMoment B raw31054 raw31054Labels = mixedMoment B raw31054step0 raw31054step0Labels := by
      have hz : ∀ j, raw31054 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31054step0 = (fun i j => raw31054 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31054step0 raw31054; decide +kernel
      have hl : raw31054step0Labels = raw31054Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31054 raw31054Labels permutation434 hz
    mixedMoment B raw31054step0 raw31054step0Labels = mixedMoment B raw31054step1 raw31054step1Labels := by
      have hz : ∀ j, raw31054step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31054step1 = (fun i j => raw31054step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31054step1 raw31054step0; decide +kernel
      have hl : raw31054step1Labels = raw31054step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31054step0 raw31054step0Labels permutation80 hz
    mixedMoment B raw31054step1 raw31054step1Labels = mixedMoment B raw31054step2 raw31054step2Labels := by
      have ha : raw31054step2 = (fun i j => raw31054step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31054step2 raw31054step1; decide +kernel
      have hl : raw31054step2Labels = raw31054step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31054step1 raw31054step1Labels permutation8 permutation3
    _ = mixedMoment B node743 node743Labels := by rfl

def raw31055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw31055Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw31055step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31055step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 0, 2], ![2, -2, 0], ![3, -1, -2]]
def raw31055step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31055step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, 0, -2], ![3, -2, -1]]
def raw31055step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31055 raw31055Labels = mixedMoment B node1819 node1819Labels := by
  calc
    mixedMoment B raw31055 raw31055Labels = mixedMoment B raw31055step0 raw31055step0Labels := by
      have hz : ∀ j, raw31055 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31055step0 = (fun i j => raw31055 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31055step0 raw31055; decide +kernel
      have hl : raw31055step0Labels = raw31055Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31055 raw31055Labels permutation434 hz
    mixedMoment B raw31055step0 raw31055step0Labels = mixedMoment B raw31055step1 raw31055step1Labels := by
      have hz : ∀ j, raw31055step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31055step1 = (fun i j => raw31055step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31055step1 raw31055step0; decide +kernel
      have hl : raw31055step1Labels = raw31055step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31055step0 raw31055step0Labels permutation80 hz
    mixedMoment B raw31055step1 raw31055step1Labels = mixedMoment B raw31055step2 raw31055step2Labels := by
      have ha : raw31055step2 = (fun i j => raw31055step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31055step2 raw31055step1; decide +kernel
      have hl : raw31055step2Labels = raw31055step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31055step1 raw31055step1Labels permutation8 permutation3
    _ = mixedMoment B node1819 node1819Labels := by rfl

def raw31056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw31056Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31056step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw31056step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31056step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw31056step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31056 raw31056Labels = mixedMoment B node1881 node1881Labels := by
  calc
    mixedMoment B raw31056 raw31056Labels = mixedMoment B raw31056step0 raw31056step0Labels := by
      have hz : ∀ j, raw31056 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31056step0 = (fun i j => raw31056 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31056step0 raw31056; decide +kernel
      have hl : raw31056step0Labels = raw31056Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31056 raw31056Labels permutation434 hz
    mixedMoment B raw31056step0 raw31056step0Labels = mixedMoment B raw31056step1 raw31056step1Labels := by
      have ha : raw31056step1 = (fun i j => raw31056step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31056step1 raw31056step0; decide +kernel
      have hl : raw31056step1Labels = raw31056step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31056step0 raw31056step0Labels permutation38 permutation3
    _ = mixedMoment B node1881 node1881Labels := by rfl

def raw31057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw31057Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31057step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw31057step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31057step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![2, 0, -2], ![3, -2, -1]]
def raw31057step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31057 raw31057Labels = mixedMoment B node1881 node1881Labels := by
  calc
    mixedMoment B raw31057 raw31057Labels = mixedMoment B raw31057step0 raw31057step0Labels := by
      have hz : ∀ j, raw31057 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31057step0 = (fun i j => raw31057 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31057step0 raw31057; decide +kernel
      have hl : raw31057step0Labels = raw31057Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31057 raw31057Labels permutation346 hz
    mixedMoment B raw31057step0 raw31057step0Labels = mixedMoment B raw31057step1 raw31057step1Labels := by
      have ha : raw31057step1 = (fun i j => raw31057step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31057step1 raw31057step0; decide +kernel
      have hl : raw31057step1Labels = raw31057step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31057step0 raw31057step0Labels permutation38 permutation3
    _ = mixedMoment B node1881 node1881Labels := by rfl

def raw31058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw31058Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31058step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw31058step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31058step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![3, -1, -2]]
def raw31058step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31058step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![3, -2, -1]]
def raw31058step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31058 raw31058Labels = mixedMoment B node2112 node2112Labels := by
  calc
    mixedMoment B raw31058 raw31058Labels = mixedMoment B raw31058step0 raw31058step0Labels := by
      have hz : ∀ j, raw31058 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31058step0 = (fun i j => raw31058 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31058step0 raw31058; decide +kernel
      have hl : raw31058step0Labels = raw31058Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31058 raw31058Labels permutation434 hz
    mixedMoment B raw31058step0 raw31058step0Labels = mixedMoment B raw31058step1 raw31058step1Labels := by
      have hz : ∀ j, raw31058step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31058step1 = (fun i j => raw31058step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31058step1 raw31058step0; decide +kernel
      have hl : raw31058step1Labels = raw31058step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31058step0 raw31058step0Labels permutation80 hz
    mixedMoment B raw31058step1 raw31058step1Labels = mixedMoment B raw31058step2 raw31058step2Labels := by
      have ha : raw31058step2 = (fun i j => raw31058step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw31058step2 raw31058step1; decide +kernel
      have hl : raw31058step2Labels = raw31058step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31058step1 raw31058step1Labels permutation8 permutation3
    _ = mixedMoment B node2112 node2112Labels := by rfl

def raw31059 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31059Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31059step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31059step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw31059step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw31059step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw31059step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31059 raw31059Labels = mixedMoment B node5188 node5188Labels := by
  calc
    mixedMoment B raw31059 raw31059Labels = mixedMoment B raw31059step0 raw31059step0Labels := by
      have hz : ∀ j, raw31059 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31059step0 = (fun i j => raw31059 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31059step0 raw31059; decide +kernel
      have hl : raw31059step0Labels = raw31059Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31059 raw31059Labels permutation434 hz
    mixedMoment B raw31059step0 raw31059step0Labels = mixedMoment B raw31059step1 raw31059step1Labels := by
      have ha : raw31059step1 = (fun i j => raw31059step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31059step1 raw31059step0; decide +kernel
      have hl : raw31059step1Labels = raw31059step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31059step0 raw31059step0Labels permutation33 permutation6
    mixedMoment B raw31059step1 raw31059step1Labels = mixedMoment B raw31059step2 raw31059step2Labels := by
      have ha : raw31059step2 = raw31059step1 := by apply Matrix.ext; unfold raw31059step2 raw31059step1; decide +kernel
      have hl : raw31059step1Labels = labelEmbedding9 ∘ raw31059step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31059step1 raw31059step1Labels raw31059step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5188 node5188Labels := by rfl

def raw31060 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw31060Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31060step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw31060step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31060step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, -2, 2], ![-3, 1, 2]]
def raw31060step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31060step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw31060step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw31060step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw31060step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31060 raw31060Labels = mixedMoment B node5206 node5206Labels := by
  calc
    mixedMoment B raw31060 raw31060Labels = mixedMoment B raw31060step0 raw31060step0Labels := by
      have hz : ∀ j, raw31060 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31060step0 = (fun i j => raw31060 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31060step0 raw31060; decide +kernel
      have hl : raw31060step0Labels = raw31060Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31060 raw31060Labels permutation434 hz
    mixedMoment B raw31060step0 raw31060step0Labels = mixedMoment B raw31060step1 raw31060step1Labels := by
      have hz : ∀ j, raw31060step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31060step1 = (fun i j => raw31060step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31060step1 raw31060step0; decide +kernel
      have hl : raw31060step1Labels = raw31060step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31060step0 raw31060step0Labels permutation80 hz
    mixedMoment B raw31060step1 raw31060step1Labels = mixedMoment B raw31060step2 raw31060step2Labels := by
      have ha : raw31060step2 = (fun i j => raw31060step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31060step2 raw31060step1; decide +kernel
      have hl : raw31060step2Labels = raw31060step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31060step1 raw31060step1Labels permutation9 permutation6
    mixedMoment B raw31060step2 raw31060step2Labels = mixedMoment B raw31060step3 raw31060step3Labels := by
      have ha : raw31060step3 = raw31060step2 := by apply Matrix.ext; unfold raw31060step3 raw31060step2; decide +kernel
      have hl : raw31060step2Labels = labelEmbedding9 ∘ raw31060step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31060step2 raw31060step2Labels raw31060step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5206 node5206Labels := by rfl

def raw31061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31061Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31061step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -2, -1], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31061step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31061step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -2, -1], ![0, -2, 2], ![-2, 0, 2]]
def raw31061step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31061step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-2, 3, -1], ![-2, 0, 2]]
def raw31061step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31061step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw31061step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31061step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw31061step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31061 raw31061Labels = mixedMoment B node4479 node4479Labels := by
  calc
    mixedMoment B raw31061 raw31061Labels = mixedMoment B raw31061step0 raw31061step0Labels := by
      have hz : ∀ j, raw31061 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31061step0 = (fun i j => raw31061 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31061step0 raw31061; decide +kernel
      have hl : raw31061step0Labels = raw31061Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31061 raw31061Labels permutation434 hz
    mixedMoment B raw31061step0 raw31061step0Labels = mixedMoment B raw31061step1 raw31061step1Labels := by
      have hz : ∀ j, raw31061step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31061step1 = (fun i j => raw31061step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31061step1 raw31061step0; decide +kernel
      have hl : raw31061step1Labels = raw31061step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31061step0 raw31061step0Labels permutation80 hz
    mixedMoment B raw31061step1 raw31061step1Labels = mixedMoment B raw31061step2 raw31061step2Labels := by
      have ha : raw31061step2 = (fun i j => raw31061step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31061step2 raw31061step1; decide +kernel
      have hl : raw31061step2Labels = raw31061step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31061step1 raw31061step1Labels permutation12 permutation4
    mixedMoment B raw31061step2 raw31061step2Labels = mixedMoment B raw31061step3 raw31061step3Labels := by
      have ha : raw31061step3 = -raw31061step2 := by apply Matrix.ext; change ∀ i j, raw31061step3 i j = -(raw31061step2 i j); unfold raw31061step3 raw31061step2; decide +kernel
      have hl : raw31061step3Labels = raw31061step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31061step3 raw31061step3Labels = mixedMoment B raw31061step4 raw31061step4Labels := by
      have ha : raw31061step4 = raw31061step3 := by apply Matrix.ext; unfold raw31061step4 raw31061step3; decide +kernel
      have hl : raw31061step3Labels = labelEmbedding7 ∘ raw31061step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31061step3 raw31061step3Labels raw31061step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4479 node4479Labels := by rfl

def raw31062 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31062Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31062step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31062step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31062step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-2, 3, -1], ![-2, 0, 2]]
def raw31062step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31062step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw31062step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31062step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw31062step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31062 raw31062Labels = mixedMoment B node4820 node4820Labels := by
  calc
    mixedMoment B raw31062 raw31062Labels = mixedMoment B raw31062step0 raw31062step0Labels := by
      have hz : ∀ j, raw31062 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31062step0 = (fun i j => raw31062 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31062step0 raw31062; decide +kernel
      have hl : raw31062step0Labels = raw31062Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31062 raw31062Labels permutation434 hz
    mixedMoment B raw31062step0 raw31062step0Labels = mixedMoment B raw31062step1 raw31062step1Labels := by
      have ha : raw31062step1 = (fun i j => raw31062step0 (permutation42 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31062step1 raw31062step0; decide +kernel
      have hl : raw31062step1Labels = raw31062step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31062step0 raw31062step0Labels permutation42 permutation4
    mixedMoment B raw31062step1 raw31062step1Labels = mixedMoment B raw31062step2 raw31062step2Labels := by
      have ha : raw31062step2 = -raw31062step1 := by apply Matrix.ext; change ∀ i j, raw31062step2 i j = -(raw31062step1 i j); unfold raw31062step2 raw31062step1; decide +kernel
      have hl : raw31062step2Labels = raw31062step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31062step2 raw31062step2Labels = mixedMoment B raw31062step3 raw31062step3Labels := by
      have ha : raw31062step3 = raw31062step2 := by apply Matrix.ext; unfold raw31062step3 raw31062step2; decide +kernel
      have hl : raw31062step2Labels = labelEmbedding7 ∘ raw31062step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31062step2 raw31062step2Labels raw31062step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4820 node4820Labels := by rfl

def raw31063 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31063Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31063step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31063step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-2, 3, -1], ![-2, 0, 2]]
def raw31063step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31063step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw31063step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31063step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw31063step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31063 raw31063Labels = mixedMoment B node4820 node4820Labels := by
  calc
    mixedMoment B raw31063 raw31063Labels = mixedMoment B raw31063step0 raw31063step0Labels := by
      have hz : ∀ j, raw31063 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31063step0 = (fun i j => raw31063 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31063step0 raw31063; decide +kernel
      have hl : raw31063step0Labels = raw31063Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31063 raw31063Labels permutation346 hz
    mixedMoment B raw31063step0 raw31063step0Labels = mixedMoment B raw31063step1 raw31063step1Labels := by
      have ha : raw31063step1 = (fun i j => raw31063step0 (permutation42 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31063step1 raw31063step0; decide +kernel
      have hl : raw31063step1Labels = raw31063step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31063step0 raw31063step0Labels permutation42 permutation4
    mixedMoment B raw31063step1 raw31063step1Labels = mixedMoment B raw31063step2 raw31063step2Labels := by
      have ha : raw31063step2 = -raw31063step1 := by apply Matrix.ext; change ∀ i j, raw31063step2 i j = -(raw31063step1 i j); unfold raw31063step2 raw31063step1; decide +kernel
      have hl : raw31063step2Labels = raw31063step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31063step2 raw31063step2Labels = mixedMoment B raw31063step3 raw31063step3Labels := by
      have ha : raw31063step3 = raw31063step2 := by apply Matrix.ext; unfold raw31063step3 raw31063step2; decide +kernel
      have hl : raw31063step2Labels = labelEmbedding7 ∘ raw31063step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31063step2 raw31063step2Labels raw31063step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4820 node4820Labels := by rfl

def raw31064 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31064Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31064step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31064step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw31064step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31064step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw31064step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw31064step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw31064step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31064 raw31064Labels = mixedMoment B node4884 node4884Labels := by
  calc
    mixedMoment B raw31064 raw31064Labels = mixedMoment B raw31064step0 raw31064step0Labels := by
      have hz : ∀ j, raw31064 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31064step0 = (fun i j => raw31064 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31064step0 raw31064; decide +kernel
      have hl : raw31064step0Labels = raw31064Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31064 raw31064Labels permutation434 hz
    mixedMoment B raw31064step0 raw31064step0Labels = mixedMoment B raw31064step1 raw31064step1Labels := by
      have hz : ∀ j, raw31064step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31064step1 = (fun i j => raw31064step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31064step1 raw31064step0; decide +kernel
      have hl : raw31064step1Labels = raw31064step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31064step0 raw31064step0Labels permutation80 hz
    mixedMoment B raw31064step1 raw31064step1Labels = mixedMoment B raw31064step2 raw31064step2Labels := by
      have ha : raw31064step2 = (fun i j => raw31064step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31064step2 raw31064step1; decide +kernel
      have hl : raw31064step2Labels = raw31064step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31064step1 raw31064step1Labels permutation9 permutation6
    mixedMoment B raw31064step2 raw31064step2Labels = mixedMoment B raw31064step3 raw31064step3Labels := by
      have ha : raw31064step3 = raw31064step2 := by apply Matrix.ext; unfold raw31064step3 raw31064step2; decide +kernel
      have hl : raw31064step2Labels = labelEmbedding9 ∘ raw31064step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31064step2 raw31064step2Labels raw31064step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4884 node4884Labels := by rfl

def raw31065 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw31065Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31065step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw31065step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31065step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, -2, 2], ![-3, 1, 2]]
def raw31065step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31065step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-2, 3, -1], ![-2, 0, 2]]
def raw31065step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31065step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -3, 1], ![2, 0, -2]]
def raw31065step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31065step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -3, 1], ![2, 0, -2]]
def raw31065step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31065 raw31065Labels = mixedMoment B node4883 node4883Labels := by
  calc
    mixedMoment B raw31065 raw31065Labels = mixedMoment B raw31065step0 raw31065step0Labels := by
      have hz : ∀ j, raw31065 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31065step0 = (fun i j => raw31065 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31065step0 raw31065; decide +kernel
      have hl : raw31065step0Labels = raw31065Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31065 raw31065Labels permutation434 hz
    mixedMoment B raw31065step0 raw31065step0Labels = mixedMoment B raw31065step1 raw31065step1Labels := by
      have hz : ∀ j, raw31065step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31065step1 = (fun i j => raw31065step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31065step1 raw31065step0; decide +kernel
      have hl : raw31065step1Labels = raw31065step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31065step0 raw31065step0Labels permutation80 hz
    mixedMoment B raw31065step1 raw31065step1Labels = mixedMoment B raw31065step2 raw31065step2Labels := by
      have ha : raw31065step2 = (fun i j => raw31065step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31065step2 raw31065step1; decide +kernel
      have hl : raw31065step2Labels = raw31065step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31065step1 raw31065step1Labels permutation12 permutation4
    mixedMoment B raw31065step2 raw31065step2Labels = mixedMoment B raw31065step3 raw31065step3Labels := by
      have ha : raw31065step3 = -raw31065step2 := by apply Matrix.ext; change ∀ i j, raw31065step3 i j = -(raw31065step2 i j); unfold raw31065step3 raw31065step2; decide +kernel
      have hl : raw31065step3Labels = raw31065step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31065step3 raw31065step3Labels = mixedMoment B raw31065step4 raw31065step4Labels := by
      have ha : raw31065step4 = raw31065step3 := by apply Matrix.ext; unfold raw31065step4 raw31065step3; decide +kernel
      have hl : raw31065step3Labels = labelEmbedding7 ∘ raw31065step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31065step3 raw31065step3Labels raw31065step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4883 node4883Labels := by rfl

def raw31066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31066Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31066step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31066step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31066step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw31066step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31066step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw31066step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31066step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw31066step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31066 raw31066Labels = mixedMoment B node4470 node4470Labels := by
  calc
    mixedMoment B raw31066 raw31066Labels = mixedMoment B raw31066step0 raw31066step0Labels := by
      have hz : ∀ j, raw31066 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31066step0 = (fun i j => raw31066 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31066step0 raw31066; decide +kernel
      have hl : raw31066step0Labels = raw31066Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31066 raw31066Labels permutation434 hz
    mixedMoment B raw31066step0 raw31066step0Labels = mixedMoment B raw31066step1 raw31066step1Labels := by
      have ha : raw31066step1 = (fun i j => raw31066step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31066step1 raw31066step0; decide +kernel
      have hl : raw31066step1Labels = raw31066step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31066step0 raw31066step0Labels permutation50 permutation4
    mixedMoment B raw31066step1 raw31066step1Labels = mixedMoment B raw31066step2 raw31066step2Labels := by
      have ha : raw31066step2 = -raw31066step1 := by apply Matrix.ext; change ∀ i j, raw31066step2 i j = -(raw31066step1 i j); unfold raw31066step2 raw31066step1; decide +kernel
      have hl : raw31066step2Labels = raw31066step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31066step2 raw31066step2Labels = mixedMoment B raw31066step3 raw31066step3Labels := by
      have ha : raw31066step3 = raw31066step2 := by apply Matrix.ext; unfold raw31066step3 raw31066step2; decide +kernel
      have hl : raw31066step2Labels = labelEmbedding7 ∘ raw31066step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31066step2 raw31066step2Labels raw31066step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4470 node4470Labels := by rfl

def raw31067 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31067Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31067step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw31067step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31067step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw31067step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31067step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw31067step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31067 raw31067Labels = mixedMoment B node4812 node4812Labels := by
  calc
    mixedMoment B raw31067 raw31067Labels = mixedMoment B raw31067step0 raw31067step0Labels := by
      have ha : raw31067step0 = (fun i j => raw31067 (permutation218 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31067step0 raw31067; decide +kernel
      have hl : raw31067step0Labels = raw31067Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31067 raw31067Labels permutation218 permutation4
    mixedMoment B raw31067step0 raw31067step0Labels = mixedMoment B raw31067step1 raw31067step1Labels := by
      have ha : raw31067step1 = -raw31067step0 := by apply Matrix.ext; change ∀ i j, raw31067step1 i j = -(raw31067step0 i j); unfold raw31067step1 raw31067step0; decide +kernel
      have hl : raw31067step1Labels = raw31067step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31067step1 raw31067step1Labels = mixedMoment B raw31067step2 raw31067step2Labels := by
      have ha : raw31067step2 = raw31067step1 := by apply Matrix.ext; unfold raw31067step2 raw31067step1; decide +kernel
      have hl : raw31067step1Labels = labelEmbedding7 ∘ raw31067step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31067step1 raw31067step1Labels raw31067step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4812 node4812Labels := by rfl

def raw31068 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31068Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31068step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31068step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31068step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw31068step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw31068step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw31068step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31068 raw31068Labels = mixedMoment B node4856 node4856Labels := by
  calc
    mixedMoment B raw31068 raw31068Labels = mixedMoment B raw31068step0 raw31068step0Labels := by
      have hz : ∀ j, raw31068 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31068step0 = (fun i j => raw31068 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31068step0 raw31068; decide +kernel
      have hl : raw31068step0Labels = raw31068Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31068 raw31068Labels permutation434 hz
    mixedMoment B raw31068step0 raw31068step0Labels = mixedMoment B raw31068step1 raw31068step1Labels := by
      have ha : raw31068step1 = (fun i j => raw31068step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31068step1 raw31068step0; decide +kernel
      have hl : raw31068step1Labels = raw31068step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31068step0 raw31068step0Labels permutation33 permutation6
    mixedMoment B raw31068step1 raw31068step1Labels = mixedMoment B raw31068step2 raw31068step2Labels := by
      have ha : raw31068step2 = raw31068step1 := by apply Matrix.ext; unfold raw31068step2 raw31068step1; decide +kernel
      have hl : raw31068step1Labels = labelEmbedding9 ∘ raw31068step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31068step1 raw31068step1Labels raw31068step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4856 node4856Labels := by rfl

def raw31069 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw31069Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31069step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw31069step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31069step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw31069step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw31069step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw31069step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31069 raw31069Labels = mixedMoment B node4855 node4855Labels := by
  calc
    mixedMoment B raw31069 raw31069Labels = mixedMoment B raw31069step0 raw31069step0Labels := by
      have hz : ∀ j, raw31069 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31069step0 = (fun i j => raw31069 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31069step0 raw31069; decide +kernel
      have hl : raw31069step0Labels = raw31069Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31069 raw31069Labels permutation434 hz
    mixedMoment B raw31069step0 raw31069step0Labels = mixedMoment B raw31069step1 raw31069step1Labels := by
      have ha : raw31069step1 = (fun i j => raw31069step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31069step1 raw31069step0; decide +kernel
      have hl : raw31069step1Labels = raw31069step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31069step0 raw31069step0Labels permutation33 permutation6
    mixedMoment B raw31069step1 raw31069step1Labels = mixedMoment B raw31069step2 raw31069step2Labels := by
      have ha : raw31069step2 = raw31069step1 := by apply Matrix.ext; unfold raw31069step2 raw31069step1; decide +kernel
      have hl : raw31069step1Labels = labelEmbedding9 ∘ raw31069step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31069step1 raw31069step1Labels raw31069step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4855 node4855Labels := by rfl

def raw31070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31070Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31070step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31070step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31070step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw31070step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31070step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw31070step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31070step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw31070step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31070 raw31070Labels = mixedMoment B node4470 node4470Labels := by
  calc
    mixedMoment B raw31070 raw31070Labels = mixedMoment B raw31070step0 raw31070step0Labels := by
      have hz : ∀ j, raw31070 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31070step0 = (fun i j => raw31070 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31070step0 raw31070; decide +kernel
      have hl : raw31070step0Labels = raw31070Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31070 raw31070Labels permutation346 hz
    mixedMoment B raw31070step0 raw31070step0Labels = mixedMoment B raw31070step1 raw31070step1Labels := by
      have ha : raw31070step1 = (fun i j => raw31070step0 (permutation50 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31070step1 raw31070step0; decide +kernel
      have hl : raw31070step1Labels = raw31070step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31070step0 raw31070step0Labels permutation50 permutation4
    mixedMoment B raw31070step1 raw31070step1Labels = mixedMoment B raw31070step2 raw31070step2Labels := by
      have ha : raw31070step2 = -raw31070step1 := by apply Matrix.ext; change ∀ i j, raw31070step2 i j = -(raw31070step1 i j); unfold raw31070step2 raw31070step1; decide +kernel
      have hl : raw31070step2Labels = raw31070step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31070step2 raw31070step2Labels = mixedMoment B raw31070step3 raw31070step3Labels := by
      have ha : raw31070step3 = raw31070step2 := by apply Matrix.ext; unfold raw31070step3 raw31070step2; decide +kernel
      have hl : raw31070step2Labels = labelEmbedding7 ∘ raw31070step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31070step2 raw31070step2Labels raw31070step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4470 node4470Labels := by rfl

def raw31071 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31071Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31071step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31071step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31071step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31071step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw31071step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31071step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31071 raw31071Labels = mixedMoment B node4810 node4810Labels := by
  calc
    mixedMoment B raw31071 raw31071Labels = mixedMoment B raw31071step0 raw31071step0Labels := by
      have hz : ∀ j, raw31071 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31071step0 = (fun i j => raw31071 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31071step0 raw31071; decide +kernel
      have hl : raw31071step0Labels = raw31071Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31071 raw31071Labels permutation346 hz
    mixedMoment B raw31071step0 raw31071step0Labels = mixedMoment B raw31071step1 raw31071step1Labels := by
      have ha : raw31071step1 = (fun i j => raw31071step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31071step1 raw31071step0; decide +kernel
      have hl : raw31071step1Labels = raw31071step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31071step0 raw31071step0Labels permutation33 permutation6
    mixedMoment B raw31071step1 raw31071step1Labels = mixedMoment B raw31071step2 raw31071step2Labels := by
      have ha : raw31071step2 = raw31071step1 := by apply Matrix.ext; unfold raw31071step2 raw31071step1; decide +kernel
      have hl : raw31071step1Labels = labelEmbedding9 ∘ raw31071step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31071step1 raw31071step1Labels raw31071step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4810 node4810Labels := by rfl

def raw31072 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31072Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31072step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw31072step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31072step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw31072step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31072step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw31072step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31072 raw31072Labels = mixedMoment B node4812 node4812Labels := by
  calc
    mixedMoment B raw31072 raw31072Labels = mixedMoment B raw31072step0 raw31072step0Labels := by
      have ha : raw31072step0 = (fun i j => raw31072 (permutation194 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31072step0 raw31072; decide +kernel
      have hl : raw31072step0Labels = raw31072Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31072 raw31072Labels permutation194 permutation4
    mixedMoment B raw31072step0 raw31072step0Labels = mixedMoment B raw31072step1 raw31072step1Labels := by
      have ha : raw31072step1 = -raw31072step0 := by apply Matrix.ext; change ∀ i j, raw31072step1 i j = -(raw31072step0 i j); unfold raw31072step1 raw31072step0; decide +kernel
      have hl : raw31072step1Labels = raw31072step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31072step1 raw31072step1Labels = mixedMoment B raw31072step2 raw31072step2Labels := by
      have ha : raw31072step2 = raw31072step1 := by apply Matrix.ext; unfold raw31072step2 raw31072step1; decide +kernel
      have hl : raw31072step1Labels = labelEmbedding7 ∘ raw31072step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31072step1 raw31072step1Labels raw31072step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4812 node4812Labels := by rfl

def raw31073 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31073Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31073step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31073step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31073step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw31073step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw31073step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw31073step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31073 raw31073Labels = mixedMoment B node4856 node4856Labels := by
  calc
    mixedMoment B raw31073 raw31073Labels = mixedMoment B raw31073step0 raw31073step0Labels := by
      have hz : ∀ j, raw31073 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31073step0 = (fun i j => raw31073 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31073step0 raw31073; decide +kernel
      have hl : raw31073step0Labels = raw31073Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31073 raw31073Labels permutation346 hz
    mixedMoment B raw31073step0 raw31073step0Labels = mixedMoment B raw31073step1 raw31073step1Labels := by
      have ha : raw31073step1 = (fun i j => raw31073step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31073step1 raw31073step0; decide +kernel
      have hl : raw31073step1Labels = raw31073step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31073step0 raw31073step0Labels permutation33 permutation6
    mixedMoment B raw31073step1 raw31073step1Labels = mixedMoment B raw31073step2 raw31073step2Labels := by
      have ha : raw31073step2 = raw31073step1 := by apply Matrix.ext; unfold raw31073step2 raw31073step1; decide +kernel
      have hl : raw31073step1Labels = labelEmbedding9 ∘ raw31073step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31073step1 raw31073step1Labels raw31073step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4856 node4856Labels := by rfl

def raw31074 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw31074Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw31074step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31074step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw31074step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw31074step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw31074step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31074 raw31074Labels = mixedMoment B node4855 node4855Labels := by
  calc
    mixedMoment B raw31074 raw31074Labels = mixedMoment B raw31074step0 raw31074step0Labels := by
      have hz : ∀ j, raw31074 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31074step0 = (fun i j => raw31074 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31074step0 raw31074; decide +kernel
      have hl : raw31074step0Labels = raw31074Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31074 raw31074Labels permutation346 hz
    mixedMoment B raw31074step0 raw31074step0Labels = mixedMoment B raw31074step1 raw31074step1Labels := by
      have ha : raw31074step1 = (fun i j => raw31074step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31074step1 raw31074step0; decide +kernel
      have hl : raw31074step1Labels = raw31074step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31074step0 raw31074step0Labels permutation33 permutation6
    mixedMoment B raw31074step1 raw31074step1Labels = mixedMoment B raw31074step2 raw31074step2Labels := by
      have ha : raw31074step2 = raw31074step1 := by apply Matrix.ext; unfold raw31074step2 raw31074step1; decide +kernel
      have hl : raw31074step1Labels = labelEmbedding9 ∘ raw31074step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31074step1 raw31074step1Labels raw31074step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4855 node4855Labels := by rfl

def raw31075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw31075Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31075step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw31075step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31075step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![1, -3, 2], ![-2, 0, 2]]
def raw31075step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31075step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![0, -2, 2], ![-1, 2, -1], ![-3, 1, 2]]
def raw31075step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31075step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def raw31075step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31075step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def raw31075step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31075 raw31075Labels = mixedMoment B node4472 node4472Labels := by
  calc
    mixedMoment B raw31075 raw31075Labels = mixedMoment B raw31075step0 raw31075step0Labels := by
      have hz : ∀ j, raw31075 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31075step0 = (fun i j => raw31075 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31075step0 raw31075; decide +kernel
      have hl : raw31075step0Labels = raw31075Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31075 raw31075Labels permutation434 hz
    mixedMoment B raw31075step0 raw31075step0Labels = mixedMoment B raw31075step1 raw31075step1Labels := by
      have hz : ∀ j, raw31075step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31075step1 = (fun i j => raw31075step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31075step1 raw31075step0; decide +kernel
      have hl : raw31075step1Labels = raw31075step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31075step0 raw31075step0Labels permutation80 hz
    mixedMoment B raw31075step1 raw31075step1Labels = mixedMoment B raw31075step2 raw31075step2Labels := by
      have ha : raw31075step2 = (fun i j => raw31075step1 (permutation12 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31075step2 raw31075step1; decide +kernel
      have hl : raw31075step2Labels = raw31075step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31075step1 raw31075step1Labels permutation12 permutation4
    mixedMoment B raw31075step2 raw31075step2Labels = mixedMoment B raw31075step3 raw31075step3Labels := by
      have ha : raw31075step3 = -raw31075step2 := by apply Matrix.ext; change ∀ i j, raw31075step3 i j = -(raw31075step2 i j); unfold raw31075step3 raw31075step2; decide +kernel
      have hl : raw31075step3Labels = raw31075step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31075step3 raw31075step3Labels = mixedMoment B raw31075step4 raw31075step4Labels := by
      have ha : raw31075step4 = raw31075step3 := by apply Matrix.ext; unfold raw31075step4 raw31075step3; decide +kernel
      have hl : raw31075step3Labels = labelEmbedding7 ∘ raw31075step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31075step3 raw31075step3Labels raw31075step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4472 node4472Labels := by rfl

def raw31076 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw31076Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw31076step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31076step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-3, 1, 2]]
def raw31076step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31076step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def raw31076step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31076step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def raw31076step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31076 raw31076Labels = mixedMoment B node4814 node4814Labels := by
  calc
    mixedMoment B raw31076 raw31076Labels = mixedMoment B raw31076step0 raw31076step0Labels := by
      have hz : ∀ j, raw31076 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31076step0 = (fun i j => raw31076 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31076step0 raw31076; decide +kernel
      have hl : raw31076step0Labels = raw31076Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31076 raw31076Labels permutation434 hz
    mixedMoment B raw31076step0 raw31076step0Labels = mixedMoment B raw31076step1 raw31076step1Labels := by
      have ha : raw31076step1 = (fun i j => raw31076step0 (permutation42 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31076step1 raw31076step0; decide +kernel
      have hl : raw31076step1Labels = raw31076step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31076step0 raw31076step0Labels permutation42 permutation4
    mixedMoment B raw31076step1 raw31076step1Labels = mixedMoment B raw31076step2 raw31076step2Labels := by
      have ha : raw31076step2 = -raw31076step1 := by apply Matrix.ext; change ∀ i j, raw31076step2 i j = -(raw31076step1 i j); unfold raw31076step2 raw31076step1; decide +kernel
      have hl : raw31076step2Labels = raw31076step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31076step2 raw31076step2Labels = mixedMoment B raw31076step3 raw31076step3Labels := by
      have ha : raw31076step3 = raw31076step2 := by apply Matrix.ext; unfold raw31076step3 raw31076step2; decide +kernel
      have hl : raw31076step2Labels = labelEmbedding7 ∘ raw31076step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31076step2 raw31076step2Labels raw31076step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4814 node4814Labels := by rfl

def raw31077 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw31077Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw31077step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31077step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-3, 1, 2]]
def raw31077step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31077step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def raw31077step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31077step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def raw31077step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31077 raw31077Labels = mixedMoment B node4814 node4814Labels := by
  calc
    mixedMoment B raw31077 raw31077Labels = mixedMoment B raw31077step0 raw31077step0Labels := by
      have hz : ∀ j, raw31077 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31077step0 = (fun i j => raw31077 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31077step0 raw31077; decide +kernel
      have hl : raw31077step0Labels = raw31077Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31077 raw31077Labels permutation346 hz
    mixedMoment B raw31077step0 raw31077step0Labels = mixedMoment B raw31077step1 raw31077step1Labels := by
      have ha : raw31077step1 = (fun i j => raw31077step0 (permutation42 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31077step1 raw31077step0; decide +kernel
      have hl : raw31077step1Labels = raw31077step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31077step0 raw31077step0Labels permutation42 permutation4
    mixedMoment B raw31077step1 raw31077step1Labels = mixedMoment B raw31077step2 raw31077step2Labels := by
      have ha : raw31077step2 = -raw31077step1 := by apply Matrix.ext; change ∀ i j, raw31077step2 i j = -(raw31077step1 i j); unfold raw31077step2 raw31077step1; decide +kernel
      have hl : raw31077step2Labels = raw31077step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31077step2 raw31077step2Labels = mixedMoment B raw31077step3 raw31077step3Labels := by
      have ha : raw31077step3 = raw31077step2 := by apply Matrix.ext; unfold raw31077step3 raw31077step2; decide +kernel
      have hl : raw31077step2Labels = labelEmbedding7 ∘ raw31077step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31077step2 raw31077step2Labels raw31077step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4814 node4814Labels := by rfl

def raw31078 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw31078Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw31078step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31078step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -3, 2], ![-3, 1, 2]]
def raw31078step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31078step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -3, 1], ![2, 1, -3]]
def raw31078step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw31078step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -3, 1], ![2, 1, -3]]
def raw31078step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31078 raw31078Labels = mixedMoment B node4873 node4873Labels := by
  calc
    mixedMoment B raw31078 raw31078Labels = mixedMoment B raw31078step0 raw31078step0Labels := by
      have hz : ∀ j, raw31078 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31078step0 = (fun i j => raw31078 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31078step0 raw31078; decide +kernel
      have hl : raw31078step0Labels = raw31078Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31078 raw31078Labels permutation434 hz
    mixedMoment B raw31078step0 raw31078step0Labels = mixedMoment B raw31078step1 raw31078step1Labels := by
      have hz : ∀ j, raw31078step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31078step1 = (fun i j => raw31078step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31078step1 raw31078step0; decide +kernel
      have hl : raw31078step1Labels = raw31078step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31078step0 raw31078step0Labels permutation80 hz
    mixedMoment B raw31078step1 raw31078step1Labels = mixedMoment B raw31078step2 raw31078step2Labels := by
      have ha : raw31078step2 = (fun i j => raw31078step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31078step2 raw31078step1; decide +kernel
      have hl : raw31078step2Labels = raw31078step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31078step1 raw31078step1Labels permutation9 permutation6
    mixedMoment B raw31078step2 raw31078step2Labels = mixedMoment B raw31078step3 raw31078step3Labels := by
      have ha : raw31078step3 = raw31078step2 := by apply Matrix.ext; unfold raw31078step3 raw31078step2; decide +kernel
      have hl : raw31078step2Labels = labelEmbedding9 ∘ raw31078step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31078step2 raw31078step2Labels raw31078step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4873 node4873Labels := by rfl

def raw31079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31079Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31079step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31079step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, -2, 2], ![-1, -1, 2]]
def raw31079step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31079step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw31079step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31079step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31079step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31079step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31079step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31079 raw31079Labels = mixedMoment B node4491 node4491Labels := by
  calc
    mixedMoment B raw31079 raw31079Labels = mixedMoment B raw31079step0 raw31079step0Labels := by
      have hz : ∀ j, raw31079 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31079step0 = (fun i j => raw31079 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31079step0 raw31079; decide +kernel
      have hl : raw31079step0Labels = raw31079Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31079 raw31079Labels permutation434 hz
    mixedMoment B raw31079step0 raw31079step0Labels = mixedMoment B raw31079step1 raw31079step1Labels := by
      have hz : ∀ j, raw31079step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31079step1 = (fun i j => raw31079step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31079step1 raw31079step0; decide +kernel
      have hl : raw31079step1Labels = raw31079step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31079step0 raw31079step0Labels permutation80 hz
    mixedMoment B raw31079step1 raw31079step1Labels = mixedMoment B raw31079step2 raw31079step2Labels := by
      have ha : raw31079step2 = (fun i j => raw31079step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31079step2 raw31079step1; decide +kernel
      have hl : raw31079step2Labels = raw31079step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31079step1 raw31079step1Labels permutation9 permutation4
    mixedMoment B raw31079step2 raw31079step2Labels = mixedMoment B raw31079step3 raw31079step3Labels := by
      have ha : raw31079step3 = -raw31079step2 := by apply Matrix.ext; change ∀ i j, raw31079step3 i j = -(raw31079step2 i j); unfold raw31079step3 raw31079step2; decide +kernel
      have hl : raw31079step3Labels = raw31079step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31079step3 raw31079step3Labels = mixedMoment B raw31079step4 raw31079step4Labels := by
      have ha : raw31079step4 = raw31079step3 := by apply Matrix.ext; unfold raw31079step4 raw31079step3; decide +kernel
      have hl : raw31079step3Labels = labelEmbedding7 ∘ raw31079step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31079step3 raw31079step3Labels raw31079step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4491 node4491Labels := by rfl

def raw31080 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31080Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31080step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw31080step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw31080step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw31080step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31080step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31080step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw31080step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw31080step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical31080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31080 raw31080Labels = mixedMoment B node4828 node4828Labels := by
  calc
    mixedMoment B raw31080 raw31080Labels = mixedMoment B raw31080step0 raw31080step0Labels := by
      have hz : ∀ j, raw31080 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31080step0 = (fun i j => raw31080 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31080step0 raw31080; decide +kernel
      have hl : raw31080step0Labels = raw31080Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31080 raw31080Labels permutation434 hz
    mixedMoment B raw31080step0 raw31080step0Labels = mixedMoment B raw31080step1 raw31080step1Labels := by
      have ha : raw31080step1 = (fun i j => raw31080step0 (permutation39 i) (permutation4 j)) := by apply Matrix.ext; unfold raw31080step1 raw31080step0; decide +kernel
      have hl : raw31080step1Labels = raw31080step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31080step0 raw31080step0Labels permutation39 permutation4
    mixedMoment B raw31080step1 raw31080step1Labels = mixedMoment B raw31080step2 raw31080step2Labels := by
      have ha : raw31080step2 = -raw31080step1 := by apply Matrix.ext; change ∀ i j, raw31080step2 i j = -(raw31080step1 i j); unfold raw31080step2 raw31080step1; decide +kernel
      have hl : raw31080step2Labels = raw31080step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw31080step2 raw31080step2Labels = mixedMoment B raw31080step3 raw31080step3Labels := by
      have ha : raw31080step3 = raw31080step2 := by apply Matrix.ext; unfold raw31080step3 raw31080step2; decide +kernel
      have hl : raw31080step2Labels = labelEmbedding7 ∘ raw31080step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw31080step2 raw31080step2Labels raw31080step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4828 node4828Labels := by rfl

def raw31081 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31081Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31081step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31081step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31081step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw31081step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31081 raw31081Labels = mixedMoment B node2620 node2620Labels := by
  calc
    mixedMoment B raw31081 raw31081Labels = mixedMoment B raw31081step0 raw31081step0Labels := by
      have hz : ∀ j, raw31081 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31081step0 = (fun i j => raw31081 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31081step0 raw31081; decide +kernel
      have hl : raw31081step0Labels = raw31081Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31081 raw31081Labels permutation434 hz
    mixedMoment B raw31081step0 raw31081step0Labels = mixedMoment B raw31081step1 raw31081step1Labels := by
      have ha : raw31081step1 = (fun i j => raw31081step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31081step1 raw31081step0; decide +kernel
      have hl : raw31081step1Labels = raw31081step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31081step0 raw31081step0Labels permutation33 permutation6
    _ = mixedMoment B node2620 node2620Labels := by rfl

def raw31082 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31082Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31082step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31082step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw31082step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31082 raw31082Labels = mixedMoment B node2620 node2620Labels := by
  calc
    mixedMoment B raw31082 raw31082Labels = mixedMoment B raw31082step0 raw31082step0Labels := by
      have hz : ∀ j, raw31082 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31082step0 = (fun i j => raw31082 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31082step0 raw31082; decide +kernel
      have hl : raw31082step0Labels = raw31082Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31082 raw31082Labels permutation346 hz
    mixedMoment B raw31082step0 raw31082step0Labels = mixedMoment B raw31082step1 raw31082step1Labels := by
      have ha : raw31082step1 = (fun i j => raw31082step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31082step1 raw31082step0; decide +kernel
      have hl : raw31082step1Labels = raw31082step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31082step0 raw31082step0Labels permutation33 permutation6
    _ = mixedMoment B node2620 node2620Labels := by rfl

def raw31083 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31083Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31083step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31083step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw31083step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31083step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw31083step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31083 raw31083Labels = mixedMoment B node2644 node2644Labels := by
  calc
    mixedMoment B raw31083 raw31083Labels = mixedMoment B raw31083step0 raw31083step0Labels := by
      have hz : ∀ j, raw31083 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31083step0 = (fun i j => raw31083 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31083step0 raw31083; decide +kernel
      have hl : raw31083step0Labels = raw31083Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31083 raw31083Labels permutation434 hz
    mixedMoment B raw31083step0 raw31083step0Labels = mixedMoment B raw31083step1 raw31083step1Labels := by
      have hz : ∀ j, raw31083step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31083step1 = (fun i j => raw31083step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31083step1 raw31083step0; decide +kernel
      have hl : raw31083step1Labels = raw31083step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31083step0 raw31083step0Labels permutation80 hz
    mixedMoment B raw31083step1 raw31083step1Labels = mixedMoment B raw31083step2 raw31083step2Labels := by
      have ha : raw31083step2 = (fun i j => raw31083step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31083step2 raw31083step1; decide +kernel
      have hl : raw31083step2Labels = raw31083step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31083step1 raw31083step1Labels permutation9 permutation6
    _ = mixedMoment B node2644 node2644Labels := by rfl

def raw31084 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw31084Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw31084step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31084step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, -2, 2], ![-3, 1, 2]]
def raw31084step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31084step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw31084step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31084 raw31084Labels = mixedMoment B node2643 node2643Labels := by
  calc
    mixedMoment B raw31084 raw31084Labels = mixedMoment B raw31084step0 raw31084step0Labels := by
      have hz : ∀ j, raw31084 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31084step0 = (fun i j => raw31084 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31084step0 raw31084; decide +kernel
      have hl : raw31084step0Labels = raw31084Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31084 raw31084Labels permutation434 hz
    mixedMoment B raw31084step0 raw31084step0Labels = mixedMoment B raw31084step1 raw31084step1Labels := by
      have hz : ∀ j, raw31084step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31084step1 = (fun i j => raw31084step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31084step1 raw31084step0; decide +kernel
      have hl : raw31084step1Labels = raw31084step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31084step0 raw31084step0Labels permutation80 hz
    mixedMoment B raw31084step1 raw31084step1Labels = mixedMoment B raw31084step2 raw31084step2Labels := by
      have ha : raw31084step2 = (fun i j => raw31084step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31084step2 raw31084step1; decide +kernel
      have hl : raw31084step2Labels = raw31084step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31084step1 raw31084step1Labels permutation9 permutation6
    _ = mixedMoment B node2643 node2643Labels := by rfl

def raw31085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31085Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31085step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -2, -1], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31085step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31085step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![3, -2, -1], ![0, -2, 2], ![-2, 0, 2]]
def raw31085step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31085step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 3, -2], ![2, -2, 0], ![2, 0, -2]]
def raw31085step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31085 raw31085Labels = mixedMoment B node1660 node1660Labels := by
  calc
    mixedMoment B raw31085 raw31085Labels = mixedMoment B raw31085step0 raw31085step0Labels := by
      have hz : ∀ j, raw31085 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31085step0 = (fun i j => raw31085 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31085step0 raw31085; decide +kernel
      have hl : raw31085step0Labels = raw31085Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31085 raw31085Labels permutation434 hz
    mixedMoment B raw31085step0 raw31085step0Labels = mixedMoment B raw31085step1 raw31085step1Labels := by
      have hz : ∀ j, raw31085step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31085step1 = (fun i j => raw31085step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31085step1 raw31085step0; decide +kernel
      have hl : raw31085step1Labels = raw31085step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31085step0 raw31085step0Labels permutation80 hz
    mixedMoment B raw31085step1 raw31085step1Labels = mixedMoment B raw31085step2 raw31085step2Labels := by
      have ha : raw31085step2 = (fun i j => raw31085step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31085step2 raw31085step1; decide +kernel
      have hl : raw31085step2Labels = raw31085step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31085step1 raw31085step1Labels permutation9 permutation6
    _ = mixedMoment B node1660 node1660Labels := by rfl

def raw31086 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31086Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31086step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31086step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31086step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw31086step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31086 raw31086Labels = mixedMoment B node2122 node2122Labels := by
  calc
    mixedMoment B raw31086 raw31086Labels = mixedMoment B raw31086step0 raw31086step0Labels := by
      have hz : ∀ j, raw31086 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31086step0 = (fun i j => raw31086 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31086step0 raw31086; decide +kernel
      have hl : raw31086step0Labels = raw31086Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31086 raw31086Labels permutation434 hz
    mixedMoment B raw31086step0 raw31086step0Labels = mixedMoment B raw31086step1 raw31086step1Labels := by
      have ha : raw31086step1 = (fun i j => raw31086step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31086step1 raw31086step0; decide +kernel
      have hl : raw31086step1Labels = raw31086step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31086step0 raw31086step0Labels permutation33 permutation6
    _ = mixedMoment B node2122 node2122Labels := by rfl

def raw31087 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31087Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31087step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31087step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw31087step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31087 raw31087Labels = mixedMoment B node2122 node2122Labels := by
  calc
    mixedMoment B raw31087 raw31087Labels = mixedMoment B raw31087step0 raw31087step0Labels := by
      have hz : ∀ j, raw31087 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31087step0 = (fun i j => raw31087 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31087step0 raw31087; decide +kernel
      have hl : raw31087step0Labels = raw31087Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31087 raw31087Labels permutation346 hz
    mixedMoment B raw31087step0 raw31087step0Labels = mixedMoment B raw31087step1 raw31087step1Labels := by
      have ha : raw31087step1 = (fun i j => raw31087step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31087step1 raw31087step0; decide +kernel
      have hl : raw31087step1Labels = raw31087step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31087step0 raw31087step0Labels permutation33 permutation6
    _ = mixedMoment B node2122 node2122Labels := by rfl

def raw31088 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31088Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31088step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31088step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31088step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw31088step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31088step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -2, 0], ![2, -1, -1]]
def raw31088step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31088 raw31088Labels = mixedMoment B node2138 node2138Labels := by
  calc
    mixedMoment B raw31088 raw31088Labels = mixedMoment B raw31088step0 raw31088step0Labels := by
      have hz : ∀ j, raw31088 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31088step0 = (fun i j => raw31088 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31088step0 raw31088; decide +kernel
      have hl : raw31088step0Labels = raw31088Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31088 raw31088Labels permutation434 hz
    mixedMoment B raw31088step0 raw31088step0Labels = mixedMoment B raw31088step1 raw31088step1Labels := by
      have hz : ∀ j, raw31088step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31088step1 = (fun i j => raw31088step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31088step1 raw31088step0; decide +kernel
      have hl : raw31088step1Labels = raw31088step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31088step0 raw31088step0Labels permutation80 hz
    mixedMoment B raw31088step1 raw31088step1Labels = mixedMoment B raw31088step2 raw31088step2Labels := by
      have ha : raw31088step2 = (fun i j => raw31088step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31088step2 raw31088step1; decide +kernel
      have hl : raw31088step2Labels = raw31088step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31088step1 raw31088step1Labels permutation9 permutation6
    _ = mixedMoment B node2138 node2138Labels := by rfl

def raw31089 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw31089Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, 0, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw31089step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31089step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![3, -2, -1], ![0, -2, 2], ![-3, 1, 2]]
def raw31089step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31089step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![2, -3, 1], ![2, 0, -2]]
def raw31089step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31089 raw31089Labels = mixedMoment B node2137 node2137Labels := by
  calc
    mixedMoment B raw31089 raw31089Labels = mixedMoment B raw31089step0 raw31089step0Labels := by
      have hz : ∀ j, raw31089 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31089step0 = (fun i j => raw31089 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31089step0 raw31089; decide +kernel
      have hl : raw31089step0Labels = raw31089Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31089 raw31089Labels permutation434 hz
    mixedMoment B raw31089step0 raw31089step0Labels = mixedMoment B raw31089step1 raw31089step1Labels := by
      have hz : ∀ j, raw31089step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31089step1 = (fun i j => raw31089step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31089step1 raw31089step0; decide +kernel
      have hl : raw31089step1Labels = raw31089step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31089step0 raw31089step0Labels permutation80 hz
    mixedMoment B raw31089step1 raw31089step1Labels = mixedMoment B raw31089step2 raw31089step2Labels := by
      have ha : raw31089step2 = (fun i j => raw31089step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31089step2 raw31089step1; decide +kernel
      have hl : raw31089step2Labels = raw31089step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31089step1 raw31089step1Labels permutation9 permutation6
    _ = mixedMoment B node2137 node2137Labels := by rfl

def raw31090 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31090Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31090step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31090step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31090step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31090 raw31090Labels = mixedMoment B node1640 node1640Labels := by
  calc
    mixedMoment B raw31090 raw31090Labels = mixedMoment B raw31090step0 raw31090step0Labels := by
      have hz : ∀ j, raw31090 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31090step0 = (fun i j => raw31090 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31090step0 raw31090; decide +kernel
      have hl : raw31090step0Labels = raw31090Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31090 raw31090Labels permutation434 hz
    mixedMoment B raw31090step0 raw31090step0Labels = mixedMoment B raw31090step1 raw31090step1Labels := by
      have ha : raw31090step1 = (fun i j => raw31090step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31090step1 raw31090step0; decide +kernel
      have hl : raw31090step1Labels = raw31090step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31090step0 raw31090step0Labels permutation33 permutation6
    _ = mixedMoment B node1640 node1640Labels := by rfl

def raw31091 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31091Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31091step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31091step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31091 raw31091Labels = mixedMoment B node2072 node2072Labels := by
  calc
    mixedMoment B raw31091 raw31091Labels = mixedMoment B raw31091step0 raw31091step0Labels := by
      have ha : raw31091step0 = (fun i j => raw31091 (permutation159 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31091step0 raw31091; decide +kernel
      have hl : raw31091step0Labels = raw31091Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31091 raw31091Labels permutation159 permutation6
    _ = mixedMoment B node2072 node2072Labels := by rfl

def raw31092 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31092Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31092step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31092step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw31092step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31092 raw31092Labels = mixedMoment B node2094 node2094Labels := by
  calc
    mixedMoment B raw31092 raw31092Labels = mixedMoment B raw31092step0 raw31092step0Labels := by
      have hz : ∀ j, raw31092 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31092step0 = (fun i j => raw31092 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31092step0 raw31092; decide +kernel
      have hl : raw31092step0Labels = raw31092Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31092 raw31092Labels permutation434 hz
    mixedMoment B raw31092step0 raw31092step0Labels = mixedMoment B raw31092step1 raw31092step1Labels := by
      have ha : raw31092step1 = (fun i j => raw31092step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31092step1 raw31092step0; decide +kernel
      have hl : raw31092step1Labels = raw31092step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31092step0 raw31092step0Labels permutation33 permutation6
    _ = mixedMoment B node2094 node2094Labels := by rfl

def raw31093 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw31093Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw31093step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31093step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw31093step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31093 raw31093Labels = mixedMoment B node2093 node2093Labels := by
  calc
    mixedMoment B raw31093 raw31093Labels = mixedMoment B raw31093step0 raw31093step0Labels := by
      have hz : ∀ j, raw31093 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31093step0 = (fun i j => raw31093 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31093step0 raw31093; decide +kernel
      have hl : raw31093step0Labels = raw31093Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31093 raw31093Labels permutation434 hz
    mixedMoment B raw31093step0 raw31093step0Labels = mixedMoment B raw31093step1 raw31093step1Labels := by
      have ha : raw31093step1 = (fun i j => raw31093step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31093step1 raw31093step0; decide +kernel
      have hl : raw31093step1Labels = raw31093step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31093step0 raw31093step0Labels permutation33 permutation6
    _ = mixedMoment B node2093 node2093Labels := by rfl

def raw31094 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31094Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31094step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31094step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31094step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31094step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31094 raw31094Labels = mixedMoment B node1640 node1640Labels := by
  calc
    mixedMoment B raw31094 raw31094Labels = mixedMoment B raw31094step0 raw31094step0Labels := by
      have hz : ∀ j, raw31094 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31094step0 = (fun i j => raw31094 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31094step0 raw31094; decide +kernel
      have hl : raw31094step0Labels = raw31094Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31094 raw31094Labels permutation346 hz
    mixedMoment B raw31094step0 raw31094step0Labels = mixedMoment B raw31094step1 raw31094step1Labels := by
      have ha : raw31094step1 = (fun i j => raw31094step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31094step1 raw31094step0; decide +kernel
      have hl : raw31094step1Labels = raw31094step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31094step0 raw31094step0Labels permutation33 permutation6
    _ = mixedMoment B node1640 node1640Labels := by rfl

def raw31095 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31095Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31095step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31095step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31095step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31095 raw31095Labels = mixedMoment B node2028 node2028Labels := by
  calc
    mixedMoment B raw31095 raw31095Labels = mixedMoment B raw31095step0 raw31095step0Labels := by
      have hz : ∀ j, raw31095 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31095step0 = (fun i j => raw31095 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31095step0 raw31095; decide +kernel
      have hl : raw31095step0Labels = raw31095Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31095 raw31095Labels permutation346 hz
    mixedMoment B raw31095step0 raw31095step0Labels = mixedMoment B raw31095step1 raw31095step1Labels := by
      have ha : raw31095step1 = (fun i j => raw31095step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31095step1 raw31095step0; decide +kernel
      have hl : raw31095step1Labels = raw31095step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31095step0 raw31095step0Labels permutation33 permutation6
    _ = mixedMoment B node2028 node2028Labels := by rfl

def raw31096 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw31096Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31096step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw31096step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31096 raw31096Labels = mixedMoment B node2072 node2072Labels := by
  calc
    mixedMoment B raw31096 raw31096Labels = mixedMoment B raw31096step0 raw31096step0Labels := by
      have ha : raw31096step0 = (fun i j => raw31096 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31096step0 raw31096; decide +kernel
      have hl : raw31096step0Labels = raw31096Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31096 raw31096Labels permutation153 permutation6
    _ = mixedMoment B node2072 node2072Labels := by rfl

def raw31097 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31097Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw31097step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31097step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw31097step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31097 raw31097Labels = mixedMoment B node2094 node2094Labels := by
  calc
    mixedMoment B raw31097 raw31097Labels = mixedMoment B raw31097step0 raw31097step0Labels := by
      have hz : ∀ j, raw31097 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31097step0 = (fun i j => raw31097 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31097step0 raw31097; decide +kernel
      have hl : raw31097step0Labels = raw31097Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31097 raw31097Labels permutation346 hz
    mixedMoment B raw31097step0 raw31097step0Labels = mixedMoment B raw31097step1 raw31097step1Labels := by
      have ha : raw31097step1 = (fun i j => raw31097step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31097step1 raw31097step0; decide +kernel
      have hl : raw31097step1Labels = raw31097step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31097step0 raw31097step0Labels permutation33 permutation6
    _ = mixedMoment B node2094 node2094Labels := by rfl

def raw31098 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw31098Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31098step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw31098step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31098step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw31098step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31098 raw31098Labels = mixedMoment B node2093 node2093Labels := by
  calc
    mixedMoment B raw31098 raw31098Labels = mixedMoment B raw31098step0 raw31098step0Labels := by
      have hz : ∀ j, raw31098 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31098step0 = (fun i j => raw31098 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31098step0 raw31098; decide +kernel
      have hl : raw31098step0Labels = raw31098Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31098 raw31098Labels permutation346 hz
    mixedMoment B raw31098step0 raw31098step0Labels = mixedMoment B raw31098step1 raw31098step1Labels := by
      have ha : raw31098step1 = (fun i j => raw31098step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31098step1 raw31098step0; decide +kernel
      have hl : raw31098step1Labels = raw31098step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31098step0 raw31098step0Labels permutation33 permutation6
    _ = mixedMoment B node2093 node2093Labels := by rfl

def raw31099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw31099Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31099step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw31099step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31099step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 4, -3], ![2, -1, -1], ![1, -3, 2], ![-2, 0, 2]]
def raw31099step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31099step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![2, -2, 0], ![2, 1, -3]]
def raw31099step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31099 raw31099Labels = mixedMoment B node1652 node1652Labels := by
  calc
    mixedMoment B raw31099 raw31099Labels = mixedMoment B raw31099step0 raw31099step0Labels := by
      have hz : ∀ j, raw31099 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31099step0 = (fun i j => raw31099 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31099step0 raw31099; decide +kernel
      have hl : raw31099step0Labels = raw31099Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31099 raw31099Labels permutation434 hz
    mixedMoment B raw31099step0 raw31099step0Labels = mixedMoment B raw31099step1 raw31099step1Labels := by
      have hz : ∀ j, raw31099step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31099step1 = (fun i j => raw31099step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31099step1 raw31099step0; decide +kernel
      have hl : raw31099step1Labels = raw31099step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31099step0 raw31099step0Labels permutation80 hz
    mixedMoment B raw31099step1 raw31099step1Labels = mixedMoment B raw31099step2 raw31099step2Labels := by
      have ha : raw31099step2 = (fun i j => raw31099step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31099step2 raw31099step1; decide +kernel
      have hl : raw31099step2Labels = raw31099step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31099step1 raw31099step1Labels permutation9 permutation6
    _ = mixedMoment B node1652 node1652Labels := by rfl

def raw31100 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw31100Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31100step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw31100step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31100step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -3, 2], ![-2, 0, 2]]
def raw31100step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31100step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw31100step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31100 raw31100Labels = mixedMoment B node2065 node2065Labels := by
  calc
    mixedMoment B raw31100 raw31100Labels = mixedMoment B raw31100step0 raw31100step0Labels := by
      have hz : ∀ j, raw31100 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31100step0 = (fun i j => raw31100 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31100step0 raw31100; decide +kernel
      have hl : raw31100step0Labels = raw31100Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31100 raw31100Labels permutation434 hz
    mixedMoment B raw31100step0 raw31100step0Labels = mixedMoment B raw31100step1 raw31100step1Labels := by
      have hz : ∀ j, raw31100step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31100step1 = (fun i j => raw31100step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31100step1 raw31100step0; decide +kernel
      have hl : raw31100step1Labels = raw31100step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31100step0 raw31100step0Labels permutation80 hz
    mixedMoment B raw31100step1 raw31100step1Labels = mixedMoment B raw31100step2 raw31100step2Labels := by
      have ha : raw31100step2 = (fun i j => raw31100step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31100step2 raw31100step1; decide +kernel
      have hl : raw31100step2Labels = raw31100step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31100step1 raw31100step1Labels permutation9 permutation6
    _ = mixedMoment B node2065 node2065Labels := by rfl

def raw31101 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw31101Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31101step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw31101step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31101step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw31101step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31101 raw31101Labels = mixedMoment B node2081 node2081Labels := by
  calc
    mixedMoment B raw31101 raw31101Labels = mixedMoment B raw31101step0 raw31101step0Labels := by
      have hz : ∀ j, raw31101 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31101step0 = (fun i j => raw31101 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31101step0 raw31101; decide +kernel
      have hl : raw31101step0Labels = raw31101Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31101 raw31101Labels permutation434 hz
    mixedMoment B raw31101step0 raw31101step0Labels = mixedMoment B raw31101step1 raw31101step1Labels := by
      have ha : raw31101step1 = (fun i j => raw31101step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31101step1 raw31101step0; decide +kernel
      have hl : raw31101step1Labels = raw31101step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31101step0 raw31101step0Labels permutation33 permutation6
    _ = mixedMoment B node2081 node2081Labels := by rfl

def raw31102 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw31102Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw31102step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31102step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw31102step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31102 raw31102Labels = mixedMoment B node2081 node2081Labels := by
  calc
    mixedMoment B raw31102 raw31102Labels = mixedMoment B raw31102step0 raw31102step0Labels := by
      have hz : ∀ j, raw31102 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw31102step0 = (fun i j => raw31102 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw31102step0 raw31102; decide +kernel
      have hl : raw31102step0Labels = raw31102Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31102 raw31102Labels permutation346 hz
    mixedMoment B raw31102step0 raw31102step0Labels = mixedMoment B raw31102step1 raw31102step1Labels := by
      have ha : raw31102step1 = (fun i j => raw31102step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31102step1 raw31102step0; decide +kernel
      have hl : raw31102step1Labels = raw31102step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31102step0 raw31102step0Labels permutation33 permutation6
    _ = mixedMoment B node2081 node2081Labels := by rfl

def raw31103 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw31103Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31103step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw31103step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31103step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -3, 2], ![-3, 1, 2]]
def raw31103step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw31103step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -3, 1], ![2, 1, -3]]
def raw31103step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical31103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw31103 raw31103Labels = mixedMoment B node2114 node2114Labels := by
  calc
    mixedMoment B raw31103 raw31103Labels = mixedMoment B raw31103step0 raw31103step0Labels := by
      have hz : ∀ j, raw31103 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw31103step0 = (fun i j => raw31103 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw31103step0 raw31103; decide +kernel
      have hl : raw31103step0Labels = raw31103Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31103 raw31103Labels permutation434 hz
    mixedMoment B raw31103step0 raw31103step0Labels = mixedMoment B raw31103step1 raw31103step1Labels := by
      have hz : ∀ j, raw31103step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw31103step1 = (fun i j => raw31103step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw31103step1 raw31103step0; decide +kernel
      have hl : raw31103step1Labels = raw31103step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw31103step0 raw31103step0Labels permutation80 hz
    mixedMoment B raw31103step1 raw31103step1Labels = mixedMoment B raw31103step2 raw31103step2Labels := by
      have ha : raw31103step2 = (fun i j => raw31103step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw31103step2 raw31103step1; decide +kernel
      have hl : raw31103step2Labels = raw31103step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw31103step1 raw31103step1Labels permutation9 permutation6
    _ = mixedMoment B node2114 node2114Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
