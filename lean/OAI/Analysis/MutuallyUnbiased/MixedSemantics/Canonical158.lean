import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
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
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw20224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20224Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20224step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![4, -1, -3]]
def raw20224step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20224step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-4, 3, 1]]
def raw20224step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20224step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw20224step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20224 raw20224Labels = mixedMoment B node911 node911Labels := by
  calc
    mixedMoment B raw20224 raw20224Labels = mixedMoment B raw20224step0 raw20224step0Labels := by
      have hz : ∀ j, raw20224 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20224step0 = (fun i j => raw20224 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20224step0 raw20224; decide +kernel
      have hl : raw20224step0Labels = raw20224Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20224 raw20224Labels permutation265 hz
    mixedMoment B raw20224step0 raw20224step0Labels = mixedMoment B raw20224step1 raw20224step1Labels := by
      have ha : raw20224step1 = (fun i j => raw20224step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20224step1 raw20224step0; decide +kernel
      have hl : raw20224step1Labels = raw20224step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20224step0 raw20224step0Labels permutation151 permutation2
    mixedMoment B raw20224step1 raw20224step1Labels = mixedMoment B raw20224step2 raw20224step2Labels := by
      have ha : raw20224step2 = -raw20224step1 := by apply Matrix.ext; change ∀ i j, raw20224step2 i j = -(raw20224step1 i j); unfold raw20224step2 raw20224step1; decide +kernel
      have hl : raw20224step2Labels = raw20224step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node911 node911Labels := by rfl

def raw20225 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw20225Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20225step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw20225step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20225 raw20225Labels = mixedMoment B node1995 node1995Labels := by
  calc
    mixedMoment B raw20225 raw20225Labels = mixedMoment B raw20225step0 raw20225step0Labels := by
      have ha : raw20225step0 = (fun i j => raw20225 (permutation620 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20225step0 raw20225; decide +kernel
      have hl : raw20225step0Labels = raw20225Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20225 raw20225Labels permutation620 permutation2
    _ = mixedMoment B node1995 node1995Labels := by rfl

def raw20226 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw20226Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw20226step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20226step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw20226step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20226step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw20226step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20226 raw20226Labels = mixedMoment B node2226 node2226Labels := by
  calc
    mixedMoment B raw20226 raw20226Labels = mixedMoment B raw20226step0 raw20226step0Labels := by
      have hz : ∀ j, raw20226 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20226step0 = (fun i j => raw20226 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20226step0 raw20226; decide +kernel
      have hl : raw20226step0Labels = raw20226Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20226 raw20226Labels permutation434 hz
    mixedMoment B raw20226step0 raw20226step0Labels = mixedMoment B raw20226step1 raw20226step1Labels := by
      have hz : ∀ j, raw20226step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20226step1 = (fun i j => raw20226step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20226step1 raw20226step0; decide +kernel
      have hl : raw20226step1Labels = raw20226step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20226step0 raw20226step0Labels permutation56 hz
    mixedMoment B raw20226step1 raw20226step1Labels = mixedMoment B raw20226step2 raw20226step2Labels := by
      have ha : raw20226step2 = (fun i j => raw20226step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20226step2 raw20226step1; decide +kernel
      have hl : raw20226step2Labels = raw20226step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20226step1 raw20226step1Labels permutation31 permutation2
    _ = mixedMoment B node2226 node2226Labels := by rfl

def raw20227 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-4, 1, 3]]
def raw20227Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-4, 1, 3]]
def raw20227step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20227step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw20227step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20227 raw20227Labels = mixedMoment B node997 node997Labels := by
  calc
    mixedMoment B raw20227 raw20227Labels = mixedMoment B raw20227step0 raw20227step0Labels := by
      have hz : ∀ j, raw20227 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20227step0 = (fun i j => raw20227 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20227step0 raw20227; decide +kernel
      have hl : raw20227step0Labels = raw20227Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20227 raw20227Labels permutation265 hz
    mixedMoment B raw20227step0 raw20227step0Labels = mixedMoment B raw20227step1 raw20227step1Labels := by
      have ha : raw20227step1 = (fun i j => raw20227step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20227step1 raw20227step0; decide +kernel
      have hl : raw20227step1Labels = raw20227step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20227step0 raw20227step0Labels permutation149 permutation2
    _ = mixedMoment B node997 node997Labels := by rfl

def raw20228 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw20228Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20228step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, 0, -4], ![0, -3, 3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw20228step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20228step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw20228step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20228 raw20228Labels = mixedMoment B node833 node833Labels := by
  calc
    mixedMoment B raw20228 raw20228Labels = mixedMoment B raw20228step0 raw20228step0Labels := by
      have ha : raw20228step0 = (fun i j => raw20228 (permutation246 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20228step0 raw20228; decide +kernel
      have hl : raw20228step0Labels = raw20228Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20228 raw20228Labels permutation246 permutation4
    mixedMoment B raw20228step0 raw20228step0Labels = mixedMoment B raw20228step1 raw20228step1Labels := by
      have ha : raw20228step1 = -raw20228step0 := by apply Matrix.ext; change ∀ i j, raw20228step1 i j = -(raw20228step0 i j); unfold raw20228step1 raw20228step0; decide +kernel
      have hl : raw20228step1Labels = raw20228step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node833 node833Labels := by rfl

def raw20229 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw20229Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![2, -2, 0], ![1, -1, 0], ![0, -1, 1], ![-3, 0, 3]]
def raw20229step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20229step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -3, 3], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw20229step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20229step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw20229step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20229 raw20229Labels = mixedMoment B node835 node835Labels := by
  calc
    mixedMoment B raw20229 raw20229Labels = mixedMoment B raw20229step0 raw20229step0Labels := by
      have hz : ∀ j, raw20229 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20229step0 = (fun i j => raw20229 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20229step0 raw20229; decide +kernel
      have hl : raw20229step0Labels = raw20229Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20229 raw20229Labels permutation265 hz
    mixedMoment B raw20229step0 raw20229step0Labels = mixedMoment B raw20229step1 raw20229step1Labels := by
      have ha : raw20229step1 = (fun i j => raw20229step0 (permutation53 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20229step1 raw20229step0; decide +kernel
      have hl : raw20229step1Labels = raw20229step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20229step0 raw20229step0Labels permutation53 permutation4
    mixedMoment B raw20229step1 raw20229step1Labels = mixedMoment B raw20229step2 raw20229step2Labels := by
      have ha : raw20229step2 = -raw20229step1 := by apply Matrix.ext; change ∀ i j, raw20229step2 i j = -(raw20229step1 i j); unfold raw20229step2 raw20229step1; decide +kernel
      have hl : raw20229step2Labels = raw20229step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node835 node835Labels := by rfl

def raw20230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw20230Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20230step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw20230step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20230step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20230step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20230 raw20230Labels = mixedMoment B node1355 node1355Labels := by
  calc
    mixedMoment B raw20230 raw20230Labels = mixedMoment B raw20230step0 raw20230step0Labels := by
      have hz : ∀ j, raw20230 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20230step0 = (fun i j => raw20230 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20230step0 raw20230; decide +kernel
      have hl : raw20230step0Labels = raw20230Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20230 raw20230Labels permutation265 hz
    mixedMoment B raw20230step0 raw20230step0Labels = mixedMoment B raw20230step1 raw20230step1Labels := by
      have ha : raw20230step1 = (fun i j => raw20230step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20230step1 raw20230step0; decide +kernel
      have hl : raw20230step1Labels = raw20230step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20230step0 raw20230step0Labels permutation38 permutation2
    _ = mixedMoment B node1355 node1355Labels := by rfl

def raw20231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw20231Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20231step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw20231step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20231step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw20231step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20231 raw20231Labels = mixedMoment B node1902 node1902Labels := by
  calc
    mixedMoment B raw20231 raw20231Labels = mixedMoment B raw20231step0 raw20231step0Labels := by
      have ha : raw20231step0 = (fun i j => raw20231 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20231step0 raw20231; decide +kernel
      have hl : raw20231step0Labels = raw20231Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20231 raw20231Labels permutation682 permutation2
    mixedMoment B raw20231step0 raw20231step0Labels = mixedMoment B raw20231step1 raw20231step1Labels := by
      have ha : raw20231step1 = -raw20231step0 := by apply Matrix.ext; change ∀ i j, raw20231step1 i j = -(raw20231step0 i j); unfold raw20231step1 raw20231step0; decide +kernel
      have hl : raw20231step1Labels = raw20231step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1902 node1902Labels := by rfl

def raw20232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw20232Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![3, 0, -3]]
def raw20232step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20232step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-3, 2, 1]]
def raw20232step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20232step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![3, -2, -1]]
def raw20232step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20232 raw20232Labels = mixedMoment B node1926 node1926Labels := by
  calc
    mixedMoment B raw20232 raw20232Labels = mixedMoment B raw20232step0 raw20232step0Labels := by
      have hz : ∀ j, raw20232 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20232step0 = (fun i j => raw20232 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20232step0 raw20232; decide +kernel
      have hl : raw20232step0Labels = raw20232Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20232 raw20232Labels permutation265 hz
    mixedMoment B raw20232step0 raw20232step0Labels = mixedMoment B raw20232step1 raw20232step1Labels := by
      have ha : raw20232step1 = (fun i j => raw20232step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20232step1 raw20232step0; decide +kernel
      have hl : raw20232step1Labels = raw20232step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20232step0 raw20232step0Labels permutation151 permutation2
    mixedMoment B raw20232step1 raw20232step1Labels = mixedMoment B raw20232step2 raw20232step2Labels := by
      have ha : raw20232step2 = -raw20232step1 := by apply Matrix.ext; change ∀ i j, raw20232step2 i j = -(raw20232step1 i j); unfold raw20232step2 raw20232step1; decide +kernel
      have hl : raw20232step2Labels = raw20232step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1926 node1926Labels := by rfl

def raw20233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![3, 0, -3]]
def raw20233Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![3, 0, -3]]
def raw20233step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20233step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw20233step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20233step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw20233step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20233 raw20233Labels = mixedMoment B node1915 node1915Labels := by
  calc
    mixedMoment B raw20233 raw20233Labels = mixedMoment B raw20233step0 raw20233step0Labels := by
      have hz : ∀ j, raw20233 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20233step0 = (fun i j => raw20233 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20233step0 raw20233; decide +kernel
      have hl : raw20233step0Labels = raw20233Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20233 raw20233Labels permutation265 hz
    mixedMoment B raw20233step0 raw20233step0Labels = mixedMoment B raw20233step1 raw20233step1Labels := by
      have ha : raw20233step1 = (fun i j => raw20233step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20233step1 raw20233step0; decide +kernel
      have hl : raw20233step1Labels = raw20233step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20233step0 raw20233step0Labels permutation149 permutation2
    mixedMoment B raw20233step1 raw20233step1Labels = mixedMoment B raw20233step2 raw20233step2Labels := by
      have ha : raw20233step2 = -raw20233step1 := by apply Matrix.ext; change ∀ i j, raw20233step2 i j = -(raw20233step1 i j); unfold raw20233step2 raw20233step1; decide +kernel
      have hl : raw20233step2Labels = raw20233step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1915 node1915Labels := by rfl

def raw20234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![3, 0, -3]]
def raw20234Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![3, 0, -3]]
def raw20234step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20234step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-3, 2, 1]]
def raw20234step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20234step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![3, -2, -1]]
def raw20234step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20234 raw20234Labels = mixedMoment B node2197 node2197Labels := by
  calc
    mixedMoment B raw20234 raw20234Labels = mixedMoment B raw20234step0 raw20234step0Labels := by
      have hz : ∀ j, raw20234 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20234step0 = (fun i j => raw20234 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20234step0 raw20234; decide +kernel
      have hl : raw20234step0Labels = raw20234Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20234 raw20234Labels permutation265 hz
    mixedMoment B raw20234step0 raw20234step0Labels = mixedMoment B raw20234step1 raw20234step1Labels := by
      have ha : raw20234step1 = (fun i j => raw20234step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20234step1 raw20234step0; decide +kernel
      have hl : raw20234step1Labels = raw20234step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20234step0 raw20234step0Labels permutation149 permutation2
    mixedMoment B raw20234step1 raw20234step1Labels = mixedMoment B raw20234step2 raw20234step2Labels := by
      have ha : raw20234step2 = -raw20234step1 := by apply Matrix.ext; change ∀ i j, raw20234step2 i j = -(raw20234step1 i j); unfold raw20234step2 raw20234step1; decide +kernel
      have hl : raw20234step2Labels = raw20234step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2197 node2197Labels := by rfl

def raw20235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw20235Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw20235step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20235step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw20235step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20235 raw20235Labels = mixedMoment B node3024 node3024Labels := by
  calc
    mixedMoment B raw20235 raw20235Labels = mixedMoment B raw20235step0 raw20235step0Labels := by
      have hz : ∀ j, raw20235 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20235step0 = (fun i j => raw20235 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20235step0 raw20235; decide +kernel
      have hl : raw20235step0Labels = raw20235Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20235 raw20235Labels permutation265 hz
    mixedMoment B raw20235step0 raw20235step0Labels = mixedMoment B raw20235step1 raw20235step1Labels := by
      have ha : raw20235step1 = (fun i j => raw20235step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20235step1 raw20235step0; decide +kernel
      have hl : raw20235step1Labels = raw20235step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20235step0 raw20235step0Labels permutation38 permutation2
    _ = mixedMoment B node3024 node3024Labels := by rfl

def raw20236 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-1, 1], ![-2, 2], ![1, -1], ![3, -3]]
def raw20236Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20236step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-2, 2], ![1, -1], ![3, -3]]
def raw20236step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20236step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw20236step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20236step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw20236step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical20236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20236 raw20236Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw20236 raw20236Labels = mixedMoment B raw20236step0 raw20236step0Labels := by
      have hz : ∀ j, raw20236 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20236step0 = (fun i j => raw20236 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20236step0 raw20236; decide +kernel
      have hl : raw20236step0Labels = raw20236Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20236 raw20236Labels permutation265 hz
    mixedMoment B raw20236step0 raw20236step0Labels = mixedMoment B raw20236step1 raw20236step1Labels := by
      have ha : raw20236step1 = (fun i j => raw20236step0 (permutation146 i) (permutation0 j)) := by apply Matrix.ext; unfold raw20236step1 raw20236step0; decide +kernel
      have hl : raw20236step1Labels = raw20236step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20236step0 raw20236step0Labels permutation146 permutation0
    mixedMoment B raw20236step1 raw20236step1Labels = mixedMoment B raw20236step2 raw20236step2Labels := by
      have ha : raw20236step2 = -raw20236step1 := by apply Matrix.ext; change ∀ i j, raw20236step2 i j = -(raw20236step1 i j); unfold raw20236step2 raw20236step1; decide +kernel
      have hl : raw20236step2Labels = raw20236step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw20237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20237Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20237 raw20237Labels = mixedMoment B node1376 node1376Labels := by
  calc
    _ = mixedMoment B node1376 node1376Labels := by rfl

def raw20238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20238Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20238step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw20238step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20238step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20238step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20238 raw20238Labels = mixedMoment B node1898 node1898Labels := by
  calc
    mixedMoment B raw20238 raw20238Labels = mixedMoment B raw20238step0 raw20238step0Labels := by
      have ha : raw20238step0 = (fun i j => raw20238 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20238step0 raw20238; decide +kernel
      have hl : raw20238step0Labels = raw20238Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20238 raw20238Labels permutation682 permutation2
    mixedMoment B raw20238step0 raw20238step0Labels = mixedMoment B raw20238step1 raw20238step1Labels := by
      have ha : raw20238step1 = -raw20238step0 := by apply Matrix.ext; change ∀ i j, raw20238step1 i j = -(raw20238step0 i j); unfold raw20238step1 raw20238step0; decide +kernel
      have hl : raw20238step1Labels = raw20238step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1898 node1898Labels := by rfl

def raw20239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20239Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20239step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw20239step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20239step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20239step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20239 raw20239Labels = mixedMoment B node1898 node1898Labels := by
  calc
    mixedMoment B raw20239 raw20239Labels = mixedMoment B raw20239step0 raw20239step0Labels := by
      have ha : raw20239step0 = (fun i j => raw20239 (permutation676 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20239step0 raw20239; decide +kernel
      have hl : raw20239step0Labels = raw20239Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20239 raw20239Labels permutation676 permutation2
    mixedMoment B raw20239step0 raw20239step0Labels = mixedMoment B raw20239step1 raw20239step1Labels := by
      have ha : raw20239step1 = -raw20239step0 := by apply Matrix.ext; change ∀ i j, raw20239step1 i j = -(raw20239step0 i j); unfold raw20239step1 raw20239step0; decide +kernel
      have hl : raw20239step1Labels = raw20239step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1898 node1898Labels := by rfl

def raw20240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw20240Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20240step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw20240step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20240step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20240step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20240 raw20240Labels = mixedMoment B node1898 node1898Labels := by
  calc
    mixedMoment B raw20240 raw20240Labels = mixedMoment B raw20240step0 raw20240step0Labels := by
      have ha : raw20240step0 = (fun i j => raw20240 (permutation674 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20240step0 raw20240; decide +kernel
      have hl : raw20240step0Labels = raw20240Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20240 raw20240Labels permutation674 permutation2
    mixedMoment B raw20240step0 raw20240step0Labels = mixedMoment B raw20240step1 raw20240step1Labels := by
      have ha : raw20240step1 = -raw20240step0 := by apply Matrix.ext; change ∀ i j, raw20240step1 i j = -(raw20240step0 i j); unfold raw20240step1 raw20240step0; decide +kernel
      have hl : raw20240step1Labels = raw20240step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1898 node1898Labels := by rfl

def raw20241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw20241Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20241step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 2, 1]]
def raw20241step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20241step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -2, -1]]
def raw20241step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20241 raw20241Labels = mixedMoment B node2187 node2187Labels := by
  calc
    mixedMoment B raw20241 raw20241Labels = mixedMoment B raw20241step0 raw20241step0Labels := by
      have ha : raw20241step0 = (fun i j => raw20241 (permutation674 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20241step0 raw20241; decide +kernel
      have hl : raw20241step0Labels = raw20241Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20241 raw20241Labels permutation674 permutation2
    mixedMoment B raw20241step0 raw20241step0Labels = mixedMoment B raw20241step1 raw20241step1Labels := by
      have ha : raw20241step1 = -raw20241step0 := by apply Matrix.ext; change ∀ i j, raw20241step1 i j = -(raw20241step0 i j); unfold raw20241step1 raw20241step0; decide +kernel
      have hl : raw20241step1Labels = raw20241step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2187 node2187Labels := by rfl

def raw20242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw20242Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20242 raw20242Labels = mixedMoment B node3058 node3058Labels := by
  calc
    _ = mixedMoment B node3058 node3058Labels := by rfl

def raw20243 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![3, -3]]
def raw20243Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20243step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw20243step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20243step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw20243step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical20243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20243 raw20243Labels = mixedMoment B node4079 node4079Labels := by
  calc
    mixedMoment B raw20243 raw20243Labels = mixedMoment B raw20243step0 raw20243step0Labels := by
      have ha : raw20243step0 = (fun i j => raw20243 (permutation665 i) (permutation0 j)) := by apply Matrix.ext; unfold raw20243step0 raw20243; decide +kernel
      have hl : raw20243step0Labels = raw20243Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20243 raw20243Labels permutation665 permutation0
    mixedMoment B raw20243step0 raw20243step0Labels = mixedMoment B raw20243step1 raw20243step1Labels := by
      have ha : raw20243step1 = -raw20243step0 := by apply Matrix.ext; change ∀ i j, raw20243step1 i j = -(raw20243step0 i j); unfold raw20243step1 raw20243step0; decide +kernel
      have hl : raw20243step1Labels = raw20243step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4079 node4079Labels := by rfl

def raw20244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2], ![3, -2, -1]]
def raw20244Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw20244step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20244 raw20244Labels = mixedMoment B node1132 node1132Labels := by
  calc
    mixedMoment B raw20244 raw20244Labels = mixedMoment B raw20244step0 raw20244step0Labels := by
      have hz : ∀ j, raw20244 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20244step0 = (fun i j => raw20244 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20244step0 raw20244; decide +kernel
      have hl : raw20244step0Labels = raw20244Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20244 raw20244Labels permutation434 hz
    _ = mixedMoment B node1132 node1132Labels := by rfl

def raw20245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw20245Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw20245step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20245 raw20245Labels = mixedMoment B node1132 node1132Labels := by
  calc
    mixedMoment B raw20245 raw20245Labels = mixedMoment B raw20245step0 raw20245step0Labels := by
      have hz : ∀ j, raw20245 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20245step0 = (fun i j => raw20245 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20245step0 raw20245; decide +kernel
      have hl : raw20245step0Labels = raw20245Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20245 raw20245Labels permutation346 hz
    _ = mixedMoment B node1132 node1132Labels := by rfl

def raw20246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw20246Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20246step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw20246step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20246step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw20246step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20246 raw20246Labels = mixedMoment B node1145 node1145Labels := by
  calc
    mixedMoment B raw20246 raw20246Labels = mixedMoment B raw20246step0 raw20246step0Labels := by
      have hz : ∀ j, raw20246 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20246step0 = (fun i j => raw20246 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20246step0 raw20246; decide +kernel
      have hl : raw20246step0Labels = raw20246Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20246 raw20246Labels permutation434 hz
    mixedMoment B raw20246step0 raw20246step0Labels = mixedMoment B raw20246step1 raw20246step1Labels := by
      have hz : ∀ j, raw20246step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20246step1 = (fun i j => raw20246step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20246step1 raw20246step0; decide +kernel
      have hl : raw20246step1Labels = raw20246step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20246step0 raw20246step0Labels permutation80 hz
    _ = mixedMoment B node1145 node1145Labels := by rfl

def raw20247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![4, -3, -1]]
def raw20247Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20247step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![4, -3, -1]]
def raw20247step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20247step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![4, -3, -1]]
def raw20247step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20247 raw20247Labels = mixedMoment B node1142 node1142Labels := by
  calc
    mixedMoment B raw20247 raw20247Labels = mixedMoment B raw20247step0 raw20247step0Labels := by
      have hz : ∀ j, raw20247 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20247step0 = (fun i j => raw20247 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20247step0 raw20247; decide +kernel
      have hl : raw20247step0Labels = raw20247Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20247 raw20247Labels permutation434 hz
    mixedMoment B raw20247step0 raw20247step0Labels = mixedMoment B raw20247step1 raw20247step1Labels := by
      have hz : ∀ j, raw20247step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20247step1 = (fun i j => raw20247step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20247step1 raw20247step0; decide +kernel
      have hl : raw20247step1Labels = raw20247step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20247step0 raw20247step0Labels permutation80 hz
    _ = mixedMoment B node1142 node1142Labels := by rfl

def raw20248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw20248Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw20248step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20248step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw20248step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20248 raw20248Labels = mixedMoment B node636 node636Labels := by
  calc
    mixedMoment B raw20248 raw20248Labels = mixedMoment B raw20248step0 raw20248step0Labels := by
      have hz : ∀ j, raw20248 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20248step0 = (fun i j => raw20248 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20248step0 raw20248; decide +kernel
      have hl : raw20248step0Labels = raw20248Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20248 raw20248Labels permutation434 hz
    mixedMoment B raw20248step0 raw20248step0Labels = mixedMoment B raw20248step1 raw20248step1Labels := by
      have hz : ∀ j, raw20248step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20248step1 = (fun i j => raw20248step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20248step1 raw20248step0; decide +kernel
      have hl : raw20248step1Labels = raw20248step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20248step0 raw20248step0Labels permutation80 hz
    _ = mixedMoment B node636 node636Labels := by rfl

def raw20249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2], ![3, -2, -1]]
def raw20249Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20249step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw20249step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20249step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw20249step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20249 raw20249Labels = mixedMoment B node1155 node1155Labels := by
  calc
    mixedMoment B raw20249 raw20249Labels = mixedMoment B raw20249step0 raw20249step0Labels := by
      have hz : ∀ j, raw20249 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20249step0 = (fun i j => raw20249 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20249step0 raw20249; decide +kernel
      have hl : raw20249step0Labels = raw20249Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20249 raw20249Labels permutation434 hz
    mixedMoment B raw20249step0 raw20249step0Labels = mixedMoment B raw20249step1 raw20249step1Labels := by
      have ha : raw20249step1 = (fun i j => raw20249step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20249step1 raw20249step0; decide +kernel
      have hl : raw20249step1Labels = raw20249step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20249step0 raw20249step0Labels permutation38 permutation2
    _ = mixedMoment B node1155 node1155Labels := by rfl

def raw20250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw20250Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw20250step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20250step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -2, -1]]
def raw20250step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20250 raw20250Labels = mixedMoment B node1155 node1155Labels := by
  calc
    mixedMoment B raw20250 raw20250Labels = mixedMoment B raw20250step0 raw20250step0Labels := by
      have hz : ∀ j, raw20250 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20250step0 = (fun i j => raw20250 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20250step0 raw20250; decide +kernel
      have hl : raw20250step0Labels = raw20250Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20250 raw20250Labels permutation346 hz
    mixedMoment B raw20250step0 raw20250step0Labels = mixedMoment B raw20250step1 raw20250step1Labels := by
      have ha : raw20250step1 = (fun i j => raw20250step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20250step1 raw20250step0; decide +kernel
      have hl : raw20250step1Labels = raw20250step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20250step0 raw20250step0Labels permutation38 permutation2
    _ = mixedMoment B node1155 node1155Labels := by rfl

def raw20251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw20251Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2], ![2, -1, -1]]
def raw20251step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20251step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, 0, -2], ![2, -1, -1]]
def raw20251step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20251step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw20251step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20251 raw20251Labels = mixedMoment B node1246 node1246Labels := by
  calc
    mixedMoment B raw20251 raw20251Labels = mixedMoment B raw20251step0 raw20251step0Labels := by
      have hz : ∀ j, raw20251 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20251step0 = (fun i j => raw20251 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20251step0 raw20251; decide +kernel
      have hl : raw20251step0Labels = raw20251Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20251 raw20251Labels permutation434 hz
    mixedMoment B raw20251step0 raw20251step0Labels = mixedMoment B raw20251step1 raw20251step1Labels := by
      have hz : ∀ j, raw20251step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20251step1 = (fun i j => raw20251step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20251step1 raw20251step0; decide +kernel
      have hl : raw20251step1Labels = raw20251step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20251step0 raw20251step0Labels permutation80 hz
    mixedMoment B raw20251step1 raw20251step1Labels = mixedMoment B raw20251step2 raw20251step2Labels := by
      have ha : raw20251step2 = (fun i j => raw20251step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20251step2 raw20251step1; decide +kernel
      have hl : raw20251step2Labels = raw20251step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20251step1 raw20251step1Labels permutation9 permutation2
    _ = mixedMoment B node1246 node1246Labels := by rfl

def raw20252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw20252Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw20252step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20252step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw20252step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20252step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20252step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20252 raw20252Labels = mixedMoment B node641 node641Labels := by
  calc
    mixedMoment B raw20252 raw20252Labels = mixedMoment B raw20252step0 raw20252step0Labels := by
      have hz : ∀ j, raw20252 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20252step0 = (fun i j => raw20252 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20252step0 raw20252; decide +kernel
      have hl : raw20252step0Labels = raw20252Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20252 raw20252Labels permutation434 hz
    mixedMoment B raw20252step0 raw20252step0Labels = mixedMoment B raw20252step1 raw20252step1Labels := by
      have hz : ∀ j, raw20252step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20252step1 = (fun i j => raw20252step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20252step1 raw20252step0; decide +kernel
      have hl : raw20252step1Labels = raw20252step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20252step0 raw20252step0Labels permutation80 hz
    mixedMoment B raw20252step1 raw20252step1Labels = mixedMoment B raw20252step2 raw20252step2Labels := by
      have ha : raw20252step2 = (fun i j => raw20252step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20252step2 raw20252step1; decide +kernel
      have hl : raw20252step2Labels = raw20252step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20252step1 raw20252step1Labels permutation10 permutation2
    _ = mixedMoment B node641 node641Labels := by rfl

def raw20253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw20253Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw20253step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20253step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20253step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20253 raw20253Labels = mixedMoment B node1159 node1159Labels := by
  calc
    mixedMoment B raw20253 raw20253Labels = mixedMoment B raw20253step0 raw20253step0Labels := by
      have hz : ∀ j, raw20253 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20253step0 = (fun i j => raw20253 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20253step0 raw20253; decide +kernel
      have hl : raw20253step0Labels = raw20253Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20253 raw20253Labels permutation434 hz
    mixedMoment B raw20253step0 raw20253step0Labels = mixedMoment B raw20253step1 raw20253step1Labels := by
      have ha : raw20253step1 = (fun i j => raw20253step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20253step1 raw20253step0; decide +kernel
      have hl : raw20253step1Labels = raw20253step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20253step0 raw20253step0Labels permutation40 permutation2
    _ = mixedMoment B node1159 node1159Labels := by rfl

def raw20254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw20254Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20254step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw20254step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20254step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20254step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20254 raw20254Labels = mixedMoment B node1159 node1159Labels := by
  calc
    mixedMoment B raw20254 raw20254Labels = mixedMoment B raw20254step0 raw20254step0Labels := by
      have hz : ∀ j, raw20254 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20254step0 = (fun i j => raw20254 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20254step0 raw20254; decide +kernel
      have hl : raw20254step0Labels = raw20254Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20254 raw20254Labels permutation346 hz
    mixedMoment B raw20254step0 raw20254step0Labels = mixedMoment B raw20254step1 raw20254step1Labels := by
      have ha : raw20254step1 = (fun i j => raw20254step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20254step1 raw20254step0; decide +kernel
      have hl : raw20254step1Labels = raw20254step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20254step0 raw20254step0Labels permutation40 permutation2
    _ = mixedMoment B node1159 node1159Labels := by rfl

def raw20255 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20255Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20255step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20255step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20255step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20255step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw20255step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20255step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw20255step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20255 raw20255Labels = mixedMoment B node3302 node3302Labels := by
  calc
    mixedMoment B raw20255 raw20255Labels = mixedMoment B raw20255step0 raw20255step0Labels := by
      have hz : ∀ j, raw20255 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20255step0 = (fun i j => raw20255 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20255step0 raw20255; decide +kernel
      have hl : raw20255step0Labels = raw20255Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20255 raw20255Labels permutation434 hz
    mixedMoment B raw20255step0 raw20255step0Labels = mixedMoment B raw20255step1 raw20255step1Labels := by
      have hz : ∀ j, raw20255step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20255step1 = (fun i j => raw20255step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20255step1 raw20255step0; decide +kernel
      have hl : raw20255step1Labels = raw20255step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20255step0 raw20255step0Labels permutation80 hz
    mixedMoment B raw20255step1 raw20255step1Labels = mixedMoment B raw20255step2 raw20255step2Labels := by
      have ha : raw20255step2 = (fun i j => raw20255step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20255step2 raw20255step1; decide +kernel
      have hl : raw20255step2Labels = raw20255step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20255step1 raw20255step1Labels permutation9 permutation4
    mixedMoment B raw20255step2 raw20255step2Labels = mixedMoment B raw20255step3 raw20255step3Labels := by
      have ha : raw20255step3 = -raw20255step2 := by apply Matrix.ext; change ∀ i j, raw20255step3 i j = -(raw20255step2 i j); unfold raw20255step3 raw20255step2; decide +kernel
      have hl : raw20255step3Labels = raw20255step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3302 node3302Labels := by rfl

def raw20256 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20256Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20256step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20256step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20256step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20256step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw20256step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20256step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![2, -2, 0], ![2, 1, -3]]
def raw20256step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20256 raw20256Labels = mixedMoment B node1652 node1652Labels := by
  calc
    mixedMoment B raw20256 raw20256Labels = mixedMoment B raw20256step0 raw20256step0Labels := by
      have hz : ∀ j, raw20256 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20256step0 = (fun i j => raw20256 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20256step0 raw20256; decide +kernel
      have hl : raw20256step0Labels = raw20256Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20256 raw20256Labels permutation434 hz
    mixedMoment B raw20256step0 raw20256step0Labels = mixedMoment B raw20256step1 raw20256step1Labels := by
      have hz : ∀ j, raw20256step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20256step1 = (fun i j => raw20256step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20256step1 raw20256step0; decide +kernel
      have hl : raw20256step1Labels = raw20256step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20256step0 raw20256step0Labels permutation80 hz
    mixedMoment B raw20256step1 raw20256step1Labels = mixedMoment B raw20256step2 raw20256step2Labels := by
      have ha : raw20256step2 = (fun i j => raw20256step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20256step2 raw20256step1; decide +kernel
      have hl : raw20256step2Labels = raw20256step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20256step1 raw20256step1Labels permutation10 permutation2
    mixedMoment B raw20256step2 raw20256step2Labels = mixedMoment B raw20256step3 raw20256step3Labels := by
      have ha : raw20256step3 = -raw20256step2 := by apply Matrix.ext; change ∀ i j, raw20256step3 i j = -(raw20256step2 i j); unfold raw20256step3 raw20256step2; decide +kernel
      have hl : raw20256step3Labels = raw20256step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1652 node1652Labels := by rfl

def raw20257 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20257Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20257step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20257step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20257step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw20257step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20257step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw20257step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20257 raw20257Labels = mixedMoment B node1643 node1643Labels := by
  calc
    mixedMoment B raw20257 raw20257Labels = mixedMoment B raw20257step0 raw20257step0Labels := by
      have hz : ∀ j, raw20257 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20257step0 = (fun i j => raw20257 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20257step0 raw20257; decide +kernel
      have hl : raw20257step0Labels = raw20257Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20257 raw20257Labels permutation434 hz
    mixedMoment B raw20257step0 raw20257step0Labels = mixedMoment B raw20257step1 raw20257step1Labels := by
      have ha : raw20257step1 = (fun i j => raw20257step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20257step1 raw20257step0; decide +kernel
      have hl : raw20257step1Labels = raw20257step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20257step0 raw20257step0Labels permutation44 permutation2
    mixedMoment B raw20257step1 raw20257step1Labels = mixedMoment B raw20257step2 raw20257step2Labels := by
      have ha : raw20257step2 = -raw20257step1 := by apply Matrix.ext; change ∀ i j, raw20257step2 i j = -(raw20257step1 i j); unfold raw20257step2 raw20257step1; decide +kernel
      have hl : raw20257step2Labels = raw20257step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1643 node1643Labels := by rfl

def raw20258 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20258Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20258step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20258step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw20258step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20258step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw20258step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20258 raw20258Labels = mixedMoment B node1643 node1643Labels := by
  calc
    mixedMoment B raw20258 raw20258Labels = mixedMoment B raw20258step0 raw20258step0Labels := by
      have hz : ∀ j, raw20258 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20258step0 = (fun i j => raw20258 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20258step0 raw20258; decide +kernel
      have hl : raw20258step0Labels = raw20258Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20258 raw20258Labels permutation346 hz
    mixedMoment B raw20258step0 raw20258step0Labels = mixedMoment B raw20258step1 raw20258step1Labels := by
      have ha : raw20258step1 = (fun i j => raw20258step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20258step1 raw20258step0; decide +kernel
      have hl : raw20258step1Labels = raw20258step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20258step0 raw20258step0Labels permutation44 permutation2
    mixedMoment B raw20258step1 raw20258step1Labels = mixedMoment B raw20258step2 raw20258step2Labels := by
      have ha : raw20258step2 = -raw20258step1 := by apply Matrix.ext; change ∀ i j, raw20258step2 i j = -(raw20258step1 i j); unfold raw20258step2 raw20258step1; decide +kernel
      have hl : raw20258step2Labels = raw20258step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1643 node1643Labels := by rfl

def raw20259 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20259Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20259step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20259step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20259step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20259step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20259step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw20259step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20259step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw20259step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20259 raw20259Labels = mixedMoment B node1725 node1725Labels := by
  calc
    mixedMoment B raw20259 raw20259Labels = mixedMoment B raw20259step0 raw20259step0Labels := by
      have hz : ∀ j, raw20259 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20259step0 = (fun i j => raw20259 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20259step0 raw20259; decide +kernel
      have hl : raw20259step0Labels = raw20259Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20259 raw20259Labels permutation434 hz
    mixedMoment B raw20259step0 raw20259step0Labels = mixedMoment B raw20259step1 raw20259step1Labels := by
      have hz : ∀ j, raw20259step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20259step1 = (fun i j => raw20259step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20259step1 raw20259step0; decide +kernel
      have hl : raw20259step1Labels = raw20259step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20259step0 raw20259step0Labels permutation80 hz
    mixedMoment B raw20259step1 raw20259step1Labels = mixedMoment B raw20259step2 raw20259step2Labels := by
      have ha : raw20259step2 = (fun i j => raw20259step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20259step2 raw20259step1; decide +kernel
      have hl : raw20259step2Labels = raw20259step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20259step1 raw20259step1Labels permutation10 permutation2
    mixedMoment B raw20259step2 raw20259step2Labels = mixedMoment B raw20259step3 raw20259step3Labels := by
      have ha : raw20259step3 = -raw20259step2 := by apply Matrix.ext; change ∀ i j, raw20259step3 i j = -(raw20259step2 i j); unfold raw20259step3 raw20259step2; decide +kernel
      have hl : raw20259step3Labels = raw20259step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1725 node1725Labels := by rfl

def raw20260 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw20260Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw20260step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20260step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw20260step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20260step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw20260step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20260step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![3, 0, -3]]
def raw20260step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20260 raw20260Labels = mixedMoment B node1647 node1647Labels := by
  calc
    mixedMoment B raw20260 raw20260Labels = mixedMoment B raw20260step0 raw20260step0Labels := by
      have hz : ∀ j, raw20260 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20260step0 = (fun i j => raw20260 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20260step0 raw20260; decide +kernel
      have hl : raw20260step0Labels = raw20260Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20260 raw20260Labels permutation434 hz
    mixedMoment B raw20260step0 raw20260step0Labels = mixedMoment B raw20260step1 raw20260step1Labels := by
      have hz : ∀ j, raw20260step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20260step1 = (fun i j => raw20260step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20260step1 raw20260step0; decide +kernel
      have hl : raw20260step1Labels = raw20260step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20260step0 raw20260step0Labels permutation80 hz
    mixedMoment B raw20260step1 raw20260step1Labels = mixedMoment B raw20260step2 raw20260step2Labels := by
      have ha : raw20260step2 = (fun i j => raw20260step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20260step2 raw20260step1; decide +kernel
      have hl : raw20260step2Labels = raw20260step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20260step1 raw20260step1Labels permutation10 permutation2
    mixedMoment B raw20260step2 raw20260step2Labels = mixedMoment B raw20260step3 raw20260step3Labels := by
      have ha : raw20260step3 = -raw20260step2 := by apply Matrix.ext; change ∀ i j, raw20260step3 i j = -(raw20260step2 i j); unfold raw20260step3 raw20260step2; decide +kernel
      have hl : raw20260step3Labels = raw20260step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1647 node1647Labels := by rfl

def raw20261 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20261Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20261step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20261step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw20261step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20261step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw20261step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20261 raw20261Labels = mixedMoment B node1619 node1619Labels := by
  calc
    mixedMoment B raw20261 raw20261Labels = mixedMoment B raw20261step0 raw20261step0Labels := by
      have hz : ∀ j, raw20261 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20261step0 = (fun i j => raw20261 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20261step0 raw20261; decide +kernel
      have hl : raw20261step0Labels = raw20261Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20261 raw20261Labels permutation434 hz
    mixedMoment B raw20261step0 raw20261step0Labels = mixedMoment B raw20261step1 raw20261step1Labels := by
      have ha : raw20261step1 = (fun i j => raw20261step0 (permutation33 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20261step1 raw20261step0; decide +kernel
      have hl : raw20261step1Labels = raw20261step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20261step0 raw20261step0Labels permutation33 permutation4
    mixedMoment B raw20261step1 raw20261step1Labels = mixedMoment B raw20261step2 raw20261step2Labels := by
      have ha : raw20261step2 = -raw20261step1 := by apply Matrix.ext; change ∀ i j, raw20261step2 i j = -(raw20261step1 i j); unfold raw20261step2 raw20261step1; decide +kernel
      have hl : raw20261step2Labels = raw20261step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1619 node1619Labels := by rfl

def raw20262 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20262Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20262step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20262step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20262step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20262step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20262step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw20262step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20262step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw20262step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20262 raw20262Labels = mixedMoment B node1630 node1630Labels := by
  calc
    mixedMoment B raw20262 raw20262Labels = mixedMoment B raw20262step0 raw20262step0Labels := by
      have hz : ∀ j, raw20262 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20262step0 = (fun i j => raw20262 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20262step0 raw20262; decide +kernel
      have hl : raw20262step0Labels = raw20262Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20262 raw20262Labels permutation434 hz
    mixedMoment B raw20262step0 raw20262step0Labels = mixedMoment B raw20262step1 raw20262step1Labels := by
      have hz : ∀ j, raw20262step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20262step1 = (fun i j => raw20262step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20262step1 raw20262step0; decide +kernel
      have hl : raw20262step1Labels = raw20262step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20262step0 raw20262step0Labels permutation80 hz
    mixedMoment B raw20262step1 raw20262step1Labels = mixedMoment B raw20262step2 raw20262step2Labels := by
      have ha : raw20262step2 = (fun i j => raw20262step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20262step2 raw20262step1; decide +kernel
      have hl : raw20262step2Labels = raw20262step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20262step1 raw20262step1Labels permutation8 permutation4
    mixedMoment B raw20262step2 raw20262step2Labels = mixedMoment B raw20262step3 raw20262step3Labels := by
      have ha : raw20262step3 = -raw20262step2 := by apply Matrix.ext; change ∀ i j, raw20262step3 i j = -(raw20262step2 i j); unfold raw20262step3 raw20262step2; decide +kernel
      have hl : raw20262step3Labels = raw20262step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1630 node1630Labels := by rfl

def raw20263 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20263Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20263step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20263step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20263step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20263step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw20263step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20263step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw20263step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20263 raw20263Labels = mixedMoment B node3302 node3302Labels := by
  calc
    mixedMoment B raw20263 raw20263Labels = mixedMoment B raw20263step0 raw20263step0Labels := by
      have hz : ∀ j, raw20263 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20263step0 = (fun i j => raw20263 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20263step0 raw20263; decide +kernel
      have hl : raw20263step0Labels = raw20263Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20263 raw20263Labels permutation434 hz
    mixedMoment B raw20263step0 raw20263step0Labels = mixedMoment B raw20263step1 raw20263step1Labels := by
      have hz : ∀ j, raw20263step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20263step1 = (fun i j => raw20263step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20263step1 raw20263step0; decide +kernel
      have hl : raw20263step1Labels = raw20263step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20263step0 raw20263step0Labels permutation56 hz
    mixedMoment B raw20263step1 raw20263step1Labels = mixedMoment B raw20263step2 raw20263step2Labels := by
      have ha : raw20263step2 = (fun i j => raw20263step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20263step2 raw20263step1; decide +kernel
      have hl : raw20263step2Labels = raw20263step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20263step1 raw20263step1Labels permutation9 permutation4
    mixedMoment B raw20263step2 raw20263step2Labels = mixedMoment B raw20263step3 raw20263step3Labels := by
      have ha : raw20263step3 = -raw20263step2 := by apply Matrix.ext; change ∀ i j, raw20263step3 i j = -(raw20263step2 i j); unfold raw20263step3 raw20263step2; decide +kernel
      have hl : raw20263step3Labels = raw20263step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3302 node3302Labels := by rfl

def raw20264 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20264Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20264step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20264step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20264step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -2, 1], ![-2, -1, 3]]
def raw20264step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20264step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw20264step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20264step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw20264step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20264 raw20264Labels = mixedMoment B node3302 node3302Labels := by
  calc
    mixedMoment B raw20264 raw20264Labels = mixedMoment B raw20264step0 raw20264step0Labels := by
      have hz : ∀ j, raw20264 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20264step0 = (fun i j => raw20264 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20264step0 raw20264; decide +kernel
      have hl : raw20264step0Labels = raw20264Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20264 raw20264Labels permutation346 hz
    mixedMoment B raw20264step0 raw20264step0Labels = mixedMoment B raw20264step1 raw20264step1Labels := by
      have hz : ∀ j, raw20264step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20264step1 = (fun i j => raw20264step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20264step1 raw20264step0; decide +kernel
      have hl : raw20264step1Labels = raw20264step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20264step0 raw20264step0Labels permutation56 hz
    mixedMoment B raw20264step1 raw20264step1Labels = mixedMoment B raw20264step2 raw20264step2Labels := by
      have ha : raw20264step2 = (fun i j => raw20264step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20264step2 raw20264step1; decide +kernel
      have hl : raw20264step2Labels = raw20264step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20264step1 raw20264step1Labels permutation9 permutation4
    mixedMoment B raw20264step2 raw20264step2Labels = mixedMoment B raw20264step3 raw20264step3Labels := by
      have ha : raw20264step3 = -raw20264step2 := by apply Matrix.ext; change ∀ i j, raw20264step3 i j = -(raw20264step2 i j); unfold raw20264step3 raw20264step2; decide +kernel
      have hl : raw20264step3Labels = raw20264step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3302 node3302Labels := by rfl

def raw20265 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20265Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20265step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20265step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20265step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20265step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20265step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![-2, -1, 3]]
def raw20265step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20265step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![2, 1, -3]]
def raw20265step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20265 raw20265Labels = mixedMoment B node3310 node3310Labels := by
  calc
    mixedMoment B raw20265 raw20265Labels = mixedMoment B raw20265step0 raw20265step0Labels := by
      have hz : ∀ j, raw20265 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20265step0 = (fun i j => raw20265 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20265step0 raw20265; decide +kernel
      have hl : raw20265step0Labels = raw20265Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20265 raw20265Labels permutation434 hz
    mixedMoment B raw20265step0 raw20265step0Labels = mixedMoment B raw20265step1 raw20265step1Labels := by
      have hz : ∀ j, raw20265step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20265step1 = (fun i j => raw20265step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20265step1 raw20265step0; decide +kernel
      have hl : raw20265step1Labels = raw20265step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20265step0 raw20265step0Labels permutation80 hz
    mixedMoment B raw20265step1 raw20265step1Labels = mixedMoment B raw20265step2 raw20265step2Labels := by
      have hz : ∀ j, raw20265step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20265step2 = (fun i j => raw20265step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20265step2 raw20265step1; decide +kernel
      have hl : raw20265step2Labels = raw20265step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20265step1 raw20265step1Labels permutation14 hz
    mixedMoment B raw20265step2 raw20265step2Labels = mixedMoment B raw20265step3 raw20265step3Labels := by
      have ha : raw20265step3 = -raw20265step2 := by apply Matrix.ext; change ∀ i j, raw20265step3 i j = -(raw20265step2 i j); unfold raw20265step3 raw20265step2; decide +kernel
      have hl : raw20265step3Labels = raw20265step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3310 node3310Labels := by rfl

def raw20266 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20266Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20266step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20266step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20266step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw20266step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20266step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw20266step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20266 raw20266Labels = mixedMoment B node3291 node3291Labels := by
  calc
    mixedMoment B raw20266 raw20266Labels = mixedMoment B raw20266step0 raw20266step0Labels := by
      have hz : ∀ j, raw20266 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20266step0 = (fun i j => raw20266 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20266step0 raw20266; decide +kernel
      have hl : raw20266step0Labels = raw20266Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20266 raw20266Labels permutation434 hz
    mixedMoment B raw20266step0 raw20266step0Labels = mixedMoment B raw20266step1 raw20266step1Labels := by
      have ha : raw20266step1 = (fun i j => raw20266step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20266step1 raw20266step0; decide +kernel
      have hl : raw20266step1Labels = raw20266step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20266step0 raw20266step0Labels permutation40 permutation2
    mixedMoment B raw20266step1 raw20266step1Labels = mixedMoment B raw20266step2 raw20266step2Labels := by
      have ha : raw20266step2 = -raw20266step1 := by apply Matrix.ext; change ∀ i j, raw20266step2 i j = -(raw20266step1 i j); unfold raw20266step2 raw20266step1; decide +kernel
      have hl : raw20266step2Labels = raw20266step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3291 node3291Labels := by rfl

def raw20267 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20267Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20267step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20267step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw20267step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20267step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw20267step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20267 raw20267Labels = mixedMoment B node3291 node3291Labels := by
  calc
    mixedMoment B raw20267 raw20267Labels = mixedMoment B raw20267step0 raw20267step0Labels := by
      have hz : ∀ j, raw20267 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20267step0 = (fun i j => raw20267 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20267step0 raw20267; decide +kernel
      have hl : raw20267step0Labels = raw20267Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20267 raw20267Labels permutation346 hz
    mixedMoment B raw20267step0 raw20267step0Labels = mixedMoment B raw20267step1 raw20267step1Labels := by
      have ha : raw20267step1 = (fun i j => raw20267step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20267step1 raw20267step0; decide +kernel
      have hl : raw20267step1Labels = raw20267step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20267step0 raw20267step0Labels permutation40 permutation2
    mixedMoment B raw20267step1 raw20267step1Labels = mixedMoment B raw20267step2 raw20267step2Labels := by
      have ha : raw20267step2 = -raw20267step1 := by apply Matrix.ext; change ∀ i j, raw20267step2 i j = -(raw20267step1 i j); unfold raw20267step2 raw20267step1; decide +kernel
      have hl : raw20267step2Labels = raw20267step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3291 node3291Labels := by rfl

def raw20268 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20268Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20268step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20268step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20268step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20268step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20268step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20268step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw20268step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20268 raw20268Labels = mixedMoment B node3300 node3300Labels := by
  calc
    mixedMoment B raw20268 raw20268Labels = mixedMoment B raw20268step0 raw20268step0Labels := by
      have hz : ∀ j, raw20268 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20268step0 = (fun i j => raw20268 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20268step0 raw20268; decide +kernel
      have hl : raw20268step0Labels = raw20268Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20268 raw20268Labels permutation434 hz
    mixedMoment B raw20268step0 raw20268step0Labels = mixedMoment B raw20268step1 raw20268step1Labels := by
      have hz : ∀ j, raw20268step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20268step1 = (fun i j => raw20268step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20268step1 raw20268step0; decide +kernel
      have hl : raw20268step1Labels = raw20268step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20268step0 raw20268step0Labels permutation80 hz
    mixedMoment B raw20268step1 raw20268step1Labels = mixedMoment B raw20268step2 raw20268step2Labels := by
      have ha : raw20268step2 = (fun i j => raw20268step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20268step2 raw20268step1; decide +kernel
      have hl : raw20268step2Labels = raw20268step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20268step1 raw20268step1Labels permutation8 permutation4
    mixedMoment B raw20268step2 raw20268step2Labels = mixedMoment B raw20268step3 raw20268step3Labels := by
      have ha : raw20268step3 = -raw20268step2 := by apply Matrix.ext; change ∀ i j, raw20268step3 i j = -(raw20268step2 i j); unfold raw20268step3 raw20268step2; decide +kernel
      have hl : raw20268step3Labels = raw20268step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3300 node3300Labels := by rfl

def raw20269 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20269Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20269step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20269step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20269step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20269step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20269step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw20269step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20269step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![2, -1, -1], ![2, 1, -3]]
def raw20269step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20269 raw20269Labels = mixedMoment B node3247 node3247Labels := by
  calc
    mixedMoment B raw20269 raw20269Labels = mixedMoment B raw20269step0 raw20269step0Labels := by
      have hz : ∀ j, raw20269 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20269step0 = (fun i j => raw20269 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20269step0 raw20269; decide +kernel
      have hl : raw20269step0Labels = raw20269Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20269 raw20269Labels permutation434 hz
    mixedMoment B raw20269step0 raw20269step0Labels = mixedMoment B raw20269step1 raw20269step1Labels := by
      have hz : ∀ j, raw20269step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20269step1 = (fun i j => raw20269step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20269step1 raw20269step0; decide +kernel
      have hl : raw20269step1Labels = raw20269step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20269step0 raw20269step0Labels permutation80 hz
    mixedMoment B raw20269step1 raw20269step1Labels = mixedMoment B raw20269step2 raw20269step2Labels := by
      have ha : raw20269step2 = (fun i j => raw20269step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20269step2 raw20269step1; decide +kernel
      have hl : raw20269step2Labels = raw20269step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20269step1 raw20269step1Labels permutation8 permutation4
    mixedMoment B raw20269step2 raw20269step2Labels = mixedMoment B raw20269step3 raw20269step3Labels := by
      have ha : raw20269step3 = -raw20269step2 := by apply Matrix.ext; change ∀ i j, raw20269step3 i j = -(raw20269step2 i j); unfold raw20269step3 raw20269step2; decide +kernel
      have hl : raw20269step3Labels = raw20269step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3247 node3247Labels := by rfl

def raw20270 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20270Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20270step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20270step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20270step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw20270step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20270step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw20270step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20270 raw20270Labels = mixedMoment B node3283 node3283Labels := by
  calc
    mixedMoment B raw20270 raw20270Labels = mixedMoment B raw20270step0 raw20270step0Labels := by
      have hz : ∀ j, raw20270 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20270step0 = (fun i j => raw20270 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20270step0 raw20270; decide +kernel
      have hl : raw20270step0Labels = raw20270Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20270 raw20270Labels permutation434 hz
    mixedMoment B raw20270step0 raw20270step0Labels = mixedMoment B raw20270step1 raw20270step1Labels := by
      have ha : raw20270step1 = (fun i j => raw20270step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20270step1 raw20270step0; decide +kernel
      have hl : raw20270step1Labels = raw20270step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20270step0 raw20270step0Labels permutation32 permutation4
    mixedMoment B raw20270step1 raw20270step1Labels = mixedMoment B raw20270step2 raw20270step2Labels := by
      have ha : raw20270step2 = -raw20270step1 := by apply Matrix.ext; change ∀ i j, raw20270step2 i j = -(raw20270step1 i j); unfold raw20270step2 raw20270step1; decide +kernel
      have hl : raw20270step2Labels = raw20270step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3283 node3283Labels := by rfl

def raw20271 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20271Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20271step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw20271step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20271step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw20271step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20271step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw20271step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20271 raw20271Labels = mixedMoment B node3283 node3283Labels := by
  calc
    mixedMoment B raw20271 raw20271Labels = mixedMoment B raw20271step0 raw20271step0Labels := by
      have hz : ∀ j, raw20271 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20271step0 = (fun i j => raw20271 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20271step0 raw20271; decide +kernel
      have hl : raw20271step0Labels = raw20271Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20271 raw20271Labels permutation346 hz
    mixedMoment B raw20271step0 raw20271step0Labels = mixedMoment B raw20271step1 raw20271step1Labels := by
      have ha : raw20271step1 = (fun i j => raw20271step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20271step1 raw20271step0; decide +kernel
      have hl : raw20271step1Labels = raw20271step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20271step0 raw20271step0Labels permutation32 permutation4
    mixedMoment B raw20271step1 raw20271step1Labels = mixedMoment B raw20271step2 raw20271step2Labels := by
      have ha : raw20271step2 = -raw20271step1 := by apply Matrix.ext; change ∀ i j, raw20271step2 i j = -(raw20271step1 i j); unfold raw20271step2 raw20271step1; decide +kernel
      have hl : raw20271step2Labels = raw20271step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3283 node3283Labels := by rfl

def raw20272 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw20272Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![-3, 0, 3]]
def raw20272step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20272step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def raw20272step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20272 raw20272Labels = mixedMoment B node2045 node2045Labels := by
  calc
    mixedMoment B raw20272 raw20272Labels = mixedMoment B raw20272step0 raw20272step0Labels := by
      have hz : ∀ j, raw20272 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20272step0 = (fun i j => raw20272 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20272step0 raw20272; decide +kernel
      have hl : raw20272step0Labels = raw20272Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20272 raw20272Labels permutation434 hz
    mixedMoment B raw20272step0 raw20272step0Labels = mixedMoment B raw20272step1 raw20272step1Labels := by
      have ha : raw20272step1 = (fun i j => raw20272step0 (permutation139 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20272step1 raw20272step0; decide +kernel
      have hl : raw20272step1Labels = raw20272step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20272step0 raw20272step0Labels permutation139 permutation2
    _ = mixedMoment B node2045 node2045Labels := by rfl

def raw20273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw20273Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw20273step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20273step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -3, 2], ![3, 0, -3]]
def raw20273step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20273step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 2, -1], ![-3, 1, 2]]
def raw20273step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20273step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -2, 1], ![3, -1, -2]]
def raw20273step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20273 raw20273Labels = mixedMoment B node2130 node2130Labels := by
  calc
    mixedMoment B raw20273 raw20273Labels = mixedMoment B raw20273step0 raw20273step0Labels := by
      have hz : ∀ j, raw20273 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20273step0 = (fun i j => raw20273 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20273step0 raw20273; decide +kernel
      have hl : raw20273step0Labels = raw20273Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20273 raw20273Labels permutation434 hz
    mixedMoment B raw20273step0 raw20273step0Labels = mixedMoment B raw20273step1 raw20273step1Labels := by
      have hz : ∀ j, raw20273step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20273step1 = (fun i j => raw20273step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20273step1 raw20273step0; decide +kernel
      have hl : raw20273step1Labels = raw20273step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20273step0 raw20273step0Labels permutation80 hz
    mixedMoment B raw20273step1 raw20273step1Labels = mixedMoment B raw20273step2 raw20273step2Labels := by
      have ha : raw20273step2 = (fun i j => raw20273step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20273step2 raw20273step1; decide +kernel
      have hl : raw20273step2Labels = raw20273step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20273step1 raw20273step1Labels permutation31 permutation2
    mixedMoment B raw20273step2 raw20273step2Labels = mixedMoment B raw20273step3 raw20273step3Labels := by
      have ha : raw20273step3 = -raw20273step2 := by apply Matrix.ext; change ∀ i j, raw20273step3 i j = -(raw20273step2 i j); unfold raw20273step3 raw20273step2; decide +kernel
      have hl : raw20273step3Labels = raw20273step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2130 node2130Labels := by rfl

def raw20274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![3, 0, -3]]
def raw20274Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20274step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw20274step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20274step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![0, 1, -1], ![-1, 1, 0], ![-3, 1, 2]]
def raw20274step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20274step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw20274step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20274 raw20274Labels = mixedMoment B node2119 node2119Labels := by
  calc
    mixedMoment B raw20274 raw20274Labels = mixedMoment B raw20274step0 raw20274step0Labels := by
      have hz : ∀ j, raw20274 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20274step0 = (fun i j => raw20274 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20274step0 raw20274; decide +kernel
      have hl : raw20274step0Labels = raw20274Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20274 raw20274Labels permutation434 hz
    mixedMoment B raw20274step0 raw20274step0Labels = mixedMoment B raw20274step1 raw20274step1Labels := by
      have ha : raw20274step1 = (fun i j => raw20274step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20274step1 raw20274step0; decide +kernel
      have hl : raw20274step1Labels = raw20274step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20274step0 raw20274step0Labels permutation149 permutation2
    mixedMoment B raw20274step1 raw20274step1Labels = mixedMoment B raw20274step2 raw20274step2Labels := by
      have ha : raw20274step2 = -raw20274step1 := by apply Matrix.ext; change ∀ i j, raw20274step2 i j = -(raw20274step1 i j); unfold raw20274step2 raw20274step1; decide +kernel
      have hl : raw20274step2Labels = raw20274step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2119 node2119Labels := by rfl

def raw20275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw20275Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20275step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -3, 2], ![3, 0, -3]]
def raw20275step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20275step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![0, 1, -1], ![-1, 1, 0], ![-3, 1, 2]]
def raw20275step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20275step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw20275step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20275 raw20275Labels = mixedMoment B node2119 node2119Labels := by
  calc
    mixedMoment B raw20275 raw20275Labels = mixedMoment B raw20275step0 raw20275step0Labels := by
      have hz : ∀ j, raw20275 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20275step0 = (fun i j => raw20275 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20275step0 raw20275; decide +kernel
      have hl : raw20275step0Labels = raw20275Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20275 raw20275Labels permutation346 hz
    mixedMoment B raw20275step0 raw20275step0Labels = mixedMoment B raw20275step1 raw20275step1Labels := by
      have ha : raw20275step1 = (fun i j => raw20275step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20275step1 raw20275step0; decide +kernel
      have hl : raw20275step1Labels = raw20275step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20275step0 raw20275step0Labels permutation149 permutation2
    mixedMoment B raw20275step1 raw20275step1Labels = mixedMoment B raw20275step2 raw20275step2Labels := by
      have ha : raw20275step2 = -raw20275step1 := by apply Matrix.ext; change ∀ i j, raw20275step2 i j = -(raw20275step1 i j); unfold raw20275step2 raw20275step1; decide +kernel
      have hl : raw20275step2Labels = raw20275step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2119 node2119Labels := by rfl

def raw20276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw20276Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20276step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw20276step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20276step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw20276step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20276 raw20276Labels = mixedMoment B node2761 node2761Labels := by
  calc
    mixedMoment B raw20276 raw20276Labels = mixedMoment B raw20276step0 raw20276step0Labels := by
      have hz : ∀ j, raw20276 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20276step0 = (fun i j => raw20276 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20276step0 raw20276; decide +kernel
      have hl : raw20276step0Labels = raw20276Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20276 raw20276Labels permutation434 hz
    mixedMoment B raw20276step0 raw20276step0Labels = mixedMoment B raw20276step1 raw20276step1Labels := by
      have hz : ∀ j, raw20276step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20276step1 = (fun i j => raw20276step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20276step1 raw20276step0; decide +kernel
      have hl : raw20276step1Labels = raw20276step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20276step0 raw20276step0Labels permutation80 hz
    _ = mixedMoment B node2761 node2761Labels := by rfl

def raw20277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20277Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20277step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20277 raw20277Labels = mixedMoment B node2482 node2482Labels := by
  calc
    mixedMoment B raw20277 raw20277Labels = mixedMoment B raw20277step0 raw20277step0Labels := by
      have hz : ∀ j, raw20277 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20277step0 = (fun i j => raw20277 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20277step0 raw20277; decide +kernel
      have hl : raw20277step0Labels = raw20277Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20277 raw20277Labels permutation346 hz
    _ = mixedMoment B node2482 node2482Labels := by rfl

def raw20278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20278Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20278step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20278step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20278 raw20278Labels = mixedMoment B node1215 node1215Labels := by
  calc
    mixedMoment B raw20278 raw20278Labels = mixedMoment B raw20278step0 raw20278step0Labels := by
      have hz : ∀ j, raw20278 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20278step0 = (fun i j => raw20278 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20278step0 raw20278; decide +kernel
      have hl : raw20278step0Labels = raw20278Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20278 raw20278Labels permutation346 hz
    _ = mixedMoment B node1215 node1215Labels := by rfl

def raw20279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20279Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20279step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20279step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20279 raw20279Labels = mixedMoment B node1111 node1111Labels := by
  calc
    mixedMoment B raw20279 raw20279Labels = mixedMoment B raw20279step0 raw20279step0Labels := by
      have ha : raw20279step0 = (fun i j => raw20279 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20279step0 raw20279; decide +kernel
      have hl : raw20279step0Labels = raw20279Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20279 raw20279Labels permutation158 permutation2
    _ = mixedMoment B node1111 node1111Labels := by rfl

def raw20280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20280Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20280step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20280step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20280step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20280 raw20280Labels = mixedMoment B node1131 node1131Labels := by
  calc
    mixedMoment B raw20280 raw20280Labels = mixedMoment B raw20280step0 raw20280step0Labels := by
      have hz : ∀ j, raw20280 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20280step0 = (fun i j => raw20280 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20280step0 raw20280; decide +kernel
      have hl : raw20280step0Labels = raw20280Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20280 raw20280Labels permutation346 hz
    mixedMoment B raw20280step0 raw20280step0Labels = mixedMoment B raw20280step1 raw20280step1Labels := by
      have ha : raw20280step1 = (fun i j => raw20280step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20280step1 raw20280step0; decide +kernel
      have hl : raw20280step1Labels = raw20280step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20280step0 raw20280step0Labels permutation34 permutation2
    _ = mixedMoment B node1131 node1131Labels := by rfl

def raw20281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw20281Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20281step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw20281step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20281 raw20281Labels = mixedMoment B node1119 node1119Labels := by
  calc
    mixedMoment B raw20281 raw20281Labels = mixedMoment B raw20281step0 raw20281step0Labels := by
      have hz : ∀ j, raw20281 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20281step0 = (fun i j => raw20281 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20281step0 raw20281; decide +kernel
      have hl : raw20281step0Labels = raw20281Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20281 raw20281Labels permutation346 hz
    _ = mixedMoment B node1119 node1119Labels := by rfl

def raw20282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw20282Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -2, -2]]
def raw20282step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20282 raw20282Labels = mixedMoment B node1115 node1115Labels := by
  calc
    mixedMoment B raw20282 raw20282Labels = mixedMoment B raw20282step0 raw20282step0Labels := by
      have hz : ∀ j, raw20282 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20282step0 = (fun i j => raw20282 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20282step0 raw20282; decide +kernel
      have hl : raw20282step0Labels = raw20282Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20282 raw20282Labels permutation346 hz
    _ = mixedMoment B node1115 node1115Labels := by rfl

def raw20283 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![1, -1], ![0, 0], ![2, -2]]
def raw20283Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20283step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![0, 0], ![1, -1], ![2, -2]]
def raw20283step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20283step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw20283step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical20283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20283 raw20283Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw20283 raw20283Labels = mixedMoment B raw20283step0 raw20283step0Labels := by
      have hz : ∀ j, raw20283 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20283step0 = (fun i j => raw20283 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20283step0 raw20283; decide +kernel
      have hl : raw20283step0Labels = raw20283Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20283 raw20283Labels permutation520 hz
    mixedMoment B raw20283step0 raw20283step0Labels = mixedMoment B raw20283step1 raw20283step1Labels := by
      have hz : ∀ j, raw20283step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20283step1 = (fun i j => raw20283step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20283step1 raw20283step0; decide +kernel
      have hl : raw20283step1Labels = raw20283step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20283step0 raw20283step0Labels permutation80 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw20284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20284Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20284step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20284step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20284step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20284step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20284 raw20284Labels = mixedMoment B node626 node626Labels := by
  calc
    mixedMoment B raw20284 raw20284Labels = mixedMoment B raw20284step0 raw20284step0Labels := by
      have hz : ∀ j, raw20284 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20284step0 = (fun i j => raw20284 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20284step0 raw20284; decide +kernel
      have hl : raw20284step0Labels = raw20284Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20284 raw20284Labels permutation346 hz
    mixedMoment B raw20284step0 raw20284step0Labels = mixedMoment B raw20284step1 raw20284step1Labels := by
      have ha : raw20284step1 = (fun i j => raw20284step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20284step1 raw20284step0; decide +kernel
      have hl : raw20284step1Labels = raw20284step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20284step0 raw20284step0Labels permutation34 permutation2
    _ = mixedMoment B node626 node626Labels := by rfl

def raw20285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20285Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20285step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20285step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20285 raw20285Labels = mixedMoment B node1148 node1148Labels := by
  calc
    mixedMoment B raw20285 raw20285Labels = mixedMoment B raw20285step0 raw20285step0Labels := by
      have ha : raw20285step0 = (fun i j => raw20285 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20285step0 raw20285; decide +kernel
      have hl : raw20285step0Labels = raw20285Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20285 raw20285Labels permutation178 permutation2
    _ = mixedMoment B node1148 node1148Labels := by rfl

def raw20286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0], ![3, -1, -2]]
def raw20286Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20286step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20286step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20286step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20286step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20286 raw20286Labels = mixedMoment B node1242 node1242Labels := by
  calc
    mixedMoment B raw20286 raw20286Labels = mixedMoment B raw20286step0 raw20286step0Labels := by
      have hz : ∀ j, raw20286 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20286step0 = (fun i j => raw20286 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20286step0 raw20286; decide +kernel
      have hl : raw20286step0Labels = raw20286Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20286 raw20286Labels permutation520 hz
    mixedMoment B raw20286step0 raw20286step0Labels = mixedMoment B raw20286step1 raw20286step1Labels := by
      have hz : ∀ j, raw20286step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20286step1 = (fun i j => raw20286step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20286step1 raw20286step0; decide +kernel
      have hl : raw20286step1Labels = raw20286step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20286step0 raw20286step0Labels permutation80 hz
    _ = mixedMoment B node1242 node1242Labels := by rfl

def raw20287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw20287Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw20287step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20287step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw20287step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20287 raw20287Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw20287 raw20287Labels = mixedMoment B raw20287step0 raw20287step0Labels := by
      have hz : ∀ j, raw20287 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20287step0 = (fun i j => raw20287 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20287step0 raw20287; decide +kernel
      have hl : raw20287step0Labels = raw20287Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20287 raw20287Labels permutation346 hz
    mixedMoment B raw20287step0 raw20287step0Labels = mixedMoment B raw20287step1 raw20287step1Labels := by
      have ha : raw20287step1 = (fun i j => raw20287step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20287step1 raw20287step0; decide +kernel
      have hl : raw20287step1Labels = raw20287step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20287step0 raw20287step0Labels permutation34 permutation2
    _ = mixedMoment B node1236 node1236Labels := by rfl

def raw20288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw20288Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20288step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw20288step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20288step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20288step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20288 raw20288Labels = mixedMoment B node630 node630Labels := by
  calc
    mixedMoment B raw20288 raw20288Labels = mixedMoment B raw20288step0 raw20288step0Labels := by
      have hz : ∀ j, raw20288 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20288step0 = (fun i j => raw20288 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20288step0 raw20288; decide +kernel
      have hl : raw20288step0Labels = raw20288Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20288 raw20288Labels permutation346 hz
    mixedMoment B raw20288step0 raw20288step0Labels = mixedMoment B raw20288step1 raw20288step1Labels := by
      have ha : raw20288step1 = (fun i j => raw20288step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20288step1 raw20288step0; decide +kernel
      have hl : raw20288step1Labels = raw20288step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20288step0 raw20288step0Labels permutation38 permutation2
    _ = mixedMoment B node630 node630Labels := by rfl

def raw20289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw20289Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20289step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20289step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20289 raw20289Labels = mixedMoment B node1150 node1150Labels := by
  calc
    mixedMoment B raw20289 raw20289Labels = mixedMoment B raw20289step0 raw20289step0Labels := by
      have ha : raw20289step0 = (fun i j => raw20289 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20289step0 raw20289; decide +kernel
      have hl : raw20289step0Labels = raw20289Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20289 raw20289Labels permutation182 permutation2
    _ = mixedMoment B node1150 node1150Labels := by rfl

def raw20290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw20290Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20290step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw20290step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20290step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20290step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20290 raw20290Labels = mixedMoment B node1136 node1136Labels := by
  calc
    mixedMoment B raw20290 raw20290Labels = mixedMoment B raw20290step0 raw20290step0Labels := by
      have hz : ∀ j, raw20290 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20290step0 = (fun i j => raw20290 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20290step0 raw20290; decide +kernel
      have hl : raw20290step0Labels = raw20290Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20290 raw20290Labels permutation346 hz
    mixedMoment B raw20290step0 raw20290step0Labels = mixedMoment B raw20290step1 raw20290step1Labels := by
      have ha : raw20290step1 = (fun i j => raw20290step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20290step1 raw20290step0; decide +kernel
      have hl : raw20290step1Labels = raw20290step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20290step0 raw20290step0Labels permutation38 permutation2
    _ = mixedMoment B node1136 node1136Labels := by rfl

def raw20291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw20291Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20291step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw20291step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20291step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20291step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20291 raw20291Labels = mixedMoment B node1217 node1217Labels := by
  calc
    mixedMoment B raw20291 raw20291Labels = mixedMoment B raw20291step0 raw20291step0Labels := by
      have hz : ∀ j, raw20291 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20291step0 = (fun i j => raw20291 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20291step0 raw20291; decide +kernel
      have hl : raw20291step0Labels = raw20291Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20291 raw20291Labels permutation346 hz
    mixedMoment B raw20291step0 raw20291step0Labels = mixedMoment B raw20291step1 raw20291step1Labels := by
      have ha : raw20291step1 = (fun i j => raw20291step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20291step1 raw20291step0; decide +kernel
      have hl : raw20291step1Labels = raw20291step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20291step0 raw20291step0Labels permutation40 permutation2
    _ = mixedMoment B node1217 node1217Labels := by rfl

def raw20292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw20292Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20292step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20292step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20292 raw20292Labels = mixedMoment B node1112 node1112Labels := by
  calc
    mixedMoment B raw20292 raw20292Labels = mixedMoment B raw20292step0 raw20292step0Labels := by
      have ha : raw20292step0 = (fun i j => raw20292 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20292step0 raw20292; decide +kernel
      have hl : raw20292step0Labels = raw20292Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20292 raw20292Labels permutation200 permutation2
    _ = mixedMoment B node1112 node1112Labels := by rfl

def raw20293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, -2, -1]]
def raw20293Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![-1, 0, 1], ![2, -1, -1], ![3, -2, -1]]
def raw20293step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20293step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw20293step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20293 raw20293Labels = mixedMoment B node1120 node1120Labels := by
  calc
    mixedMoment B raw20293 raw20293Labels = mixedMoment B raw20293step0 raw20293step0Labels := by
      have hz : ∀ j, raw20293 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20293step0 = (fun i j => raw20293 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20293step0 raw20293; decide +kernel
      have hl : raw20293step0Labels = raw20293Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20293 raw20293Labels permutation346 hz
    mixedMoment B raw20293step0 raw20293step0Labels = mixedMoment B raw20293step1 raw20293step1Labels := by
      have ha : raw20293step1 = (fun i j => raw20293step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20293step1 raw20293step0; decide +kernel
      have hl : raw20293step1Labels = raw20293step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20293step0 raw20293step0Labels permutation38 permutation2
    _ = mixedMoment B node1120 node1120Labels := by rfl

def raw20294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -3, -1]]
def raw20294Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![-1, 0, 1], ![1, 0, -1], ![4, -3, -1]]
def raw20294step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20294step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![4, -3, -1]]
def raw20294step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20294 raw20294Labels = mixedMoment B node1118 node1118Labels := by
  calc
    mixedMoment B raw20294 raw20294Labels = mixedMoment B raw20294step0 raw20294step0Labels := by
      have hz : ∀ j, raw20294 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20294step0 = (fun i j => raw20294 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20294step0 raw20294; decide +kernel
      have hl : raw20294step0Labels = raw20294Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20294 raw20294Labels permutation346 hz
    mixedMoment B raw20294step0 raw20294step0Labels = mixedMoment B raw20294step1 raw20294step1Labels := by
      have ha : raw20294step1 = (fun i j => raw20294step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20294step1 raw20294step0; decide +kernel
      have hl : raw20294step1Labels = raw20294step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20294step0 raw20294step0Labels permutation38 permutation2
    _ = mixedMoment B node1118 node1118Labels := by rfl

def raw20295 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20295Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20295step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20295step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20295step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw20295step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20295step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw20295step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20295 raw20295Labels = mixedMoment B node3291 node3291Labels := by
  calc
    mixedMoment B raw20295 raw20295Labels = mixedMoment B raw20295step0 raw20295step0Labels := by
      have hz : ∀ j, raw20295 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20295step0 = (fun i j => raw20295 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20295step0 raw20295; decide +kernel
      have hl : raw20295step0Labels = raw20295Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20295 raw20295Labels permutation346 hz
    mixedMoment B raw20295step0 raw20295step0Labels = mixedMoment B raw20295step1 raw20295step1Labels := by
      have ha : raw20295step1 = (fun i j => raw20295step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20295step1 raw20295step0; decide +kernel
      have hl : raw20295step1Labels = raw20295step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20295step0 raw20295step0Labels permutation34 permutation4
    mixedMoment B raw20295step1 raw20295step1Labels = mixedMoment B raw20295step2 raw20295step2Labels := by
      have ha : raw20295step2 = -raw20295step1 := by apply Matrix.ext; change ∀ i j, raw20295step2 i j = -(raw20295step1 i j); unfold raw20295step2 raw20295step1; decide +kernel
      have hl : raw20295step2Labels = raw20295step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3291 node3291Labels := by rfl

def raw20296 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20296Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20296step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20296step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20296step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3], ![-2, 2, 0]]
def raw20296step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20296step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 2, -3], ![2, -2, 0]]
def raw20296step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20296 raw20296Labels = mixedMoment B node1624 node1624Labels := by
  calc
    mixedMoment B raw20296 raw20296Labels = mixedMoment B raw20296step0 raw20296step0Labels := by
      have hz : ∀ j, raw20296 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20296step0 = (fun i j => raw20296 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20296step0 raw20296; decide +kernel
      have hl : raw20296step0Labels = raw20296Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20296 raw20296Labels permutation346 hz
    mixedMoment B raw20296step0 raw20296step0Labels = mixedMoment B raw20296step1 raw20296step1Labels := by
      have ha : raw20296step1 = (fun i j => raw20296step0 (permutation41 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20296step1 raw20296step0; decide +kernel
      have hl : raw20296step1Labels = raw20296step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20296step0 raw20296step0Labels permutation41 permutation2
    mixedMoment B raw20296step1 raw20296step1Labels = mixedMoment B raw20296step2 raw20296step2Labels := by
      have ha : raw20296step2 = -raw20296step1 := by apply Matrix.ext; change ∀ i j, raw20296step2 i j = -(raw20296step1 i j); unfold raw20296step2 raw20296step1; decide +kernel
      have hl : raw20296step2Labels = raw20296step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1624 node1624Labels := by rfl

def raw20297 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20297Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20297step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20297step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20297step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw20297step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20297 raw20297Labels = mixedMoment B node1613 node1613Labels := by
  calc
    mixedMoment B raw20297 raw20297Labels = mixedMoment B raw20297step0 raw20297step0Labels := by
      have ha : raw20297step0 = (fun i j => raw20297 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20297step0 raw20297; decide +kernel
      have hl : raw20297step0Labels = raw20297Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20297 raw20297Labels permutation200 permutation2
    mixedMoment B raw20297step0 raw20297step0Labels = mixedMoment B raw20297step1 raw20297step1Labels := by
      have ha : raw20297step1 = -raw20297step0 := by apply Matrix.ext; change ∀ i j, raw20297step1 i j = -(raw20297step0 i j); unfold raw20297step1 raw20297step0; decide +kernel
      have hl : raw20297step1Labels = raw20297step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1613 node1613Labels := by rfl

def raw20298 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20298Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20298step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20298step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20298step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20298step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw20298step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20298 raw20298Labels = mixedMoment B node1750 node1750Labels := by
  calc
    mixedMoment B raw20298 raw20298Labels = mixedMoment B raw20298step0 raw20298step0Labels := by
      have hz : ∀ j, raw20298 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20298step0 = (fun i j => raw20298 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20298step0 raw20298; decide +kernel
      have hl : raw20298step0Labels = raw20298Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20298 raw20298Labels permutation434 hz
    mixedMoment B raw20298step0 raw20298step0Labels = mixedMoment B raw20298step1 raw20298step1Labels := by
      have hz : ∀ j, raw20298step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20298step1 = (fun i j => raw20298step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20298step1 raw20298step0; decide +kernel
      have hl : raw20298step1Labels = raw20298step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20298step0 raw20298step0Labels permutation80 hz
    mixedMoment B raw20298step1 raw20298step1Labels = mixedMoment B raw20298step2 raw20298step2Labels := by
      have ha : raw20298step2 = -raw20298step1 := by apply Matrix.ext; change ∀ i j, raw20298step2 i j = -(raw20298step1 i j); unfold raw20298step2 raw20298step1; decide +kernel
      have hl : raw20298step2Labels = raw20298step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1750 node1750Labels := by rfl

def raw20299 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20299Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20299step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20299step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw20299step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20299step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw20299step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20299 raw20299Labels = mixedMoment B node1619 node1619Labels := by
  calc
    mixedMoment B raw20299 raw20299Labels = mixedMoment B raw20299step0 raw20299step0Labels := by
      have hz : ∀ j, raw20299 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20299step0 = (fun i j => raw20299 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20299step0 raw20299; decide +kernel
      have hl : raw20299step0Labels = raw20299Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20299 raw20299Labels permutation346 hz
    mixedMoment B raw20299step0 raw20299step0Labels = mixedMoment B raw20299step1 raw20299step1Labels := by
      have ha : raw20299step1 = (fun i j => raw20299step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20299step1 raw20299step0; decide +kernel
      have hl : raw20299step1Labels = raw20299step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20299step0 raw20299step0Labels permutation39 permutation2
    mixedMoment B raw20299step1 raw20299step1Labels = mixedMoment B raw20299step2 raw20299step2Labels := by
      have ha : raw20299step2 = -raw20299step1 := by apply Matrix.ext; change ∀ i j, raw20299step2 i j = -(raw20299step1 i j); unfold raw20299step2 raw20299step1; decide +kernel
      have hl : raw20299step2Labels = raw20299step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1619 node1619Labels := by rfl

def raw20300 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20300Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20300step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20300step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20300step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20300step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw20300step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20300 raw20300Labels = mixedMoment B node1617 node1617Labels := by
  calc
    mixedMoment B raw20300 raw20300Labels = mixedMoment B raw20300step0 raw20300step0Labels := by
      have hz : ∀ j, raw20300 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20300step0 = (fun i j => raw20300 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20300step0 raw20300; decide +kernel
      have hl : raw20300step0Labels = raw20300Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20300 raw20300Labels permutation346 hz
    mixedMoment B raw20300step0 raw20300step0Labels = mixedMoment B raw20300step1 raw20300step1Labels := by
      have ha : raw20300step1 = (fun i j => raw20300step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20300step1 raw20300step0; decide +kernel
      have hl : raw20300step1Labels = raw20300step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20300step0 raw20300step0Labels permutation38 permutation2
    mixedMoment B raw20300step1 raw20300step1Labels = mixedMoment B raw20300step2 raw20300step2Labels := by
      have ha : raw20300step2 = -raw20300step1 := by apply Matrix.ext; change ∀ i j, raw20300step2 i j = -(raw20300step1 i j); unfold raw20300step2 raw20300step1; decide +kernel
      have hl : raw20300step2Labels = raw20300step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1617 node1617Labels := by rfl

def raw20301 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20301Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20301step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20301step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20301step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20301step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw20301step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20301 raw20301Labels = mixedMoment B node1617 node1617Labels := by
  calc
    mixedMoment B raw20301 raw20301Labels = mixedMoment B raw20301step0 raw20301step0Labels := by
      have hz : ∀ j, raw20301 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20301step0 = (fun i j => raw20301 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20301step0 raw20301; decide +kernel
      have hl : raw20301step0Labels = raw20301Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20301 raw20301Labels permutation346 hz
    mixedMoment B raw20301step0 raw20301step0Labels = mixedMoment B raw20301step1 raw20301step1Labels := by
      have ha : raw20301step1 = (fun i j => raw20301step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20301step1 raw20301step0; decide +kernel
      have hl : raw20301step1Labels = raw20301step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20301step0 raw20301step0Labels permutation32 permutation4
    mixedMoment B raw20301step1 raw20301step1Labels = mixedMoment B raw20301step2 raw20301step2Labels := by
      have ha : raw20301step2 = -raw20301step1 := by apply Matrix.ext; change ∀ i j, raw20301step2 i j = -(raw20301step1 i j); unfold raw20301step2 raw20301step1; decide +kernel
      have hl : raw20301step2Labels = raw20301step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1617 node1617Labels := by rfl

def raw20302 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20302Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20302step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20302step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw20302step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20302step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw20302step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20302 raw20302Labels = mixedMoment B node1599 node1599Labels := by
  calc
    mixedMoment B raw20302 raw20302Labels = mixedMoment B raw20302step0 raw20302step0Labels := by
      have hz : ∀ j, raw20302 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20302step0 = (fun i j => raw20302 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20302step0 raw20302; decide +kernel
      have hl : raw20302step0Labels = raw20302Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20302 raw20302Labels permutation346 hz
    mixedMoment B raw20302step0 raw20302step0Labels = mixedMoment B raw20302step1 raw20302step1Labels := by
      have ha : raw20302step1 = (fun i j => raw20302step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20302step1 raw20302step0; decide +kernel
      have hl : raw20302step1Labels = raw20302step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20302step0 raw20302step0Labels permutation34 permutation4
    mixedMoment B raw20302step1 raw20302step1Labels = mixedMoment B raw20302step2 raw20302step2Labels := by
      have ha : raw20302step2 = -raw20302step1 := by apply Matrix.ext; change ∀ i j, raw20302step2 i j = -(raw20302step1 i j); unfold raw20302step2 raw20302step1; decide +kernel
      have hl : raw20302step2Labels = raw20302step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1599 node1599Labels := by rfl

def raw20303 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20303Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20303step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20303step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20303step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20303step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![-1, -2, 3]]
def raw20303step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20303step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![-2, -1, 3]]
def raw20303step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20303step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -2, 4], ![0, 1, -1], ![2, 1, -3]]
def raw20303step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20303 raw20303Labels = mixedMoment B node3310 node3310Labels := by
  calc
    mixedMoment B raw20303 raw20303Labels = mixedMoment B raw20303step0 raw20303step0Labels := by
      have hz : ∀ j, raw20303 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20303step0 = (fun i j => raw20303 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20303step0 raw20303; decide +kernel
      have hl : raw20303step0Labels = raw20303Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20303 raw20303Labels permutation434 hz
    mixedMoment B raw20303step0 raw20303step0Labels = mixedMoment B raw20303step1 raw20303step1Labels := by
      have hz : ∀ j, raw20303step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20303step1 = (fun i j => raw20303step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20303step1 raw20303step0; decide +kernel
      have hl : raw20303step1Labels = raw20303step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20303step0 raw20303step0Labels permutation80 hz
    mixedMoment B raw20303step1 raw20303step1Labels = mixedMoment B raw20303step2 raw20303step2Labels := by
      have hz : ∀ j, raw20303step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20303step2 = (fun i j => raw20303step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20303step2 raw20303step1; decide +kernel
      have hl : raw20303step2Labels = raw20303step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20303step1 raw20303step1Labels permutation14 hz
    mixedMoment B raw20303step2 raw20303step2Labels = mixedMoment B raw20303step3 raw20303step3Labels := by
      have ha : raw20303step3 = (fun i j => raw20303step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20303step3 raw20303step2; decide +kernel
      have hl : raw20303step3Labels = raw20303step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20303step2 raw20303step2Labels permutation2 permutation4
    mixedMoment B raw20303step3 raw20303step3Labels = mixedMoment B raw20303step4 raw20303step4Labels := by
      have ha : raw20303step4 = -raw20303step3 := by apply Matrix.ext; change ∀ i j, raw20303step4 i j = -(raw20303step3 i j); unfold raw20303step4 raw20303step3; decide +kernel
      have hl : raw20303step4Labels = raw20303step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3310 node3310Labels := by rfl

def raw20304 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20304Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20304step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20304step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw20304step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20304step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw20304step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20304 raw20304Labels = mixedMoment B node3291 node3291Labels := by
  calc
    mixedMoment B raw20304 raw20304Labels = mixedMoment B raw20304step0 raw20304step0Labels := by
      have hz : ∀ j, raw20304 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20304step0 = (fun i j => raw20304 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20304step0 raw20304; decide +kernel
      have hl : raw20304step0Labels = raw20304Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20304 raw20304Labels permutation434 hz
    mixedMoment B raw20304step0 raw20304step0Labels = mixedMoment B raw20304step1 raw20304step1Labels := by
      have ha : raw20304step1 = (fun i j => raw20304step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20304step1 raw20304step0; decide +kernel
      have hl : raw20304step1Labels = raw20304step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20304step0 raw20304step0Labels permutation34 permutation4
    mixedMoment B raw20304step1 raw20304step1Labels = mixedMoment B raw20304step2 raw20304step2Labels := by
      have ha : raw20304step2 = -raw20304step1 := by apply Matrix.ext; change ∀ i j, raw20304step2 i j = -(raw20304step1 i j); unfold raw20304step2 raw20304step1; decide +kernel
      have hl : raw20304step2Labels = raw20304step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3291 node3291Labels := by rfl

def raw20305 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20305Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20305step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20305step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20305step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20305step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20305step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw20305step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20305 raw20305Labels = mixedMoment B node2226 node2226Labels := by
  calc
    mixedMoment B raw20305 raw20305Labels = mixedMoment B raw20305step0 raw20305step0Labels := by
      have hz : ∀ j, raw20305 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20305step0 = (fun i j => raw20305 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20305step0 raw20305; decide +kernel
      have hl : raw20305step0Labels = raw20305Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20305 raw20305Labels permutation434 hz
    mixedMoment B raw20305step0 raw20305step0Labels = mixedMoment B raw20305step1 raw20305step1Labels := by
      have hz : ∀ j, raw20305step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20305step1 = (fun i j => raw20305step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20305step1 raw20305step0; decide +kernel
      have hl : raw20305step1Labels = raw20305step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20305step0 raw20305step0Labels permutation80 hz
    mixedMoment B raw20305step1 raw20305step1Labels = mixedMoment B raw20305step2 raw20305step2Labels := by
      have ha : raw20305step2 = (fun i j => raw20305step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20305step2 raw20305step1; decide +kernel
      have hl : raw20305step2Labels = raw20305step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20305step1 raw20305step1Labels permutation31 permutation4
    _ = mixedMoment B node2226 node2226Labels := by rfl

def raw20306 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20306Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20306step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20306step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20306step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20306step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw20306step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20306 raw20306Labels = mixedMoment B node3242 node3242Labels := by
  calc
    mixedMoment B raw20306 raw20306Labels = mixedMoment B raw20306step0 raw20306step0Labels := by
      have hz : ∀ j, raw20306 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20306step0 = (fun i j => raw20306 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20306step0 raw20306; decide +kernel
      have hl : raw20306step0Labels = raw20306Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20306 raw20306Labels permutation346 hz
    mixedMoment B raw20306step0 raw20306step0Labels = mixedMoment B raw20306step1 raw20306step1Labels := by
      have ha : raw20306step1 = (fun i j => raw20306step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20306step1 raw20306step0; decide +kernel
      have hl : raw20306step1Labels = raw20306step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20306step0 raw20306step0Labels permutation32 permutation4
    mixedMoment B raw20306step1 raw20306step1Labels = mixedMoment B raw20306step2 raw20306step2Labels := by
      have ha : raw20306step2 = -raw20306step1 := by apply Matrix.ext; change ∀ i j, raw20306step2 i j = -(raw20306step1 i j); unfold raw20306step2 raw20306step1; decide +kernel
      have hl : raw20306step2Labels = raw20306step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3242 node3242Labels := by rfl

def raw20307 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20307Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20307step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20307step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20307step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw20307step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20307 raw20307Labels = mixedMoment B node3279 node3279Labels := by
  calc
    mixedMoment B raw20307 raw20307Labels = mixedMoment B raw20307step0 raw20307step0Labels := by
      have ha : raw20307step0 = (fun i j => raw20307 (permutation152 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20307step0 raw20307; decide +kernel
      have hl : raw20307step0Labels = raw20307Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20307 raw20307Labels permutation152 permutation4
    mixedMoment B raw20307step0 raw20307step0Labels = mixedMoment B raw20307step1 raw20307step1Labels := by
      have ha : raw20307step1 = -raw20307step0 := by apply Matrix.ext; change ∀ i j, raw20307step1 i j = -(raw20307step0 i j); unfold raw20307step1 raw20307step0; decide +kernel
      have hl : raw20307step1Labels = raw20307step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3279 node3279Labels := by rfl

def raw20308 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20308Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20308step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20308step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 2, -4]]
def raw20308step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20308 raw20308Labels = mixedMoment B node2005 node2005Labels := by
  calc
    mixedMoment B raw20308 raw20308Labels = mixedMoment B raw20308step0 raw20308step0Labels := by
      have hz : ∀ j, raw20308 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20308step0 = (fun i j => raw20308 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20308step0 raw20308; decide +kernel
      have hl : raw20308step0Labels = raw20308Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20308 raw20308Labels permutation346 hz
    mixedMoment B raw20308step0 raw20308step0Labels = mixedMoment B raw20308step1 raw20308step1Labels := by
      have ha : raw20308step1 = (fun i j => raw20308step0 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20308step1 raw20308step0; decide +kernel
      have hl : raw20308step1Labels = raw20308step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20308step0 raw20308step0Labels permutation145 permutation4
    _ = mixedMoment B node2005 node2005Labels := by rfl

def raw20309 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20309Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20309step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw20309step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20309 raw20309Labels = mixedMoment B node1995 node1995Labels := by
  calc
    mixedMoment B raw20309 raw20309Labels = mixedMoment B raw20309step0 raw20309step0Labels := by
      have ha : raw20309step0 = (fun i j => raw20309 (permutation662 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20309step0 raw20309; decide +kernel
      have hl : raw20309step0Labels = raw20309Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20309 raw20309Labels permutation662 permutation4
    _ = mixedMoment B node1995 node1995Labels := by rfl

def raw20310 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20310Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20310step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20310step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 2, -4]]
def raw20310step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20310 raw20310Labels = mixedMoment B node2045 node2045Labels := by
  calc
    mixedMoment B raw20310 raw20310Labels = mixedMoment B raw20310step0 raw20310step0Labels := by
      have hz : ∀ j, raw20310 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20310step0 = (fun i j => raw20310 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20310step0 raw20310; decide +kernel
      have hl : raw20310step0Labels = raw20310Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20310 raw20310Labels permutation346 hz
    mixedMoment B raw20310step0 raw20310step0Labels = mixedMoment B raw20310step1 raw20310step1Labels := by
      have ha : raw20310step1 = (fun i j => raw20310step0 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20310step1 raw20310step0; decide +kernel
      have hl : raw20310step1Labels = raw20310step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20310step0 raw20310step0Labels permutation145 permutation4
    _ = mixedMoment B node2045 node2045Labels := by rfl

def raw20311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw20311Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw20311step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20311step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw20311step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20311step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw20311step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20311 raw20311Labels = mixedMoment B node2087 node2087Labels := by
  calc
    mixedMoment B raw20311 raw20311Labels = mixedMoment B raw20311step0 raw20311step0Labels := by
      have hz : ∀ j, raw20311 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20311step0 = (fun i j => raw20311 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20311step0 raw20311; decide +kernel
      have hl : raw20311step0Labels = raw20311Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20311 raw20311Labels permutation346 hz
    mixedMoment B raw20311step0 raw20311step0Labels = mixedMoment B raw20311step1 raw20311step1Labels := by
      have ha : raw20311step1 = (fun i j => raw20311step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20311step1 raw20311step0; decide +kernel
      have hl : raw20311step1Labels = raw20311step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20311step0 raw20311step0Labels permutation151 permutation2
    mixedMoment B raw20311step1 raw20311step1Labels = mixedMoment B raw20311step2 raw20311step2Labels := by
      have ha : raw20311step2 = -raw20311step1 := by apply Matrix.ext; change ∀ i j, raw20311step2 i j = -(raw20311step1 i j); unfold raw20311step2 raw20311step1; decide +kernel
      have hl : raw20311step2Labels = raw20311step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2087 node2087Labels := by rfl

def raw20312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![3, 0, -3]]
def raw20312Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20312step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 1, 2]]
def raw20312step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20312step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20312step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20312 raw20312Labels = mixedMoment B node2070 node2070Labels := by
  calc
    mixedMoment B raw20312 raw20312Labels = mixedMoment B raw20312step0 raw20312step0Labels := by
      have ha : raw20312step0 = (fun i j => raw20312 (permutation676 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20312step0 raw20312; decide +kernel
      have hl : raw20312step0Labels = raw20312Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20312 raw20312Labels permutation676 permutation2
    mixedMoment B raw20312step0 raw20312step0Labels = mixedMoment B raw20312step1 raw20312step1Labels := by
      have ha : raw20312step1 = -raw20312step0 := by apply Matrix.ext; change ∀ i j, raw20312step1 i j = -(raw20312step0 i j); unfold raw20312step1 raw20312step0; decide +kernel
      have hl : raw20312step1Labels = raw20312step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2070 node2070Labels := by rfl

def raw20313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw20313Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![1, -2, 1], ![3, 0, -3]]
def raw20313step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20313step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw20313step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20313step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20313step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20313 raw20313Labels = mixedMoment B node2079 node2079Labels := by
  calc
    mixedMoment B raw20313 raw20313Labels = mixedMoment B raw20313step0 raw20313step0Labels := by
      have hz : ∀ j, raw20313 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20313step0 = (fun i j => raw20313 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20313step0 raw20313; decide +kernel
      have hl : raw20313step0Labels = raw20313Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20313 raw20313Labels permutation346 hz
    mixedMoment B raw20313step0 raw20313step0Labels = mixedMoment B raw20313step1 raw20313step1Labels := by
      have ha : raw20313step1 = (fun i j => raw20313step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20313step1 raw20313step0; decide +kernel
      have hl : raw20313step1Labels = raw20313step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20313step0 raw20313step0Labels permutation149 permutation2
    mixedMoment B raw20313step1 raw20313step1Labels = mixedMoment B raw20313step2 raw20313step2Labels := by
      have ha : raw20313step2 = -raw20313step1 := by apply Matrix.ext; change ∀ i j, raw20313step2 i j = -(raw20313step1 i j); unfold raw20313step2 raw20313step1; decide +kernel
      have hl : raw20313step2Labels = raw20313step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2079 node2079Labels := by rfl

def raw20314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw20314Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw20314step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20314step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw20314step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20314 raw20314Labels = mixedMoment B node2719 node2719Labels := by
  calc
    mixedMoment B raw20314 raw20314Labels = mixedMoment B raw20314step0 raw20314step0Labels := by
      have hz : ∀ j, raw20314 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20314step0 = (fun i j => raw20314 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20314step0 raw20314; decide +kernel
      have hl : raw20314step0Labels = raw20314Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20314 raw20314Labels permutation346 hz
    mixedMoment B raw20314step0 raw20314step0Labels = mixedMoment B raw20314step1 raw20314step1Labels := by
      have ha : raw20314step1 = (fun i j => raw20314step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20314step1 raw20314step0; decide +kernel
      have hl : raw20314step1Labels = raw20314step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20314step0 raw20314step0Labels permutation38 permutation2
    _ = mixedMoment B node2719 node2719Labels := by rfl

def raw20315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw20315Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw20315step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20315step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20315step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20315 raw20315Labels = mixedMoment B node1181 node1181Labels := by
  calc
    mixedMoment B raw20315 raw20315Labels = mixedMoment B raw20315step0 raw20315step0Labels := by
      have hz : ∀ j, raw20315 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20315step0 = (fun i j => raw20315 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20315step0 raw20315; decide +kernel
      have hl : raw20315step0Labels = raw20315Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20315 raw20315Labels permutation346 hz
    mixedMoment B raw20315step0 raw20315step0Labels = mixedMoment B raw20315step1 raw20315step1Labels := by
      have ha : raw20315step1 = (fun i j => raw20315step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20315step1 raw20315step0; decide +kernel
      have hl : raw20315step1Labels = raw20315step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20315step0 raw20315step0Labels permutation38 permutation2
    _ = mixedMoment B node1181 node1181Labels := by rfl

def raw20316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw20316Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20316step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw20316step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20316step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-3, 1, 2]]
def raw20316step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20316step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def raw20316step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20316 raw20316Labels = mixedMoment B node2492 node2492Labels := by
  calc
    mixedMoment B raw20316 raw20316Labels = mixedMoment B raw20316step0 raw20316step0Labels := by
      have hz : ∀ j, raw20316 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20316step0 = (fun i j => raw20316 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20316step0 raw20316; decide +kernel
      have hl : raw20316step0Labels = raw20316Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20316 raw20316Labels permutation346 hz
    mixedMoment B raw20316step0 raw20316step0Labels = mixedMoment B raw20316step1 raw20316step1Labels := by
      have ha : raw20316step1 = (fun i j => raw20316step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20316step1 raw20316step0; decide +kernel
      have hl : raw20316step1Labels = raw20316step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20316step0 raw20316step0Labels permutation151 permutation2
    mixedMoment B raw20316step1 raw20316step1Labels = mixedMoment B raw20316step2 raw20316step2Labels := by
      have ha : raw20316step2 = -raw20316step1 := by apply Matrix.ext; change ∀ i j, raw20316step2 i j = -(raw20316step1 i j); unfold raw20316step2 raw20316step1; decide +kernel
      have hl : raw20316step2Labels = raw20316step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2492 node2492Labels := by rfl

def raw20317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw20317Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20317step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw20317step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20317step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw20317step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20317 raw20317Labels = mixedMoment B node2453 node2453Labels := by
  calc
    mixedMoment B raw20317 raw20317Labels = mixedMoment B raw20317step0 raw20317step0Labels := by
      have ha : raw20317step0 = (fun i j => raw20317 (permutation676 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20317step0 raw20317; decide +kernel
      have hl : raw20317step0Labels = raw20317Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20317 raw20317Labels permutation676 permutation2
    mixedMoment B raw20317step0 raw20317step0Labels = mixedMoment B raw20317step1 raw20317step1Labels := by
      have ha : raw20317step1 = -raw20317step0 := by apply Matrix.ext; change ∀ i j, raw20317step1 i j = -(raw20317step0 i j); unfold raw20317step1 raw20317step0; decide +kernel
      have hl : raw20317step1Labels = raw20317step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2453 node2453Labels := by rfl

def raw20318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw20318Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw20318step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20318step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20318step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20318 raw20318Labels = mixedMoment B node2385 node2385Labels := by
  calc
    mixedMoment B raw20318 raw20318Labels = mixedMoment B raw20318step0 raw20318step0Labels := by
      have hz : ∀ j, raw20318 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20318step0 = (fun i j => raw20318 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20318step0 raw20318; decide +kernel
      have hl : raw20318step0Labels = raw20318Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20318 raw20318Labels permutation346 hz
    mixedMoment B raw20318step0 raw20318step0Labels = mixedMoment B raw20318step1 raw20318step1Labels := by
      have ha : raw20318step1 = (fun i j => raw20318step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20318step1 raw20318step0; decide +kernel
      have hl : raw20318step1Labels = raw20318step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20318step0 raw20318step0Labels permutation38 permutation2
    _ = mixedMoment B node2385 node2385Labels := by rfl

def raw20319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![3, -1, -2]]
def raw20319Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -2, 2], ![0, 1, -1], ![3, -1, -2]]
def raw20319step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20319step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw20319step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20319 raw20319Labels = mixedMoment B node2664 node2664Labels := by
  calc
    mixedMoment B raw20319 raw20319Labels = mixedMoment B raw20319step0 raw20319step0Labels := by
      have hz : ∀ j, raw20319 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20319step0 = (fun i j => raw20319 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20319step0 raw20319; decide +kernel
      have hl : raw20319step0Labels = raw20319Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20319 raw20319Labels permutation346 hz
    mixedMoment B raw20319step0 raw20319step0Labels = mixedMoment B raw20319step1 raw20319step1Labels := by
      have ha : raw20319step1 = (fun i j => raw20319step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20319step1 raw20319step0; decide +kernel
      have hl : raw20319step1Labels = raw20319step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20319step0 raw20319step0Labels permutation38 permutation2
    _ = mixedMoment B node2664 node2664Labels := by rfl

def raw20320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw20320Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20320step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw20320step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20320step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw20320step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20320 raw20320Labels = mixedMoment B node2672 node2672Labels := by
  calc
    mixedMoment B raw20320 raw20320Labels = mixedMoment B raw20320step0 raw20320step0Labels := by
      have hz : ∀ j, raw20320 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20320step0 = (fun i j => raw20320 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20320step0 raw20320; decide +kernel
      have hl : raw20320step0Labels = raw20320Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20320 raw20320Labels permutation346 hz
    mixedMoment B raw20320step0 raw20320step0Labels = mixedMoment B raw20320step1 raw20320step1Labels := by
      have ha : raw20320step1 = (fun i j => raw20320step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20320step1 raw20320step0; decide +kernel
      have hl : raw20320step1Labels = raw20320step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20320step0 raw20320step0Labels permutation38 permutation2
    _ = mixedMoment B node2672 node2672Labels := by rfl

def raw20321 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![-2, 2], ![1, -1], ![2, -2]]
def raw20321Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20321step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-2, 2], ![1, -1], ![2, -2]]
def raw20321step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20321step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw20321step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical20321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20321 raw20321Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw20321 raw20321Labels = mixedMoment B raw20321step0 raw20321step0Labels := by
      have hz : ∀ j, raw20321 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20321step0 = (fun i j => raw20321 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20321step0 raw20321; decide +kernel
      have hl : raw20321step0Labels = raw20321Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20321 raw20321Labels permutation346 hz
    mixedMoment B raw20321step0 raw20321step0Labels = mixedMoment B raw20321step1 raw20321step1Labels := by
      have ha : raw20321step1 = (fun i j => raw20321step0 (permutation38 i) (permutation0 j)) := by apply Matrix.ext; unfold raw20321step1 raw20321step0; decide +kernel
      have hl : raw20321step1Labels = raw20321step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20321step0 raw20321step0Labels permutation38 permutation0
    _ = mixedMoment B node4088 node4088Labels := by rfl

def raw20322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw20322Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20322step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw20322step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20322step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw20322step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20322 raw20322Labels = mixedMoment B node1188 node1188Labels := by
  calc
    mixedMoment B raw20322 raw20322Labels = mixedMoment B raw20322step0 raw20322step0Labels := by
      have hz : ∀ j, raw20322 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20322step0 = (fun i j => raw20322 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20322step0 raw20322; decide +kernel
      have hl : raw20322step0Labels = raw20322Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20322 raw20322Labels permutation346 hz
    mixedMoment B raw20322step0 raw20322step0Labels = mixedMoment B raw20322step1 raw20322step1Labels := by
      have ha : raw20322step1 = (fun i j => raw20322step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20322step1 raw20322step0; decide +kernel
      have hl : raw20322step1Labels = raw20322step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20322step0 raw20322step0Labels permutation38 permutation2
    _ = mixedMoment B node1188 node1188Labels := by rfl

def raw20323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw20323Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20323step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw20323step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20323 raw20323Labels = mixedMoment B node1178 node1178Labels := by
  calc
    mixedMoment B raw20323 raw20323Labels = mixedMoment B raw20323step0 raw20323step0Labels := by
      have ha : raw20323step0 = (fun i j => raw20323 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20323step0 raw20323; decide +kernel
      have hl : raw20323step0Labels = raw20323Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20323 raw20323Labels permutation200 permutation2
    _ = mixedMoment B node1178 node1178Labels := by rfl

def raw20324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw20324Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw20324step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20324 raw20324Labels = mixedMoment B node1257 node1257Labels := by
  calc
    mixedMoment B raw20324 raw20324Labels = mixedMoment B raw20324step0 raw20324step0Labels := by
      have hz : ∀ j, raw20324 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20324step0 = (fun i j => raw20324 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20324step0 raw20324; decide +kernel
      have hl : raw20324step0Labels = raw20324Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20324 raw20324Labels permutation346 hz
    _ = mixedMoment B node1257 node1257Labels := by rfl

def raw20325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw20325Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20325step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw20325step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20325step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw20325step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20325 raw20325Labels = mixedMoment B node1182 node1182Labels := by
  calc
    mixedMoment B raw20325 raw20325Labels = mixedMoment B raw20325step0 raw20325step0Labels := by
      have hz : ∀ j, raw20325 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20325step0 = (fun i j => raw20325 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20325step0 raw20325; decide +kernel
      have hl : raw20325step0Labels = raw20325Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20325 raw20325Labels permutation346 hz
    mixedMoment B raw20325step0 raw20325step0Labels = mixedMoment B raw20325step1 raw20325step1Labels := by
      have ha : raw20325step1 = (fun i j => raw20325step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20325step1 raw20325step0; decide +kernel
      have hl : raw20325step1Labels = raw20325step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20325step0 raw20325step0Labels permutation38 permutation2
    _ = mixedMoment B node1182 node1182Labels := by rfl

def raw20326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw20326Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw20326step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20326step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw20326step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20326 raw20326Labels = mixedMoment B node1179 node1179Labels := by
  calc
    mixedMoment B raw20326 raw20326Labels = mixedMoment B raw20326step0 raw20326step0Labels := by
      have hz : ∀ j, raw20326 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20326step0 = (fun i j => raw20326 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20326step0 raw20326; decide +kernel
      have hl : raw20326step0Labels = raw20326Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20326 raw20326Labels permutation346 hz
    mixedMoment B raw20326step0 raw20326step0Labels = mixedMoment B raw20326step1 raw20326step1Labels := by
      have ha : raw20326step1 = (fun i j => raw20326step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20326step1 raw20326step0; decide +kernel
      have hl : raw20326step1Labels = raw20326step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20326step0 raw20326step0Labels permutation38 permutation2
    _ = mixedMoment B node1179 node1179Labels := by rfl

def raw20327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw20327Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw20327step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20327step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-3, 1, 2]]
def raw20327step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20327step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![3, -1, -2]]
def raw20327step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20327 raw20327Labels = mixedMoment B node2032 node2032Labels := by
  calc
    mixedMoment B raw20327 raw20327Labels = mixedMoment B raw20327step0 raw20327step0Labels := by
      have hz : ∀ j, raw20327 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20327step0 = (fun i j => raw20327 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20327step0 raw20327; decide +kernel
      have hl : raw20327step0Labels = raw20327Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20327 raw20327Labels permutation346 hz
    mixedMoment B raw20327step0 raw20327step0Labels = mixedMoment B raw20327step1 raw20327step1Labels := by
      have ha : raw20327step1 = (fun i j => raw20327step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20327step1 raw20327step0; decide +kernel
      have hl : raw20327step1Labels = raw20327step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20327step0 raw20327step0Labels permutation151 permutation2
    mixedMoment B raw20327step1 raw20327step1Labels = mixedMoment B raw20327step2 raw20327step2Labels := by
      have ha : raw20327step2 = -raw20327step1 := by apply Matrix.ext; change ∀ i j, raw20327step2 i j = -(raw20327step1 i j); unfold raw20327step2 raw20327step1; decide +kernel
      have hl : raw20327step2Labels = raw20327step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2032 node2032Labels := by rfl

def raw20328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![3, 0, -3]]
def raw20328Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20328step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-3, 1, 2]]
def raw20328step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20328step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![3, -1, -2]]
def raw20328step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20328 raw20328Labels = mixedMoment B node1991 node1991Labels := by
  calc
    mixedMoment B raw20328 raw20328Labels = mixedMoment B raw20328step0 raw20328step0Labels := by
      have ha : raw20328step0 = (fun i j => raw20328 (permutation676 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20328step0 raw20328; decide +kernel
      have hl : raw20328step0Labels = raw20328Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20328 raw20328Labels permutation676 permutation2
    mixedMoment B raw20328step0 raw20328step0Labels = mixedMoment B raw20328step1 raw20328step1Labels := by
      have ha : raw20328step1 = -raw20328step0 := by apply Matrix.ext; change ∀ i j, raw20328step1 i j = -(raw20328step0 i j); unfold raw20328step1 raw20328step0; decide +kernel
      have hl : raw20328step1Labels = raw20328step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1991 node1991Labels := by rfl

def raw20329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, -1, 2], ![1, -1, 0], ![3, 0, -3]]
def raw20329Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, -1, 2], ![1, -1, 0], ![3, 0, -3]]
def raw20329step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20329step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 1, 2]]
def raw20329step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20329step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw20329step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20329 raw20329Labels = mixedMoment B node2003 node2003Labels := by
  calc
    mixedMoment B raw20329 raw20329Labels = mixedMoment B raw20329step0 raw20329step0Labels := by
      have hz : ∀ j, raw20329 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20329step0 = (fun i j => raw20329 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20329step0 raw20329; decide +kernel
      have hl : raw20329step0Labels = raw20329Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20329 raw20329Labels permutation346 hz
    mixedMoment B raw20329step0 raw20329step0Labels = mixedMoment B raw20329step1 raw20329step1Labels := by
      have ha : raw20329step1 = (fun i j => raw20329step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20329step1 raw20329step0; decide +kernel
      have hl : raw20329step1Labels = raw20329step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20329step0 raw20329step0Labels permutation149 permutation2
    mixedMoment B raw20329step1 raw20329step1Labels = mixedMoment B raw20329step2 raw20329step2Labels := by
      have ha : raw20329step2 = -raw20329step1 := by apply Matrix.ext; change ∀ i j, raw20329step2 i j = -(raw20329step1 i j); unfold raw20329step2 raw20329step1; decide +kernel
      have hl : raw20329step2Labels = raw20329step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2003 node2003Labels := by rfl

def raw20330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![0, 0, 0], ![3, 0, -3]]
def raw20330Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![3, 0, -3]]
def raw20330step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20330step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -2, 2], ![3, 0, -3]]
def raw20330step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20330step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-3, 1, 2]]
def raw20330step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20330step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw20330step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20330 raw20330Labels = mixedMoment B node2218 node2218Labels := by
  calc
    mixedMoment B raw20330 raw20330Labels = mixedMoment B raw20330step0 raw20330step0Labels := by
      have hz : ∀ j, raw20330 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20330step0 = (fun i j => raw20330 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20330step0 raw20330; decide +kernel
      have hl : raw20330step0Labels = raw20330Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20330 raw20330Labels permutation520 hz
    mixedMoment B raw20330step0 raw20330step0Labels = mixedMoment B raw20330step1 raw20330step1Labels := by
      have hz : ∀ j, raw20330step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20330step1 = (fun i j => raw20330step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20330step1 raw20330step0; decide +kernel
      have hl : raw20330step1Labels = raw20330step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20330step0 raw20330step0Labels permutation80 hz
    mixedMoment B raw20330step1 raw20330step1Labels = mixedMoment B raw20330step2 raw20330step2Labels := by
      have ha : raw20330step2 = (fun i j => raw20330step1 (permutation29 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20330step2 raw20330step1; decide +kernel
      have hl : raw20330step2Labels = raw20330step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20330step1 raw20330step1Labels permutation29 permutation2
    mixedMoment B raw20330step2 raw20330step2Labels = mixedMoment B raw20330step3 raw20330step3Labels := by
      have ha : raw20330step3 = -raw20330step2 := by apply Matrix.ext; change ∀ i j, raw20330step3 i j = -(raw20330step2 i j); unfold raw20330step3 raw20330step2; decide +kernel
      have hl : raw20330step3Labels = raw20330step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2218 node2218Labels := by rfl

def raw20331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw20331Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw20331step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20331step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw20331step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20331 raw20331Labels = mixedMoment B node2670 node2670Labels := by
  calc
    mixedMoment B raw20331 raw20331Labels = mixedMoment B raw20331step0 raw20331step0Labels := by
      have hz : ∀ j, raw20331 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20331step0 = (fun i j => raw20331 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20331step0 raw20331; decide +kernel
      have hl : raw20331step0Labels = raw20331Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20331 raw20331Labels permutation346 hz
    mixedMoment B raw20331step0 raw20331step0Labels = mixedMoment B raw20331step1 raw20331step1Labels := by
      have ha : raw20331step1 = (fun i j => raw20331step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20331step1 raw20331step0; decide +kernel
      have hl : raw20331step1Labels = raw20331step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20331step0 raw20331step0Labels permutation38 permutation2
    _ = mixedMoment B node2670 node2670Labels := by rfl

def raw20332 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![-2, 2], ![0, 0], ![3, -3]]
def raw20332Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20332step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![0, 0], ![-2, 2], ![3, -3]]
def raw20332step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20332step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-2, 2], ![3, -3]]
def raw20332step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20332step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-2, 2], ![-2, 2]]
def raw20332step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20332step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw20332step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical20332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20332 raw20332Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw20332 raw20332Labels = mixedMoment B raw20332step0 raw20332step0Labels := by
      have hz : ∀ j, raw20332 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20332step0 = (fun i j => raw20332 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20332step0 raw20332; decide +kernel
      have hl : raw20332step0Labels = raw20332Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20332 raw20332Labels permutation520 hz
    mixedMoment B raw20332step0 raw20332step0Labels = mixedMoment B raw20332step1 raw20332step1Labels := by
      have hz : ∀ j, raw20332step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20332step1 = (fun i j => raw20332step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20332step1 raw20332step0; decide +kernel
      have hl : raw20332step1Labels = raw20332step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20332step0 raw20332step0Labels permutation80 hz
    mixedMoment B raw20332step1 raw20332step1Labels = mixedMoment B raw20332step2 raw20332step2Labels := by
      have ha : raw20332step2 = (fun i j => raw20332step1 (permutation28 i) (permutation0 j)) := by apply Matrix.ext; unfold raw20332step2 raw20332step1; decide +kernel
      have hl : raw20332step2Labels = raw20332step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20332step1 raw20332step1Labels permutation28 permutation0
    mixedMoment B raw20332step2 raw20332step2Labels = mixedMoment B raw20332step3 raw20332step3Labels := by
      have ha : raw20332step3 = -raw20332step2 := by apply Matrix.ext; change ∀ i j, raw20332step3 i j = -(raw20332step2 i j); unfold raw20332step3 raw20332step2; decide +kernel
      have hl : raw20332step3Labels = raw20332step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4082 node4082Labels := by rfl

def raw20333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20333Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20333step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20333step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20333 raw20333Labels = mixedMoment B node1195 node1195Labels := by
  calc
    mixedMoment B raw20333 raw20333Labels = mixedMoment B raw20333step0 raw20333step0Labels := by
      have ha : raw20333step0 = (fun i j => raw20333 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20333step0 raw20333; decide +kernel
      have hl : raw20333step0Labels = raw20333Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20333 raw20333Labels permutation182 permutation2
    _ = mixedMoment B node1195 node1195Labels := by rfl

def raw20334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20334Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20334step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw20334step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20334step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw20334step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20334 raw20334Labels = mixedMoment B node2469 node2469Labels := by
  calc
    mixedMoment B raw20334 raw20334Labels = mixedMoment B raw20334step0 raw20334step0Labels := by
      have ha : raw20334step0 = (fun i j => raw20334 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20334step0 raw20334; decide +kernel
      have hl : raw20334step0Labels = raw20334Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20334 raw20334Labels permutation682 permutation2
    mixedMoment B raw20334step0 raw20334step0Labels = mixedMoment B raw20334step1 raw20334step1Labels := by
      have ha : raw20334step1 = -raw20334step0 := by apply Matrix.ext; change ∀ i j, raw20334step1 i j = -(raw20334step0 i j); unfold raw20334step1 raw20334step0; decide +kernel
      have hl : raw20334step1Labels = raw20334step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2469 node2469Labels := by rfl

def raw20335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20335Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20335step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20335step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20335 raw20335Labels = mixedMoment B node2449 node2449Labels := by
  calc
    mixedMoment B raw20335 raw20335Labels = mixedMoment B raw20335step0 raw20335step0Labels := by
      have ha : raw20335step0 = (fun i j => raw20335 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20335step0 raw20335; decide +kernel
      have hl : raw20335step0Labels = raw20335Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20335 raw20335Labels permutation182 permutation2
    _ = mixedMoment B node2449 node2449Labels := by rfl

def raw20336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20336Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20336step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20336step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20336 raw20336Labels = mixedMoment B node2449 node2449Labels := by
  calc
    mixedMoment B raw20336 raw20336Labels = mixedMoment B raw20336step0 raw20336step0Labels := by
      have ha : raw20336step0 = (fun i j => raw20336 (permutation206 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20336step0 raw20336; decide +kernel
      have hl : raw20336step0Labels = raw20336Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20336 raw20336Labels permutation206 permutation2
    _ = mixedMoment B node2449 node2449Labels := by rfl

def raw20337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw20337Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20337step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw20337step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20337 raw20337Labels = mixedMoment B node2691 node2691Labels := by
  calc
    mixedMoment B raw20337 raw20337Labels = mixedMoment B raw20337step0 raw20337step0Labels := by
      have ha : raw20337step0 = (fun i j => raw20337 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20337step0 raw20337; decide +kernel
      have hl : raw20337step0Labels = raw20337Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20337 raw20337Labels permutation182 permutation2
    _ = mixedMoment B node2691 node2691Labels := by rfl

def raw20338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20338Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20338step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw20338step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20338 raw20338Labels = mixedMoment B node2694 node2694Labels := by
  calc
    mixedMoment B raw20338 raw20338Labels = mixedMoment B raw20338step0 raw20338step0Labels := by
      have ha : raw20338step0 = (fun i j => raw20338 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20338step0 raw20338; decide +kernel
      have hl : raw20338step0Labels = raw20338Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20338 raw20338Labels permutation182 permutation2
    _ = mixedMoment B node2694 node2694Labels := by rfl

def raw20339 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]
def raw20339Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20339step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw20339step0Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical20339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20339 raw20339Labels = mixedMoment B node4090 node4090Labels := by
  calc
    mixedMoment B raw20339 raw20339Labels = mixedMoment B raw20339step0 raw20339step0Labels := by
      have ha : raw20339step0 = (fun i j => raw20339 (permutation182 i) (permutation0 j)) := by apply Matrix.ext; unfold raw20339step0 raw20339; decide +kernel
      have hl : raw20339step0Labels = raw20339Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20339 raw20339Labels permutation182 permutation0
    _ = mixedMoment B node4090 node4090Labels := by rfl

def raw20340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20340Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20340step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw20340step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20340 raw20340Labels = mixedMoment B node1200 node1200Labels := by
  calc
    mixedMoment B raw20340 raw20340Labels = mixedMoment B raw20340step0 raw20340step0Labels := by
      have ha : raw20340step0 = (fun i j => raw20340 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20340step0 raw20340; decide +kernel
      have hl : raw20340step0Labels = raw20340Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20340 raw20340Labels permutation182 permutation2
    _ = mixedMoment B node1200 node1200Labels := by rfl

def raw20341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20341Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20341step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20341step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20341 raw20341Labels = mixedMoment B node1210 node1210Labels := by
  calc
    mixedMoment B raw20341 raw20341Labels = mixedMoment B raw20341step0 raw20341step0Labels := by
      have ha : raw20341step0 = (fun i j => raw20341 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20341step0 raw20341; decide +kernel
      have hl : raw20341step0Labels = raw20341Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20341 raw20341Labels permutation200 permutation2
    _ = mixedMoment B node1210 node1210Labels := by rfl

def raw20342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20342Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20342step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw20342step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20342 raw20342Labels = mixedMoment B node1210 node1210Labels := by
  calc
    mixedMoment B raw20342 raw20342Labels = mixedMoment B raw20342step0 raw20342step0Labels := by
      have ha : raw20342step0 = (fun i j => raw20342 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20342step0 raw20342; decide +kernel
      have hl : raw20342step0Labels = raw20342Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20342 raw20342Labels permutation176 permutation2
    _ = mixedMoment B node1210 node1210Labels := by rfl

def raw20343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw20343Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20343step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw20343step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20343 raw20343Labels = mixedMoment B node1196 node1196Labels := by
  calc
    mixedMoment B raw20343 raw20343Labels = mixedMoment B raw20343step0 raw20343step0Labels := by
      have ha : raw20343step0 = (fun i j => raw20343 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20343step0 raw20343; decide +kernel
      have hl : raw20343step0Labels = raw20343Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20343 raw20343Labels permutation182 permutation2
    _ = mixedMoment B node1196 node1196Labels := by rfl

def raw20344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20344Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20344step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw20344step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20344 raw20344Labels = mixedMoment B node1194 node1194Labels := by
  calc
    mixedMoment B raw20344 raw20344Labels = mixedMoment B raw20344step0 raw20344step0Labels := by
      have ha : raw20344step0 = (fun i j => raw20344 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20344step0 raw20344; decide +kernel
      have hl : raw20344step0Labels = raw20344Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20344 raw20344Labels permutation182 permutation2
    _ = mixedMoment B node1194 node1194Labels := by rfl

def raw20345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20345Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20345step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-3, 1, 2]]
def raw20345step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20345step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw20345step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20345 raw20345Labels = mixedMoment B node2008 node2008Labels := by
  calc
    mixedMoment B raw20345 raw20345Labels = mixedMoment B raw20345step0 raw20345step0Labels := by
      have ha : raw20345step0 = (fun i j => raw20345 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20345step0 raw20345; decide +kernel
      have hl : raw20345step0Labels = raw20345Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20345 raw20345Labels permutation682 permutation2
    mixedMoment B raw20345step0 raw20345step0Labels = mixedMoment B raw20345step1 raw20345step1Labels := by
      have ha : raw20345step1 = -raw20345step0 := by apply Matrix.ext; change ∀ i j, raw20345step1 i j = -(raw20345step0 i j); unfold raw20345step1 raw20345step0; decide +kernel
      have hl : raw20345step1Labels = raw20345step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2008 node2008Labels := by rfl

def raw20346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20346Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20346step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw20346step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20346step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20346step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20346 raw20346Labels = mixedMoment B node1987 node1987Labels := by
  calc
    mixedMoment B raw20346 raw20346Labels = mixedMoment B raw20346step0 raw20346step0Labels := by
      have ha : raw20346step0 = (fun i j => raw20346 (permutation676 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20346step0 raw20346; decide +kernel
      have hl : raw20346step0Labels = raw20346Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20346 raw20346Labels permutation676 permutation2
    mixedMoment B raw20346step0 raw20346step0Labels = mixedMoment B raw20346step1 raw20346step1Labels := by
      have ha : raw20346step1 = -raw20346step0 := by apply Matrix.ext; change ∀ i j, raw20346step1 i j = -(raw20346step0 i j); unfold raw20346step1 raw20346step0; decide +kernel
      have hl : raw20346step1Labels = raw20346step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1987 node1987Labels := by rfl

def raw20347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20347Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20347step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw20347step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20347step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw20347step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20347 raw20347Labels = mixedMoment B node1987 node1987Labels := by
  calc
    mixedMoment B raw20347 raw20347Labels = mixedMoment B raw20347step0 raw20347step0Labels := by
      have ha : raw20347step0 = (fun i j => raw20347 (permutation674 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20347step0 raw20347; decide +kernel
      have hl : raw20347step0Labels = raw20347Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20347 raw20347Labels permutation674 permutation2
    mixedMoment B raw20347step0 raw20347step0Labels = mixedMoment B raw20347step1 raw20347step1Labels := by
      have ha : raw20347step1 = -raw20347step0 := by apply Matrix.ext; change ∀ i j, raw20347step1 i j = -(raw20347step0 i j); unfold raw20347step1 raw20347step0; decide +kernel
      have hl : raw20347step1Labels = raw20347step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1987 node1987Labels := by rfl

def raw20348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![0, 0, 0], ![3, 0, -3]]
def raw20348Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20348step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![3, 0, -3]]
def raw20348step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20348step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw20348step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20348step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw20348step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20348 raw20348Labels = mixedMoment B node2193 node2193Labels := by
  calc
    mixedMoment B raw20348 raw20348Labels = mixedMoment B raw20348step0 raw20348step0Labels := by
      have hz : ∀ j, raw20348 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20348step0 = (fun i j => raw20348 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20348step0 raw20348; decide +kernel
      have hl : raw20348step0Labels = raw20348Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20348 raw20348Labels permutation520 hz
    mixedMoment B raw20348step0 raw20348step0Labels = mixedMoment B raw20348step1 raw20348step1Labels := by
      have ha : raw20348step1 = (fun i j => raw20348step0 (permutation137 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20348step1 raw20348step0; decide +kernel
      have hl : raw20348step1Labels = raw20348step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20348step0 raw20348step0Labels permutation137 permutation2
    mixedMoment B raw20348step1 raw20348step1Labels = mixedMoment B raw20348step2 raw20348step2Labels := by
      have ha : raw20348step2 = -raw20348step1 := by apply Matrix.ext; change ∀ i j, raw20348step2 i j = -(raw20348step1 i j); unfold raw20348step2 raw20348step1; decide +kernel
      have hl : raw20348step2Labels = raw20348step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2193 node2193Labels := by rfl

def raw20349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw20349Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20349step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw20349step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20349 raw20349Labels = mixedMoment B node2693 node2693Labels := by
  calc
    mixedMoment B raw20349 raw20349Labels = mixedMoment B raw20349step0 raw20349step0Labels := by
      have ha : raw20349step0 = (fun i j => raw20349 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20349step0 raw20349; decide +kernel
      have hl : raw20349step0Labels = raw20349Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20349 raw20349Labels permutation182 permutation2
    _ = mixedMoment B node2693 node2693Labels := by rfl

def raw20350 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![-1, 1], ![0, 0], ![3, -3]]
def raw20350Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20350step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![-1, 1], ![3, -3]]
def raw20350step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20350step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-1, 1], ![-1, 1], ![-2, 2]]
def raw20350step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw20350step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw20350step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical20350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20350 raw20350Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw20350 raw20350Labels = mixedMoment B raw20350step0 raw20350step0Labels := by
      have hz : ∀ j, raw20350 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20350step0 = (fun i j => raw20350 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20350step0 raw20350; decide +kernel
      have hl : raw20350step0Labels = raw20350Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20350 raw20350Labels permutation520 hz
    mixedMoment B raw20350step0 raw20350step0Labels = mixedMoment B raw20350step1 raw20350step1Labels := by
      have ha : raw20350step1 = (fun i j => raw20350step0 (permutation137 i) (permutation0 j)) := by apply Matrix.ext; unfold raw20350step1 raw20350step0; decide +kernel
      have hl : raw20350step1Labels = raw20350step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20350step0 raw20350step0Labels permutation137 permutation0
    mixedMoment B raw20350step1 raw20350step1Labels = mixedMoment B raw20350step2 raw20350step2Labels := by
      have ha : raw20350step2 = -raw20350step1 := by apply Matrix.ext; change ∀ i j, raw20350step2 i j = -(raw20350step1 i j); unfold raw20350step2 raw20350step1; decide +kernel
      have hl : raw20350step2Labels = raw20350step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw20351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20351Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20351step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20351step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20351step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20351step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20351step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20351step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20351step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20351step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20351 raw20351Labels = mixedMoment B node4183 node4183Labels := by
  calc
    mixedMoment B raw20351 raw20351Labels = mixedMoment B raw20351step0 raw20351step0Labels := by
      have hz : ∀ j, raw20351 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20351step0 = (fun i j => raw20351 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20351step0 raw20351; decide +kernel
      have hl : raw20351step0Labels = raw20351Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20351 raw20351Labels permutation434 hz
    mixedMoment B raw20351step0 raw20351step0Labels = mixedMoment B raw20351step1 raw20351step1Labels := by
      have hz : ∀ j, raw20351step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20351step1 = (fun i j => raw20351step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20351step1 raw20351step0; decide +kernel
      have hl : raw20351step1Labels = raw20351step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20351step0 raw20351step0Labels permutation80 hz
    mixedMoment B raw20351step1 raw20351step1Labels = mixedMoment B raw20351step2 raw20351step2Labels := by
      have ha : raw20351step2 = (fun i j => raw20351step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20351step2 raw20351step1; decide +kernel
      have hl : raw20351step2Labels = raw20351step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20351step1 raw20351step1Labels permutation8 permutation3
    mixedMoment B raw20351step2 raw20351step2Labels = mixedMoment B raw20351step3 raw20351step3Labels := by
      have ha : raw20351step3 = raw20351step2 := by apply Matrix.ext; unfold raw20351step3 raw20351step2; decide +kernel
      have hl : raw20351step2Labels = labelEmbedding6 ∘ raw20351step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20351step2 raw20351step2Labels raw20351step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4183 node4183Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
