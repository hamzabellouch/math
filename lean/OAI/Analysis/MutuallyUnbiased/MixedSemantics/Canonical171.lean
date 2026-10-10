import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes11
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw21888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 3, -3], ![3, -2, -1]]
def raw21888Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![0, 3, -3], ![3, -2, -1]]
def raw21888step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21888step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![3, -2, -1]]
def raw21888step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21888 raw21888Labels = mixedMoment B node2222 node2222Labels := by
  calc
    mixedMoment B raw21888 raw21888Labels = mixedMoment B raw21888step0 raw21888step0Labels := by
      have hz : ∀ j, raw21888 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21888step0 = (fun i j => raw21888 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21888step0 raw21888; decide +kernel
      have hl : raw21888step0Labels = raw21888Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21888 raw21888Labels permutation346 hz
    mixedMoment B raw21888step0 raw21888step0Labels = mixedMoment B raw21888step1 raw21888step1Labels := by
      have hz : ∀ j, raw21888step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21888step1 = (fun i j => raw21888step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21888step1 raw21888step0; decide +kernel
      have hl : raw21888step1Labels = raw21888step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21888step0 raw21888step0Labels permutation56 hz
    _ = mixedMoment B node2222 node2222Labels := by rfl

def raw21889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw21889Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21889step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw21889step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21889step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw21889step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21889 raw21889Labels = mixedMoment B node2230 node2230Labels := by
  calc
    mixedMoment B raw21889 raw21889Labels = mixedMoment B raw21889step0 raw21889step0Labels := by
      have hz : ∀ j, raw21889 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21889step0 = (fun i j => raw21889 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21889step0 raw21889; decide +kernel
      have hl : raw21889step0Labels = raw21889Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21889 raw21889Labels permutation346 hz
    mixedMoment B raw21889step0 raw21889step0Labels = mixedMoment B raw21889step1 raw21889step1Labels := by
      have hz : ∀ j, raw21889step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21889step1 = (fun i j => raw21889step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21889step1 raw21889step0; decide +kernel
      have hl : raw21889step1Labels = raw21889step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21889step0 raw21889step0Labels permutation56 hz
    _ = mixedMoment B node2230 node2230Labels := by rfl

def raw21890 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![-1, 1], ![3, -3], ![1, -1]]
def raw21890Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21890step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![-1, 1], ![3, -3], ![1, -1]]
def raw21890step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21890step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![3, -3], ![1, -1]]
def raw21890step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21890step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw21890step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical21890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21890 raw21890Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw21890 raw21890Labels = mixedMoment B raw21890step0 raw21890step0Labels := by
      have hz : ∀ j, raw21890 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21890step0 = (fun i j => raw21890 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21890step0 raw21890; decide +kernel
      have hl : raw21890step0Labels = raw21890Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21890 raw21890Labels permutation346 hz
    mixedMoment B raw21890step0 raw21890step0Labels = mixedMoment B raw21890step1 raw21890step1Labels := by
      have hz : ∀ j, raw21890step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21890step1 = (fun i j => raw21890step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21890step1 raw21890step0; decide +kernel
      have hl : raw21890step1Labels = raw21890step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21890step0 raw21890step0Labels permutation56 hz
    mixedMoment B raw21890step1 raw21890step1Labels = mixedMoment B raw21890step2 raw21890step2Labels := by
      have ha : raw21890step2 = (fun i j => raw21890step1 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw21890step2 raw21890step1; decide +kernel
      have hl : raw21890step2Labels = raw21890step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21890step1 raw21890step1Labels permutation9 permutation0
    _ = mixedMoment B node4081 node4081Labels := by rfl

def raw21891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw21891Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21891step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw21891step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21891step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw21891step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21891 raw21891Labels = mixedMoment B node1001 node1001Labels := by
  calc
    mixedMoment B raw21891 raw21891Labels = mixedMoment B raw21891step0 raw21891step0Labels := by
      have hz : ∀ j, raw21891 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21891step0 = (fun i j => raw21891 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21891step0 raw21891; decide +kernel
      have hl : raw21891step0Labels = raw21891Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21891 raw21891Labels permutation346 hz
    mixedMoment B raw21891step0 raw21891step0Labels = mixedMoment B raw21891step1 raw21891step1Labels := by
      have ha : raw21891step1 = (fun i j => raw21891step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21891step1 raw21891step0; decide +kernel
      have hl : raw21891step1Labels = raw21891step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21891step0 raw21891step0Labels permutation38 permutation2
    _ = mixedMoment B node1001 node1001Labels := by rfl

def raw21892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw21892Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw21892step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21892step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw21892step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21892 raw21892Labels = mixedMoment B node1001 node1001Labels := by
  calc
    mixedMoment B raw21892 raw21892Labels = mixedMoment B raw21892step0 raw21892step0Labels := by
      have hz : ∀ j, raw21892 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21892step0 = (fun i j => raw21892 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21892step0 raw21892; decide +kernel
      have hl : raw21892step0Labels = raw21892Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21892 raw21892Labels permutation265 hz
    mixedMoment B raw21892step0 raw21892step0Labels = mixedMoment B raw21892step1 raw21892step1Labels := by
      have ha : raw21892step1 = (fun i j => raw21892step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21892step1 raw21892step0; decide +kernel
      have hl : raw21892step1Labels = raw21892step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21892step0 raw21892step0Labels permutation38 permutation2
    _ = mixedMoment B node1001 node1001Labels := by rfl

def raw21893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw21893Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21893step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw21893step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21893step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 2, -3], ![2, -1, -1]]
def raw21893step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21893 raw21893Labels = mixedMoment B node1076 node1076Labels := by
  calc
    mixedMoment B raw21893 raw21893Labels = mixedMoment B raw21893step0 raw21893step0Labels := by
      have hz : ∀ j, raw21893 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21893step0 = (fun i j => raw21893 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21893step0 raw21893; decide +kernel
      have hl : raw21893step0Labels = raw21893Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21893 raw21893Labels permutation346 hz
    mixedMoment B raw21893step0 raw21893step0Labels = mixedMoment B raw21893step1 raw21893step1Labels := by
      have hz : ∀ j, raw21893step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21893step1 = (fun i j => raw21893step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21893step1 raw21893step0; decide +kernel
      have hl : raw21893step1Labels = raw21893step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21893step0 raw21893step0Labels permutation56 hz
    _ = mixedMoment B node1076 node1076Labels := by rfl

def raw21894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3], ![2, -1, -1]]
def raw21894Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21894step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![2, 1, -3], ![2, -1, -1]]
def raw21894step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21894step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, 1, -3], ![2, -1, -1]]
def raw21894step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21894step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw21894step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21894 raw21894Labels = mixedMoment B node1012 node1012Labels := by
  calc
    mixedMoment B raw21894 raw21894Labels = mixedMoment B raw21894step0 raw21894step0Labels := by
      have hz : ∀ j, raw21894 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21894step0 = (fun i j => raw21894 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21894step0 raw21894; decide +kernel
      have hl : raw21894step0Labels = raw21894Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21894 raw21894Labels permutation346 hz
    mixedMoment B raw21894step0 raw21894step0Labels = mixedMoment B raw21894step1 raw21894step1Labels := by
      have hz : ∀ j, raw21894step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21894step1 = (fun i j => raw21894step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21894step1 raw21894step0; decide +kernel
      have hl : raw21894step1Labels = raw21894step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21894step0 raw21894step0Labels permutation56 hz
    mixedMoment B raw21894step1 raw21894step1Labels = mixedMoment B raw21894step2 raw21894step2Labels := by
      have ha : raw21894step2 = (fun i j => raw21894step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21894step2 raw21894step1; decide +kernel
      have hl : raw21894step2Labels = raw21894step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21894step1 raw21894step1Labels permutation9 permutation2
    _ = mixedMoment B node1012 node1012Labels := by rfl

def raw21895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21895Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21895step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21895step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21895step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21895step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21895 raw21895Labels = mixedMoment B node1009 node1009Labels := by
  calc
    mixedMoment B raw21895 raw21895Labels = mixedMoment B raw21895step0 raw21895step0Labels := by
      have hz : ∀ j, raw21895 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21895step0 = (fun i j => raw21895 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21895step0 raw21895; decide +kernel
      have hl : raw21895step0Labels = raw21895Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21895 raw21895Labels permutation346 hz
    mixedMoment B raw21895step0 raw21895step0Labels = mixedMoment B raw21895step1 raw21895step1Labels := by
      have hz : ∀ j, raw21895step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21895step1 = (fun i j => raw21895step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21895step1 raw21895step0; decide +kernel
      have hl : raw21895step1Labels = raw21895step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21895step0 raw21895step0Labels permutation56 hz
    _ = mixedMoment B node1009 node1009Labels := by rfl

def raw21896 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21896Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21896step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21896step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21896 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21896 raw21896Labels = mixedMoment B node2003 node2003Labels := by
  calc
    mixedMoment B raw21896 raw21896Labels = mixedMoment B raw21896step0 raw21896step0Labels := by
      have hz : ∀ j, raw21896 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21896step0 = (fun i j => raw21896 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21896step0 raw21896; decide +kernel
      have hl : raw21896step0Labels = raw21896Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21896 raw21896Labels permutation346 hz
    _ = mixedMoment B node2003 node2003Labels := by rfl

def raw21897 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21897Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21897step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21897step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21897 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21897 raw21897Labels = mixedMoment B node2003 node2003Labels := by
  calc
    mixedMoment B raw21897 raw21897Labels = mixedMoment B raw21897step0 raw21897step0Labels := by
      have hz : ∀ j, raw21897 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21897step0 = (fun i j => raw21897 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21897step0 raw21897; decide +kernel
      have hl : raw21897step0Labels = raw21897Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21897 raw21897Labels permutation265 hz
    _ = mixedMoment B node2003 node2003Labels := by rfl

def raw21898 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21898Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21898step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21898step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21898step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21898step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21898 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21898 raw21898Labels = mixedMoment B node1950 node1950Labels := by
  calc
    mixedMoment B raw21898 raw21898Labels = mixedMoment B raw21898step0 raw21898step0Labels := by
      have hz : ∀ j, raw21898 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21898step0 = (fun i j => raw21898 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21898step0 raw21898; decide +kernel
      have hl : raw21898step0Labels = raw21898Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21898 raw21898Labels permutation346 hz
    mixedMoment B raw21898step0 raw21898step0Labels = mixedMoment B raw21898step1 raw21898step1Labels := by
      have hz : ∀ j, raw21898step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21898step1 = (fun i j => raw21898step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21898step1 raw21898step0; decide +kernel
      have hl : raw21898step1Labels = raw21898step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21898step0 raw21898step0Labels permutation56 hz
    _ = mixedMoment B node1950 node1950Labels := by rfl

def raw21899 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw21899Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21899step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw21899step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21899step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw21899step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21899 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21899 raw21899Labels = mixedMoment B node2218 node2218Labels := by
  calc
    mixedMoment B raw21899 raw21899Labels = mixedMoment B raw21899step0 raw21899step0Labels := by
      have hz : ∀ j, raw21899 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21899step0 = (fun i j => raw21899 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21899step0 raw21899; decide +kernel
      have hl : raw21899step0Labels = raw21899Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21899 raw21899Labels permutation346 hz
    mixedMoment B raw21899step0 raw21899step0Labels = mixedMoment B raw21899step1 raw21899step1Labels := by
      have hz : ∀ j, raw21899step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21899step1 = (fun i j => raw21899step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21899step1 raw21899step0; decide +kernel
      have hl : raw21899step1Labels = raw21899step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21899step0 raw21899step0Labels permutation56 hz
    _ = mixedMoment B node2218 node2218Labels := by rfl

def raw21900 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw21900Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21900step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw21900step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21900step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw21900step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21900 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21900 raw21900Labels = mixedMoment B node2229 node2229Labels := by
  calc
    mixedMoment B raw21900 raw21900Labels = mixedMoment B raw21900step0 raw21900step0Labels := by
      have hz : ∀ j, raw21900 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21900step0 = (fun i j => raw21900 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21900step0 raw21900; decide +kernel
      have hl : raw21900step0Labels = raw21900Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21900 raw21900Labels permutation346 hz
    mixedMoment B raw21900step0 raw21900step0Labels = mixedMoment B raw21900step1 raw21900step1Labels := by
      have hz : ∀ j, raw21900step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21900step1 = (fun i j => raw21900step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21900step1 raw21900step0; decide +kernel
      have hl : raw21900step1Labels = raw21900step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21900step0 raw21900step0Labels permutation56 hz
    _ = mixedMoment B node2229 node2229Labels := by rfl

def raw21901 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![-1, 1], ![2, -2], ![2, -2]]
def raw21901Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21901step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![-1, 1], ![2, -2], ![2, -2]]
def raw21901step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21901step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw21901step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical21901 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21901 raw21901Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw21901 raw21901Labels = mixedMoment B raw21901step0 raw21901step0Labels := by
      have hz : ∀ j, raw21901 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21901step0 = (fun i j => raw21901 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21901step0 raw21901; decide +kernel
      have hl : raw21901step0Labels = raw21901Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21901 raw21901Labels permutation346 hz
    mixedMoment B raw21901step0 raw21901step0Labels = mixedMoment B raw21901step1 raw21901step1Labels := by
      have hz : ∀ j, raw21901step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21901step1 = (fun i j => raw21901step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21901step1 raw21901step0; decide +kernel
      have hl : raw21901step1Labels = raw21901step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21901step0 raw21901step0Labels permutation56 hz
    _ = mixedMoment B node4082 node4082Labels := by rfl

def raw21902 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21902Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21902step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21902step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21902step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw21902step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21902 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21902 raw21902Labels = mixedMoment B node881 node881Labels := by
  calc
    mixedMoment B raw21902 raw21902Labels = mixedMoment B raw21902step0 raw21902step0Labels := by
      have hz : ∀ j, raw21902 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21902step0 = (fun i j => raw21902 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21902step0 raw21902; decide +kernel
      have hl : raw21902step0Labels = raw21902Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21902 raw21902Labels permutation346 hz
    mixedMoment B raw21902step0 raw21902step0Labels = mixedMoment B raw21902step1 raw21902step1Labels := by
      have ha : raw21902step1 = (fun i j => raw21902step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21902step1 raw21902step0; decide +kernel
      have hl : raw21902step1Labels = raw21902step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21902step0 raw21902step0Labels permutation38 permutation2
    _ = mixedMoment B node881 node881Labels := by rfl

def raw21903 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21903Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21903step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -1, -2]]
def raw21903step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21903step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw21903step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21903 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21903 raw21903Labels = mixedMoment B node881 node881Labels := by
  calc
    mixedMoment B raw21903 raw21903Labels = mixedMoment B raw21903step0 raw21903step0Labels := by
      have hz : ∀ j, raw21903 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21903step0 = (fun i j => raw21903 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21903step0 raw21903; decide +kernel
      have hl : raw21903step0Labels = raw21903Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21903 raw21903Labels permutation265 hz
    mixedMoment B raw21903step0 raw21903step0Labels = mixedMoment B raw21903step1 raw21903step1Labels := by
      have ha : raw21903step1 = (fun i j => raw21903step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21903step1 raw21903step0; decide +kernel
      have hl : raw21903step1Labels = raw21903step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21903step0 raw21903step0Labels permutation38 permutation2
    _ = mixedMoment B node881 node881Labels := by rfl

def raw21904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -1, -2]]
def raw21904Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21904step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 0, 1], ![2, 0, -2], ![3, -1, -2]]
def raw21904step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21904step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, 0, -2], ![3, -1, -2]]
def raw21904step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21904 raw21904Labels = mixedMoment B node896 node896Labels := by
  calc
    mixedMoment B raw21904 raw21904Labels = mixedMoment B raw21904step0 raw21904step0Labels := by
      have hz : ∀ j, raw21904 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21904step0 = (fun i j => raw21904 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21904step0 raw21904; decide +kernel
      have hl : raw21904step0Labels = raw21904Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21904 raw21904Labels permutation346 hz
    mixedMoment B raw21904step0 raw21904step0Labels = mixedMoment B raw21904step1 raw21904step1Labels := by
      have hz : ∀ j, raw21904step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21904step1 = (fun i j => raw21904step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21904step1 raw21904step0; decide +kernel
      have hl : raw21904step1Labels = raw21904step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21904step0 raw21904step0Labels permutation56 hz
    _ = mixedMoment B node896 node896Labels := by rfl

def raw21905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw21905Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21905step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw21905step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21905step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![4, -2, -2]]
def raw21905step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21905 raw21905Labels = mixedMoment B node893 node893Labels := by
  calc
    mixedMoment B raw21905 raw21905Labels = mixedMoment B raw21905step0 raw21905step0Labels := by
      have hz : ∀ j, raw21905 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21905step0 = (fun i j => raw21905 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21905step0 raw21905; decide +kernel
      have hl : raw21905step0Labels = raw21905Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21905 raw21905Labels permutation346 hz
    mixedMoment B raw21905step0 raw21905step0Labels = mixedMoment B raw21905step1 raw21905step1Labels := by
      have hz : ∀ j, raw21905step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21905step1 = (fun i j => raw21905step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21905step1 raw21905step0; decide +kernel
      have hl : raw21905step1Labels = raw21905step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21905step0 raw21905step0Labels permutation56 hz
    _ = mixedMoment B node893 node893Labels := by rfl

def raw21906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw21906Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw21906step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21906step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw21906step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21906 raw21906Labels = mixedMoment B node576 node576Labels := by
  calc
    mixedMoment B raw21906 raw21906Labels = mixedMoment B raw21906step0 raw21906step0Labels := by
      have hz : ∀ j, raw21906 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21906step0 = (fun i j => raw21906 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21906step0 raw21906; decide +kernel
      have hl : raw21906step0Labels = raw21906Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21906 raw21906Labels permutation346 hz
    mixedMoment B raw21906step0 raw21906step0Labels = mixedMoment B raw21906step1 raw21906step1Labels := by
      have hz : ∀ j, raw21906step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21906step1 = (fun i j => raw21906step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21906step1 raw21906step0; decide +kernel
      have hl : raw21906step1Labels = raw21906step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21906step0 raw21906step0Labels permutation56 hz
    _ = mixedMoment B node576 node576Labels := by rfl

def raw21907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw21907Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21907step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw21907step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21907 raw21907Labels = mixedMoment B node903 node903Labels := by
  calc
    mixedMoment B raw21907 raw21907Labels = mixedMoment B raw21907step0 raw21907step0Labels := by
      have hz : ∀ j, raw21907 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21907step0 = (fun i j => raw21907 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21907step0 raw21907; decide +kernel
      have hl : raw21907step0Labels = raw21907Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21907 raw21907Labels permutation346 hz
    _ = mixedMoment B node903 node903Labels := by rfl

def raw21908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw21908Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21908step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw21908step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21908 raw21908Labels = mixedMoment B node903 node903Labels := by
  calc
    mixedMoment B raw21908 raw21908Labels = mixedMoment B raw21908step0 raw21908step0Labels := by
      have hz : ∀ j, raw21908 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21908step0 = (fun i j => raw21908 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21908step0 raw21908; decide +kernel
      have hl : raw21908step0Labels = raw21908Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21908 raw21908Labels permutation265 hz
    _ = mixedMoment B node903 node903Labels := by rfl

def raw21909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw21909Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21909step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw21909step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21909step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw21909step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21909 raw21909Labels = mixedMoment B node1013 node1013Labels := by
  calc
    mixedMoment B raw21909 raw21909Labels = mixedMoment B raw21909step0 raw21909step0Labels := by
      have hz : ∀ j, raw21909 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21909step0 = (fun i j => raw21909 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21909step0 raw21909; decide +kernel
      have hl : raw21909step0Labels = raw21909Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21909 raw21909Labels permutation346 hz
    mixedMoment B raw21909step0 raw21909step0Labels = mixedMoment B raw21909step1 raw21909step1Labels := by
      have hz : ∀ j, raw21909step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21909step1 = (fun i j => raw21909step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21909step1 raw21909step0; decide +kernel
      have hl : raw21909step1Labels = raw21909step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21909step0 raw21909step0Labels permutation56 hz
    _ = mixedMoment B node1013 node1013Labels := by rfl

def raw21910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw21910Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21910step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw21910step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21910step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw21910step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21910 raw21910Labels = mixedMoment B node1000 node1000Labels := by
  calc
    mixedMoment B raw21910 raw21910Labels = mixedMoment B raw21910step0 raw21910step0Labels := by
      have hz : ∀ j, raw21910 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21910step0 = (fun i j => raw21910 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21910step0 raw21910; decide +kernel
      have hl : raw21910step0Labels = raw21910Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21910 raw21910Labels permutation346 hz
    mixedMoment B raw21910step0 raw21910step0Labels = mixedMoment B raw21910step1 raw21910step1Labels := by
      have ha : raw21910step1 = (fun i j => raw21910step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21910step1 raw21910step0; decide +kernel
      have hl : raw21910step1Labels = raw21910step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21910step0 raw21910step0Labels permutation38 permutation2
    _ = mixedMoment B node1000 node1000Labels := by rfl

def raw21911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw21911Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21911step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw21911step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21911step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw21911step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21911 raw21911Labels = mixedMoment B node1000 node1000Labels := by
  calc
    mixedMoment B raw21911 raw21911Labels = mixedMoment B raw21911step0 raw21911step0Labels := by
      have hz : ∀ j, raw21911 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21911step0 = (fun i j => raw21911 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21911step0 raw21911; decide +kernel
      have hl : raw21911step0Labels = raw21911Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21911 raw21911Labels permutation265 hz
    mixedMoment B raw21911step0 raw21911step0Labels = mixedMoment B raw21911step1 raw21911step1Labels := by
      have ha : raw21911step1 = (fun i j => raw21911step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21911step1 raw21911step0; decide +kernel
      have hl : raw21911step1Labels = raw21911step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21911step0 raw21911step0Labels permutation38 permutation2
    _ = mixedMoment B node1000 node1000Labels := by rfl

def raw21912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw21912Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21912step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw21912step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21912step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw21912step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21912 raw21912Labels = mixedMoment B node1075 node1075Labels := by
  calc
    mixedMoment B raw21912 raw21912Labels = mixedMoment B raw21912step0 raw21912step0Labels := by
      have hz : ∀ j, raw21912 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21912step0 = (fun i j => raw21912 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21912step0 raw21912; decide +kernel
      have hl : raw21912step0Labels = raw21912Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21912 raw21912Labels permutation346 hz
    mixedMoment B raw21912step0 raw21912step0Labels = mixedMoment B raw21912step1 raw21912step1Labels := by
      have hz : ∀ j, raw21912step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21912step1 = (fun i j => raw21912step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21912step1 raw21912step0; decide +kernel
      have hl : raw21912step1Labels = raw21912step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21912step0 raw21912step0Labels permutation56 hz
    _ = mixedMoment B node1075 node1075Labels := by rfl

def raw21913 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw21913Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21913step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw21913step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21913step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![-2, -1, 3]]
def raw21913step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21913step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw21913step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21913 raw21913Labels = mixedMoment B node716 node716Labels := by
  calc
    mixedMoment B raw21913 raw21913Labels = mixedMoment B raw21913step0 raw21913step0Labels := by
      have hz : ∀ j, raw21913 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21913step0 = (fun i j => raw21913 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21913step0 raw21913; decide +kernel
      have hl : raw21913step0Labels = raw21913Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21913 raw21913Labels permutation265 hz
    mixedMoment B raw21913step0 raw21913step0Labels = mixedMoment B raw21913step1 raw21913step1Labels := by
      have ha : raw21913step1 = (fun i j => raw21913step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21913step1 raw21913step0; decide +kernel
      have hl : raw21913step1Labels = raw21913step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21913step0 raw21913step0Labels permutation38 permutation4
    mixedMoment B raw21913step1 raw21913step1Labels = mixedMoment B raw21913step2 raw21913step2Labels := by
      have ha : raw21913step2 = -raw21913step1 := by apply Matrix.ext; change ∀ i j, raw21913step2 i j = -(raw21913step1 i j); unfold raw21913step2 raw21913step1; decide +kernel
      have hl : raw21913step2Labels = raw21913step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node716 node716Labels := by rfl

def raw21914 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw21914Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21914step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw21914step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21914step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw21914step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21914step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 4, -4], ![1, -2, 1], ![-1, -2, 3]]
def raw21914step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21914step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, 0, -4], ![-2, 1, 1], ![-2, -1, 3]]
def raw21914step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21914step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 0, 4], ![2, -1, -1], ![2, 1, -3]]
def raw21914step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21914 raw21914Labels = mixedMoment B node863 node863Labels := by
  calc
    mixedMoment B raw21914 raw21914Labels = mixedMoment B raw21914step0 raw21914step0Labels := by
      have hz : ∀ j, raw21914 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21914step0 = (fun i j => raw21914 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21914step0 raw21914; decide +kernel
      have hl : raw21914step0Labels = raw21914Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21914 raw21914Labels permutation434 hz
    mixedMoment B raw21914step0 raw21914step0Labels = mixedMoment B raw21914step1 raw21914step1Labels := by
      have hz : ∀ j, raw21914step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21914step1 = (fun i j => raw21914step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21914step1 raw21914step0; decide +kernel
      have hl : raw21914step1Labels = raw21914step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21914step0 raw21914step0Labels permutation80 hz
    mixedMoment B raw21914step1 raw21914step1Labels = mixedMoment B raw21914step2 raw21914step2Labels := by
      have hz : ∀ j, raw21914step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21914step2 = (fun i j => raw21914step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21914step2 raw21914step1; decide +kernel
      have hl : raw21914step2Labels = raw21914step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21914step1 raw21914step1Labels permutation14 hz
    mixedMoment B raw21914step2 raw21914step2Labels = mixedMoment B raw21914step3 raw21914step3Labels := by
      have ha : raw21914step3 = (fun i j => raw21914step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21914step3 raw21914step2; decide +kernel
      have hl : raw21914step3Labels = raw21914step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21914step2 raw21914step2Labels permutation2 permutation4
    mixedMoment B raw21914step3 raw21914step3Labels = mixedMoment B raw21914step4 raw21914step4Labels := by
      have ha : raw21914step4 = -raw21914step3 := by apply Matrix.ext; change ∀ i j, raw21914step4 i j = -(raw21914step3 i j); unfold raw21914step4 raw21914step3; decide +kernel
      have hl : raw21914step4Labels = raw21914step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node863 node863Labels := by rfl

def raw21915 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -2, 3]]
def raw21915Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21915step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![-1, -2, 3]]
def raw21915step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21915step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![2, -3, 1], ![-1, -2, 3]]
def raw21915step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21915step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-2, -1, 3], ![-3, 2, 1]]
def raw21915step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21915step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw21915step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21915 raw21915Labels = mixedMoment B node729 node729Labels := by
  calc
    mixedMoment B raw21915 raw21915Labels = mixedMoment B raw21915step0 raw21915step0Labels := by
      have hz : ∀ j, raw21915 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21915step0 = (fun i j => raw21915 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21915step0 raw21915; decide +kernel
      have hl : raw21915step0Labels = raw21915Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21915 raw21915Labels permutation346 hz
    mixedMoment B raw21915step0 raw21915step0Labels = mixedMoment B raw21915step1 raw21915step1Labels := by
      have hz : ∀ j, raw21915step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21915step1 = (fun i j => raw21915step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21915step1 raw21915step0; decide +kernel
      have hl : raw21915step1Labels = raw21915step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21915step0 raw21915step0Labels permutation56 hz
    mixedMoment B raw21915step1 raw21915step1Labels = mixedMoment B raw21915step2 raw21915step2Labels := by
      have ha : raw21915step2 = (fun i j => raw21915step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21915step2 raw21915step1; decide +kernel
      have hl : raw21915step2Labels = raw21915step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21915step1 raw21915step1Labels permutation9 permutation4
    mixedMoment B raw21915step2 raw21915step2Labels = mixedMoment B raw21915step3 raw21915step3Labels := by
      have ha : raw21915step3 = -raw21915step2 := by apply Matrix.ext; change ∀ i j, raw21915step3 i j = -(raw21915step2 i j); unfold raw21915step3 raw21915step2; decide +kernel
      have hl : raw21915step3Labels = raw21915step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node729 node729Labels := by rfl

def raw21916 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -3, 3]]
def raw21916Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21916step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -3, 3]]
def raw21916step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21916step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![1, -2, 1], ![0, -3, 3]]
def raw21916step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21916step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-2, 1, 1], ![-3, 0, 3]]
def raw21916step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21916step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, -1, -1], ![3, 0, -3]]
def raw21916step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21916 raw21916Labels = mixedMoment B node728 node728Labels := by
  calc
    mixedMoment B raw21916 raw21916Labels = mixedMoment B raw21916step0 raw21916step0Labels := by
      have hz : ∀ j, raw21916 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21916step0 = (fun i j => raw21916 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21916step0 raw21916; decide +kernel
      have hl : raw21916step0Labels = raw21916Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21916 raw21916Labels permutation346 hz
    mixedMoment B raw21916step0 raw21916step0Labels = mixedMoment B raw21916step1 raw21916step1Labels := by
      have hz : ∀ j, raw21916step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21916step1 = (fun i j => raw21916step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21916step1 raw21916step0; decide +kernel
      have hl : raw21916step1Labels = raw21916step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21916step0 raw21916step0Labels permutation56 hz
    mixedMoment B raw21916step1 raw21916step1Labels = mixedMoment B raw21916step2 raw21916step2Labels := by
      have ha : raw21916step2 = (fun i j => raw21916step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21916step2 raw21916step1; decide +kernel
      have hl : raw21916step2Labels = raw21916step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21916step1 raw21916step1Labels permutation8 permutation4
    mixedMoment B raw21916step2 raw21916step2Labels = mixedMoment B raw21916step3 raw21916step3Labels := by
      have ha : raw21916step3 = -raw21916step2 := by apply Matrix.ext; change ∀ i j, raw21916step3 i j = -(raw21916step2 i j); unfold raw21916step3 raw21916step2; decide +kernel
      have hl : raw21916step3Labels = raw21916step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node728 node728Labels := by rfl

def raw21917 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -3, 3]]
def raw21917Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21917step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -3, 3]]
def raw21917step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21917step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-3, 0, 3]]
def raw21917step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21917step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![3, 0, -3]]
def raw21917step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21917 raw21917Labels = mixedMoment B node1584 node1584Labels := by
  calc
    mixedMoment B raw21917 raw21917Labels = mixedMoment B raw21917step0 raw21917step0Labels := by
      have hz : ∀ j, raw21917 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21917step0 = (fun i j => raw21917 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21917step0 raw21917; decide +kernel
      have hl : raw21917step0Labels = raw21917Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21917 raw21917Labels permutation346 hz
    mixedMoment B raw21917step0 raw21917step0Labels = mixedMoment B raw21917step1 raw21917step1Labels := by
      have ha : raw21917step1 = (fun i j => raw21917step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21917step1 raw21917step0; decide +kernel
      have hl : raw21917step1Labels = raw21917step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21917step0 raw21917step0Labels permutation32 permutation4
    mixedMoment B raw21917step1 raw21917step1Labels = mixedMoment B raw21917step2 raw21917step2Labels := by
      have ha : raw21917step2 = -raw21917step1 := by apply Matrix.ext; change ∀ i j, raw21917step2 i j = -(raw21917step1 i j); unfold raw21917step2 raw21917step1; decide +kernel
      have hl : raw21917step2Labels = raw21917step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1584 node1584Labels := by rfl

def raw21918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21918Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21918step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21918step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21918step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw21918step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21918step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21918step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21918 raw21918Labels = mixedMoment B node4738 node4738Labels := by
  calc
    mixedMoment B raw21918 raw21918Labels = mixedMoment B raw21918step0 raw21918step0Labels := by
      have hz : ∀ j, raw21918 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21918step0 = (fun i j => raw21918 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21918step0 raw21918; decide +kernel
      have hl : raw21918step0Labels = raw21918Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21918 raw21918Labels permutation346 hz
    mixedMoment B raw21918step0 raw21918step0Labels = mixedMoment B raw21918step1 raw21918step1Labels := by
      have ha : raw21918step1 = (fun i j => raw21918step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21918step1 raw21918step0; decide +kernel
      have hl : raw21918step1Labels = raw21918step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21918step0 raw21918step0Labels permutation151 permutation2
    mixedMoment B raw21918step1 raw21918step1Labels = mixedMoment B raw21918step2 raw21918step2Labels := by
      have ha : raw21918step2 = -raw21918step1 := by apply Matrix.ext; change ∀ i j, raw21918step2 i j = -(raw21918step1 i j); unfold raw21918step2 raw21918step1; decide +kernel
      have hl : raw21918step2Labels = raw21918step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4738 node4738Labels := by rfl

def raw21919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21919Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21919step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21919step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21919step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw21919step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21919step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21919step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21919 raw21919Labels = mixedMoment B node4738 node4738Labels := by
  calc
    mixedMoment B raw21919 raw21919Labels = mixedMoment B raw21919step0 raw21919step0Labels := by
      have hz : ∀ j, raw21919 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21919step0 = (fun i j => raw21919 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21919step0 raw21919; decide +kernel
      have hl : raw21919step0Labels = raw21919Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21919 raw21919Labels permutation265 hz
    mixedMoment B raw21919step0 raw21919step0Labels = mixedMoment B raw21919step1 raw21919step1Labels := by
      have ha : raw21919step1 = (fun i j => raw21919step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21919step1 raw21919step0; decide +kernel
      have hl : raw21919step1Labels = raw21919step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21919step0 raw21919step0Labels permutation151 permutation2
    mixedMoment B raw21919step1 raw21919step1Labels = mixedMoment B raw21919step2 raw21919step2Labels := by
      have ha : raw21919step2 = -raw21919step1 := by apply Matrix.ext; change ∀ i j, raw21919step2 i j = -(raw21919step1 i j); unfold raw21919step2 raw21919step1; decide +kernel
      have hl : raw21919step2Labels = raw21919step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4738 node4738Labels := by rfl

def raw21920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21920Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21920step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21920step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21920step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21920step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21920step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw21920step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw21920step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw21920step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical21920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21920 raw21920Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw21920 raw21920Labels = mixedMoment B raw21920step0 raw21920step0Labels := by
      have hz : ∀ j, raw21920 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21920step0 = (fun i j => raw21920 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21920step0 raw21920; decide +kernel
      have hl : raw21920step0Labels = raw21920Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21920 raw21920Labels permutation346 hz
    mixedMoment B raw21920step0 raw21920step0Labels = mixedMoment B raw21920step1 raw21920step1Labels := by
      have hz : ∀ j, raw21920step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21920step1 = (fun i j => raw21920step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21920step1 raw21920step0; decide +kernel
      have hl : raw21920step1Labels = raw21920step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21920step0 raw21920step0Labels permutation56 hz
    mixedMoment B raw21920step1 raw21920step1Labels = mixedMoment B raw21920step2 raw21920step2Labels := by
      have hz : ∀ i, raw21920step1 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw21920step2 = (fun i j => raw21920step1 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw21920step2 raw21920step1; decide +kernel
      have hl : raw21920step2Labels = (fun j => raw21920step1Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw21920step1 raw21920step1Labels permutation4 hz
    mixedMoment B raw21920step2 raw21920step2Labels = mixedMoment B raw21920step3 raw21920step3Labels := by
      have ha : raw21920step3 = raw21920step2 := by apply Matrix.ext; unfold raw21920step3 raw21920step2; decide +kernel
      have hl : raw21920step2Labels = labelEmbedding2 ∘ raw21920step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21920step2 raw21920step2Labels raw21920step3Labels labelEmbedding2 hl
    _ = mixedMoment B node4081 node4081Labels := by rfl

def raw21921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21921Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21921step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21921step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21921step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21921step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21921step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw21921step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21921step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21921 raw21921Labels = mixedMoment B node4837 node4837Labels := by
  calc
    mixedMoment B raw21921 raw21921Labels = mixedMoment B raw21921step0 raw21921step0Labels := by
      have hz : ∀ j, raw21921 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21921step0 = (fun i j => raw21921 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21921step0 raw21921; decide +kernel
      have hl : raw21921step0Labels = raw21921Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21921 raw21921Labels permutation346 hz
    mixedMoment B raw21921step0 raw21921step0Labels = mixedMoment B raw21921step1 raw21921step1Labels := by
      have hz : ∀ j, raw21921step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21921step1 = (fun i j => raw21921step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21921step1 raw21921step0; decide +kernel
      have hl : raw21921step1Labels = raw21921step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21921step0 raw21921step0Labels permutation56 hz
    mixedMoment B raw21921step1 raw21921step1Labels = mixedMoment B raw21921step2 raw21921step2Labels := by
      have ha : raw21921step2 = (fun i j => raw21921step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21921step2 raw21921step1; decide +kernel
      have hl : raw21921step2Labels = raw21921step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21921step1 raw21921step1Labels permutation31 permutation7
    mixedMoment B raw21921step2 raw21921step2Labels = mixedMoment B raw21921step3 raw21921step3Labels := by
      have ha : raw21921step3 = raw21921step2 := by apply Matrix.ext; unfold raw21921step3 raw21921step2; decide +kernel
      have hl : raw21921step2Labels = labelEmbedding10 ∘ raw21921step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21921step2 raw21921step2Labels raw21921step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4837 node4837Labels := by rfl

def raw21922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21922Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21922step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21922step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21922step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21922step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21922step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw21922step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw21922step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21922step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw21922step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21922step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21922 raw21922Labels = mixedMoment B node4841 node4841Labels := by
  calc
    mixedMoment B raw21922 raw21922Labels = mixedMoment B raw21922step0 raw21922step0Labels := by
      have hz : ∀ j, raw21922 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21922step0 = (fun i j => raw21922 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21922step0 raw21922; decide +kernel
      have hl : raw21922step0Labels = raw21922Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21922 raw21922Labels permutation346 hz
    mixedMoment B raw21922step0 raw21922step0Labels = mixedMoment B raw21922step1 raw21922step1Labels := by
      have hz : ∀ j, raw21922step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21922step1 = (fun i j => raw21922step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21922step1 raw21922step0; decide +kernel
      have hl : raw21922step1Labels = raw21922step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21922step0 raw21922step0Labels permutation56 hz
    mixedMoment B raw21922step1 raw21922step1Labels = mixedMoment B raw21922step2 raw21922step2Labels := by
      have ha : raw21922step2 = (fun i j => raw21922step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21922step2 raw21922step1; decide +kernel
      have hl : raw21922step2Labels = raw21922step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21922step1 raw21922step1Labels permutation8 permutation7
    mixedMoment B raw21922step2 raw21922step2Labels = mixedMoment B raw21922step3 raw21922step3Labels := by
      have ha : raw21922step3 = -raw21922step2 := by apply Matrix.ext; change ∀ i j, raw21922step3 i j = -(raw21922step2 i j); unfold raw21922step3 raw21922step2; decide +kernel
      have hl : raw21922step3Labels = raw21922step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21922step3 raw21922step3Labels = mixedMoment B raw21922step4 raw21922step4Labels := by
      have ha : raw21922step4 = raw21922step3 := by apply Matrix.ext; unfold raw21922step4 raw21922step3; decide +kernel
      have hl : raw21922step3Labels = labelEmbedding10 ∘ raw21922step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21922step3 raw21922step3Labels raw21922step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4841 node4841Labels := by rfl

def raw21923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21923Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21923step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21923step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21923step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw21923step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21923 raw21923Labels = mixedMoment B node4140 node4140Labels := by
  calc
    mixedMoment B raw21923 raw21923Labels = mixedMoment B raw21923step0 raw21923step0Labels := by
      have hz : ∀ j, raw21923 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21923step0 = (fun i j => raw21923 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21923step0 raw21923; decide +kernel
      have hl : raw21923step0Labels = raw21923Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21923 raw21923Labels permutation346 hz
    mixedMoment B raw21923step0 raw21923step0Labels = mixedMoment B raw21923step1 raw21923step1Labels := by
      have ha : raw21923step1 = (fun i j => raw21923step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21923step1 raw21923step0; decide +kernel
      have hl : raw21923step1Labels = raw21923step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21923step0 raw21923step0Labels permutation38 permutation2
    _ = mixedMoment B node4140 node4140Labels := by rfl

def raw21924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21924Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21924step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw21924step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21924 raw21924Labels = mixedMoment B node4320 node4320Labels := by
  calc
    mixedMoment B raw21924 raw21924Labels = mixedMoment B raw21924step0 raw21924step0Labels := by
      have ha : raw21924step0 = (fun i j => raw21924 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21924step0 raw21924; decide +kernel
      have hl : raw21924step0Labels = raw21924Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21924 raw21924Labels permutation182 permutation2
    _ = mixedMoment B node4320 node4320Labels := by rfl

def raw21925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21925Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21925step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21925step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21925step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw21925step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21925 raw21925Labels = mixedMoment B node4302 node4302Labels := by
  calc
    mixedMoment B raw21925 raw21925Labels = mixedMoment B raw21925step0 raw21925step0Labels := by
      have hz : ∀ j, raw21925 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21925step0 = (fun i j => raw21925 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21925step0 raw21925; decide +kernel
      have hl : raw21925step0Labels = raw21925Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21925 raw21925Labels permutation346 hz
    mixedMoment B raw21925step0 raw21925step0Labels = mixedMoment B raw21925step1 raw21925step1Labels := by
      have ha : raw21925step1 = (fun i j => raw21925step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21925step1 raw21925step0; decide +kernel
      have hl : raw21925step1Labels = raw21925step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21925step0 raw21925step0Labels permutation38 permutation2
    _ = mixedMoment B node4302 node4302Labels := by rfl

def raw21926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21926Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21926step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21926step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21926step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21926 raw21926Labels = mixedMoment B node4398 node4398Labels := by
  calc
    mixedMoment B raw21926 raw21926Labels = mixedMoment B raw21926step0 raw21926step0Labels := by
      have hz : ∀ j, raw21926 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21926step0 = (fun i j => raw21926 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21926step0 raw21926; decide +kernel
      have hl : raw21926step0Labels = raw21926Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21926 raw21926Labels permutation346 hz
    mixedMoment B raw21926step0 raw21926step0Labels = mixedMoment B raw21926step1 raw21926step1Labels := by
      have ha : raw21926step1 = (fun i j => raw21926step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21926step1 raw21926step0; decide +kernel
      have hl : raw21926step1Labels = raw21926step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21926step0 raw21926step0Labels permutation40 permutation2
    _ = mixedMoment B node4398 node4398Labels := by rfl

def raw21927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21927Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21927step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21927step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21927step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw21927step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21927 raw21927Labels = mixedMoment B node4418 node4418Labels := by
  calc
    mixedMoment B raw21927 raw21927Labels = mixedMoment B raw21927step0 raw21927step0Labels := by
      have hz : ∀ j, raw21927 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21927step0 = (fun i j => raw21927 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21927step0 raw21927; decide +kernel
      have hl : raw21927step0Labels = raw21927Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21927 raw21927Labels permutation346 hz
    mixedMoment B raw21927step0 raw21927step0Labels = mixedMoment B raw21927step1 raw21927step1Labels := by
      have ha : raw21927step1 = (fun i j => raw21927step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21927step1 raw21927step0; decide +kernel
      have hl : raw21927step1Labels = raw21927step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21927step0 raw21927step0Labels permutation38 permutation2
    _ = mixedMoment B node4418 node4418Labels := by rfl

def raw21928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21928Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21928step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21928step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21928step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw21928step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21928 raw21928Labels = mixedMoment B node4140 node4140Labels := by
  calc
    mixedMoment B raw21928 raw21928Labels = mixedMoment B raw21928step0 raw21928step0Labels := by
      have hz : ∀ j, raw21928 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21928step0 = (fun i j => raw21928 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21928step0 raw21928; decide +kernel
      have hl : raw21928step0Labels = raw21928Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21928 raw21928Labels permutation265 hz
    mixedMoment B raw21928step0 raw21928step0Labels = mixedMoment B raw21928step1 raw21928step1Labels := by
      have ha : raw21928step1 = (fun i j => raw21928step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21928step1 raw21928step0; decide +kernel
      have hl : raw21928step1Labels = raw21928step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21928step0 raw21928step0Labels permutation38 permutation2
    _ = mixedMoment B node4140 node4140Labels := by rfl

def raw21929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21929Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21929step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw21929step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21929 raw21929Labels = mixedMoment B node4320 node4320Labels := by
  calc
    mixedMoment B raw21929 raw21929Labels = mixedMoment B raw21929step0 raw21929step0Labels := by
      have ha : raw21929step0 = (fun i j => raw21929 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21929step0 raw21929; decide +kernel
      have hl : raw21929step0Labels = raw21929Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21929 raw21929Labels permutation158 permutation2
    _ = mixedMoment B node4320 node4320Labels := by rfl

def raw21930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21930Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21930step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21930step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21930step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw21930step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21930 raw21930Labels = mixedMoment B node4302 node4302Labels := by
  calc
    mixedMoment B raw21930 raw21930Labels = mixedMoment B raw21930step0 raw21930step0Labels := by
      have hz : ∀ j, raw21930 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21930step0 = (fun i j => raw21930 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21930step0 raw21930; decide +kernel
      have hl : raw21930step0Labels = raw21930Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21930 raw21930Labels permutation265 hz
    mixedMoment B raw21930step0 raw21930step0Labels = mixedMoment B raw21930step1 raw21930step1Labels := by
      have ha : raw21930step1 = (fun i j => raw21930step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21930step1 raw21930step0; decide +kernel
      have hl : raw21930step1Labels = raw21930step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21930step0 raw21930step0Labels permutation38 permutation2
    _ = mixedMoment B node4302 node4302Labels := by rfl

def raw21931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21931Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21931step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21931step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21931step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21931 raw21931Labels = mixedMoment B node4398 node4398Labels := by
  calc
    mixedMoment B raw21931 raw21931Labels = mixedMoment B raw21931step0 raw21931step0Labels := by
      have hz : ∀ j, raw21931 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21931step0 = (fun i j => raw21931 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21931step0 raw21931; decide +kernel
      have hl : raw21931step0Labels = raw21931Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21931 raw21931Labels permutation265 hz
    mixedMoment B raw21931step0 raw21931step0Labels = mixedMoment B raw21931step1 raw21931step1Labels := by
      have ha : raw21931step1 = (fun i j => raw21931step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21931step1 raw21931step0; decide +kernel
      have hl : raw21931step1Labels = raw21931step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21931step0 raw21931step0Labels permutation40 permutation2
    _ = mixedMoment B node4398 node4398Labels := by rfl

def raw21932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21932Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21932step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21932step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21932step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw21932step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21932 raw21932Labels = mixedMoment B node4418 node4418Labels := by
  calc
    mixedMoment B raw21932 raw21932Labels = mixedMoment B raw21932step0 raw21932step0Labels := by
      have hz : ∀ j, raw21932 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21932step0 = (fun i j => raw21932 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21932step0 raw21932; decide +kernel
      have hl : raw21932step0Labels = raw21932Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21932 raw21932Labels permutation265 hz
    mixedMoment B raw21932step0 raw21932step0Labels = mixedMoment B raw21932step1 raw21932step1Labels := by
      have ha : raw21932step1 = (fun i j => raw21932step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21932step1 raw21932step0; decide +kernel
      have hl : raw21932step1Labels = raw21932step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21932step0 raw21932step0Labels permutation38 permutation2
    _ = mixedMoment B node4418 node4418Labels := by rfl

def raw21933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21933Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21933step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21933step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21933step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21933step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21933 raw21933Labels = mixedMoment B node4166 node4166Labels := by
  calc
    mixedMoment B raw21933 raw21933Labels = mixedMoment B raw21933step0 raw21933step0Labels := by
      have hz : ∀ j, raw21933 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21933step0 = (fun i j => raw21933 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21933step0 raw21933; decide +kernel
      have hl : raw21933step0Labels = raw21933Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21933 raw21933Labels permutation346 hz
    mixedMoment B raw21933step0 raw21933step0Labels = mixedMoment B raw21933step1 raw21933step1Labels := by
      have hz : ∀ j, raw21933step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21933step1 = (fun i j => raw21933step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21933step1 raw21933step0; decide +kernel
      have hl : raw21933step1Labels = raw21933step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21933step0 raw21933step0Labels permutation56 hz
    _ = mixedMoment B node4166 node4166Labels := by rfl

def raw21934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21934Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21934step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21934step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21934 raw21934Labels = mixedMoment B node4338 node4338Labels := by
  calc
    mixedMoment B raw21934 raw21934Labels = mixedMoment B raw21934step0 raw21934step0Labels := by
      have hz : ∀ j, raw21934 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21934step0 = (fun i j => raw21934 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21934step0 raw21934; decide +kernel
      have hl : raw21934step0Labels = raw21934Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21934 raw21934Labels permutation346 hz
    _ = mixedMoment B node4338 node4338Labels := by rfl

def raw21935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21935Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21935step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21935step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21935 raw21935Labels = mixedMoment B node4338 node4338Labels := by
  calc
    mixedMoment B raw21935 raw21935Labels = mixedMoment B raw21935step0 raw21935step0Labels := by
      have hz : ∀ j, raw21935 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21935step0 = (fun i j => raw21935 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21935step0 raw21935; decide +kernel
      have hl : raw21935step0Labels = raw21935Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21935 raw21935Labels permutation265 hz
    _ = mixedMoment B node4338 node4338Labels := by rfl

def raw21936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21936Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21936step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21936step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21936step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21936step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw21936step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21936 raw21936Labels = mixedMoment B node4454 node4454Labels := by
  calc
    mixedMoment B raw21936 raw21936Labels = mixedMoment B raw21936step0 raw21936step0Labels := by
      have hz : ∀ j, raw21936 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21936step0 = (fun i j => raw21936 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21936step0 raw21936; decide +kernel
      have hl : raw21936step0Labels = raw21936Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21936 raw21936Labels permutation346 hz
    mixedMoment B raw21936step0 raw21936step0Labels = mixedMoment B raw21936step1 raw21936step1Labels := by
      have hz : ∀ j, raw21936step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21936step1 = (fun i j => raw21936step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21936step1 raw21936step0; decide +kernel
      have hl : raw21936step1Labels = raw21936step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21936step0 raw21936step0Labels permutation56 hz
    mixedMoment B raw21936step1 raw21936step1Labels = mixedMoment B raw21936step2 raw21936step2Labels := by
      have ha : raw21936step2 = (fun i j => raw21936step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21936step2 raw21936step1; decide +kernel
      have hl : raw21936step2Labels = raw21936step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21936step1 raw21936step1Labels permutation10 permutation2
    _ = mixedMoment B node4454 node4454Labels := by rfl

def raw21937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21937Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21937step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21937step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21937step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21937step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21937 raw21937Labels = mixedMoment B node4490 node4490Labels := by
  calc
    mixedMoment B raw21937 raw21937Labels = mixedMoment B raw21937step0 raw21937step0Labels := by
      have hz : ∀ j, raw21937 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21937step0 = (fun i j => raw21937 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21937step0 raw21937; decide +kernel
      have hl : raw21937step0Labels = raw21937Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21937 raw21937Labels permutation346 hz
    mixedMoment B raw21937step0 raw21937step0Labels = mixedMoment B raw21937step1 raw21937step1Labels := by
      have hz : ∀ j, raw21937step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21937step1 = (fun i j => raw21937step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21937step1 raw21937step0; decide +kernel
      have hl : raw21937step1Labels = raw21937step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21937step0 raw21937step0Labels permutation56 hz
    _ = mixedMoment B node4490 node4490Labels := by rfl

def raw21938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21938Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21938step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21938step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21938step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21938step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21938 raw21938Labels = mixedMoment B node4147 node4147Labels := by
  calc
    mixedMoment B raw21938 raw21938Labels = mixedMoment B raw21938step0 raw21938step0Labels := by
      have hz : ∀ j, raw21938 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21938step0 = (fun i j => raw21938 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21938step0 raw21938; decide +kernel
      have hl : raw21938step0Labels = raw21938Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21938 raw21938Labels permutation346 hz
    mixedMoment B raw21938step0 raw21938step0Labels = mixedMoment B raw21938step1 raw21938step1Labels := by
      have hz : ∀ j, raw21938step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21938step1 = (fun i j => raw21938step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21938step1 raw21938step0; decide +kernel
      have hl : raw21938step1Labels = raw21938step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21938step0 raw21938step0Labels permutation56 hz
    _ = mixedMoment B node4147 node4147Labels := by rfl

def raw21939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21939Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21939step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21939step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21939 raw21939Labels = mixedMoment B node4324 node4324Labels := by
  calc
    mixedMoment B raw21939 raw21939Labels = mixedMoment B raw21939step0 raw21939step0Labels := by
      have hz : ∀ j, raw21939 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21939step0 = (fun i j => raw21939 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21939step0 raw21939; decide +kernel
      have hl : raw21939step0Labels = raw21939Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21939 raw21939Labels permutation346 hz
    _ = mixedMoment B node4324 node4324Labels := by rfl

def raw21940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21940Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21940step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21940step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21940 raw21940Labels = mixedMoment B node4324 node4324Labels := by
  calc
    mixedMoment B raw21940 raw21940Labels = mixedMoment B raw21940step0 raw21940step0Labels := by
      have hz : ∀ j, raw21940 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21940step0 = (fun i j => raw21940 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21940step0 raw21940; decide +kernel
      have hl : raw21940step0Labels = raw21940Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21940 raw21940Labels permutation265 hz
    _ = mixedMoment B node4324 node4324Labels := by rfl

def raw21941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21941Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21941step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21941step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21941step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21941step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21941 raw21941Labels = mixedMoment B node4317 node4317Labels := by
  calc
    mixedMoment B raw21941 raw21941Labels = mixedMoment B raw21941step0 raw21941step0Labels := by
      have hz : ∀ j, raw21941 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21941step0 = (fun i j => raw21941 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21941step0 raw21941; decide +kernel
      have hl : raw21941step0Labels = raw21941Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21941 raw21941Labels permutation346 hz
    mixedMoment B raw21941step0 raw21941step0Labels = mixedMoment B raw21941step1 raw21941step1Labels := by
      have hz : ∀ j, raw21941step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21941step1 = (fun i j => raw21941step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21941step1 raw21941step0; decide +kernel
      have hl : raw21941step1Labels = raw21941step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21941step0 raw21941step0Labels permutation56 hz
    _ = mixedMoment B node4317 node4317Labels := by rfl

def raw21942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw21942Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21942step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw21942step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21942step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw21942step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21942 raw21942Labels = mixedMoment B node4431 node4431Labels := by
  calc
    mixedMoment B raw21942 raw21942Labels = mixedMoment B raw21942step0 raw21942step0Labels := by
      have hz : ∀ j, raw21942 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21942step0 = (fun i j => raw21942 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21942step0 raw21942; decide +kernel
      have hl : raw21942step0Labels = raw21942Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21942 raw21942Labels permutation346 hz
    mixedMoment B raw21942step0 raw21942step0Labels = mixedMoment B raw21942step1 raw21942step1Labels := by
      have hz : ∀ j, raw21942step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21942step1 = (fun i j => raw21942step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21942step1 raw21942step0; decide +kernel
      have hl : raw21942step1Labels = raw21942step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21942step0 raw21942step0Labels permutation56 hz
    _ = mixedMoment B node4431 node4431Labels := by rfl

def raw21943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21943Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21943step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21943step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21943step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21943step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21943 raw21943Labels = mixedMoment B node4146 node4146Labels := by
  calc
    mixedMoment B raw21943 raw21943Labels = mixedMoment B raw21943step0 raw21943step0Labels := by
      have hz : ∀ j, raw21943 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21943step0 = (fun i j => raw21943 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21943step0 raw21943; decide +kernel
      have hl : raw21943step0Labels = raw21943Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21943 raw21943Labels permutation346 hz
    mixedMoment B raw21943step0 raw21943step0Labels = mixedMoment B raw21943step1 raw21943step1Labels := by
      have hz : ∀ j, raw21943step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21943step1 = (fun i j => raw21943step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21943step1 raw21943step0; decide +kernel
      have hl : raw21943step1Labels = raw21943step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21943step0 raw21943step0Labels permutation56 hz
    _ = mixedMoment B node4146 node4146Labels := by rfl

def raw21944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21944Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21944step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21944step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21944step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw21944step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21944step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw21944step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21944 raw21944Labels = mixedMoment B node4289 node4289Labels := by
  calc
    mixedMoment B raw21944 raw21944Labels = mixedMoment B raw21944step0 raw21944step0Labels := by
      have hz : ∀ j, raw21944 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21944step0 = (fun i j => raw21944 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21944step0 raw21944; decide +kernel
      have hl : raw21944step0Labels = raw21944Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21944 raw21944Labels permutation346 hz
    mixedMoment B raw21944step0 raw21944step0Labels = mixedMoment B raw21944step1 raw21944step1Labels := by
      have ha : raw21944step1 = (fun i j => raw21944step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21944step1 raw21944step0; decide +kernel
      have hl : raw21944step1Labels = raw21944step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21944step0 raw21944step0Labels permutation151 permutation2
    mixedMoment B raw21944step1 raw21944step1Labels = mixedMoment B raw21944step2 raw21944step2Labels := by
      have ha : raw21944step2 = -raw21944step1 := by apply Matrix.ext; change ∀ i j, raw21944step2 i j = -(raw21944step1 i j); unfold raw21944step2 raw21944step1; decide +kernel
      have hl : raw21944step2Labels = raw21944step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4289 node4289Labels := by rfl

def raw21945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21945Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21945step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21945step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21945step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw21945step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21945step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw21945step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21945 raw21945Labels = mixedMoment B node4289 node4289Labels := by
  calc
    mixedMoment B raw21945 raw21945Labels = mixedMoment B raw21945step0 raw21945step0Labels := by
      have hz : ∀ j, raw21945 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21945step0 = (fun i j => raw21945 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21945step0 raw21945; decide +kernel
      have hl : raw21945step0Labels = raw21945Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21945 raw21945Labels permutation265 hz
    mixedMoment B raw21945step0 raw21945step0Labels = mixedMoment B raw21945step1 raw21945step1Labels := by
      have ha : raw21945step1 = (fun i j => raw21945step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21945step1 raw21945step0; decide +kernel
      have hl : raw21945step1Labels = raw21945step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21945step0 raw21945step0Labels permutation151 permutation2
    mixedMoment B raw21945step1 raw21945step1Labels = mixedMoment B raw21945step2 raw21945step2Labels := by
      have ha : raw21945step2 = -raw21945step1 := by apply Matrix.ext; change ∀ i j, raw21945step2 i j = -(raw21945step1 i j); unfold raw21945step2 raw21945step1; decide +kernel
      have hl : raw21945step2Labels = raw21945step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4289 node4289Labels := by rfl

def raw21946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21946Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21946step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21946step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21946step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21946 raw21946Labels = mixedMoment B node4312 node4312Labels := by
  calc
    mixedMoment B raw21946 raw21946Labels = mixedMoment B raw21946step0 raw21946step0Labels := by
      have hz : ∀ j, raw21946 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21946step0 = (fun i j => raw21946 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21946step0 raw21946; decide +kernel
      have hl : raw21946step0Labels = raw21946Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21946 raw21946Labels permutation346 hz
    mixedMoment B raw21946step0 raw21946step0Labels = mixedMoment B raw21946step1 raw21946step1Labels := by
      have hz : ∀ j, raw21946step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21946step1 = (fun i j => raw21946step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21946step1 raw21946step0; decide +kernel
      have hl : raw21946step1Labels = raw21946step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21946step0 raw21946step0Labels permutation56 hz
    _ = mixedMoment B node4312 node4312Labels := by rfl

def raw21947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw21947Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21947step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw21947step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21947step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw21947step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21947 raw21947Labels = mixedMoment B node4405 node4405Labels := by
  calc
    mixedMoment B raw21947 raw21947Labels = mixedMoment B raw21947step0 raw21947step0Labels := by
      have hz : ∀ j, raw21947 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21947step0 = (fun i j => raw21947 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21947step0 raw21947; decide +kernel
      have hl : raw21947step0Labels = raw21947Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21947 raw21947Labels permutation346 hz
    mixedMoment B raw21947step0 raw21947step0Labels = mixedMoment B raw21947step1 raw21947step1Labels := by
      have hz : ∀ j, raw21947step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21947step1 = (fun i j => raw21947step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21947step1 raw21947step0; decide +kernel
      have hl : raw21947step1Labels = raw21947step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21947step0 raw21947step0Labels permutation56 hz
    _ = mixedMoment B node4405 node4405Labels := by rfl

def raw21948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21948Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21948step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21948step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21948step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21948step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21948step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21948step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21948 raw21948Labels = mixedMoment B node1911 node1911Labels := by
  calc
    mixedMoment B raw21948 raw21948Labels = mixedMoment B raw21948step0 raw21948step0Labels := by
      have hz : ∀ j, raw21948 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21948step0 = (fun i j => raw21948 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21948step0 raw21948; decide +kernel
      have hl : raw21948step0Labels = raw21948Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21948 raw21948Labels permutation346 hz
    mixedMoment B raw21948step0 raw21948step0Labels = mixedMoment B raw21948step1 raw21948step1Labels := by
      have ha : raw21948step1 = (fun i j => raw21948step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21948step1 raw21948step0; decide +kernel
      have hl : raw21948step1Labels = raw21948step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21948step0 raw21948step0Labels permutation149 permutation7
    mixedMoment B raw21948step1 raw21948step1Labels = mixedMoment B raw21948step2 raw21948step2Labels := by
      have ha : raw21948step2 = raw21948step1 := by apply Matrix.ext; unfold raw21948step2 raw21948step1; decide +kernel
      have hl : raw21948step1Labels = labelEmbedding1 ∘ raw21948step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21948step1 raw21948step1Labels raw21948step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1911 node1911Labels := by rfl

def raw21949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21949Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21949step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21949step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21949step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21949step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21949step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21949step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21949 raw21949Labels = mixedMoment B node1911 node1911Labels := by
  calc
    mixedMoment B raw21949 raw21949Labels = mixedMoment B raw21949step0 raw21949step0Labels := by
      have hz : ∀ j, raw21949 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21949step0 = (fun i j => raw21949 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21949step0 raw21949; decide +kernel
      have hl : raw21949step0Labels = raw21949Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21949 raw21949Labels permutation265 hz
    mixedMoment B raw21949step0 raw21949step0Labels = mixedMoment B raw21949step1 raw21949step1Labels := by
      have ha : raw21949step1 = (fun i j => raw21949step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21949step1 raw21949step0; decide +kernel
      have hl : raw21949step1Labels = raw21949step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21949step0 raw21949step0Labels permutation149 permutation7
    mixedMoment B raw21949step1 raw21949step1Labels = mixedMoment B raw21949step2 raw21949step2Labels := by
      have ha : raw21949step2 = raw21949step1 := by apply Matrix.ext; unfold raw21949step2 raw21949step1; decide +kernel
      have hl : raw21949step1Labels = labelEmbedding1 ∘ raw21949step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21949step1 raw21949step1Labels raw21949step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1911 node1911Labels := by rfl

def raw21950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21950Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21950step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21950step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21950step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21950step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21950step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw21950step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical21950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21950 raw21950Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw21950 raw21950Labels = mixedMoment B raw21950step0 raw21950step0Labels := by
      have hz : ∀ j, raw21950 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21950step0 = (fun i j => raw21950 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21950step0 raw21950; decide +kernel
      have hl : raw21950step0Labels = raw21950Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21950 raw21950Labels permutation346 hz
    mixedMoment B raw21950step0 raw21950step0Labels = mixedMoment B raw21950step1 raw21950step1Labels := by
      have hz : ∀ j, raw21950step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21950step1 = (fun i j => raw21950step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21950step1 raw21950step0; decide +kernel
      have hl : raw21950step1Labels = raw21950step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21950step0 raw21950step0Labels permutation56 hz
    mixedMoment B raw21950step1 raw21950step1Labels = mixedMoment B raw21950step2 raw21950step2Labels := by
      have hz : ∀ i, raw21950step1 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw21950step2 = (fun i j => raw21950step1 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw21950step2 raw21950step1; decide +kernel
      have hl : raw21950step2Labels = (fun j => raw21950step1Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw21950step1 raw21950step1Labels permutation4 hz
    _ = mixedMoment B node4081 node4081Labels := by rfl

def raw21951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21951Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21951step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21951step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21951step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21951step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21951step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21951step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw21951step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21951 raw21951Labels = mixedMoment B node2056 node2056Labels := by
  calc
    mixedMoment B raw21951 raw21951Labels = mixedMoment B raw21951step0 raw21951step0Labels := by
      have hz : ∀ j, raw21951 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21951step0 = (fun i j => raw21951 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21951step0 raw21951; decide +kernel
      have hl : raw21951step0Labels = raw21951Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21951 raw21951Labels permutation346 hz
    mixedMoment B raw21951step0 raw21951step0Labels = mixedMoment B raw21951step1 raw21951step1Labels := by
      have hz : ∀ j, raw21951step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21951step1 = (fun i j => raw21951step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21951step1 raw21951step0; decide +kernel
      have hl : raw21951step1Labels = raw21951step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21951step0 raw21951step0Labels permutation56 hz
    mixedMoment B raw21951step1 raw21951step1Labels = mixedMoment B raw21951step2 raw21951step2Labels := by
      have ha : raw21951step2 = (fun i j => raw21951step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21951step2 raw21951step1; decide +kernel
      have hl : raw21951step2Labels = raw21951step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21951step1 raw21951step1Labels permutation31 permutation7
    mixedMoment B raw21951step2 raw21951step2Labels = mixedMoment B raw21951step3 raw21951step3Labels := by
      have ha : raw21951step3 = raw21951step2 := by apply Matrix.ext; unfold raw21951step3 raw21951step2; decide +kernel
      have hl : raw21951step2Labels = labelEmbedding1 ∘ raw21951step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21951step2 raw21951step2Labels raw21951step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2056 node2056Labels := by rfl

def raw21952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21952Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21952step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21952step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21952step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21952step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21952step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw21952step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21952step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21952step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21952step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw21952step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21952 raw21952Labels = mixedMoment B node2060 node2060Labels := by
  calc
    mixedMoment B raw21952 raw21952Labels = mixedMoment B raw21952step0 raw21952step0Labels := by
      have hz : ∀ j, raw21952 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21952step0 = (fun i j => raw21952 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21952step0 raw21952; decide +kernel
      have hl : raw21952step0Labels = raw21952Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21952 raw21952Labels permutation346 hz
    mixedMoment B raw21952step0 raw21952step0Labels = mixedMoment B raw21952step1 raw21952step1Labels := by
      have hz : ∀ j, raw21952step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21952step1 = (fun i j => raw21952step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21952step1 raw21952step0; decide +kernel
      have hl : raw21952step1Labels = raw21952step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21952step0 raw21952step0Labels permutation56 hz
    mixedMoment B raw21952step1 raw21952step1Labels = mixedMoment B raw21952step2 raw21952step2Labels := by
      have ha : raw21952step2 = (fun i j => raw21952step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21952step2 raw21952step1; decide +kernel
      have hl : raw21952step2Labels = raw21952step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21952step1 raw21952step1Labels permutation8 permutation7
    mixedMoment B raw21952step2 raw21952step2Labels = mixedMoment B raw21952step3 raw21952step3Labels := by
      have ha : raw21952step3 = -raw21952step2 := by apply Matrix.ext; change ∀ i j, raw21952step3 i j = -(raw21952step2 i j); unfold raw21952step3 raw21952step2; decide +kernel
      have hl : raw21952step3Labels = raw21952step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21952step3 raw21952step3Labels = mixedMoment B raw21952step4 raw21952step4Labels := by
      have ha : raw21952step4 = raw21952step3 := by apply Matrix.ext; unfold raw21952step4 raw21952step3; decide +kernel
      have hl : raw21952step3Labels = labelEmbedding1 ∘ raw21952step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21952step3 raw21952step3Labels raw21952step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2060 node2060Labels := by rfl

def raw21953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21953Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21953step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21953step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21953step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 0, 3]]
def raw21953step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21953step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw21953step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21953step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw21953step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21953 raw21953Labels = mixedMoment B node1489 node1489Labels := by
  calc
    mixedMoment B raw21953 raw21953Labels = mixedMoment B raw21953step0 raw21953step0Labels := by
      have hz : ∀ j, raw21953 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21953step0 = (fun i j => raw21953 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21953step0 raw21953; decide +kernel
      have hl : raw21953step0Labels = raw21953Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21953 raw21953Labels permutation346 hz
    mixedMoment B raw21953step0 raw21953step0Labels = mixedMoment B raw21953step1 raw21953step1Labels := by
      have ha : raw21953step1 = (fun i j => raw21953step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21953step1 raw21953step0; decide +kernel
      have hl : raw21953step1Labels = raw21953step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21953step0 raw21953step0Labels permutation38 permutation7
    mixedMoment B raw21953step1 raw21953step1Labels = mixedMoment B raw21953step2 raw21953step2Labels := by
      have ha : raw21953step2 = -raw21953step1 := by apply Matrix.ext; change ∀ i j, raw21953step2 i j = -(raw21953step1 i j); unfold raw21953step2 raw21953step1; decide +kernel
      have hl : raw21953step2Labels = raw21953step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21953step2 raw21953step2Labels = mixedMoment B raw21953step3 raw21953step3Labels := by
      have ha : raw21953step3 = raw21953step2 := by apply Matrix.ext; unfold raw21953step3 raw21953step2; decide +kernel
      have hl : raw21953step2Labels = labelEmbedding1 ∘ raw21953step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21953step2 raw21953step2Labels raw21953step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1489 node1489Labels := by rfl

def raw21954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21954Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21954step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 0, 3]]
def raw21954step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21954step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw21954step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21954step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw21954step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21954 raw21954Labels = mixedMoment B node1586 node1586Labels := by
  calc
    mixedMoment B raw21954 raw21954Labels = mixedMoment B raw21954step0 raw21954step0Labels := by
      have ha : raw21954step0 = (fun i j => raw21954 (permutation206 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21954step0 raw21954; decide +kernel
      have hl : raw21954step0Labels = raw21954Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21954 raw21954Labels permutation206 permutation7
    mixedMoment B raw21954step0 raw21954step0Labels = mixedMoment B raw21954step1 raw21954step1Labels := by
      have ha : raw21954step1 = -raw21954step0 := by apply Matrix.ext; change ∀ i j, raw21954step1 i j = -(raw21954step0 i j); unfold raw21954step1 raw21954step0; decide +kernel
      have hl : raw21954step1Labels = raw21954step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21954step1 raw21954step1Labels = mixedMoment B raw21954step2 raw21954step2Labels := by
      have ha : raw21954step2 = raw21954step1 := by apply Matrix.ext; unfold raw21954step2 raw21954step1; decide +kernel
      have hl : raw21954step1Labels = labelEmbedding1 ∘ raw21954step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21954step1 raw21954step1Labels raw21954step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1586 node1586Labels := by rfl

def raw21955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21955Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21955step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21955step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21955step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 0, 3]]
def raw21955step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21955step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw21955step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21955step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw21955step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21955 raw21955Labels = mixedMoment B node1557 node1557Labels := by
  calc
    mixedMoment B raw21955 raw21955Labels = mixedMoment B raw21955step0 raw21955step0Labels := by
      have hz : ∀ j, raw21955 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21955step0 = (fun i j => raw21955 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21955step0 raw21955; decide +kernel
      have hl : raw21955step0Labels = raw21955Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21955 raw21955Labels permutation346 hz
    mixedMoment B raw21955step0 raw21955step0Labels = mixedMoment B raw21955step1 raw21955step1Labels := by
      have ha : raw21955step1 = (fun i j => raw21955step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21955step1 raw21955step0; decide +kernel
      have hl : raw21955step1Labels = raw21955step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21955step0 raw21955step0Labels permutation38 permutation7
    mixedMoment B raw21955step1 raw21955step1Labels = mixedMoment B raw21955step2 raw21955step2Labels := by
      have ha : raw21955step2 = -raw21955step1 := by apply Matrix.ext; change ∀ i j, raw21955step2 i j = -(raw21955step1 i j); unfold raw21955step2 raw21955step1; decide +kernel
      have hl : raw21955step2Labels = raw21955step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21955step2 raw21955step2Labels = mixedMoment B raw21955step3 raw21955step3Labels := by
      have ha : raw21955step3 = raw21955step2 := by apply Matrix.ext; unfold raw21955step3 raw21955step2; decide +kernel
      have hl : raw21955step2Labels = labelEmbedding1 ∘ raw21955step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21955step2 raw21955step2Labels raw21955step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1557 node1557Labels := by rfl

def raw21956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21956Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21956step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21956step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw21956step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21956step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21956step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21956step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21956step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21956 raw21956Labels = mixedMoment B node1599 node1599Labels := by
  calc
    mixedMoment B raw21956 raw21956Labels = mixedMoment B raw21956step0 raw21956step0Labels := by
      have hz : ∀ j, raw21956 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21956step0 = (fun i j => raw21956 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21956step0 raw21956; decide +kernel
      have hl : raw21956step0Labels = raw21956Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21956 raw21956Labels permutation346 hz
    mixedMoment B raw21956step0 raw21956step0Labels = mixedMoment B raw21956step1 raw21956step1Labels := by
      have ha : raw21956step1 = (fun i j => raw21956step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21956step1 raw21956step0; decide +kernel
      have hl : raw21956step1Labels = raw21956step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21956step0 raw21956step0Labels permutation38 permutation7
    mixedMoment B raw21956step1 raw21956step1Labels = mixedMoment B raw21956step2 raw21956step2Labels := by
      have ha : raw21956step2 = -raw21956step1 := by apply Matrix.ext; change ∀ i j, raw21956step2 i j = -(raw21956step1 i j); unfold raw21956step2 raw21956step1; decide +kernel
      have hl : raw21956step2Labels = raw21956step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21956step2 raw21956step2Labels = mixedMoment B raw21956step3 raw21956step3Labels := by
      have ha : raw21956step3 = raw21956step2 := by apply Matrix.ext; unfold raw21956step3 raw21956step2; decide +kernel
      have hl : raw21956step2Labels = labelEmbedding1 ∘ raw21956step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21956step2 raw21956step2Labels raw21956step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1599 node1599Labels := by rfl

def raw21957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21957Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21957step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21957step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21957step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw21957step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21957step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21957step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21957step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21957step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21957 raw21957Labels = mixedMoment B node1602 node1602Labels := by
  calc
    mixedMoment B raw21957 raw21957Labels = mixedMoment B raw21957step0 raw21957step0Labels := by
      have hz : ∀ j, raw21957 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21957step0 = (fun i j => raw21957 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21957step0 raw21957; decide +kernel
      have hl : raw21957step0Labels = raw21957Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21957 raw21957Labels permutation346 hz
    mixedMoment B raw21957step0 raw21957step0Labels = mixedMoment B raw21957step1 raw21957step1Labels := by
      have ha : raw21957step1 = (fun i j => raw21957step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21957step1 raw21957step0; decide +kernel
      have hl : raw21957step1Labels = raw21957step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21957step0 raw21957step0Labels permutation38 permutation7
    mixedMoment B raw21957step1 raw21957step1Labels = mixedMoment B raw21957step2 raw21957step2Labels := by
      have ha : raw21957step2 = -raw21957step1 := by apply Matrix.ext; change ∀ i j, raw21957step2 i j = -(raw21957step1 i j); unfold raw21957step2 raw21957step1; decide +kernel
      have hl : raw21957step2Labels = raw21957step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21957step2 raw21957step2Labels = mixedMoment B raw21957step3 raw21957step3Labels := by
      have ha : raw21957step3 = raw21957step2 := by apply Matrix.ext; unfold raw21957step3 raw21957step2; decide +kernel
      have hl : raw21957step2Labels = labelEmbedding1 ∘ raw21957step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21957step2 raw21957step2Labels raw21957step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1602 node1602Labels := by rfl

def raw21958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21958Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21958step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21958step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21958step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 0, 3]]
def raw21958step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21958step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw21958step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21958step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw21958step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21958 raw21958Labels = mixedMoment B node1489 node1489Labels := by
  calc
    mixedMoment B raw21958 raw21958Labels = mixedMoment B raw21958step0 raw21958step0Labels := by
      have hz : ∀ j, raw21958 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21958step0 = (fun i j => raw21958 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21958step0 raw21958; decide +kernel
      have hl : raw21958step0Labels = raw21958Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21958 raw21958Labels permutation265 hz
    mixedMoment B raw21958step0 raw21958step0Labels = mixedMoment B raw21958step1 raw21958step1Labels := by
      have ha : raw21958step1 = (fun i j => raw21958step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21958step1 raw21958step0; decide +kernel
      have hl : raw21958step1Labels = raw21958step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21958step0 raw21958step0Labels permutation38 permutation7
    mixedMoment B raw21958step1 raw21958step1Labels = mixedMoment B raw21958step2 raw21958step2Labels := by
      have ha : raw21958step2 = -raw21958step1 := by apply Matrix.ext; change ∀ i j, raw21958step2 i j = -(raw21958step1 i j); unfold raw21958step2 raw21958step1; decide +kernel
      have hl : raw21958step2Labels = raw21958step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21958step2 raw21958step2Labels = mixedMoment B raw21958step3 raw21958step3Labels := by
      have ha : raw21958step3 = raw21958step2 := by apply Matrix.ext; unfold raw21958step3 raw21958step2; decide +kernel
      have hl : raw21958step2Labels = labelEmbedding1 ∘ raw21958step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21958step2 raw21958step2Labels raw21958step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1489 node1489Labels := by rfl

def raw21959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21959Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21959step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 0, 3]]
def raw21959step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21959step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw21959step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21959step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw21959step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21959 raw21959Labels = mixedMoment B node1586 node1586Labels := by
  calc
    mixedMoment B raw21959 raw21959Labels = mixedMoment B raw21959step0 raw21959step0Labels := by
      have ha : raw21959step0 = (fun i j => raw21959 (permutation200 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21959step0 raw21959; decide +kernel
      have hl : raw21959step0Labels = raw21959Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21959 raw21959Labels permutation200 permutation7
    mixedMoment B raw21959step0 raw21959step0Labels = mixedMoment B raw21959step1 raw21959step1Labels := by
      have ha : raw21959step1 = -raw21959step0 := by apply Matrix.ext; change ∀ i j, raw21959step1 i j = -(raw21959step0 i j); unfold raw21959step1 raw21959step0; decide +kernel
      have hl : raw21959step1Labels = raw21959step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21959step1 raw21959step1Labels = mixedMoment B raw21959step2 raw21959step2Labels := by
      have ha : raw21959step2 = raw21959step1 := by apply Matrix.ext; unfold raw21959step2 raw21959step1; decide +kernel
      have hl : raw21959step1Labels = labelEmbedding1 ∘ raw21959step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21959step1 raw21959step1Labels raw21959step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1586 node1586Labels := by rfl

def raw21960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21960Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21960step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21960step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 0, 3]]
def raw21960step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21960step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw21960step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21960step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw21960step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21960 raw21960Labels = mixedMoment B node1557 node1557Labels := by
  calc
    mixedMoment B raw21960 raw21960Labels = mixedMoment B raw21960step0 raw21960step0Labels := by
      have hz : ∀ j, raw21960 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21960step0 = (fun i j => raw21960 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21960step0 raw21960; decide +kernel
      have hl : raw21960step0Labels = raw21960Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21960 raw21960Labels permutation265 hz
    mixedMoment B raw21960step0 raw21960step0Labels = mixedMoment B raw21960step1 raw21960step1Labels := by
      have ha : raw21960step1 = (fun i j => raw21960step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21960step1 raw21960step0; decide +kernel
      have hl : raw21960step1Labels = raw21960step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21960step0 raw21960step0Labels permutation38 permutation7
    mixedMoment B raw21960step1 raw21960step1Labels = mixedMoment B raw21960step2 raw21960step2Labels := by
      have ha : raw21960step2 = -raw21960step1 := by apply Matrix.ext; change ∀ i j, raw21960step2 i j = -(raw21960step1 i j); unfold raw21960step2 raw21960step1; decide +kernel
      have hl : raw21960step2Labels = raw21960step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21960step2 raw21960step2Labels = mixedMoment B raw21960step3 raw21960step3Labels := by
      have ha : raw21960step3 = raw21960step2 := by apply Matrix.ext; unfold raw21960step3 raw21960step2; decide +kernel
      have hl : raw21960step2Labels = labelEmbedding1 ∘ raw21960step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21960step2 raw21960step2Labels raw21960step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1557 node1557Labels := by rfl

def raw21961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21961Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21961step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21961step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw21961step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21961step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21961step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21961step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21961step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21961 raw21961Labels = mixedMoment B node1599 node1599Labels := by
  calc
    mixedMoment B raw21961 raw21961Labels = mixedMoment B raw21961step0 raw21961step0Labels := by
      have hz : ∀ j, raw21961 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21961step0 = (fun i j => raw21961 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21961step0 raw21961; decide +kernel
      have hl : raw21961step0Labels = raw21961Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21961 raw21961Labels permutation265 hz
    mixedMoment B raw21961step0 raw21961step0Labels = mixedMoment B raw21961step1 raw21961step1Labels := by
      have ha : raw21961step1 = (fun i j => raw21961step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21961step1 raw21961step0; decide +kernel
      have hl : raw21961step1Labels = raw21961step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21961step0 raw21961step0Labels permutation38 permutation7
    mixedMoment B raw21961step1 raw21961step1Labels = mixedMoment B raw21961step2 raw21961step2Labels := by
      have ha : raw21961step2 = -raw21961step1 := by apply Matrix.ext; change ∀ i j, raw21961step2 i j = -(raw21961step1 i j); unfold raw21961step2 raw21961step1; decide +kernel
      have hl : raw21961step2Labels = raw21961step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21961step2 raw21961step2Labels = mixedMoment B raw21961step3 raw21961step3Labels := by
      have ha : raw21961step3 = raw21961step2 := by apply Matrix.ext; unfold raw21961step3 raw21961step2; decide +kernel
      have hl : raw21961step2Labels = labelEmbedding1 ∘ raw21961step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21961step2 raw21961step2Labels raw21961step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1599 node1599Labels := by rfl

def raw21962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21962Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21962step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21962step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21962step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw21962step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21962step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21962step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21962step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21962step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21962 raw21962Labels = mixedMoment B node1602 node1602Labels := by
  calc
    mixedMoment B raw21962 raw21962Labels = mixedMoment B raw21962step0 raw21962step0Labels := by
      have hz : ∀ j, raw21962 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21962step0 = (fun i j => raw21962 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21962step0 raw21962; decide +kernel
      have hl : raw21962step0Labels = raw21962Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21962 raw21962Labels permutation265 hz
    mixedMoment B raw21962step0 raw21962step0Labels = mixedMoment B raw21962step1 raw21962step1Labels := by
      have ha : raw21962step1 = (fun i j => raw21962step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21962step1 raw21962step0; decide +kernel
      have hl : raw21962step1Labels = raw21962step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21962step0 raw21962step0Labels permutation38 permutation7
    mixedMoment B raw21962step1 raw21962step1Labels = mixedMoment B raw21962step2 raw21962step2Labels := by
      have ha : raw21962step2 = -raw21962step1 := by apply Matrix.ext; change ∀ i j, raw21962step2 i j = -(raw21962step1 i j); unfold raw21962step2 raw21962step1; decide +kernel
      have hl : raw21962step2Labels = raw21962step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21962step2 raw21962step2Labels = mixedMoment B raw21962step3 raw21962step3Labels := by
      have ha : raw21962step3 = raw21962step2 := by apply Matrix.ext; unfold raw21962step3 raw21962step2; decide +kernel
      have hl : raw21962step2Labels = labelEmbedding1 ∘ raw21962step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21962step2 raw21962step2Labels raw21962step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1602 node1602Labels := by rfl

def raw21963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21963Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21963step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21963step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21963step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21963step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21963step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![1, -2, 1], ![-1, 0, 1], ![-3, 0, 3]]
def raw21963step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21963step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 2, -1], ![1, 0, -1], ![3, 0, -3]]
def raw21963step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21963step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 2, -1], ![1, 0, -1], ![3, 0, -3]]
def raw21963step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21963 raw21963Labels = mixedMoment B node1499 node1499Labels := by
  calc
    mixedMoment B raw21963 raw21963Labels = mixedMoment B raw21963step0 raw21963step0Labels := by
      have hz : ∀ j, raw21963 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21963step0 = (fun i j => raw21963 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21963step0 raw21963; decide +kernel
      have hl : raw21963step0Labels = raw21963Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21963 raw21963Labels permutation346 hz
    mixedMoment B raw21963step0 raw21963step0Labels = mixedMoment B raw21963step1 raw21963step1Labels := by
      have hz : ∀ j, raw21963step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21963step1 = (fun i j => raw21963step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21963step1 raw21963step0; decide +kernel
      have hl : raw21963step1Labels = raw21963step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21963step0 raw21963step0Labels permutation56 hz
    mixedMoment B raw21963step1 raw21963step1Labels = mixedMoment B raw21963step2 raw21963step2Labels := by
      have ha : raw21963step2 = (fun i j => raw21963step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21963step2 raw21963step1; decide +kernel
      have hl : raw21963step2Labels = raw21963step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21963step1 raw21963step1Labels permutation8 permutation7
    mixedMoment B raw21963step2 raw21963step2Labels = mixedMoment B raw21963step3 raw21963step3Labels := by
      have ha : raw21963step3 = -raw21963step2 := by apply Matrix.ext; change ∀ i j, raw21963step3 i j = -(raw21963step2 i j); unfold raw21963step3 raw21963step2; decide +kernel
      have hl : raw21963step3Labels = raw21963step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21963step3 raw21963step3Labels = mixedMoment B raw21963step4 raw21963step4Labels := by
      have ha : raw21963step4 = raw21963step3 := by apply Matrix.ext; unfold raw21963step4 raw21963step3; decide +kernel
      have hl : raw21963step3Labels = labelEmbedding1 ∘ raw21963step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21963step3 raw21963step3Labels raw21963step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1499 node1499Labels := by rfl

def raw21964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21964Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21964step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21964step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21964step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-3, 0, 3]]
def raw21964step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21964step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21964step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21964step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21964step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21964 raw21964Labels = mixedMoment B node1633 node1633Labels := by
  calc
    mixedMoment B raw21964 raw21964Labels = mixedMoment B raw21964step0 raw21964step0Labels := by
      have hz : ∀ j, raw21964 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21964step0 = (fun i j => raw21964 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21964step0 raw21964; decide +kernel
      have hl : raw21964step0Labels = raw21964Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21964 raw21964Labels permutation346 hz
    mixedMoment B raw21964step0 raw21964step0Labels = mixedMoment B raw21964step1 raw21964step1Labels := by
      have ha : raw21964step1 = (fun i j => raw21964step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21964step1 raw21964step0; decide +kernel
      have hl : raw21964step1Labels = raw21964step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21964step0 raw21964step0Labels permutation38 permutation7
    mixedMoment B raw21964step1 raw21964step1Labels = mixedMoment B raw21964step2 raw21964step2Labels := by
      have ha : raw21964step2 = -raw21964step1 := by apply Matrix.ext; change ∀ i j, raw21964step2 i j = -(raw21964step1 i j); unfold raw21964step2 raw21964step1; decide +kernel
      have hl : raw21964step2Labels = raw21964step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21964step2 raw21964step2Labels = mixedMoment B raw21964step3 raw21964step3Labels := by
      have ha : raw21964step3 = raw21964step2 := by apply Matrix.ext; unfold raw21964step3 raw21964step2; decide +kernel
      have hl : raw21964step2Labels = labelEmbedding1 ∘ raw21964step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21964step2 raw21964step2Labels raw21964step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1633 node1633Labels := by rfl

def raw21965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21965Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21965step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21965step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21965step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-3, 0, 3]]
def raw21965step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21965step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21965step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21965step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21965step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21965 raw21965Labels = mixedMoment B node1633 node1633Labels := by
  calc
    mixedMoment B raw21965 raw21965Labels = mixedMoment B raw21965step0 raw21965step0Labels := by
      have hz : ∀ j, raw21965 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21965step0 = (fun i j => raw21965 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21965step0 raw21965; decide +kernel
      have hl : raw21965step0Labels = raw21965Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21965 raw21965Labels permutation265 hz
    mixedMoment B raw21965step0 raw21965step0Labels = mixedMoment B raw21965step1 raw21965step1Labels := by
      have ha : raw21965step1 = (fun i j => raw21965step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21965step1 raw21965step0; decide +kernel
      have hl : raw21965step1Labels = raw21965step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21965step0 raw21965step0Labels permutation38 permutation7
    mixedMoment B raw21965step1 raw21965step1Labels = mixedMoment B raw21965step2 raw21965step2Labels := by
      have ha : raw21965step2 = -raw21965step1 := by apply Matrix.ext; change ∀ i j, raw21965step2 i j = -(raw21965step1 i j); unfold raw21965step2 raw21965step1; decide +kernel
      have hl : raw21965step2Labels = raw21965step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21965step2 raw21965step2Labels = mixedMoment B raw21965step3 raw21965step3Labels := by
      have ha : raw21965step3 = raw21965step2 := by apply Matrix.ext; unfold raw21965step3 raw21965step2; decide +kernel
      have hl : raw21965step2Labels = labelEmbedding1 ∘ raw21965step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21965step2 raw21965step2Labels raw21965step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1633 node1633Labels := by rfl

def raw21966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21966Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21966step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21966step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![0, 1, -1], ![3, 0, -3]]
def raw21966step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21966step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw21966step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21966step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21966step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21966step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21966step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21966 raw21966Labels = mixedMoment B node1647 node1647Labels := by
  calc
    mixedMoment B raw21966 raw21966Labels = mixedMoment B raw21966step0 raw21966step0Labels := by
      have hz : ∀ j, raw21966 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21966step0 = (fun i j => raw21966 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21966step0 raw21966; decide +kernel
      have hl : raw21966step0Labels = raw21966Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21966 raw21966Labels permutation346 hz
    mixedMoment B raw21966step0 raw21966step0Labels = mixedMoment B raw21966step1 raw21966step1Labels := by
      have hz : ∀ j, raw21966step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21966step1 = (fun i j => raw21966step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21966step1 raw21966step0; decide +kernel
      have hl : raw21966step1Labels = raw21966step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21966step0 raw21966step0Labels permutation56 hz
    mixedMoment B raw21966step1 raw21966step1Labels = mixedMoment B raw21966step2 raw21966step2Labels := by
      have ha : raw21966step2 = (fun i j => raw21966step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21966step2 raw21966step1; decide +kernel
      have hl : raw21966step2Labels = raw21966step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21966step1 raw21966step1Labels permutation8 permutation7
    mixedMoment B raw21966step2 raw21966step2Labels = mixedMoment B raw21966step3 raw21966step3Labels := by
      have ha : raw21966step3 = -raw21966step2 := by apply Matrix.ext; change ∀ i j, raw21966step3 i j = -(raw21966step2 i j); unfold raw21966step3 raw21966step2; decide +kernel
      have hl : raw21966step3Labels = raw21966step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21966step3 raw21966step3Labels = mixedMoment B raw21966step4 raw21966step4Labels := by
      have ha : raw21966step4 = raw21966step3 := by apply Matrix.ext; unfold raw21966step4 raw21966step3; decide +kernel
      have hl : raw21966step3Labels = labelEmbedding1 ∘ raw21966step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21966step3 raw21966step3Labels raw21966step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1647 node1647Labels := by rfl

def raw21967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21967Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21967step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21967step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21967step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw21967step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21967step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -2, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw21967step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21967step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21967step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21967step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 2, -1], ![1, 0, -1], ![3, -1, -2]]
def raw21967step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21967 raw21967Labels = mixedMoment B node1650 node1650Labels := by
  calc
    mixedMoment B raw21967 raw21967Labels = mixedMoment B raw21967step0 raw21967step0Labels := by
      have hz : ∀ j, raw21967 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21967step0 = (fun i j => raw21967 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21967step0 raw21967; decide +kernel
      have hl : raw21967step0Labels = raw21967Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21967 raw21967Labels permutation346 hz
    mixedMoment B raw21967step0 raw21967step0Labels = mixedMoment B raw21967step1 raw21967step1Labels := by
      have hz : ∀ j, raw21967step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21967step1 = (fun i j => raw21967step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21967step1 raw21967step0; decide +kernel
      have hl : raw21967step1Labels = raw21967step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21967step0 raw21967step0Labels permutation56 hz
    mixedMoment B raw21967step1 raw21967step1Labels = mixedMoment B raw21967step2 raw21967step2Labels := by
      have ha : raw21967step2 = (fun i j => raw21967step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21967step2 raw21967step1; decide +kernel
      have hl : raw21967step2Labels = raw21967step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21967step1 raw21967step1Labels permutation8 permutation7
    mixedMoment B raw21967step2 raw21967step2Labels = mixedMoment B raw21967step3 raw21967step3Labels := by
      have ha : raw21967step3 = -raw21967step2 := by apply Matrix.ext; change ∀ i j, raw21967step3 i j = -(raw21967step2 i j); unfold raw21967step3 raw21967step2; decide +kernel
      have hl : raw21967step3Labels = raw21967step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21967step3 raw21967step3Labels = mixedMoment B raw21967step4 raw21967step4Labels := by
      have ha : raw21967step4 = raw21967step3 := by apply Matrix.ext; unfold raw21967step4 raw21967step3; decide +kernel
      have hl : raw21967step3Labels = labelEmbedding1 ∘ raw21967step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21967step3 raw21967step3Labels raw21967step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1650 node1650Labels := by rfl

def raw21968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21968Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21968step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21968step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21968step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21968step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21968step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![-1, -1, 2], ![-3, 0, 3]]
def raw21968step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21968step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 1, -2], ![3, 0, -3]]
def raw21968step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21968step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 1, -2], ![3, 0, -3]]
def raw21968step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21968 raw21968Labels = mixedMoment B node1495 node1495Labels := by
  calc
    mixedMoment B raw21968 raw21968Labels = mixedMoment B raw21968step0 raw21968step0Labels := by
      have hz : ∀ j, raw21968 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21968step0 = (fun i j => raw21968 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21968step0 raw21968; decide +kernel
      have hl : raw21968step0Labels = raw21968Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21968 raw21968Labels permutation346 hz
    mixedMoment B raw21968step0 raw21968step0Labels = mixedMoment B raw21968step1 raw21968step1Labels := by
      have hz : ∀ j, raw21968step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21968step1 = (fun i j => raw21968step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21968step1 raw21968step0; decide +kernel
      have hl : raw21968step1Labels = raw21968step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21968step0 raw21968step0Labels permutation56 hz
    mixedMoment B raw21968step1 raw21968step1Labels = mixedMoment B raw21968step2 raw21968step2Labels := by
      have ha : raw21968step2 = (fun i j => raw21968step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21968step2 raw21968step1; decide +kernel
      have hl : raw21968step2Labels = raw21968step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21968step1 raw21968step1Labels permutation8 permutation7
    mixedMoment B raw21968step2 raw21968step2Labels = mixedMoment B raw21968step3 raw21968step3Labels := by
      have ha : raw21968step3 = -raw21968step2 := by apply Matrix.ext; change ∀ i j, raw21968step3 i j = -(raw21968step2 i j); unfold raw21968step3 raw21968step2; decide +kernel
      have hl : raw21968step3Labels = raw21968step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21968step3 raw21968step3Labels = mixedMoment B raw21968step4 raw21968step4Labels := by
      have ha : raw21968step4 = raw21968step3 := by apply Matrix.ext; unfold raw21968step4 raw21968step3; decide +kernel
      have hl : raw21968step3Labels = labelEmbedding1 ∘ raw21968step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21968step3 raw21968step3Labels raw21968step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1495 node1495Labels := by rfl

def raw21969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21969Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21969step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21969step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21969step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 0, 3]]
def raw21969step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21969step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, 0, -3]]
def raw21969step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21969step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, 0, -3]]
def raw21969step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21969 raw21969Labels = mixedMoment B node1590 node1590Labels := by
  calc
    mixedMoment B raw21969 raw21969Labels = mixedMoment B raw21969step0 raw21969step0Labels := by
      have hz : ∀ j, raw21969 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21969step0 = (fun i j => raw21969 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21969step0 raw21969; decide +kernel
      have hl : raw21969step0Labels = raw21969Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21969 raw21969Labels permutation346 hz
    mixedMoment B raw21969step0 raw21969step0Labels = mixedMoment B raw21969step1 raw21969step1Labels := by
      have ha : raw21969step1 = (fun i j => raw21969step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21969step1 raw21969step0; decide +kernel
      have hl : raw21969step1Labels = raw21969step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21969step0 raw21969step0Labels permutation38 permutation7
    mixedMoment B raw21969step1 raw21969step1Labels = mixedMoment B raw21969step2 raw21969step2Labels := by
      have ha : raw21969step2 = -raw21969step1 := by apply Matrix.ext; change ∀ i j, raw21969step2 i j = -(raw21969step1 i j); unfold raw21969step2 raw21969step1; decide +kernel
      have hl : raw21969step2Labels = raw21969step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21969step2 raw21969step2Labels = mixedMoment B raw21969step3 raw21969step3Labels := by
      have ha : raw21969step3 = raw21969step2 := by apply Matrix.ext; unfold raw21969step3 raw21969step2; decide +kernel
      have hl : raw21969step2Labels = labelEmbedding1 ∘ raw21969step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21969step2 raw21969step2Labels raw21969step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1590 node1590Labels := by rfl

def raw21970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21970Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21970step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21970step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21970step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 0, 3]]
def raw21970step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21970step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, 0, -3]]
def raw21970step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21970step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, 0, -3]]
def raw21970step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21970 raw21970Labels = mixedMoment B node1590 node1590Labels := by
  calc
    mixedMoment B raw21970 raw21970Labels = mixedMoment B raw21970step0 raw21970step0Labels := by
      have hz : ∀ j, raw21970 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21970step0 = (fun i j => raw21970 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21970step0 raw21970; decide +kernel
      have hl : raw21970step0Labels = raw21970Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21970 raw21970Labels permutation265 hz
    mixedMoment B raw21970step0 raw21970step0Labels = mixedMoment B raw21970step1 raw21970step1Labels := by
      have ha : raw21970step1 = (fun i j => raw21970step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21970step1 raw21970step0; decide +kernel
      have hl : raw21970step1Labels = raw21970step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21970step0 raw21970step0Labels permutation38 permutation7
    mixedMoment B raw21970step1 raw21970step1Labels = mixedMoment B raw21970step2 raw21970step2Labels := by
      have ha : raw21970step2 = -raw21970step1 := by apply Matrix.ext; change ∀ i j, raw21970step2 i j = -(raw21970step1 i j); unfold raw21970step2 raw21970step1; decide +kernel
      have hl : raw21970step2Labels = raw21970step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21970step2 raw21970step2Labels = mixedMoment B raw21970step3 raw21970step3Labels := by
      have ha : raw21970step3 = raw21970step2 := by apply Matrix.ext; unfold raw21970step3 raw21970step2; decide +kernel
      have hl : raw21970step2Labels = labelEmbedding1 ∘ raw21970step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21970step2 raw21970step2Labels raw21970step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1590 node1590Labels := by rfl

def raw21971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21971Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21971step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21971step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21971step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21971step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21971step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, 0, -1], ![-1, -1, 2], ![-3, 0, 3]]
def raw21971step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21971step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, 1, -2], ![3, 0, -3]]
def raw21971step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21971step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, 1, -2], ![3, 0, -3]]
def raw21971step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21971 raw21971Labels = mixedMoment B node1576 node1576Labels := by
  calc
    mixedMoment B raw21971 raw21971Labels = mixedMoment B raw21971step0 raw21971step0Labels := by
      have hz : ∀ j, raw21971 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21971step0 = (fun i j => raw21971 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21971step0 raw21971; decide +kernel
      have hl : raw21971step0Labels = raw21971Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21971 raw21971Labels permutation346 hz
    mixedMoment B raw21971step0 raw21971step0Labels = mixedMoment B raw21971step1 raw21971step1Labels := by
      have hz : ∀ j, raw21971step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21971step1 = (fun i j => raw21971step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21971step1 raw21971step0; decide +kernel
      have hl : raw21971step1Labels = raw21971step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21971step0 raw21971step0Labels permutation56 hz
    mixedMoment B raw21971step1 raw21971step1Labels = mixedMoment B raw21971step2 raw21971step2Labels := by
      have ha : raw21971step2 = (fun i j => raw21971step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21971step2 raw21971step1; decide +kernel
      have hl : raw21971step2Labels = raw21971step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21971step1 raw21971step1Labels permutation8 permutation7
    mixedMoment B raw21971step2 raw21971step2Labels = mixedMoment B raw21971step3 raw21971step3Labels := by
      have ha : raw21971step3 = -raw21971step2 := by apply Matrix.ext; change ∀ i j, raw21971step3 i j = -(raw21971step2 i j); unfold raw21971step3 raw21971step2; decide +kernel
      have hl : raw21971step3Labels = raw21971step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21971step3 raw21971step3Labels = mixedMoment B raw21971step4 raw21971step4Labels := by
      have ha : raw21971step4 = raw21971step3 := by apply Matrix.ext; unfold raw21971step4 raw21971step3; decide +kernel
      have hl : raw21971step3Labels = labelEmbedding1 ∘ raw21971step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21971step3 raw21971step3Labels raw21971step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1576 node1576Labels := by rfl

def raw21972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw21972Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21972step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw21972step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21972step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw21972step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21972step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw21972step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21972step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw21972step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21972step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw21972step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21972 raw21972Labels = mixedMoment B node1627 node1627Labels := by
  calc
    mixedMoment B raw21972 raw21972Labels = mixedMoment B raw21972step0 raw21972step0Labels := by
      have hz : ∀ j, raw21972 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21972step0 = (fun i j => raw21972 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21972step0 raw21972; decide +kernel
      have hl : raw21972step0Labels = raw21972Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21972 raw21972Labels permutation346 hz
    mixedMoment B raw21972step0 raw21972step0Labels = mixedMoment B raw21972step1 raw21972step1Labels := by
      have hz : ∀ j, raw21972step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21972step1 = (fun i j => raw21972step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21972step1 raw21972step0; decide +kernel
      have hl : raw21972step1Labels = raw21972step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21972step0 raw21972step0Labels permutation56 hz
    mixedMoment B raw21972step1 raw21972step1Labels = mixedMoment B raw21972step2 raw21972step2Labels := by
      have ha : raw21972step2 = (fun i j => raw21972step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21972step2 raw21972step1; decide +kernel
      have hl : raw21972step2Labels = raw21972step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21972step1 raw21972step1Labels permutation8 permutation7
    mixedMoment B raw21972step2 raw21972step2Labels = mixedMoment B raw21972step3 raw21972step3Labels := by
      have ha : raw21972step3 = -raw21972step2 := by apply Matrix.ext; change ∀ i j, raw21972step3 i j = -(raw21972step2 i j); unfold raw21972step3 raw21972step2; decide +kernel
      have hl : raw21972step3Labels = raw21972step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21972step3 raw21972step3Labels = mixedMoment B raw21972step4 raw21972step4Labels := by
      have ha : raw21972step4 = raw21972step3 := by apply Matrix.ext; unfold raw21972step4 raw21972step3; decide +kernel
      have hl : raw21972step3Labels = labelEmbedding1 ∘ raw21972step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21972step3 raw21972step3Labels raw21972step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1627 node1627Labels := by rfl

def raw21973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21973Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21973step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21973step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21973step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21973step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21973step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![1, -1, 0], ![-1, 0, 1], ![-3, -1, 4]]
def raw21973step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21973step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 0, -1], ![3, 1, -4]]
def raw21973step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21973step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![-1, 1, 0], ![1, 0, -1], ![3, 1, -4]]
def raw21973step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21973 raw21973Labels = mixedMoment B node1494 node1494Labels := by
  calc
    mixedMoment B raw21973 raw21973Labels = mixedMoment B raw21973step0 raw21973step0Labels := by
      have hz : ∀ j, raw21973 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21973step0 = (fun i j => raw21973 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21973step0 raw21973; decide +kernel
      have hl : raw21973step0Labels = raw21973Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21973 raw21973Labels permutation346 hz
    mixedMoment B raw21973step0 raw21973step0Labels = mixedMoment B raw21973step1 raw21973step1Labels := by
      have hz : ∀ j, raw21973step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21973step1 = (fun i j => raw21973step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21973step1 raw21973step0; decide +kernel
      have hl : raw21973step1Labels = raw21973step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21973step0 raw21973step0Labels permutation56 hz
    mixedMoment B raw21973step1 raw21973step1Labels = mixedMoment B raw21973step2 raw21973step2Labels := by
      have ha : raw21973step2 = (fun i j => raw21973step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21973step2 raw21973step1; decide +kernel
      have hl : raw21973step2Labels = raw21973step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21973step1 raw21973step1Labels permutation8 permutation7
    mixedMoment B raw21973step2 raw21973step2Labels = mixedMoment B raw21973step3 raw21973step3Labels := by
      have ha : raw21973step3 = -raw21973step2 := by apply Matrix.ext; change ∀ i j, raw21973step3 i j = -(raw21973step2 i j); unfold raw21973step3 raw21973step2; decide +kernel
      have hl : raw21973step3Labels = raw21973step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21973step3 raw21973step3Labels = mixedMoment B raw21973step4 raw21973step4Labels := by
      have ha : raw21973step4 = raw21973step3 := by apply Matrix.ext; unfold raw21973step4 raw21973step3; decide +kernel
      have hl : raw21973step3Labels = labelEmbedding1 ∘ raw21973step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21973step3 raw21973step3Labels raw21973step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1494 node1494Labels := by rfl

def raw21974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21974Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21974step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21974step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21974step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw21974step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21974step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw21974step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21974 raw21974Labels = mixedMoment B node1555 node1555Labels := by
  calc
    mixedMoment B raw21974 raw21974Labels = mixedMoment B raw21974step0 raw21974step0Labels := by
      have hz : ∀ j, raw21974 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21974step0 = (fun i j => raw21974 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21974step0 raw21974; decide +kernel
      have hl : raw21974step0Labels = raw21974Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21974 raw21974Labels permutation346 hz
    mixedMoment B raw21974step0 raw21974step0Labels = mixedMoment B raw21974step1 raw21974step1Labels := by
      have ha : raw21974step1 = (fun i j => raw21974step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21974step1 raw21974step0; decide +kernel
      have hl : raw21974step1Labels = raw21974step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21974step0 raw21974step0Labels permutation149 permutation7
    mixedMoment B raw21974step1 raw21974step1Labels = mixedMoment B raw21974step2 raw21974step2Labels := by
      have ha : raw21974step2 = raw21974step1 := by apply Matrix.ext; unfold raw21974step2 raw21974step1; decide +kernel
      have hl : raw21974step1Labels = labelEmbedding1 ∘ raw21974step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21974step1 raw21974step1Labels raw21974step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1555 node1555Labels := by rfl

def raw21975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21975Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21975step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21975step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21975step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw21975step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21975step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 1, -4]]
def raw21975step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21975 raw21975Labels = mixedMoment B node1555 node1555Labels := by
  calc
    mixedMoment B raw21975 raw21975Labels = mixedMoment B raw21975step0 raw21975step0Labels := by
      have hz : ∀ j, raw21975 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21975step0 = (fun i j => raw21975 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21975step0 raw21975; decide +kernel
      have hl : raw21975step0Labels = raw21975Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21975 raw21975Labels permutation265 hz
    mixedMoment B raw21975step0 raw21975step0Labels = mixedMoment B raw21975step1 raw21975step1Labels := by
      have ha : raw21975step1 = (fun i j => raw21975step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21975step1 raw21975step0; decide +kernel
      have hl : raw21975step1Labels = raw21975step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21975step0 raw21975step0Labels permutation149 permutation7
    mixedMoment B raw21975step1 raw21975step1Labels = mixedMoment B raw21975step2 raw21975step2Labels := by
      have ha : raw21975step2 = raw21975step1 := by apply Matrix.ext; unfold raw21975step2 raw21975step1; decide +kernel
      have hl : raw21975step1Labels = labelEmbedding1 ∘ raw21975step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21975step1 raw21975step1Labels raw21975step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1555 node1555Labels := by rfl

def raw21976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21976Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21976step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21976step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21976step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21976step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21976step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, 0, -1], ![3, 1, -4]]
def raw21976step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21976step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 0, 1], ![1, 0, -1], ![3, 1, -4]]
def raw21976step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21976 raw21976Labels = mixedMoment B node1574 node1574Labels := by
  calc
    mixedMoment B raw21976 raw21976Labels = mixedMoment B raw21976step0 raw21976step0Labels := by
      have hz : ∀ j, raw21976 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21976step0 = (fun i j => raw21976 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21976step0 raw21976; decide +kernel
      have hl : raw21976step0Labels = raw21976Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21976 raw21976Labels permutation346 hz
    mixedMoment B raw21976step0 raw21976step0Labels = mixedMoment B raw21976step1 raw21976step1Labels := by
      have hz : ∀ j, raw21976step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21976step1 = (fun i j => raw21976step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21976step1 raw21976step0; decide +kernel
      have hl : raw21976step1Labels = raw21976step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21976step0 raw21976step0Labels permutation56 hz
    mixedMoment B raw21976step1 raw21976step1Labels = mixedMoment B raw21976step2 raw21976step2Labels := by
      have ha : raw21976step2 = (fun i j => raw21976step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21976step2 raw21976step1; decide +kernel
      have hl : raw21976step2Labels = raw21976step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21976step1 raw21976step1Labels permutation31 permutation7
    mixedMoment B raw21976step2 raw21976step2Labels = mixedMoment B raw21976step3 raw21976step3Labels := by
      have ha : raw21976step3 = raw21976step2 := by apply Matrix.ext; unfold raw21976step3 raw21976step2; decide +kernel
      have hl : raw21976step2Labels = labelEmbedding1 ∘ raw21976step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21976step2 raw21976step2Labels raw21976step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1574 node1574Labels := by rfl

def raw21977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw21977Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw21977step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21977step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw21977step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw21977step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw21977step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw21977step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw21977step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21977 raw21977Labels = mixedMoment B node1620 node1620Labels := by
  calc
    mixedMoment B raw21977 raw21977Labels = mixedMoment B raw21977step0 raw21977step0Labels := by
      have hz : ∀ j, raw21977 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21977step0 = (fun i j => raw21977 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21977step0 raw21977; decide +kernel
      have hl : raw21977step0Labels = raw21977Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21977 raw21977Labels permutation346 hz
    mixedMoment B raw21977step0 raw21977step0Labels = mixedMoment B raw21977step1 raw21977step1Labels := by
      have hz : ∀ j, raw21977step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21977step1 = (fun i j => raw21977step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21977step1 raw21977step0; decide +kernel
      have hl : raw21977step1Labels = raw21977step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21977step0 raw21977step0Labels permutation56 hz
    mixedMoment B raw21977step1 raw21977step1Labels = mixedMoment B raw21977step2 raw21977step2Labels := by
      have ha : raw21977step2 = (fun i j => raw21977step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw21977step2 raw21977step1; decide +kernel
      have hl : raw21977step2Labels = raw21977step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21977step1 raw21977step1Labels permutation31 permutation7
    mixedMoment B raw21977step2 raw21977step2Labels = mixedMoment B raw21977step3 raw21977step3Labels := by
      have ha : raw21977step3 = raw21977step2 := by apply Matrix.ext; unfold raw21977step3 raw21977step2; decide +kernel
      have hl : raw21977step2Labels = labelEmbedding1 ∘ raw21977step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21977step2 raw21977step2Labels raw21977step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1620 node1620Labels := by rfl

def raw21978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21978Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21978step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21978step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21978step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw21978step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21978step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw21978step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21978 raw21978Labels = mixedMoment B node1911 node1911Labels := by
  calc
    mixedMoment B raw21978 raw21978Labels = mixedMoment B raw21978step0 raw21978step0Labels := by
      have hz : ∀ j, raw21978 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21978step0 = (fun i j => raw21978 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21978step0 raw21978; decide +kernel
      have hl : raw21978step0Labels = raw21978Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21978 raw21978Labels permutation346 hz
    mixedMoment B raw21978step0 raw21978step0Labels = mixedMoment B raw21978step1 raw21978step1Labels := by
      have ha : raw21978step1 = (fun i j => raw21978step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21978step1 raw21978step0; decide +kernel
      have hl : raw21978step1Labels = raw21978step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21978step0 raw21978step0Labels permutation151 permutation2
    mixedMoment B raw21978step1 raw21978step1Labels = mixedMoment B raw21978step2 raw21978step2Labels := by
      have ha : raw21978step2 = -raw21978step1 := by apply Matrix.ext; change ∀ i j, raw21978step2 i j = -(raw21978step1 i j); unfold raw21978step2 raw21978step1; decide +kernel
      have hl : raw21978step2Labels = raw21978step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1911 node1911Labels := by rfl

def raw21979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21979Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21979step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21979step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21979step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21979step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21979 raw21979Labels = mixedMoment B node1007 node1007Labels := by
  calc
    mixedMoment B raw21979 raw21979Labels = mixedMoment B raw21979step0 raw21979step0Labels := by
      have hz : ∀ j, raw21979 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21979step0 = (fun i j => raw21979 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21979step0 raw21979; decide +kernel
      have hl : raw21979step0Labels = raw21979Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21979 raw21979Labels permutation346 hz
    mixedMoment B raw21979step0 raw21979step0Labels = mixedMoment B raw21979step1 raw21979step1Labels := by
      have hz : ∀ j, raw21979step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21979step1 = (fun i j => raw21979step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21979step1 raw21979step0; decide +kernel
      have hl : raw21979step1Labels = raw21979step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21979step0 raw21979step0Labels permutation56 hz
    _ = mixedMoment B node1007 node1007Labels := by rfl

def raw21980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21980Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21980step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw21980step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21980 raw21980Labels = mixedMoment B node898 node898Labels := by
  calc
    mixedMoment B raw21980 raw21980Labels = mixedMoment B raw21980step0 raw21980step0Labels := by
      have ha : raw21980step0 = (fun i j => raw21980 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21980step0 raw21980; decide +kernel
      have hl : raw21980step0Labels = raw21980Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21980 raw21980Labels permutation158 permutation2
    _ = mixedMoment B node898 node898Labels := by rfl

def raw21981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21981Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21981step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21981step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21981 raw21981Labels = mixedMoment B node916 node916Labels := by
  calc
    mixedMoment B raw21981 raw21981Labels = mixedMoment B raw21981step0 raw21981step0Labels := by
      have hz : ∀ j, raw21981 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21981step0 = (fun i j => raw21981 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21981step0 raw21981; decide +kernel
      have hl : raw21981step0Labels = raw21981Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21981 raw21981Labels permutation346 hz
    _ = mixedMoment B node916 node916Labels := by rfl

def raw21982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21982Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21982step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw21982step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21982 raw21982Labels = mixedMoment B node902 node902Labels := by
  calc
    mixedMoment B raw21982 raw21982Labels = mixedMoment B raw21982step0 raw21982step0Labels := by
      have hz : ∀ j, raw21982 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21982step0 = (fun i j => raw21982 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21982step0 raw21982; decide +kernel
      have hl : raw21982step0Labels = raw21982Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21982 raw21982Labels permutation346 hz
    _ = mixedMoment B node902 node902Labels := by rfl

def raw21983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21983Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21983step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw21983step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21983step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-4, 1, 3]]
def raw21983step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw21983step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw21983step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical21983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21983 raw21983Labels = mixedMoment B node867 node867Labels := by
  calc
    mixedMoment B raw21983 raw21983Labels = mixedMoment B raw21983step0 raw21983step0Labels := by
      have hz : ∀ j, raw21983 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21983step0 = (fun i j => raw21983 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21983step0 raw21983; decide +kernel
      have hl : raw21983step0Labels = raw21983Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21983 raw21983Labels permutation346 hz
    mixedMoment B raw21983step0 raw21983step0Labels = mixedMoment B raw21983step1 raw21983step1Labels := by
      have ha : raw21983step1 = (fun i j => raw21983step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw21983step1 raw21983step0; decide +kernel
      have hl : raw21983step1Labels = raw21983step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21983step0 raw21983step0Labels permutation151 permutation2
    mixedMoment B raw21983step1 raw21983step1Labels = mixedMoment B raw21983step2 raw21983step2Labels := by
      have ha : raw21983step2 = -raw21983step1 := by apply Matrix.ext; change ∀ i j, raw21983step2 i j = -(raw21983step1 i j); unfold raw21983step2 raw21983step1; decide +kernel
      have hl : raw21983step2Labels = raw21983step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node867 node867Labels := by rfl

def raw21984 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![0, 0], ![-1, 1], ![1, -1], ![3, -3]]
def raw21984Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21984step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![-1, 1], ![1, -1], ![3, -3]]
def raw21984step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw21984step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![3, -3]]
def raw21984step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical21984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21984 raw21984Labels = mixedMoment B node4081 node4081Labels := by
  calc
    mixedMoment B raw21984 raw21984Labels = mixedMoment B raw21984step0 raw21984step0Labels := by
      have hz : ∀ j, raw21984 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21984step0 = (fun i j => raw21984 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21984step0 raw21984; decide +kernel
      have hl : raw21984step0Labels = raw21984Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21984 raw21984Labels permutation346 hz
    mixedMoment B raw21984step0 raw21984step0Labels = mixedMoment B raw21984step1 raw21984step1Labels := by
      have hz : ∀ j, raw21984step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21984step1 = (fun i j => raw21984step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21984step1 raw21984step0; decide +kernel
      have hl : raw21984step1Labels = raw21984step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21984step0 raw21984step0Labels permutation56 hz
    _ = mixedMoment B node4081 node4081Labels := by rfl

def raw21985 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw21985Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw21985step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21985step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw21985step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw21985step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw21985step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw21985step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw21985step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21985 raw21985Labels = mixedMoment B node4211 node4211Labels := by
  calc
    mixedMoment B raw21985 raw21985Labels = mixedMoment B raw21985step0 raw21985step0Labels := by
      have hz : ∀ j, raw21985 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21985step0 = (fun i j => raw21985 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21985step0 raw21985; decide +kernel
      have hl : raw21985step0Labels = raw21985Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21985 raw21985Labels permutation346 hz
    mixedMoment B raw21985step0 raw21985step0Labels = mixedMoment B raw21985step1 raw21985step1Labels := by
      have ha : raw21985step1 = (fun i j => raw21985step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21985step1 raw21985step0; decide +kernel
      have hl : raw21985step1Labels = raw21985step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21985step0 raw21985step0Labels permutation38 permutation4
    mixedMoment B raw21985step1 raw21985step1Labels = mixedMoment B raw21985step2 raw21985step2Labels := by
      have ha : raw21985step2 = -raw21985step1 := by apply Matrix.ext; change ∀ i j, raw21985step2 i j = -(raw21985step1 i j); unfold raw21985step2 raw21985step1; decide +kernel
      have hl : raw21985step2Labels = raw21985step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21985step2 raw21985step2Labels = mixedMoment B raw21985step3 raw21985step3Labels := by
      have ha : raw21985step3 = raw21985step2 := by apply Matrix.ext; unfold raw21985step3 raw21985step2; decide +kernel
      have hl : raw21985step2Labels = labelEmbedding7 ∘ raw21985step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21985step2 raw21985step2Labels raw21985step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4211 node4211Labels := by rfl

def raw21986 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw21986Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21986step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw21986step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21986step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw21986step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21986 raw21986Labels = mixedMoment B node4384 node4384Labels := by
  calc
    mixedMoment B raw21986 raw21986Labels = mixedMoment B raw21986step0 raw21986step0Labels := by
      have ha : raw21986step0 = (fun i j => raw21986 (permutation182 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21986step0 raw21986; decide +kernel
      have hl : raw21986step0Labels = raw21986Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21986 raw21986Labels permutation182 permutation6
    mixedMoment B raw21986step0 raw21986step0Labels = mixedMoment B raw21986step1 raw21986step1Labels := by
      have ha : raw21986step1 = raw21986step0 := by apply Matrix.ext; unfold raw21986step1 raw21986step0; decide +kernel
      have hl : raw21986step0Labels = labelEmbedding9 ∘ raw21986step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21986step0 raw21986step0Labels raw21986step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4384 node4384Labels := by rfl

def raw21987 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -3, 3]]
def raw21987Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -3, 3]]
def raw21987step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21987step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw21987step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21987step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw21987step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21987 raw21987Labels = mixedMoment B node4377 node4377Labels := by
  calc
    mixedMoment B raw21987 raw21987Labels = mixedMoment B raw21987step0 raw21987step0Labels := by
      have hz : ∀ j, raw21987 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21987step0 = (fun i j => raw21987 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21987step0 raw21987; decide +kernel
      have hl : raw21987step0Labels = raw21987Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21987 raw21987Labels permutation346 hz
    mixedMoment B raw21987step0 raw21987step0Labels = mixedMoment B raw21987step1 raw21987step1Labels := by
      have ha : raw21987step1 = (fun i j => raw21987step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21987step1 raw21987step0; decide +kernel
      have hl : raw21987step1Labels = raw21987step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21987step0 raw21987step0Labels permutation38 permutation6
    mixedMoment B raw21987step1 raw21987step1Labels = mixedMoment B raw21987step2 raw21987step2Labels := by
      have ha : raw21987step2 = raw21987step1 := by apply Matrix.ext; unfold raw21987step2 raw21987step1; decide +kernel
      have hl : raw21987step1Labels = labelEmbedding9 ∘ raw21987step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21987step1 raw21987step1Labels raw21987step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4377 node4377Labels := by rfl

def raw21988 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw21988Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw21988step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21988step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw21988step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw21988step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw21988step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw21988step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw21988step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21988 raw21988Labels = mixedMoment B node4211 node4211Labels := by
  calc
    mixedMoment B raw21988 raw21988Labels = mixedMoment B raw21988step0 raw21988step0Labels := by
      have hz : ∀ j, raw21988 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21988step0 = (fun i j => raw21988 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21988step0 raw21988; decide +kernel
      have hl : raw21988step0Labels = raw21988Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21988 raw21988Labels permutation265 hz
    mixedMoment B raw21988step0 raw21988step0Labels = mixedMoment B raw21988step1 raw21988step1Labels := by
      have ha : raw21988step1 = (fun i j => raw21988step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21988step1 raw21988step0; decide +kernel
      have hl : raw21988step1Labels = raw21988step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21988step0 raw21988step0Labels permutation38 permutation4
    mixedMoment B raw21988step1 raw21988step1Labels = mixedMoment B raw21988step2 raw21988step2Labels := by
      have ha : raw21988step2 = -raw21988step1 := by apply Matrix.ext; change ∀ i j, raw21988step2 i j = -(raw21988step1 i j); unfold raw21988step2 raw21988step1; decide +kernel
      have hl : raw21988step2Labels = raw21988step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21988step2 raw21988step2Labels = mixedMoment B raw21988step3 raw21988step3Labels := by
      have ha : raw21988step3 = raw21988step2 := by apply Matrix.ext; unfold raw21988step3 raw21988step2; decide +kernel
      have hl : raw21988step2Labels = labelEmbedding7 ∘ raw21988step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21988step2 raw21988step2Labels raw21988step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4211 node4211Labels := by rfl

def raw21989 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw21989Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21989step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw21989step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21989step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw21989step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21989 raw21989Labels = mixedMoment B node4384 node4384Labels := by
  calc
    mixedMoment B raw21989 raw21989Labels = mixedMoment B raw21989step0 raw21989step0Labels := by
      have ha : raw21989step0 = (fun i j => raw21989 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21989step0 raw21989; decide +kernel
      have hl : raw21989step0Labels = raw21989Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21989 raw21989Labels permutation158 permutation6
    mixedMoment B raw21989step0 raw21989step0Labels = mixedMoment B raw21989step1 raw21989step1Labels := by
      have ha : raw21989step1 = raw21989step0 := by apply Matrix.ext; unfold raw21989step1 raw21989step0; decide +kernel
      have hl : raw21989step0Labels = labelEmbedding9 ∘ raw21989step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21989step0 raw21989step0Labels raw21989step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4384 node4384Labels := by rfl

def raw21990 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -3, 3]]
def raw21990Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -3, 3]]
def raw21990step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21990step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw21990step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21990step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![3, 0, -3]]
def raw21990step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21990 raw21990Labels = mixedMoment B node4377 node4377Labels := by
  calc
    mixedMoment B raw21990 raw21990Labels = mixedMoment B raw21990step0 raw21990step0Labels := by
      have hz : ∀ j, raw21990 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21990step0 = (fun i j => raw21990 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21990step0 raw21990; decide +kernel
      have hl : raw21990step0Labels = raw21990Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21990 raw21990Labels permutation265 hz
    mixedMoment B raw21990step0 raw21990step0Labels = mixedMoment B raw21990step1 raw21990step1Labels := by
      have ha : raw21990step1 = (fun i j => raw21990step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21990step1 raw21990step0; decide +kernel
      have hl : raw21990step1Labels = raw21990step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21990step0 raw21990step0Labels permutation38 permutation6
    mixedMoment B raw21990step1 raw21990step1Labels = mixedMoment B raw21990step2 raw21990step2Labels := by
      have ha : raw21990step2 = raw21990step1 := by apply Matrix.ext; unfold raw21990step2 raw21990step1; decide +kernel
      have hl : raw21990step1Labels = labelEmbedding9 ∘ raw21990step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21990step1 raw21990step1Labels raw21990step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4377 node4377Labels := by rfl

def raw21991 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -3, 3]]
def raw21991Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21991step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -3, 3]]
def raw21991step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21991step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, -1, 1], ![0, -3, 3]]
def raw21991step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21991step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 4, -4], ![0, -1, 1], ![0, -3, 3]]
def raw21991step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21991step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![4, -4], ![-1, 1], ![-3, 3]]
def raw21991step3Labels : Fin 2 → Fin 3 := ![1, 2]

def raw21991step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]
def raw21991step4Labels : Fin 2 → Fin 3 := ![1, 2]

def raw21991step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![3, -3]]
def raw21991step5Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical21991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21991 raw21991Labels = mixedMoment B node4070 node4070Labels := by
  calc
    mixedMoment B raw21991 raw21991Labels = mixedMoment B raw21991step0 raw21991step0Labels := by
      have hz : ∀ j, raw21991 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21991step0 = (fun i j => raw21991 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21991step0 raw21991; decide +kernel
      have hl : raw21991step0Labels = raw21991Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21991 raw21991Labels permutation434 hz
    mixedMoment B raw21991step0 raw21991step0Labels = mixedMoment B raw21991step1 raw21991step1Labels := by
      have hz : ∀ j, raw21991step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21991step1 = (fun i j => raw21991step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21991step1 raw21991step0; decide +kernel
      have hl : raw21991step1Labels = raw21991step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21991step0 raw21991step0Labels permutation80 hz
    mixedMoment B raw21991step1 raw21991step1Labels = mixedMoment B raw21991step2 raw21991step2Labels := by
      have hz : ∀ j, raw21991step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw21991step2 = (fun i j => raw21991step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw21991step2 raw21991step1; decide +kernel
      have hl : raw21991step2Labels = raw21991step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21991step1 raw21991step1Labels permutation14 hz
    mixedMoment B raw21991step2 raw21991step2Labels = mixedMoment B raw21991step3 raw21991step3Labels := by
      have hz : ∀ i, raw21991step2 i (permutation2 0) = 0 := by decide +kernel
      have ha : raw21991step3 = (fun i j => raw21991step2 i (permutation2 j.succ)) := by apply Matrix.ext; unfold raw21991step3 raw21991step2; decide +kernel
      have hl : raw21991step3Labels = (fun j => raw21991step2Labels (permutation2 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw21991step2 raw21991step2Labels permutation2 hz
    mixedMoment B raw21991step3 raw21991step3Labels = mixedMoment B raw21991step4 raw21991step4Labels := by
      have ha : raw21991step4 = -raw21991step3 := by apply Matrix.ext; change ∀ i j, raw21991step4 i j = -(raw21991step3 i j); unfold raw21991step4 raw21991step3; decide +kernel
      have hl : raw21991step4Labels = raw21991step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21991step4 raw21991step4Labels = mixedMoment B raw21991step5 raw21991step5Labels := by
      have ha : raw21991step5 = raw21991step4 := by apply Matrix.ext; unfold raw21991step5 raw21991step4; decide +kernel
      have hl : raw21991step4Labels = labelEmbedding3 ∘ raw21991step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21991step4 raw21991step4Labels raw21991step5Labels labelEmbedding3 hl
    _ = mixedMoment B node4070 node4070Labels := by rfl

def raw21992 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -3, 3]]
def raw21992Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -3, 3]]
def raw21992step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21992step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw21992step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21992step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21992step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21992step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21992step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21992 raw21992Labels = mixedMoment B node4426 node4426Labels := by
  calc
    mixedMoment B raw21992 raw21992Labels = mixedMoment B raw21992step0 raw21992step0Labels := by
      have hz : ∀ j, raw21992 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21992step0 = (fun i j => raw21992 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21992step0 raw21992; decide +kernel
      have hl : raw21992step0Labels = raw21992Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21992 raw21992Labels permutation434 hz
    mixedMoment B raw21992step0 raw21992step0Labels = mixedMoment B raw21992step1 raw21992step1Labels := by
      have hz : ∀ j, raw21992step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw21992step1 = (fun i j => raw21992step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw21992step1 raw21992step0; decide +kernel
      have hl : raw21992step1Labels = raw21992step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21992step0 raw21992step0Labels permutation80 hz
    mixedMoment B raw21992step1 raw21992step1Labels = mixedMoment B raw21992step2 raw21992step2Labels := by
      have ha : raw21992step2 = (fun i j => raw21992step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21992step2 raw21992step1; decide +kernel
      have hl : raw21992step2Labels = raw21992step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21992step1 raw21992step1Labels permutation8 permutation6
    mixedMoment B raw21992step2 raw21992step2Labels = mixedMoment B raw21992step3 raw21992step3Labels := by
      have ha : raw21992step3 = raw21992step2 := by apply Matrix.ext; unfold raw21992step3 raw21992step2; decide +kernel
      have hl : raw21992step2Labels = labelEmbedding9 ∘ raw21992step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21992step2 raw21992step2Labels raw21992step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4426 node4426Labels := by rfl

def raw21993 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -3, 3]]
def raw21993Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21993step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw21993step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21993step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw21993step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21993step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21993step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21993step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw21993step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21993 raw21993Labels = mixedMoment B node4426 node4426Labels := by
  calc
    mixedMoment B raw21993 raw21993Labels = mixedMoment B raw21993step0 raw21993step0Labels := by
      have hz : ∀ j, raw21993 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw21993step0 = (fun i j => raw21993 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw21993step0 raw21993; decide +kernel
      have hl : raw21993step0Labels = raw21993Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21993 raw21993Labels permutation434 hz
    mixedMoment B raw21993step0 raw21993step0Labels = mixedMoment B raw21993step1 raw21993step1Labels := by
      have hz : ∀ j, raw21993step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21993step1 = (fun i j => raw21993step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21993step1 raw21993step0; decide +kernel
      have hl : raw21993step1Labels = raw21993step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21993step0 raw21993step0Labels permutation56 hz
    mixedMoment B raw21993step1 raw21993step1Labels = mixedMoment B raw21993step2 raw21993step2Labels := by
      have ha : raw21993step2 = (fun i j => raw21993step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21993step2 raw21993step1; decide +kernel
      have hl : raw21993step2Labels = raw21993step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21993step1 raw21993step1Labels permutation8 permutation6
    mixedMoment B raw21993step2 raw21993step2Labels = mixedMoment B raw21993step3 raw21993step3Labels := by
      have ha : raw21993step3 = raw21993step2 := by apply Matrix.ext; unfold raw21993step3 raw21993step2; decide +kernel
      have hl : raw21993step2Labels = labelEmbedding9 ∘ raw21993step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21993step2 raw21993step2Labels raw21993step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4426 node4426Labels := by rfl

def raw21994 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -3, 3]]
def raw21994Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -3, 3]]
def raw21994step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21994step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![1, -2, 1], ![0, -3, 3]]
def raw21994step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21994step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-2, 1, 1], ![-3, 0, 3]]
def raw21994step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw21994step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, -1, -1], ![3, 0, -3]]
def raw21994step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw21994step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![2, -1, -1], ![3, 0, -3]]
def raw21994step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21994 raw21994Labels = mixedMoment B node4227 node4227Labels := by
  calc
    mixedMoment B raw21994 raw21994Labels = mixedMoment B raw21994step0 raw21994step0Labels := by
      have hz : ∀ j, raw21994 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21994step0 = (fun i j => raw21994 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21994step0 raw21994; decide +kernel
      have hl : raw21994step0Labels = raw21994Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21994 raw21994Labels permutation346 hz
    mixedMoment B raw21994step0 raw21994step0Labels = mixedMoment B raw21994step1 raw21994step1Labels := by
      have hz : ∀ j, raw21994step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21994step1 = (fun i j => raw21994step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21994step1 raw21994step0; decide +kernel
      have hl : raw21994step1Labels = raw21994step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21994step0 raw21994step0Labels permutation56 hz
    mixedMoment B raw21994step1 raw21994step1Labels = mixedMoment B raw21994step2 raw21994step2Labels := by
      have ha : raw21994step2 = (fun i j => raw21994step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21994step2 raw21994step1; decide +kernel
      have hl : raw21994step2Labels = raw21994step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21994step1 raw21994step1Labels permutation8 permutation4
    mixedMoment B raw21994step2 raw21994step2Labels = mixedMoment B raw21994step3 raw21994step3Labels := by
      have ha : raw21994step3 = -raw21994step2 := by apply Matrix.ext; change ∀ i j, raw21994step3 i j = -(raw21994step2 i j); unfold raw21994step3 raw21994step2; decide +kernel
      have hl : raw21994step3Labels = raw21994step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21994step3 raw21994step3Labels = mixedMoment B raw21994step4 raw21994step4Labels := by
      have ha : raw21994step4 = raw21994step3 := by apply Matrix.ext; unfold raw21994step4 raw21994step3; decide +kernel
      have hl : raw21994step3Labels = labelEmbedding7 ∘ raw21994step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21994step3 raw21994step3Labels raw21994step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4227 node4227Labels := by rfl

def raw21995 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -3, 3]]
def raw21995Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -3, 3]]
def raw21995step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21995step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, 0, -3]]
def raw21995step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21995step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, 0, -3]]
def raw21995step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21995 raw21995Labels = mixedMoment B node4388 node4388Labels := by
  calc
    mixedMoment B raw21995 raw21995Labels = mixedMoment B raw21995step0 raw21995step0Labels := by
      have hz : ∀ j, raw21995 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21995step0 = (fun i j => raw21995 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21995step0 raw21995; decide +kernel
      have hl : raw21995step0Labels = raw21995Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21995 raw21995Labels permutation346 hz
    mixedMoment B raw21995step0 raw21995step0Labels = mixedMoment B raw21995step1 raw21995step1Labels := by
      have ha : raw21995step1 = (fun i j => raw21995step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21995step1 raw21995step0; decide +kernel
      have hl : raw21995step1Labels = raw21995step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21995step0 raw21995step0Labels permutation32 permutation6
    mixedMoment B raw21995step1 raw21995step1Labels = mixedMoment B raw21995step2 raw21995step2Labels := by
      have ha : raw21995step2 = raw21995step1 := by apply Matrix.ext; unfold raw21995step2 raw21995step1; decide +kernel
      have hl : raw21995step1Labels = labelEmbedding9 ∘ raw21995step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21995step1 raw21995step1Labels raw21995step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4388 node4388Labels := by rfl

def raw21996 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -3, 3]]
def raw21996Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -3, 3]]
def raw21996step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21996step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, 0, -3]]
def raw21996step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21996step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![3, 0, -3]]
def raw21996step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21996 raw21996Labels = mixedMoment B node4388 node4388Labels := by
  calc
    mixedMoment B raw21996 raw21996Labels = mixedMoment B raw21996step0 raw21996step0Labels := by
      have hz : ∀ j, raw21996 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw21996step0 = (fun i j => raw21996 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw21996step0 raw21996; decide +kernel
      have hl : raw21996step0Labels = raw21996Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21996 raw21996Labels permutation265 hz
    mixedMoment B raw21996step0 raw21996step0Labels = mixedMoment B raw21996step1 raw21996step1Labels := by
      have ha : raw21996step1 = (fun i j => raw21996step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21996step1 raw21996step0; decide +kernel
      have hl : raw21996step1Labels = raw21996step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21996step0 raw21996step0Labels permutation32 permutation6
    mixedMoment B raw21996step1 raw21996step1Labels = mixedMoment B raw21996step2 raw21996step2Labels := by
      have ha : raw21996step2 = raw21996step1 := by apply Matrix.ext; unfold raw21996step2 raw21996step1; decide +kernel
      have hl : raw21996step1Labels = labelEmbedding9 ∘ raw21996step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21996step1 raw21996step1Labels raw21996step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4388 node4388Labels := by rfl

def raw21997 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![0, -3, 3]]
def raw21997Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![0, -3, 3]]
def raw21997step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21997step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 2, 0], ![1, -2, 1], ![0, -3, 3]]
def raw21997step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21997step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 1, -2], ![3, 0, -3]]
def raw21997step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw21997step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![1, 1, -2], ![3, 0, -3]]
def raw21997step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21997 raw21997Labels = mixedMoment B node4382 node4382Labels := by
  calc
    mixedMoment B raw21997 raw21997Labels = mixedMoment B raw21997step0 raw21997step0Labels := by
      have hz : ∀ j, raw21997 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21997step0 = (fun i j => raw21997 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21997step0 raw21997; decide +kernel
      have hl : raw21997step0Labels = raw21997Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21997 raw21997Labels permutation346 hz
    mixedMoment B raw21997step0 raw21997step0Labels = mixedMoment B raw21997step1 raw21997step1Labels := by
      have hz : ∀ j, raw21997step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21997step1 = (fun i j => raw21997step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21997step1 raw21997step0; decide +kernel
      have hl : raw21997step1Labels = raw21997step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21997step0 raw21997step0Labels permutation56 hz
    mixedMoment B raw21997step1 raw21997step1Labels = mixedMoment B raw21997step2 raw21997step2Labels := by
      have ha : raw21997step2 = (fun i j => raw21997step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw21997step2 raw21997step1; decide +kernel
      have hl : raw21997step2Labels = raw21997step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21997step1 raw21997step1Labels permutation8 permutation6
    mixedMoment B raw21997step2 raw21997step2Labels = mixedMoment B raw21997step3 raw21997step3Labels := by
      have ha : raw21997step3 = raw21997step2 := by apply Matrix.ext; unfold raw21997step3 raw21997step2; decide +kernel
      have hl : raw21997step2Labels = labelEmbedding9 ∘ raw21997step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21997step2 raw21997step2Labels raw21997step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4382 node4382Labels := by rfl

def raw21998 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -4, 3]]
def raw21998Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21998step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 4, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -4, 3]]
def raw21998step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21998step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 4, -4], ![-1, 1, 0], ![0, -1, 1], ![1, -4, 3]]
def raw21998step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21998step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, 0, -4], ![1, -1, 0], ![-1, 0, 1], ![-4, 1, 3]]
def raw21998step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw21998step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![4, -1, -3]]
def raw21998step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw21998step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 0, 4], ![-1, 1, 0], ![1, 0, -1], ![4, -1, -3]]
def raw21998step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21998 raw21998Labels = mixedMoment B node4222 node4222Labels := by
  calc
    mixedMoment B raw21998 raw21998Labels = mixedMoment B raw21998step0 raw21998step0Labels := by
      have hz : ∀ j, raw21998 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21998step0 = (fun i j => raw21998 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21998step0 raw21998; decide +kernel
      have hl : raw21998step0Labels = raw21998Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21998 raw21998Labels permutation346 hz
    mixedMoment B raw21998step0 raw21998step0Labels = mixedMoment B raw21998step1 raw21998step1Labels := by
      have hz : ∀ j, raw21998step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw21998step1 = (fun i j => raw21998step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw21998step1 raw21998step0; decide +kernel
      have hl : raw21998step1Labels = raw21998step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21998step0 raw21998step0Labels permutation56 hz
    mixedMoment B raw21998step1 raw21998step1Labels = mixedMoment B raw21998step2 raw21998step2Labels := by
      have ha : raw21998step2 = (fun i j => raw21998step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21998step2 raw21998step1; decide +kernel
      have hl : raw21998step2Labels = raw21998step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21998step1 raw21998step1Labels permutation8 permutation4
    mixedMoment B raw21998step2 raw21998step2Labels = mixedMoment B raw21998step3 raw21998step3Labels := by
      have ha : raw21998step3 = -raw21998step2 := by apply Matrix.ext; change ∀ i j, raw21998step3 i j = -(raw21998step2 i j); unfold raw21998step3 raw21998step2; decide +kernel
      have hl : raw21998step3Labels = raw21998step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw21998step3 raw21998step3Labels = mixedMoment B raw21998step4 raw21998step4Labels := by
      have ha : raw21998step4 = raw21998step3 := by apply Matrix.ext; unfold raw21998step4 raw21998step3; decide +kernel
      have hl : raw21998step3Labels = labelEmbedding7 ∘ raw21998step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21998step3 raw21998step3Labels raw21998step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4222 node4222Labels := by rfl

def raw21999 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -4, 3]]
def raw21999Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -4, 3]]
def raw21999step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw21999step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw21999step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw21999step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw21999step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical21999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw21999 raw21999Labels = mixedMoment B node4299 node4299Labels := by
  calc
    mixedMoment B raw21999 raw21999Labels = mixedMoment B raw21999step0 raw21999step0Labels := by
      have hz : ∀ j, raw21999 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw21999step0 = (fun i j => raw21999 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw21999step0 raw21999; decide +kernel
      have hl : raw21999step0Labels = raw21999Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw21999 raw21999Labels permutation346 hz
    mixedMoment B raw21999step0 raw21999step0Labels = mixedMoment B raw21999step1 raw21999step1Labels := by
      have ha : raw21999step1 = (fun i j => raw21999step0 (permutation149 i) (permutation4 j)) := by apply Matrix.ext; unfold raw21999step1 raw21999step0; decide +kernel
      have hl : raw21999step1Labels = raw21999step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw21999step0 raw21999step0Labels permutation149 permutation4
    mixedMoment B raw21999step1 raw21999step1Labels = mixedMoment B raw21999step2 raw21999step2Labels := by
      have ha : raw21999step2 = raw21999step1 := by apply Matrix.ext; unfold raw21999step2 raw21999step1; decide +kernel
      have hl : raw21999step1Labels = labelEmbedding7 ∘ raw21999step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw21999step1 raw21999step1Labels raw21999step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4299 node4299Labels := by rfl

def raw22000 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -4, 3]]
def raw22000Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -4, 3]]
def raw22000step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22000step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw22000step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22000step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, 1, -4]]
def raw22000step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22000 raw22000Labels = mixedMoment B node4299 node4299Labels := by
  calc
    mixedMoment B raw22000 raw22000Labels = mixedMoment B raw22000step0 raw22000step0Labels := by
      have hz : ∀ j, raw22000 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw22000step0 = (fun i j => raw22000 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw22000step0 raw22000; decide +kernel
      have hl : raw22000step0Labels = raw22000Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22000 raw22000Labels permutation265 hz
    mixedMoment B raw22000step0 raw22000step0Labels = mixedMoment B raw22000step1 raw22000step1Labels := by
      have ha : raw22000step1 = (fun i j => raw22000step0 (permutation149 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22000step1 raw22000step0; decide +kernel
      have hl : raw22000step1Labels = raw22000step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22000step0 raw22000step0Labels permutation149 permutation4
    mixedMoment B raw22000step1 raw22000step1Labels = mixedMoment B raw22000step2 raw22000step2Labels := by
      have ha : raw22000step2 = raw22000step1 := by apply Matrix.ext; unfold raw22000step2 raw22000step1; decide +kernel
      have hl : raw22000step1Labels = labelEmbedding7 ∘ raw22000step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22000step1 raw22000step1Labels raw22000step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4299 node4299Labels := by rfl

def raw22001 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![1, -4, 3]]
def raw22001Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![1, -4, 3]]
def raw22001step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22001step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-2, 2, 0], ![0, -1, 1], ![1, -4, 3]]
def raw22001step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw22001step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, -2, 0], ![3, 1, -4]]
def raw22001step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw22001step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, -2, 0], ![3, 1, -4]]
def raw22001step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical22001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22001 raw22001Labels = mixedMoment B node4316 node4316Labels := by
  calc
    mixedMoment B raw22001 raw22001Labels = mixedMoment B raw22001step0 raw22001step0Labels := by
      have hz : ∀ j, raw22001 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw22001step0 = (fun i j => raw22001 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw22001step0 raw22001; decide +kernel
      have hl : raw22001step0Labels = raw22001Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22001 raw22001Labels permutation346 hz
    mixedMoment B raw22001step0 raw22001step0Labels = mixedMoment B raw22001step1 raw22001step1Labels := by
      have hz : ∀ j, raw22001step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw22001step1 = (fun i j => raw22001step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw22001step1 raw22001step0; decide +kernel
      have hl : raw22001step1Labels = raw22001step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22001step0 raw22001step0Labels permutation56 hz
    mixedMoment B raw22001step1 raw22001step1Labels = mixedMoment B raw22001step2 raw22001step2Labels := by
      have ha : raw22001step2 = (fun i j => raw22001step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw22001step2 raw22001step1; decide +kernel
      have hl : raw22001step2Labels = raw22001step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22001step1 raw22001step1Labels permutation31 permutation4
    mixedMoment B raw22001step2 raw22001step2Labels = mixedMoment B raw22001step3 raw22001step3Labels := by
      have ha : raw22001step3 = raw22001step2 := by apply Matrix.ext; unfold raw22001step3 raw22001step2; decide +kernel
      have hl : raw22001step2Labels = labelEmbedding7 ∘ raw22001step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw22001step2 raw22001step2Labels raw22001step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4316 node4316Labels := by rfl

def raw22002 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw22002Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw22002step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22002step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw22002step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22002 raw22002Labels = mixedMoment B node1715 node1715Labels := by
  calc
    mixedMoment B raw22002 raw22002Labels = mixedMoment B raw22002step0 raw22002step0Labels := by
      have hz : ∀ j, raw22002 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22002step0 = (fun i j => raw22002 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22002step0 raw22002; decide +kernel
      have hl : raw22002step0Labels = raw22002Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22002 raw22002Labels permutation434 hz
    mixedMoment B raw22002step0 raw22002step0Labels = mixedMoment B raw22002step1 raw22002step1Labels := by
      have ha : raw22002step1 = (fun i j => raw22002step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22002step1 raw22002step0; decide +kernel
      have hl : raw22002step1Labels = raw22002step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22002step0 raw22002step0Labels permutation38 permutation2
    _ = mixedMoment B node1715 node1715Labels := by rfl

def raw22003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw22003Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw22003step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22003step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw22003step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22003 raw22003Labels = mixedMoment B node811 node811Labels := by
  calc
    mixedMoment B raw22003 raw22003Labels = mixedMoment B raw22003step0 raw22003step0Labels := by
      have hz : ∀ j, raw22003 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22003step0 = (fun i j => raw22003 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22003step0 raw22003; decide +kernel
      have hl : raw22003step0Labels = raw22003Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22003 raw22003Labels permutation434 hz
    mixedMoment B raw22003step0 raw22003step0Labels = mixedMoment B raw22003step1 raw22003step1Labels := by
      have ha : raw22003step1 = (fun i j => raw22003step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22003step1 raw22003step0; decide +kernel
      have hl : raw22003step1Labels = raw22003step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22003step0 raw22003step0Labels permutation40 permutation2
    _ = mixedMoment B node811 node811Labels := by rfl

def raw22004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw22004Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw22004step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22004 raw22004Labels = mixedMoment B node827 node827Labels := by
  calc
    mixedMoment B raw22004 raw22004Labels = mixedMoment B raw22004step0 raw22004step0Labels := by
      have hz : ∀ j, raw22004 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22004step0 = (fun i j => raw22004 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22004step0 raw22004; decide +kernel
      have hl : raw22004step0Labels = raw22004Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22004 raw22004Labels permutation434 hz
    _ = mixedMoment B node827 node827Labels := by rfl

def raw22005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw22005Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22005step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw22005step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22005 raw22005Labels = mixedMoment B node793 node793Labels := by
  calc
    mixedMoment B raw22005 raw22005Labels = mixedMoment B raw22005step0 raw22005step0Labels := by
      have ha : raw22005step0 = (fun i j => raw22005 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22005step0 raw22005; decide +kernel
      have hl : raw22005step0Labels = raw22005Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22005 raw22005Labels permutation176 permutation2
    _ = mixedMoment B node793 node793Labels := by rfl

def raw22006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw22006Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw22006step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22006step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22006step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22006 raw22006Labels = mixedMoment B node796 node796Labels := by
  calc
    mixedMoment B raw22006 raw22006Labels = mixedMoment B raw22006step0 raw22006step0Labels := by
      have hz : ∀ j, raw22006 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22006step0 = (fun i j => raw22006 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22006step0 raw22006; decide +kernel
      have hl : raw22006step0Labels = raw22006Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22006 raw22006Labels permutation434 hz
    mixedMoment B raw22006step0 raw22006step0Labels = mixedMoment B raw22006step1 raw22006step1Labels := by
      have ha : raw22006step1 = (fun i j => raw22006step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22006step1 raw22006step0; decide +kernel
      have hl : raw22006step1Labels = raw22006step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22006step0 raw22006step0Labels permutation39 permutation2
    _ = mixedMoment B node796 node796Labels := by rfl

def raw22007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw22007Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw22007step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22007step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw22007step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22007 raw22007Labels = mixedMoment B node795 node795Labels := by
  calc
    mixedMoment B raw22007 raw22007Labels = mixedMoment B raw22007step0 raw22007step0Labels := by
      have hz : ∀ j, raw22007 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22007step0 = (fun i j => raw22007 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22007step0 raw22007; decide +kernel
      have hl : raw22007step0Labels = raw22007Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22007 raw22007Labels permutation434 hz
    mixedMoment B raw22007step0 raw22007step0Labels = mixedMoment B raw22007step1 raw22007step1Labels := by
      have ha : raw22007step1 = (fun i j => raw22007step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22007step1 raw22007step0; decide +kernel
      have hl : raw22007step1Labels = raw22007step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22007step0 raw22007step0Labels permutation38 permutation2
    _ = mixedMoment B node795 node795Labels := by rfl

def raw22008 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![1, -1], ![0, 0], ![1, -1], ![0, 0]]
def raw22008Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22008step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![1, -1], ![0, 0], ![1, -1]]
def raw22008step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22008step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![1, -1], ![1, -1]]
def raw22008step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22008step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw22008step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical22008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22008 raw22008Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw22008 raw22008Labels = mixedMoment B raw22008step0 raw22008step0Labels := by
      have hz : ∀ j, raw22008 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw22008step0 = (fun i j => raw22008 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw22008step0 raw22008; decide +kernel
      have hl : raw22008step0Labels = raw22008Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22008 raw22008Labels permutation590 hz
    mixedMoment B raw22008step0 raw22008step0Labels = mixedMoment B raw22008step1 raw22008step1Labels := by
      have hz : ∀ j, raw22008step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw22008step1 = (fun i j => raw22008step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw22008step1 raw22008step0; decide +kernel
      have hl : raw22008step1Labels = raw22008step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22008step0 raw22008step0Labels permutation104 hz
    mixedMoment B raw22008step1 raw22008step1Labels = mixedMoment B raw22008step2 raw22008step2Labels := by
      have ha : raw22008step2 = (fun i j => raw22008step1 (permutation11 i) (permutation0 j)) := by apply Matrix.ext; unfold raw22008step2 raw22008step1; decide +kernel
      have hl : raw22008step2Labels = raw22008step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22008step1 raw22008step1Labels permutation11 permutation0
    _ = mixedMoment B node4069 node4069Labels := by rfl

def raw22009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw22009Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22009step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw22009step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22009step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw22009step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22009 raw22009Labels = mixedMoment B node1714 node1714Labels := by
  calc
    mixedMoment B raw22009 raw22009Labels = mixedMoment B raw22009step0 raw22009step0Labels := by
      have hz : ∀ j, raw22009 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22009step0 = (fun i j => raw22009 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22009step0 raw22009; decide +kernel
      have hl : raw22009step0Labels = raw22009Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22009 raw22009Labels permutation434 hz
    mixedMoment B raw22009step0 raw22009step0Labels = mixedMoment B raw22009step1 raw22009step1Labels := by
      have ha : raw22009step1 = (fun i j => raw22009step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22009step1 raw22009step0; decide +kernel
      have hl : raw22009step1Labels = raw22009step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22009step0 raw22009step0Labels permutation38 permutation2
    _ = mixedMoment B node1714 node1714Labels := by rfl

def raw22010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw22010Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22010step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw22010step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22010step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw22010step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22010 raw22010Labels = mixedMoment B node807 node807Labels := by
  calc
    mixedMoment B raw22010 raw22010Labels = mixedMoment B raw22010step0 raw22010step0Labels := by
      have hz : ∀ j, raw22010 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22010step0 = (fun i j => raw22010 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22010step0 raw22010; decide +kernel
      have hl : raw22010step0Labels = raw22010Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22010 raw22010Labels permutation434 hz
    mixedMoment B raw22010step0 raw22010step0Labels = mixedMoment B raw22010step1 raw22010step1Labels := by
      have ha : raw22010step1 = (fun i j => raw22010step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22010step1 raw22010step0; decide +kernel
      have hl : raw22010step1Labels = raw22010step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22010step0 raw22010step0Labels permutation40 permutation2
    _ = mixedMoment B node807 node807Labels := by rfl

def raw22011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw22011Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22011step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw22011step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22011step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw22011step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22011 raw22011Labels = mixedMoment B node824 node824Labels := by
  calc
    mixedMoment B raw22011 raw22011Labels = mixedMoment B raw22011step0 raw22011step0Labels := by
      have hz : ∀ j, raw22011 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22011step0 = (fun i j => raw22011 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22011step0 raw22011; decide +kernel
      have hl : raw22011step0Labels = raw22011Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22011 raw22011Labels permutation434 hz
    mixedMoment B raw22011step0 raw22011step0Labels = mixedMoment B raw22011step1 raw22011step1Labels := by
      have ha : raw22011step1 = (fun i j => raw22011step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22011step1 raw22011step0; decide +kernel
      have hl : raw22011step1Labels = raw22011step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22011step0 raw22011step0Labels permutation34 permutation2
    _ = mixedMoment B node824 node824Labels := by rfl

def raw22012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw22012Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22012step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw22012step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22012 raw22012Labels = mixedMoment B node792 node792Labels := by
  calc
    mixedMoment B raw22012 raw22012Labels = mixedMoment B raw22012step0 raw22012step0Labels := by
      have ha : raw22012step0 = (fun i j => raw22012 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22012step0 raw22012; decide +kernel
      have hl : raw22012step0Labels = raw22012Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22012 raw22012Labels permutation176 permutation2
    _ = mixedMoment B node792 node792Labels := by rfl

def raw22013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw22013Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw22013step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22013step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw22013step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22013 raw22013Labels = mixedMoment B node796 node796Labels := by
  calc
    mixedMoment B raw22013 raw22013Labels = mixedMoment B raw22013step0 raw22013step0Labels := by
      have hz : ∀ j, raw22013 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22013step0 = (fun i j => raw22013 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22013step0 raw22013; decide +kernel
      have hl : raw22013step0Labels = raw22013Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22013 raw22013Labels permutation434 hz
    mixedMoment B raw22013step0 raw22013step0Labels = mixedMoment B raw22013step1 raw22013step1Labels := by
      have ha : raw22013step1 = (fun i j => raw22013step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22013step1 raw22013step0; decide +kernel
      have hl : raw22013step1Labels = raw22013step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22013step0 raw22013step0Labels permutation38 permutation2
    _ = mixedMoment B node796 node796Labels := by rfl

def raw22014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw22014Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22014step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw22014step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw22014step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw22014step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical22014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22014 raw22014Labels = mixedMoment B node794 node794Labels := by
  calc
    mixedMoment B raw22014 raw22014Labels = mixedMoment B raw22014step0 raw22014step0Labels := by
      have hz : ∀ j, raw22014 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw22014step0 = (fun i j => raw22014 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw22014step0 raw22014; decide +kernel
      have hl : raw22014step0Labels = raw22014Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22014 raw22014Labels permutation434 hz
    mixedMoment B raw22014step0 raw22014step0Labels = mixedMoment B raw22014step1 raw22014step1Labels := by
      have ha : raw22014step1 = (fun i j => raw22014step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw22014step1 raw22014step0; decide +kernel
      have hl : raw22014step1Labels = raw22014step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22014step0 raw22014step0Labels permutation38 permutation2
    _ = mixedMoment B node794 node794Labels := by rfl

def raw22015 : Matrix (Fin 6) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![1, -1], ![0, 0], ![0, 0], ![1, -1]]
def raw22015Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22015step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![1, -1], ![0, 0], ![1, -1]]
def raw22015step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22015step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![1, -1], ![1, -1]]
def raw22015step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw22015step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw22015step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical22015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw22015 raw22015Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw22015 raw22015Labels = mixedMoment B raw22015step0 raw22015step0Labels := by
      have hz : ∀ j, raw22015 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw22015step0 = (fun i j => raw22015 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw22015step0 raw22015; decide +kernel
      have hl : raw22015step0Labels = raw22015Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22015 raw22015Labels permutation520 hz
    mixedMoment B raw22015step0 raw22015step0Labels = mixedMoment B raw22015step1 raw22015step1Labels := by
      have hz : ∀ j, raw22015step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw22015step1 = (fun i j => raw22015step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw22015step1 raw22015step0; decide +kernel
      have hl : raw22015step1Labels = raw22015step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw22015step0 raw22015step0Labels permutation104 hz
    mixedMoment B raw22015step1 raw22015step1Labels = mixedMoment B raw22015step2 raw22015step2Labels := by
      have ha : raw22015step2 = (fun i j => raw22015step1 (permutation11 i) (permutation0 j)) := by apply Matrix.ext; unfold raw22015step2 raw22015step1; decide +kernel
      have hl : raw22015step2Labels = raw22015step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw22015step1 raw22015step1Labels permutation11 permutation0
    _ = mixedMoment B node4069 node4069Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
