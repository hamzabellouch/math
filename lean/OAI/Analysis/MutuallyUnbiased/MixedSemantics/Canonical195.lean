import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes8
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw24960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw24960Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24960step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw24960step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24960step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw24960step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24960 raw24960Labels = mixedMoment B node2215 node2215Labels := by
  calc
    mixedMoment B raw24960 raw24960Labels = mixedMoment B raw24960step0 raw24960step0Labels := by
      have hz : ∀ j, raw24960 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24960step0 = (fun i j => raw24960 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24960step0 raw24960; decide +kernel
      have hl : raw24960step0Labels = raw24960Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24960 raw24960Labels permutation520 hz
    mixedMoment B raw24960step0 raw24960step0Labels = mixedMoment B raw24960step1 raw24960step1Labels := by
      have ha : raw24960step1 = (fun i j => raw24960step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24960step1 raw24960step0; decide +kernel
      have hl : raw24960step1Labels = raw24960step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24960step0 raw24960step0Labels permutation38 permutation2
    _ = mixedMoment B node2215 node2215Labels := by rfl

def raw24961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw24961Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24961step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw24961step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24961 raw24961Labels = mixedMoment B node2213 node2213Labels := by
  calc
    mixedMoment B raw24961 raw24961Labels = mixedMoment B raw24961step0 raw24961step0Labels := by
      have ha : raw24961step0 = (fun i j => raw24961 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24961step0 raw24961; decide +kernel
      have hl : raw24961step0Labels = raw24961Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24961 raw24961Labels permutation176 permutation2
    _ = mixedMoment B node2213 node2213Labels := by rfl

def raw24962 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![-1, 1], ![0, 0], ![0, 0], ![2, -2]]
def raw24962Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24962step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![-1, 1], ![0, 0], ![2, -2]]
def raw24962step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24962step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![-1, 1], ![2, -2]]
def raw24962step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24962step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw24962step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical24962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24962 raw24962Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw24962 raw24962Labels = mixedMoment B raw24962step0 raw24962step0Labels := by
      have hz : ∀ j, raw24962 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw24962step0 = (fun i j => raw24962 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw24962step0 raw24962; decide +kernel
      have hl : raw24962step0Labels = raw24962Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24962 raw24962Labels permutation520 hz
    mixedMoment B raw24962step0 raw24962step0Labels = mixedMoment B raw24962step1 raw24962step1Labels := by
      have hz : ∀ j, raw24962step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw24962step1 = (fun i j => raw24962step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw24962step1 raw24962step0; decide +kernel
      have hl : raw24962step1Labels = raw24962step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24962step0 raw24962step0Labels permutation104 hz
    mixedMoment B raw24962step1 raw24962step1Labels = mixedMoment B raw24962step2 raw24962step2Labels := by
      have ha : raw24962step2 = (fun i j => raw24962step1 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw24962step2 raw24962step1; decide +kernel
      have hl : raw24962step2Labels = raw24962step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24962step1 raw24962step1Labels permutation10 permutation0
    _ = mixedMoment B node4082 node4082Labels := by rfl

def raw24963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw24963Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24963 raw24963Labels = mixedMoment B node1023 node1023Labels := by
  calc
    _ = mixedMoment B node1023 node1023Labels := by rfl

def raw24964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw24964Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24964 raw24964Labels = mixedMoment B node2091 node2091Labels := by
  calc
    _ = mixedMoment B node2091 node2091Labels := by rfl

def raw24965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw24965Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24965step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw24965step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24965 raw24965Labels = mixedMoment B node2091 node2091Labels := by
  calc
    mixedMoment B raw24965 raw24965Labels = mixedMoment B raw24965step0 raw24965step0Labels := by
      have ha : raw24965step0 = (fun i j => raw24965 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24965step0 raw24965; decide +kernel
      have hl : raw24965step0Labels = raw24965Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24965 raw24965Labels permutation176 permutation2
    _ = mixedMoment B node2091 node2091Labels := by rfl

def raw24966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw24966Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24966 raw24966Labels = mixedMoment B node2234 node2234Labels := by
  calc
    _ = mixedMoment B node2234 node2234Labels := by rfl

def raw24967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw24967Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24967step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw24967step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24967 raw24967Labels = mixedMoment B node2234 node2234Labels := by
  calc
    mixedMoment B raw24967 raw24967Labels = mixedMoment B raw24967step0 raw24967step0Labels := by
      have ha : raw24967step0 = (fun i j => raw24967 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24967step0 raw24967; decide +kernel
      have hl : raw24967step0Labels = raw24967Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24967 raw24967Labels permutation154 permutation2
    _ = mixedMoment B node2234 node2234Labels := by rfl

def raw24968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw24968Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24968step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw24968step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24968 raw24968Labels = mixedMoment B node2241 node2241Labels := by
  calc
    mixedMoment B raw24968 raw24968Labels = mixedMoment B raw24968step0 raw24968step0Labels := by
      have ha : raw24968step0 = (fun i j => raw24968 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24968step0 raw24968; decide +kernel
      have hl : raw24968step0Labels = raw24968Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24968 raw24968Labels permutation156 permutation2
    _ = mixedMoment B node2241 node2241Labels := by rfl

def raw24969 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1], ![1, -1], ![-1, 1]]
def raw24969Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24969step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw24969step0Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical24969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24969 raw24969Labels = mixedMoment B node4079 node4079Labels := by
  calc
    mixedMoment B raw24969 raw24969Labels = mixedMoment B raw24969step0 raw24969step0Labels := by
      have ha : raw24969step0 = (fun i j => raw24969 (permutation246 i) (permutation0 j)) := by apply Matrix.ext; unfold raw24969step0 raw24969; decide +kernel
      have hl : raw24969step0Labels = raw24969Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24969 raw24969Labels permutation246 permutation0
    _ = mixedMoment B node4079 node4079Labels := by rfl

def raw24970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw24970Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24970step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24970step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24970 raw24970Labels = mixedMoment B node1034 node1034Labels := by
  calc
    mixedMoment B raw24970 raw24970Labels = mixedMoment B raw24970step0 raw24970step0Labels := by
      have ha : raw24970step0 = (fun i j => raw24970 (permutation194 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24970step0 raw24970; decide +kernel
      have hl : raw24970step0Labels = raw24970Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24970 raw24970Labels permutation194 permutation2
    _ = mixedMoment B node1034 node1034Labels := by rfl

def raw24971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw24971Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24971step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw24971step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24971 raw24971Labels = mixedMoment B node1034 node1034Labels := by
  calc
    mixedMoment B raw24971 raw24971Labels = mixedMoment B raw24971step0 raw24971step0Labels := by
      have ha : raw24971step0 = (fun i j => raw24971 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24971step0 raw24971; decide +kernel
      have hl : raw24971step0Labels = raw24971Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24971 raw24971Labels permutation170 permutation2
    _ = mixedMoment B node1034 node1034Labels := by rfl

def raw24972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -2, 1]]
def raw24972Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24972step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw24972step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24972 raw24972Labels = mixedMoment B node1018 node1018Labels := by
  calc
    mixedMoment B raw24972 raw24972Labels = mixedMoment B raw24972step0 raw24972step0Labels := by
      have ha : raw24972step0 = (fun i j => raw24972 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24972step0 raw24972; decide +kernel
      have hl : raw24972step0Labels = raw24972Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24972 raw24972Labels permutation157 permutation2
    _ = mixedMoment B node1018 node1018Labels := by rfl

def raw24973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -2, 1]]
def raw24973Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24973step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw24973step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24973 raw24973Labels = mixedMoment B node1018 node1018Labels := by
  calc
    mixedMoment B raw24973 raw24973Labels = mixedMoment B raw24973step0 raw24973step0Labels := by
      have ha : raw24973step0 = (fun i j => raw24973 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24973step0 raw24973; decide +kernel
      have hl : raw24973step0Labels = raw24973Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24973 raw24973Labels permutation156 permutation2
    _ = mixedMoment B node1018 node1018Labels := by rfl

def raw24974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw24974Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24974step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw24974step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24974 raw24974Labels = mixedMoment B node1018 node1018Labels := by
  calc
    mixedMoment B raw24974 raw24974Labels = mixedMoment B raw24974step0 raw24974step0Labels := by
      have ha : raw24974step0 = (fun i j => raw24974 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24974step0 raw24974; decide +kernel
      have hl : raw24974step0Labels = raw24974Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24974 raw24974Labels permutation154 permutation2
    _ = mixedMoment B node1018 node1018Labels := by rfl

def raw24975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw24975Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24975step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw24975step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24975 raw24975Labels = mixedMoment B node2086 node2086Labels := by
  calc
    mixedMoment B raw24975 raw24975Labels = mixedMoment B raw24975step0 raw24975step0Labels := by
      have ha : raw24975step0 = (fun i j => raw24975 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24975step0 raw24975; decide +kernel
      have hl : raw24975step0Labels = raw24975Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24975 raw24975Labels permutation154 permutation2
    _ = mixedMoment B node2086 node2086Labels := by rfl

def raw24976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![1, 0, -1], ![1, -2, 1], ![2, -1, -1]]
def raw24976Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24976step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw24976step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24976 raw24976Labels = mixedMoment B node2086 node2086Labels := by
  calc
    mixedMoment B raw24976 raw24976Labels = mixedMoment B raw24976step0 raw24976step0Labels := by
      have ha : raw24976step0 = (fun i j => raw24976 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24976step0 raw24976; decide +kernel
      have hl : raw24976step0Labels = raw24976Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24976 raw24976Labels permutation178 permutation2
    _ = mixedMoment B node2086 node2086Labels := by rfl

def raw24977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw24977Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24977 raw24977Labels = mixedMoment B node2232 node2232Labels := by
  calc
    _ = mixedMoment B node2232 node2232Labels := by rfl

def raw24978 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![0, -1, 1], ![2, -1, -1]]
def raw24978Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24978step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24978step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24978 raw24978Labels = mixedMoment B node2191 node2191Labels := by
  calc
    mixedMoment B raw24978 raw24978Labels = mixedMoment B raw24978step0 raw24978step0Labels := by
      have ha : raw24978step0 = (fun i j => raw24978 (permutation224 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24978step0 raw24978; decide +kernel
      have hl : raw24978step0Labels = raw24978Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24978 raw24978Labels permutation224 permutation2
    _ = mixedMoment B node2191 node2191Labels := by rfl

def raw24979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw24979Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24979step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw24979step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24979 raw24979Labels = mixedMoment B node2241 node2241Labels := by
  calc
    mixedMoment B raw24979 raw24979Labels = mixedMoment B raw24979step0 raw24979step0Labels := by
      have ha : raw24979step0 = (fun i j => raw24979 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24979step0 raw24979; decide +kernel
      have hl : raw24979step0Labels = raw24979Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24979 raw24979Labels permutation154 permutation2
    _ = mixedMoment B node2241 node2241Labels := by rfl

def raw24980 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1], ![-1, 1], ![1, -1]]
def raw24980Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24980step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw24980step0Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical24980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24980 raw24980Labels = mixedMoment B node4079 node4079Labels := by
  calc
    mixedMoment B raw24980 raw24980Labels = mixedMoment B raw24980step0 raw24980step0Labels := by
      have ha : raw24980step0 = (fun i j => raw24980 (permutation224 i) (permutation0 j)) := by apply Matrix.ext; unfold raw24980step0 raw24980; decide +kernel
      have hl : raw24980step0Labels = raw24980Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24980 raw24980Labels permutation224 permutation0
    _ = mixedMoment B node4079 node4079Labels := by rfl

def raw24981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw24981Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24981step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw24981step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24981 raw24981Labels = mixedMoment B node2085 node2085Labels := by
  calc
    mixedMoment B raw24981 raw24981Labels = mixedMoment B raw24981step0 raw24981step0Labels := by
      have ha : raw24981step0 = (fun i j => raw24981 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24981step0 raw24981; decide +kernel
      have hl : raw24981step0Labels = raw24981Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24981 raw24981Labels permutation154 permutation2
    _ = mixedMoment B node2085 node2085Labels := by rfl

def raw24982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw24982Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24982step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw24982step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24982 raw24982Labels = mixedMoment B node2085 node2085Labels := by
  calc
    mixedMoment B raw24982 raw24982Labels = mixedMoment B raw24982step0 raw24982step0Labels := by
      have ha : raw24982step0 = (fun i j => raw24982 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24982step0 raw24982; decide +kernel
      have hl : raw24982step0Labels = raw24982Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24982 raw24982Labels permutation178 permutation2
    _ = mixedMoment B node2085 node2085Labels := by rfl

def raw24983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw24983Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24983step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24983step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24983 raw24983Labels = mixedMoment B node2190 node2190Labels := by
  calc
    mixedMoment B raw24983 raw24983Labels = mixedMoment B raw24983step0 raw24983step0Labels := by
      have ha : raw24983step0 = (fun i j => raw24983 (permutation224 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24983step0 raw24983; decide +kernel
      have hl : raw24983step0Labels = raw24983Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24983 raw24983Labels permutation224 permutation2
    _ = mixedMoment B node2190 node2190Labels := by rfl

def raw24984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw24984Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24984step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw24984step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24984 raw24984Labels = mixedMoment B node2240 node2240Labels := by
  calc
    mixedMoment B raw24984 raw24984Labels = mixedMoment B raw24984step0 raw24984step0Labels := by
      have ha : raw24984step0 = (fun i j => raw24984 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24984step0 raw24984; decide +kernel
      have hl : raw24984step0Labels = raw24984Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24984 raw24984Labels permutation154 permutation2
    _ = mixedMoment B node2240 node2240Labels := by rfl

def raw24985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw24985Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24985step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw24985step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24985step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw24985step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24985 raw24985Labels = mixedMoment B node1045 node1045Labels := by
  calc
    mixedMoment B raw24985 raw24985Labels = mixedMoment B raw24985step0 raw24985step0Labels := by
      have hz : ∀ j, raw24985 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24985step0 = (fun i j => raw24985 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24985step0 raw24985; decide +kernel
      have hl : raw24985step0Labels = raw24985Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24985 raw24985Labels permutation346 hz
    mixedMoment B raw24985step0 raw24985step0Labels = mixedMoment B raw24985step1 raw24985step1Labels := by
      have ha : raw24985step1 = (fun i j => raw24985step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24985step1 raw24985step0; decide +kernel
      have hl : raw24985step1Labels = raw24985step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24985step0 raw24985step0Labels permutation34 permutation2
    _ = mixedMoment B node1045 node1045Labels := by rfl

def raw24986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw24986Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24986step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw24986step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24986step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw24986step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24986 raw24986Labels = mixedMoment B node2111 node2111Labels := by
  calc
    mixedMoment B raw24986 raw24986Labels = mixedMoment B raw24986step0 raw24986step0Labels := by
      have hz : ∀ j, raw24986 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24986step0 = (fun i j => raw24986 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24986step0 raw24986; decide +kernel
      have hl : raw24986step0Labels = raw24986Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24986 raw24986Labels permutation346 hz
    mixedMoment B raw24986step0 raw24986step0Labels = mixedMoment B raw24986step1 raw24986step1Labels := by
      have ha : raw24986step1 = (fun i j => raw24986step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24986step1 raw24986step0; decide +kernel
      have hl : raw24986step1Labels = raw24986step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24986step0 raw24986step0Labels permutation34 permutation2
    _ = mixedMoment B node2111 node2111Labels := by rfl

def raw24987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![2, -3, 1]]
def raw24987Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24987step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw24987step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24987 raw24987Labels = mixedMoment B node2024 node2024Labels := by
  calc
    mixedMoment B raw24987 raw24987Labels = mixedMoment B raw24987step0 raw24987step0Labels := by
      have ha : raw24987step0 = (fun i j => raw24987 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24987step0 raw24987; decide +kernel
      have hl : raw24987step0Labels = raw24987Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24987 raw24987Labels permutation178 permutation2
    _ = mixedMoment B node2024 node2024Labels := by rfl

def raw24988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw24988Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24988step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw24988step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24988 raw24988Labels = mixedMoment B node2254 node2254Labels := by
  calc
    mixedMoment B raw24988 raw24988Labels = mixedMoment B raw24988step0 raw24988step0Labels := by
      have hz : ∀ j, raw24988 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24988step0 = (fun i j => raw24988 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24988step0 raw24988; decide +kernel
      have hl : raw24988step0Labels = raw24988Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24988 raw24988Labels permutation346 hz
    _ = mixedMoment B node2254 node2254Labels := by rfl

def raw24989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![0, 1, -1], ![2, -3, 1]]
def raw24989Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24989step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![0, 1, -1], ![2, -3, 1]]
def raw24989step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24989step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw24989step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24989 raw24989Labels = mixedMoment B node2246 node2246Labels := by
  calc
    mixedMoment B raw24989 raw24989Labels = mixedMoment B raw24989step0 raw24989step0Labels := by
      have hz : ∀ j, raw24989 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24989step0 = (fun i j => raw24989 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24989step0 raw24989; decide +kernel
      have hl : raw24989step0Labels = raw24989Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24989 raw24989Labels permutation346 hz
    mixedMoment B raw24989step0 raw24989step0Labels = mixedMoment B raw24989step1 raw24989step1Labels := by
      have ha : raw24989step1 = (fun i j => raw24989step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24989step1 raw24989step0; decide +kernel
      have hl : raw24989step1Labels = raw24989step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24989step0 raw24989step0Labels permutation34 permutation2
    _ = mixedMoment B node2246 node2246Labels := by rfl

def raw24990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw24990Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24990step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw24990step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24990step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw24990step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24990 raw24990Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw24990 raw24990Labels = mixedMoment B raw24990step0 raw24990step0Labels := by
      have hz : ∀ j, raw24990 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24990step0 = (fun i j => raw24990 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24990step0 raw24990; decide +kernel
      have hl : raw24990step0Labels = raw24990Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24990 raw24990Labels permutation346 hz
    mixedMoment B raw24990step0 raw24990step0Labels = mixedMoment B raw24990step1 raw24990step1Labels := by
      have ha : raw24990step1 = (fun i j => raw24990step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24990step1 raw24990step0; decide +kernel
      have hl : raw24990step1Labels = raw24990step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24990step0 raw24990step0Labels permutation37 permutation2
    _ = mixedMoment B node2260 node2260Labels := by rfl

def raw24991 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![2, -2], ![1, -1], ![-1, 1]]
def raw24991Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24991step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2], ![1, -1], ![-1, 1]]
def raw24991step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24991step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw24991step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical24991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24991 raw24991Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw24991 raw24991Labels = mixedMoment B raw24991step0 raw24991step0Labels := by
      have hz : ∀ j, raw24991 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24991step0 = (fun i j => raw24991 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24991step0 raw24991; decide +kernel
      have hl : raw24991step0Labels = raw24991Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24991 raw24991Labels permutation346 hz
    mixedMoment B raw24991step0 raw24991step0Labels = mixedMoment B raw24991step1 raw24991step1Labels := by
      have ha : raw24991step1 = (fun i j => raw24991step0 (permutation51 i) (permutation0 j)) := by apply Matrix.ext; unfold raw24991step1 raw24991step0; decide +kernel
      have hl : raw24991step1Labels = raw24991step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24991step0 raw24991step0Labels permutation51 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw24992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw24992Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24992step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw24992step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24992step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw24992step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24992 raw24992Labels = mixedMoment B node1073 node1073Labels := by
  calc
    mixedMoment B raw24992 raw24992Labels = mixedMoment B raw24992step0 raw24992step0Labels := by
      have hz : ∀ j, raw24992 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24992step0 = (fun i j => raw24992 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24992step0 raw24992; decide +kernel
      have hl : raw24992step0Labels = raw24992Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24992 raw24992Labels permutation346 hz
    mixedMoment B raw24992step0 raw24992step0Labels = mixedMoment B raw24992step1 raw24992step1Labels := by
      have ha : raw24992step1 = (fun i j => raw24992step0 (permutation51 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24992step1 raw24992step0; decide +kernel
      have hl : raw24992step1Labels = raw24992step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24992step0 raw24992step0Labels permutation51 permutation2
    _ = mixedMoment B node1073 node1073Labels := by rfl

def raw24993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw24993Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24993step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24993step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24993 raw24993Labels = mixedMoment B node1032 node1032Labels := by
  calc
    mixedMoment B raw24993 raw24993Labels = mixedMoment B raw24993step0 raw24993step0Labels := by
      have ha : raw24993step0 = (fun i j => raw24993 (permutation171 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24993step0 raw24993; decide +kernel
      have hl : raw24993step0Labels = raw24993Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24993 raw24993Labels permutation171 permutation2
    _ = mixedMoment B node1032 node1032Labels := by rfl

def raw24994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw24994Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24994step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, 0, -2], ![1, 0, -1], ![1, -2, 1]]
def raw24994step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24994step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24994step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24994 raw24994Labels = mixedMoment B node1035 node1035Labels := by
  calc
    mixedMoment B raw24994 raw24994Labels = mixedMoment B raw24994step0 raw24994step0Labels := by
      have hz : ∀ j, raw24994 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24994step0 = (fun i j => raw24994 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24994step0 raw24994; decide +kernel
      have hl : raw24994step0Labels = raw24994Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24994 raw24994Labels permutation346 hz
    mixedMoment B raw24994step0 raw24994step0Labels = mixedMoment B raw24994step1 raw24994step1Labels := by
      have ha : raw24994step1 = (fun i j => raw24994step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24994step1 raw24994step0; decide +kernel
      have hl : raw24994step1Labels = raw24994step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24994step0 raw24994step0Labels permutation37 permutation2
    _ = mixedMoment B node1035 node1035Labels := by rfl

def raw24995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw24995Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24995step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1], ![1, -2, 1]]
def raw24995step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24995step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw24995step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24995 raw24995Labels = mixedMoment B node1036 node1036Labels := by
  calc
    mixedMoment B raw24995 raw24995Labels = mixedMoment B raw24995step0 raw24995step0Labels := by
      have hz : ∀ j, raw24995 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24995step0 = (fun i j => raw24995 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24995step0 raw24995; decide +kernel
      have hl : raw24995step0Labels = raw24995Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24995 raw24995Labels permutation346 hz
    mixedMoment B raw24995step0 raw24995step0Labels = mixedMoment B raw24995step1 raw24995step1Labels := by
      have ha : raw24995step1 = (fun i j => raw24995step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24995step1 raw24995step0; decide +kernel
      have hl : raw24995step1Labels = raw24995step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24995step0 raw24995step0Labels permutation36 permutation2
    _ = mixedMoment B node1036 node1036Labels := by rfl

def raw24996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw24996Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24996step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw24996step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24996step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw24996step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24996 raw24996Labels = mixedMoment B node1036 node1036Labels := by
  calc
    mixedMoment B raw24996 raw24996Labels = mixedMoment B raw24996step0 raw24996step0Labels := by
      have hz : ∀ j, raw24996 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24996step0 = (fun i j => raw24996 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24996step0 raw24996; decide +kernel
      have hl : raw24996step0Labels = raw24996Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24996 raw24996Labels permutation346 hz
    mixedMoment B raw24996step0 raw24996step0Labels = mixedMoment B raw24996step1 raw24996step1Labels := by
      have ha : raw24996step1 = (fun i j => raw24996step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24996step1 raw24996step0; decide +kernel
      have hl : raw24996step1Labels = raw24996step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24996step0 raw24996step0Labels permutation34 permutation2
    _ = mixedMoment B node1036 node1036Labels := by rfl

def raw24997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw24997Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24997step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw24997step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24997step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw24997step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24997 raw24997Labels = mixedMoment B node2102 node2102Labels := by
  calc
    mixedMoment B raw24997 raw24997Labels = mixedMoment B raw24997step0 raw24997step0Labels := by
      have hz : ∀ j, raw24997 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24997step0 = (fun i j => raw24997 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24997step0 raw24997; decide +kernel
      have hl : raw24997step0Labels = raw24997Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24997 raw24997Labels permutation346 hz
    mixedMoment B raw24997step0 raw24997step0Labels = mixedMoment B raw24997step1 raw24997step1Labels := by
      have ha : raw24997step1 = (fun i j => raw24997step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24997step1 raw24997step0; decide +kernel
      have hl : raw24997step1Labels = raw24997step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24997step0 raw24997step0Labels permutation34 permutation2
    _ = mixedMoment B node2102 node2102Labels := by rfl

def raw24998 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 1, -2], ![1, -2, 1], ![2, -1, -1]]
def raw24998Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24998step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw24998step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24998 raw24998Labels = mixedMoment B node2017 node2017Labels := by
  calc
    mixedMoment B raw24998 raw24998Labels = mixedMoment B raw24998step0 raw24998step0Labels := by
      have ha : raw24998step0 = (fun i j => raw24998 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24998step0 raw24998; decide +kernel
      have hl : raw24998step0Labels = raw24998Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24998 raw24998Labels permutation178 permutation2
    _ = mixedMoment B node2017 node2017Labels := by rfl

def raw24999 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw24999Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24999step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw24999step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24999 raw24999Labels = mixedMoment B node2251 node2251Labels := by
  calc
    mixedMoment B raw24999 raw24999Labels = mixedMoment B raw24999step0 raw24999step0Labels := by
      have hz : ∀ j, raw24999 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24999step0 = (fun i j => raw24999 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24999step0 raw24999; decide +kernel
      have hl : raw24999step0Labels = raw24999Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24999 raw24999Labels permutation346 hz
    _ = mixedMoment B node2251 node2251Labels := by rfl

def raw25000 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![0, -1, 1], ![2, -1, -1]]
def raw25000Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25000step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![0, -1, 1], ![2, -1, -1]]
def raw25000step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25000step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw25000step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25000 raw25000Labels = mixedMoment B node2206 node2206Labels := by
  calc
    mixedMoment B raw25000 raw25000Labels = mixedMoment B raw25000step0 raw25000step0Labels := by
      have hz : ∀ j, raw25000 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25000step0 = (fun i j => raw25000 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25000step0 raw25000; decide +kernel
      have hl : raw25000step0Labels = raw25000Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25000 raw25000Labels permutation346 hz
    mixedMoment B raw25000step0 raw25000step0Labels = mixedMoment B raw25000step1 raw25000step1Labels := by
      have ha : raw25000step1 = (fun i j => raw25000step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25000step1 raw25000step0; decide +kernel
      have hl : raw25000step1Labels = raw25000step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25000step0 raw25000step0Labels permutation44 permutation2
    _ = mixedMoment B node2206 node2206Labels := by rfl

def raw25001 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![1, -2, 1], ![1, 0, -1]]
def raw25001Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25001step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![1, -2, 1], ![1, 0, -1]]
def raw25001step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25001step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw25001step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25001 raw25001Labels = mixedMoment B node2260 node2260Labels := by
  calc
    mixedMoment B raw25001 raw25001Labels = mixedMoment B raw25001step0 raw25001step0Labels := by
      have hz : ∀ j, raw25001 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25001step0 = (fun i j => raw25001 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25001step0 raw25001; decide +kernel
      have hl : raw25001step0Labels = raw25001Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25001 raw25001Labels permutation346 hz
    mixedMoment B raw25001step0 raw25001step0Labels = mixedMoment B raw25001step1 raw25001step1Labels := by
      have ha : raw25001step1 = (fun i j => raw25001step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25001step1 raw25001step0; decide +kernel
      have hl : raw25001step1Labels = raw25001step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25001step0 raw25001step0Labels permutation35 permutation2
    _ = mixedMoment B node2260 node2260Labels := by rfl

def raw25002 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![2, -2], ![-1, 1], ![1, -1]]
def raw25002Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25002step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2], ![-1, 1], ![1, -1]]
def raw25002step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25002step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw25002step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical25002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25002 raw25002Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw25002 raw25002Labels = mixedMoment B raw25002step0 raw25002step0Labels := by
      have hz : ∀ j, raw25002 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25002step0 = (fun i j => raw25002 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25002step0 raw25002; decide +kernel
      have hl : raw25002step0Labels = raw25002Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25002 raw25002Labels permutation346 hz
    mixedMoment B raw25002step0 raw25002step0Labels = mixedMoment B raw25002step1 raw25002step1Labels := by
      have ha : raw25002step1 = (fun i j => raw25002step0 (permutation45 i) (permutation0 j)) := by apply Matrix.ext; unfold raw25002step1 raw25002step0; decide +kernel
      have hl : raw25002step1Labels = raw25002step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25002step0 raw25002step0Labels permutation45 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw25003 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25003Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25003step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25003step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25003step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25003 raw25003Labels = mixedMoment B node4893 node4893Labels := by
  calc
    mixedMoment B raw25003 raw25003Labels = mixedMoment B raw25003step0 raw25003step0Labels := by
      have hz : ∀ j, raw25003 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25003step0 = (fun i j => raw25003 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25003step0 raw25003; decide +kernel
      have hl : raw25003step0Labels = raw25003Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25003 raw25003Labels permutation346 hz
    mixedMoment B raw25003step0 raw25003step0Labels = mixedMoment B raw25003step1 raw25003step1Labels := by
      have ha : raw25003step1 = (fun i j => raw25003step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25003step1 raw25003step0; decide +kernel
      have hl : raw25003step1Labels = raw25003step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25003step0 raw25003step0Labels permutation36 permutation2
    _ = mixedMoment B node4893 node4893Labels := by rfl

def raw25004 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25004Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25004step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25004 raw25004Labels = mixedMoment B node4182 node4182Labels := by
  calc
    mixedMoment B raw25004 raw25004Labels = mixedMoment B raw25004step0 raw25004step0Labels := by
      have hz : ∀ j, raw25004 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25004step0 = (fun i j => raw25004 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25004step0 raw25004; decide +kernel
      have hl : raw25004step0Labels = raw25004Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25004 raw25004Labels permutation346 hz
    _ = mixedMoment B node4182 node4182Labels := by rfl

def raw25005 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25005Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25005step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25005step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25005 raw25005Labels = mixedMoment B node4351 node4351Labels := by
  calc
    mixedMoment B raw25005 raw25005Labels = mixedMoment B raw25005step0 raw25005step0Labels := by
      have ha : raw25005step0 = (fun i j => raw25005 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25005step0 raw25005; decide +kernel
      have hl : raw25005step0Labels = raw25005Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25005 raw25005Labels permutation176 permutation2
    _ = mixedMoment B node4351 node4351Labels := by rfl

def raw25006 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25006Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25006step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25006step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25006step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25006step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25006 raw25006Labels = mixedMoment B node4461 node4461Labels := by
  calc
    mixedMoment B raw25006 raw25006Labels = mixedMoment B raw25006step0 raw25006step0Labels := by
      have hz : ∀ j, raw25006 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25006step0 = (fun i j => raw25006 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25006step0 raw25006; decide +kernel
      have hl : raw25006step0Labels = raw25006Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25006 raw25006Labels permutation346 hz
    mixedMoment B raw25006step0 raw25006step0Labels = mixedMoment B raw25006step1 raw25006step1Labels := by
      have ha : raw25006step1 = (fun i j => raw25006step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25006step1 raw25006step0; decide +kernel
      have hl : raw25006step1Labels = raw25006step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25006step0 raw25006step0Labels permutation38 permutation2
    _ = mixedMoment B node4461 node4461Labels := by rfl

def raw25007 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25007Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25007step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25007step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25007step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25007step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25007 raw25007Labels = mixedMoment B node4461 node4461Labels := by
  calc
    mixedMoment B raw25007 raw25007Labels = mixedMoment B raw25007step0 raw25007step0Labels := by
      have hz : ∀ j, raw25007 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25007step0 = (fun i j => raw25007 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25007step0 raw25007; decide +kernel
      have hl : raw25007step0Labels = raw25007Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25007 raw25007Labels permutation346 hz
    mixedMoment B raw25007step0 raw25007step0Labels = mixedMoment B raw25007step1 raw25007step1Labels := by
      have ha : raw25007step1 = (fun i j => raw25007step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25007step1 raw25007step0; decide +kernel
      have hl : raw25007step1Labels = raw25007step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25007step0 raw25007step0Labels permutation44 permutation2
    _ = mixedMoment B node4461 node4461Labels := by rfl

def raw25008 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25008Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25008 raw25008Labels = mixedMoment B node4152 node4152Labels := by
  calc
    _ = mixedMoment B node4152 node4152Labels := by rfl

def raw25009 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25009Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25009 raw25009Labels = mixedMoment B node4366 node4366Labels := by
  calc
    _ = mixedMoment B node4366 node4366Labels := by rfl

def raw25010 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25010Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25010step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25010step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25010 raw25010Labels = mixedMoment B node4439 node4439Labels := by
  calc
    mixedMoment B raw25010 raw25010Labels = mixedMoment B raw25010step0 raw25010step0Labels := by
      have ha : raw25010step0 = (fun i j => raw25010 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25010step0 raw25010; decide +kernel
      have hl : raw25010step0Labels = raw25010Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25010 raw25010Labels permutation158 permutation2
    _ = mixedMoment B node4439 node4439Labels := by rfl

def raw25011 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25011Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25011step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw25011step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25011 raw25011Labels = mixedMoment B node4439 node4439Labels := by
  calc
    mixedMoment B raw25011 raw25011Labels = mixedMoment B raw25011step0 raw25011step0Labels := by
      have ha : raw25011step0 = (fun i j => raw25011 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25011step0 raw25011; decide +kernel
      have hl : raw25011step0Labels = raw25011Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25011 raw25011Labels permutation164 permutation2
    _ = mixedMoment B node4439 node4439Labels := by rfl

def raw25012 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25012Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25012step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25012step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25012step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25012step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25012 raw25012Labels = mixedMoment B node4158 node4158Labels := by
  calc
    mixedMoment B raw25012 raw25012Labels = mixedMoment B raw25012step0 raw25012step0Labels := by
      have hz : ∀ j, raw25012 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25012step0 = (fun i j => raw25012 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25012step0 raw25012; decide +kernel
      have hl : raw25012step0Labels = raw25012Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25012 raw25012Labels permutation346 hz
    mixedMoment B raw25012step0 raw25012step0Labels = mixedMoment B raw25012step1 raw25012step1Labels := by
      have ha : raw25012step1 = (fun i j => raw25012step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25012step1 raw25012step0; decide +kernel
      have hl : raw25012step1Labels = raw25012step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25012step0 raw25012step0Labels permutation35 permutation2
    _ = mixedMoment B node4158 node4158Labels := by rfl

def raw25013 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25013Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25013step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25013step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25013step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25013step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25013 raw25013Labels = mixedMoment B node4372 node4372Labels := by
  calc
    mixedMoment B raw25013 raw25013Labels = mixedMoment B raw25013step0 raw25013step0Labels := by
      have hz : ∀ j, raw25013 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25013step0 = (fun i j => raw25013 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25013step0 raw25013; decide +kernel
      have hl : raw25013step0Labels = raw25013Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25013 raw25013Labels permutation346 hz
    mixedMoment B raw25013step0 raw25013step0Labels = mixedMoment B raw25013step1 raw25013step1Labels := by
      have ha : raw25013step1 = (fun i j => raw25013step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25013step1 raw25013step0; decide +kernel
      have hl : raw25013step1Labels = raw25013step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25013step0 raw25013step0Labels permutation35 permutation2
    _ = mixedMoment B node4372 node4372Labels := by rfl

def raw25014 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25014Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25014step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25014step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25014 raw25014Labels = mixedMoment B node4332 node4332Labels := by
  calc
    mixedMoment B raw25014 raw25014Labels = mixedMoment B raw25014step0 raw25014step0Labels := by
      have ha : raw25014step0 = (fun i j => raw25014 (permutation179 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25014step0 raw25014; decide +kernel
      have hl : raw25014step0Labels = raw25014Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25014 raw25014Labels permutation179 permutation2
    _ = mixedMoment B node4332 node4332Labels := by rfl

def raw25015 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25015Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25015step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25015step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25015step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25015step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25015 raw25015Labels = mixedMoment B node4444 node4444Labels := by
  calc
    mixedMoment B raw25015 raw25015Labels = mixedMoment B raw25015step0 raw25015step0Labels := by
      have hz : ∀ j, raw25015 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25015step0 = (fun i j => raw25015 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25015step0 raw25015; decide +kernel
      have hl : raw25015step0Labels = raw25015Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25015 raw25015Labels permutation346 hz
    mixedMoment B raw25015step0 raw25015step0Labels = mixedMoment B raw25015step1 raw25015step1Labels := by
      have ha : raw25015step1 = (fun i j => raw25015step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25015step1 raw25015step0; decide +kernel
      have hl : raw25015step1Labels = raw25015step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25015step0 raw25015step0Labels permutation35 permutation2
    _ = mixedMoment B node4444 node4444Labels := by rfl

def raw25016 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25016Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25016step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25016step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25016step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25016step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25016 raw25016Labels = mixedMoment B node4158 node4158Labels := by
  calc
    mixedMoment B raw25016 raw25016Labels = mixedMoment B raw25016step0 raw25016step0Labels := by
      have hz : ∀ j, raw25016 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25016step0 = (fun i j => raw25016 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25016step0 raw25016; decide +kernel
      have hl : raw25016step0Labels = raw25016Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25016 raw25016Labels permutation346 hz
    mixedMoment B raw25016step0 raw25016step0Labels = mixedMoment B raw25016step1 raw25016step1Labels := by
      have ha : raw25016step1 = (fun i j => raw25016step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25016step1 raw25016step0; decide +kernel
      have hl : raw25016step1Labels = raw25016step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25016step0 raw25016step0Labels permutation33 permutation2
    _ = mixedMoment B node4158 node4158Labels := by rfl

def raw25017 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25017Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25017step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25017step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25017step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25017step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25017 raw25017Labels = mixedMoment B node4372 node4372Labels := by
  calc
    mixedMoment B raw25017 raw25017Labels = mixedMoment B raw25017step0 raw25017step0Labels := by
      have hz : ∀ j, raw25017 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25017step0 = (fun i j => raw25017 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25017step0 raw25017; decide +kernel
      have hl : raw25017step0Labels = raw25017Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25017 raw25017Labels permutation346 hz
    mixedMoment B raw25017step0 raw25017step0Labels = mixedMoment B raw25017step1 raw25017step1Labels := by
      have ha : raw25017step1 = (fun i j => raw25017step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25017step1 raw25017step0; decide +kernel
      have hl : raw25017step1Labels = raw25017step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25017step0 raw25017step0Labels permutation33 permutation2
    _ = mixedMoment B node4372 node4372Labels := by rfl

def raw25018 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25018Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25018step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25018step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25018 raw25018Labels = mixedMoment B node4332 node4332Labels := by
  calc
    mixedMoment B raw25018 raw25018Labels = mixedMoment B raw25018step0 raw25018step0Labels := by
      have ha : raw25018step0 = (fun i j => raw25018 (permutation177 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25018step0 raw25018; decide +kernel
      have hl : raw25018step0Labels = raw25018Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25018 raw25018Labels permutation177 permutation2
    _ = mixedMoment B node4332 node4332Labels := by rfl

def raw25019 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25019Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25019step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25019step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25019step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25019step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25019 raw25019Labels = mixedMoment B node4444 node4444Labels := by
  calc
    mixedMoment B raw25019 raw25019Labels = mixedMoment B raw25019step0 raw25019step0Labels := by
      have hz : ∀ j, raw25019 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25019step0 = (fun i j => raw25019 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25019step0 raw25019; decide +kernel
      have hl : raw25019step0Labels = raw25019Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25019 raw25019Labels permutation346 hz
    mixedMoment B raw25019step0 raw25019step0Labels = mixedMoment B raw25019step1 raw25019step1Labels := by
      have ha : raw25019step1 = (fun i j => raw25019step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25019step1 raw25019step0; decide +kernel
      have hl : raw25019step1Labels = raw25019step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25019step0 raw25019step0Labels permutation33 permutation2
    _ = mixedMoment B node4444 node4444Labels := by rfl

def raw25020 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25020Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25020step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25020step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25020 raw25020Labels = mixedMoment B node4157 node4157Labels := by
  calc
    mixedMoment B raw25020 raw25020Labels = mixedMoment B raw25020step0 raw25020step0Labels := by
      have hz : ∀ j, raw25020 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25020step0 = (fun i j => raw25020 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25020step0 raw25020; decide +kernel
      have hl : raw25020step0Labels = raw25020Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25020 raw25020Labels permutation346 hz
    _ = mixedMoment B node4157 node4157Labels := by rfl

def raw25021 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25021Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25021step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25021step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25021 raw25021Labels = mixedMoment B node4371 node4371Labels := by
  calc
    mixedMoment B raw25021 raw25021Labels = mixedMoment B raw25021step0 raw25021step0Labels := by
      have hz : ∀ j, raw25021 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25021step0 = (fun i j => raw25021 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25021step0 raw25021; decide +kernel
      have hl : raw25021step0Labels = raw25021Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25021 raw25021Labels permutation346 hz
    _ = mixedMoment B node4371 node4371Labels := by rfl

def raw25022 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25022Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25022step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25022step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25022 raw25022Labels = mixedMoment B node4331 node4331Labels := by
  calc
    mixedMoment B raw25022 raw25022Labels = mixedMoment B raw25022step0 raw25022step0Labels := by
      have ha : raw25022step0 = (fun i j => raw25022 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25022step0 raw25022; decide +kernel
      have hl : raw25022step0Labels = raw25022Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25022 raw25022Labels permutation176 permutation2
    _ = mixedMoment B node4331 node4331Labels := by rfl

def raw25023 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25023Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25023step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25023step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25023 raw25023Labels = mixedMoment B node4442 node4442Labels := by
  calc
    mixedMoment B raw25023 raw25023Labels = mixedMoment B raw25023step0 raw25023step0Labels := by
      have hz : ∀ j, raw25023 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25023step0 = (fun i j => raw25023 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25023step0 raw25023; decide +kernel
      have hl : raw25023step0Labels = raw25023Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25023 raw25023Labels permutation346 hz
    _ = mixedMoment B node4442 node4442Labels := by rfl

def raw25024 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw25024Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw25024step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25024step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25024step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25024 raw25024Labels = mixedMoment B node4442 node4442Labels := by
  calc
    mixedMoment B raw25024 raw25024Labels = mixedMoment B raw25024step0 raw25024step0Labels := by
      have hz : ∀ j, raw25024 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25024step0 = (fun i j => raw25024 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25024step0 raw25024; decide +kernel
      have hl : raw25024step0Labels = raw25024Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25024 raw25024Labels permutation346 hz
    mixedMoment B raw25024step0 raw25024step0Labels = mixedMoment B raw25024step1 raw25024step1Labels := by
      have ha : raw25024step1 = (fun i j => raw25024step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25024step1 raw25024step0; decide +kernel
      have hl : raw25024step1Labels = raw25024step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25024step0 raw25024step0Labels permutation34 permutation2
    _ = mixedMoment B node4442 node4442Labels := by rfl

def raw25025 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25025Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25025step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25025step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw25025step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25025step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw25025step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25025step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw25025step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25025 raw25025Labels = mixedMoment B node2275 node2275Labels := by
  calc
    mixedMoment B raw25025 raw25025Labels = mixedMoment B raw25025step0 raw25025step0Labels := by
      have hz : ∀ j, raw25025 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25025step0 = (fun i j => raw25025 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25025step0 raw25025; decide +kernel
      have hl : raw25025step0Labels = raw25025Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25025 raw25025Labels permutation346 hz
    mixedMoment B raw25025step0 raw25025step0Labels = mixedMoment B raw25025step1 raw25025step1Labels := by
      have ha : raw25025step1 = (fun i j => raw25025step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25025step1 raw25025step0; decide +kernel
      have hl : raw25025step1Labels = raw25025step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25025step0 raw25025step0Labels permutation50 permutation7
    mixedMoment B raw25025step1 raw25025step1Labels = mixedMoment B raw25025step2 raw25025step2Labels := by
      have ha : raw25025step2 = -raw25025step1 := by apply Matrix.ext; change ∀ i j, raw25025step2 i j = -(raw25025step1 i j); unfold raw25025step2 raw25025step1; decide +kernel
      have hl : raw25025step2Labels = raw25025step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25025step2 raw25025step2Labels = mixedMoment B raw25025step3 raw25025step3Labels := by
      have ha : raw25025step3 = raw25025step2 := by apply Matrix.ext; unfold raw25025step3 raw25025step2; decide +kernel
      have hl : raw25025step2Labels = labelEmbedding1 ∘ raw25025step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25025step2 raw25025step2Labels raw25025step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2275 node2275Labels := by rfl

def raw25026 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25026Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25026step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw25026step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25026step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25026step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25026step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25026step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25026 raw25026Labels = mixedMoment B node2214 node2214Labels := by
  calc
    mixedMoment B raw25026 raw25026Labels = mixedMoment B raw25026step0 raw25026step0Labels := by
      have ha : raw25026step0 = (fun i j => raw25026 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25026step0 raw25026; decide +kernel
      have hl : raw25026step0Labels = raw25026Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25026 raw25026Labels permutation194 permutation7
    mixedMoment B raw25026step0 raw25026step0Labels = mixedMoment B raw25026step1 raw25026step1Labels := by
      have ha : raw25026step1 = -raw25026step0 := by apply Matrix.ext; change ∀ i j, raw25026step1 i j = -(raw25026step0 i j); unfold raw25026step1 raw25026step0; decide +kernel
      have hl : raw25026step1Labels = raw25026step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25026step1 raw25026step1Labels = mixedMoment B raw25026step2 raw25026step2Labels := by
      have ha : raw25026step2 = raw25026step1 := by apply Matrix.ext; unfold raw25026step2 raw25026step1; decide +kernel
      have hl : raw25026step1Labels = labelEmbedding1 ∘ raw25026step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25026step1 raw25026step1Labels raw25026step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2214 node2214Labels := by rfl

def raw25027 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25027Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25027step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25027step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw25027step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25027step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw25027step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25027step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw25027step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25027 raw25027Labels = mixedMoment B node2277 node2277Labels := by
  calc
    mixedMoment B raw25027 raw25027Labels = mixedMoment B raw25027step0 raw25027step0Labels := by
      have hz : ∀ j, raw25027 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25027step0 = (fun i j => raw25027 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25027step0 raw25027; decide +kernel
      have hl : raw25027step0Labels = raw25027Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25027 raw25027Labels permutation346 hz
    mixedMoment B raw25027step0 raw25027step0Labels = mixedMoment B raw25027step1 raw25027step1Labels := by
      have ha : raw25027step1 = (fun i j => raw25027step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25027step1 raw25027step0; decide +kernel
      have hl : raw25027step1Labels = raw25027step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25027step0 raw25027step0Labels permutation50 permutation7
    mixedMoment B raw25027step1 raw25027step1Labels = mixedMoment B raw25027step2 raw25027step2Labels := by
      have ha : raw25027step2 = -raw25027step1 := by apply Matrix.ext; change ∀ i j, raw25027step2 i j = -(raw25027step1 i j); unfold raw25027step2 raw25027step1; decide +kernel
      have hl : raw25027step2Labels = raw25027step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25027step2 raw25027step2Labels = mixedMoment B raw25027step3 raw25027step3Labels := by
      have ha : raw25027step3 = raw25027step2 := by apply Matrix.ext; unfold raw25027step3 raw25027step2; decide +kernel
      have hl : raw25027step2Labels = labelEmbedding1 ∘ raw25027step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25027step2 raw25027step2Labels raw25027step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2277 node2277Labels := by rfl

def raw25028 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25028Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25028step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25028step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25028step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw25028step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25028step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw25028step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25028step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw25028step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25028 raw25028Labels = mixedMoment B node2277 node2277Labels := by
  calc
    mixedMoment B raw25028 raw25028Labels = mixedMoment B raw25028step0 raw25028step0Labels := by
      have hz : ∀ j, raw25028 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25028step0 = (fun i j => raw25028 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25028step0 raw25028; decide +kernel
      have hl : raw25028step0Labels = raw25028Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25028 raw25028Labels permutation346 hz
    mixedMoment B raw25028step0 raw25028step0Labels = mixedMoment B raw25028step1 raw25028step1Labels := by
      have ha : raw25028step1 = (fun i j => raw25028step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25028step1 raw25028step0; decide +kernel
      have hl : raw25028step1Labels = raw25028step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25028step0 raw25028step0Labels permutation51 permutation7
    mixedMoment B raw25028step1 raw25028step1Labels = mixedMoment B raw25028step2 raw25028step2Labels := by
      have ha : raw25028step2 = -raw25028step1 := by apply Matrix.ext; change ∀ i j, raw25028step2 i j = -(raw25028step1 i j); unfold raw25028step2 raw25028step1; decide +kernel
      have hl : raw25028step2Labels = raw25028step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25028step2 raw25028step2Labels = mixedMoment B raw25028step3 raw25028step3Labels := by
      have ha : raw25028step3 = raw25028step2 := by apply Matrix.ext; unfold raw25028step3 raw25028step2; decide +kernel
      have hl : raw25028step2Labels = labelEmbedding1 ∘ raw25028step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25028step2 raw25028step2Labels raw25028step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2277 node2277Labels := by rfl

def raw25029 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25029Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25029step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25029step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25029step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw25029step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25029step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25029step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25029step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25029step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25029 raw25029Labels = mixedMoment B node2263 node2263Labels := by
  calc
    mixedMoment B raw25029 raw25029Labels = mixedMoment B raw25029step0 raw25029step0Labels := by
      have hz : ∀ j, raw25029 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25029step0 = (fun i j => raw25029 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25029step0 raw25029; decide +kernel
      have hl : raw25029step0Labels = raw25029Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25029 raw25029Labels permutation346 hz
    mixedMoment B raw25029step0 raw25029step0Labels = mixedMoment B raw25029step1 raw25029step1Labels := by
      have ha : raw25029step1 = (fun i j => raw25029step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25029step1 raw25029step0; decide +kernel
      have hl : raw25029step1Labels = raw25029step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25029step0 raw25029step0Labels permutation50 permutation7
    mixedMoment B raw25029step1 raw25029step1Labels = mixedMoment B raw25029step2 raw25029step2Labels := by
      have ha : raw25029step2 = -raw25029step1 := by apply Matrix.ext; change ∀ i j, raw25029step2 i j = -(raw25029step1 i j); unfold raw25029step2 raw25029step1; decide +kernel
      have hl : raw25029step2Labels = raw25029step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25029step2 raw25029step2Labels = mixedMoment B raw25029step3 raw25029step3Labels := by
      have ha : raw25029step3 = raw25029step2 := by apply Matrix.ext; unfold raw25029step3 raw25029step2; decide +kernel
      have hl : raw25029step2Labels = labelEmbedding1 ∘ raw25029step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25029step2 raw25029step2Labels raw25029step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2263 node2263Labels := by rfl

def raw25030 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25030Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25030step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25030step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25030step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw25030step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25030step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25030step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25030step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25030step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25030 raw25030Labels = mixedMoment B node1524 node1524Labels := by
  calc
    mixedMoment B raw25030 raw25030Labels = mixedMoment B raw25030step0 raw25030step0Labels := by
      have hz : ∀ j, raw25030 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25030step0 = (fun i j => raw25030 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25030step0 raw25030; decide +kernel
      have hl : raw25030step0Labels = raw25030Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25030 raw25030Labels permutation346 hz
    mixedMoment B raw25030step0 raw25030step0Labels = mixedMoment B raw25030step1 raw25030step1Labels := by
      have ha : raw25030step1 = (fun i j => raw25030step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25030step1 raw25030step0; decide +kernel
      have hl : raw25030step1Labels = raw25030step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25030step0 raw25030step0Labels permutation50 permutation7
    mixedMoment B raw25030step1 raw25030step1Labels = mixedMoment B raw25030step2 raw25030step2Labels := by
      have ha : raw25030step2 = -raw25030step1 := by apply Matrix.ext; change ∀ i j, raw25030step2 i j = -(raw25030step1 i j); unfold raw25030step2 raw25030step1; decide +kernel
      have hl : raw25030step2Labels = raw25030step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25030step2 raw25030step2Labels = mixedMoment B raw25030step3 raw25030step3Labels := by
      have ha : raw25030step3 = raw25030step2 := by apply Matrix.ext; unfold raw25030step3 raw25030step2; decide +kernel
      have hl : raw25030step2Labels = labelEmbedding1 ∘ raw25030step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25030step2 raw25030step2Labels raw25030step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1524 node1524Labels := by rfl

def raw25031 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25031Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25031step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw25031step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25031step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25031step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25031step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25031step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25031 raw25031Labels = mixedMoment B node1680 node1680Labels := by
  calc
    mixedMoment B raw25031 raw25031Labels = mixedMoment B raw25031step0 raw25031step0Labels := by
      have ha : raw25031step0 = (fun i j => raw25031 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25031step0 raw25031; decide +kernel
      have hl : raw25031step0Labels = raw25031Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25031 raw25031Labels permutation194 permutation7
    mixedMoment B raw25031step0 raw25031step0Labels = mixedMoment B raw25031step1 raw25031step1Labels := by
      have ha : raw25031step1 = -raw25031step0 := by apply Matrix.ext; change ∀ i j, raw25031step1 i j = -(raw25031step0 i j); unfold raw25031step1 raw25031step0; decide +kernel
      have hl : raw25031step1Labels = raw25031step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25031step1 raw25031step1Labels = mixedMoment B raw25031step2 raw25031step2Labels := by
      have ha : raw25031step2 = raw25031step1 := by apply Matrix.ext; unfold raw25031step2 raw25031step1; decide +kernel
      have hl : raw25031step1Labels = labelEmbedding1 ∘ raw25031step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25031step1 raw25031step1Labels raw25031step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1680 node1680Labels := by rfl

def raw25032 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25032Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25032step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25032step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25032step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw25032step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25032step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25032step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25032step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25032step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25032 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25032 raw25032Labels = mixedMoment B node1737 node1737Labels := by
  calc
    mixedMoment B raw25032 raw25032Labels = mixedMoment B raw25032step0 raw25032step0Labels := by
      have hz : ∀ j, raw25032 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25032step0 = (fun i j => raw25032 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25032step0 raw25032; decide +kernel
      have hl : raw25032step0Labels = raw25032Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25032 raw25032Labels permutation346 hz
    mixedMoment B raw25032step0 raw25032step0Labels = mixedMoment B raw25032step1 raw25032step1Labels := by
      have ha : raw25032step1 = (fun i j => raw25032step0 (permutation52 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25032step1 raw25032step0; decide +kernel
      have hl : raw25032step1Labels = raw25032step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25032step0 raw25032step0Labels permutation52 permutation7
    mixedMoment B raw25032step1 raw25032step1Labels = mixedMoment B raw25032step2 raw25032step2Labels := by
      have ha : raw25032step2 = -raw25032step1 := by apply Matrix.ext; change ∀ i j, raw25032step2 i j = -(raw25032step1 i j); unfold raw25032step2 raw25032step1; decide +kernel
      have hl : raw25032step2Labels = raw25032step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25032step2 raw25032step2Labels = mixedMoment B raw25032step3 raw25032step3Labels := by
      have ha : raw25032step3 = raw25032step2 := by apply Matrix.ext; unfold raw25032step3 raw25032step2; decide +kernel
      have hl : raw25032step2Labels = labelEmbedding1 ∘ raw25032step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25032step2 raw25032step2Labels raw25032step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1737 node1737Labels := by rfl

def raw25033 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25033Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25033step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25033step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25033step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw25033step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25033step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25033step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25033step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25033step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25033 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25033 raw25033Labels = mixedMoment B node1737 node1737Labels := by
  calc
    mixedMoment B raw25033 raw25033Labels = mixedMoment B raw25033step0 raw25033step0Labels := by
      have hz : ∀ j, raw25033 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25033step0 = (fun i j => raw25033 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25033step0 raw25033; decide +kernel
      have hl : raw25033step0Labels = raw25033Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25033 raw25033Labels permutation346 hz
    mixedMoment B raw25033step0 raw25033step0Labels = mixedMoment B raw25033step1 raw25033step1Labels := by
      have ha : raw25033step1 = (fun i j => raw25033step0 (permutation54 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25033step1 raw25033step0; decide +kernel
      have hl : raw25033step1Labels = raw25033step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25033step0 raw25033step0Labels permutation54 permutation7
    mixedMoment B raw25033step1 raw25033step1Labels = mixedMoment B raw25033step2 raw25033step2Labels := by
      have ha : raw25033step2 = -raw25033step1 := by apply Matrix.ext; change ∀ i j, raw25033step2 i j = -(raw25033step1 i j); unfold raw25033step2 raw25033step1; decide +kernel
      have hl : raw25033step2Labels = raw25033step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25033step2 raw25033step2Labels = mixedMoment B raw25033step3 raw25033step3Labels := by
      have ha : raw25033step3 = raw25033step2 := by apply Matrix.ext; unfold raw25033step3 raw25033step2; decide +kernel
      have hl : raw25033step2Labels = labelEmbedding1 ∘ raw25033step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25033step2 raw25033step2Labels raw25033step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1737 node1737Labels := by rfl

def raw25034 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25034Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25034step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25034step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25034step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw25034step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25034step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25034step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25034step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25034step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25034 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25034 raw25034Labels = mixedMoment B node1726 node1726Labels := by
  calc
    mixedMoment B raw25034 raw25034Labels = mixedMoment B raw25034step0 raw25034step0Labels := by
      have hz : ∀ j, raw25034 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25034step0 = (fun i j => raw25034 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25034step0 raw25034; decide +kernel
      have hl : raw25034step0Labels = raw25034Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25034 raw25034Labels permutation346 hz
    mixedMoment B raw25034step0 raw25034step0Labels = mixedMoment B raw25034step1 raw25034step1Labels := by
      have ha : raw25034step1 = (fun i j => raw25034step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25034step1 raw25034step0; decide +kernel
      have hl : raw25034step1Labels = raw25034step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25034step0 raw25034step0Labels permutation50 permutation7
    mixedMoment B raw25034step1 raw25034step1Labels = mixedMoment B raw25034step2 raw25034step2Labels := by
      have ha : raw25034step2 = -raw25034step1 := by apply Matrix.ext; change ∀ i j, raw25034step2 i j = -(raw25034step1 i j); unfold raw25034step2 raw25034step1; decide +kernel
      have hl : raw25034step2Labels = raw25034step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25034step2 raw25034step2Labels = mixedMoment B raw25034step3 raw25034step3Labels := by
      have ha : raw25034step3 = raw25034step2 := by apply Matrix.ext; unfold raw25034step3 raw25034step2; decide +kernel
      have hl : raw25034step2Labels = labelEmbedding1 ∘ raw25034step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25034step2 raw25034step2Labels raw25034step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1726 node1726Labels := by rfl

def raw25035 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25035Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25035step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw25035step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25035step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25035step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25035step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25035step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25035 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25035 raw25035Labels = mixedMoment B node1510 node1510Labels := by
  calc
    mixedMoment B raw25035 raw25035Labels = mixedMoment B raw25035step0 raw25035step0Labels := by
      have ha : raw25035step0 = (fun i j => raw25035 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25035step0 raw25035; decide +kernel
      have hl : raw25035step0Labels = raw25035Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25035 raw25035Labels permutation194 permutation7
    mixedMoment B raw25035step0 raw25035step0Labels = mixedMoment B raw25035step1 raw25035step1Labels := by
      have ha : raw25035step1 = -raw25035step0 := by apply Matrix.ext; change ∀ i j, raw25035step1 i j = -(raw25035step0 i j); unfold raw25035step1 raw25035step0; decide +kernel
      have hl : raw25035step1Labels = raw25035step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25035step1 raw25035step1Labels = mixedMoment B raw25035step2 raw25035step2Labels := by
      have ha : raw25035step2 = raw25035step1 := by apply Matrix.ext; unfold raw25035step2 raw25035step1; decide +kernel
      have hl : raw25035step1Labels = labelEmbedding1 ∘ raw25035step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25035step1 raw25035step1Labels raw25035step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1510 node1510Labels := by rfl

def raw25036 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25036Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25036step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw25036step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25036step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw25036step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25036step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw25036step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25036 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25036 raw25036Labels = mixedMoment B node1711 node1711Labels := by
  calc
    mixedMoment B raw25036 raw25036Labels = mixedMoment B raw25036step0 raw25036step0Labels := by
      have ha : raw25036step0 = (fun i j => raw25036 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25036step0 raw25036; decide +kernel
      have hl : raw25036step0Labels = raw25036Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25036 raw25036Labels permutation194 permutation7
    mixedMoment B raw25036step0 raw25036step0Labels = mixedMoment B raw25036step1 raw25036step1Labels := by
      have ha : raw25036step1 = -raw25036step0 := by apply Matrix.ext; change ∀ i j, raw25036step1 i j = -(raw25036step0 i j); unfold raw25036step1 raw25036step0; decide +kernel
      have hl : raw25036step1Labels = raw25036step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25036step1 raw25036step1Labels = mixedMoment B raw25036step2 raw25036step2Labels := by
      have ha : raw25036step2 = raw25036step1 := by apply Matrix.ext; unfold raw25036step2 raw25036step1; decide +kernel
      have hl : raw25036step1Labels = labelEmbedding1 ∘ raw25036step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25036step1 raw25036step1Labels raw25036step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1711 node1711Labels := by rfl

def raw25037 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25037Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25037step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw25037step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25037step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw25037step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25037step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw25037step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25037 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25037 raw25037Labels = mixedMoment B node1713 node1713Labels := by
  calc
    mixedMoment B raw25037 raw25037Labels = mixedMoment B raw25037step0 raw25037step0Labels := by
      have ha : raw25037step0 = (fun i j => raw25037 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25037step0 raw25037; decide +kernel
      have hl : raw25037step0Labels = raw25037Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25037 raw25037Labels permutation194 permutation7
    mixedMoment B raw25037step0 raw25037step0Labels = mixedMoment B raw25037step1 raw25037step1Labels := by
      have ha : raw25037step1 = -raw25037step0 := by apply Matrix.ext; change ∀ i j, raw25037step1 i j = -(raw25037step0 i j); unfold raw25037step1 raw25037step0; decide +kernel
      have hl : raw25037step1Labels = raw25037step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25037step1 raw25037step1Labels = mixedMoment B raw25037step2 raw25037step2Labels := by
      have ha : raw25037step2 = raw25037step1 := by apply Matrix.ext; unfold raw25037step2 raw25037step1; decide +kernel
      have hl : raw25037step1Labels = labelEmbedding1 ∘ raw25037step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25037step1 raw25037step1Labels raw25037step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1713 node1713Labels := by rfl

def raw25038 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25038Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25038step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw25038step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25038step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw25038step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25038step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw25038step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25038 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25038 raw25038Labels = mixedMoment B node1713 node1713Labels := by
  calc
    mixedMoment B raw25038 raw25038Labels = mixedMoment B raw25038step0 raw25038step0Labels := by
      have ha : raw25038step0 = (fun i j => raw25038 (permutation195 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25038step0 raw25038; decide +kernel
      have hl : raw25038step0Labels = raw25038Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25038 raw25038Labels permutation195 permutation7
    mixedMoment B raw25038step0 raw25038step0Labels = mixedMoment B raw25038step1 raw25038step1Labels := by
      have ha : raw25038step1 = -raw25038step0 := by apply Matrix.ext; change ∀ i j, raw25038step1 i j = -(raw25038step0 i j); unfold raw25038step1 raw25038step0; decide +kernel
      have hl : raw25038step1Labels = raw25038step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25038step1 raw25038step1Labels = mixedMoment B raw25038step2 raw25038step2Labels := by
      have ha : raw25038step2 = raw25038step1 := by apply Matrix.ext; unfold raw25038step2 raw25038step1; decide +kernel
      have hl : raw25038step1Labels = labelEmbedding1 ∘ raw25038step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25038step1 raw25038step1Labels raw25038step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1713 node1713Labels := by rfl

def raw25039 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25039Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25039step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw25039step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25039step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25039step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25039step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25039step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25039 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25039 raw25039Labels = mixedMoment B node1706 node1706Labels := by
  calc
    mixedMoment B raw25039 raw25039Labels = mixedMoment B raw25039step0 raw25039step0Labels := by
      have ha : raw25039step0 = (fun i j => raw25039 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25039step0 raw25039; decide +kernel
      have hl : raw25039step0Labels = raw25039Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25039 raw25039Labels permutation194 permutation7
    mixedMoment B raw25039step0 raw25039step0Labels = mixedMoment B raw25039step1 raw25039step1Labels := by
      have ha : raw25039step1 = -raw25039step0 := by apply Matrix.ext; change ∀ i j, raw25039step1 i j = -(raw25039step0 i j); unfold raw25039step1 raw25039step0; decide +kernel
      have hl : raw25039step1Labels = raw25039step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25039step1 raw25039step1Labels = mixedMoment B raw25039step2 raw25039step2Labels := by
      have ha : raw25039step2 = raw25039step1 := by apply Matrix.ext; unfold raw25039step2 raw25039step1; decide +kernel
      have hl : raw25039step1Labels = labelEmbedding1 ∘ raw25039step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25039step1 raw25039step1Labels raw25039step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1706 node1706Labels := by rfl

def raw25040 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25040Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25040step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25040step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25040step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw25040step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25040step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25040step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25040step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25040step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25040 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25040 raw25040Labels = mixedMoment B node1522 node1522Labels := by
  calc
    mixedMoment B raw25040 raw25040Labels = mixedMoment B raw25040step0 raw25040step0Labels := by
      have hz : ∀ j, raw25040 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25040step0 = (fun i j => raw25040 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25040step0 raw25040; decide +kernel
      have hl : raw25040step0Labels = raw25040Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25040 raw25040Labels permutation346 hz
    mixedMoment B raw25040step0 raw25040step0Labels = mixedMoment B raw25040step1 raw25040step1Labels := by
      have ha : raw25040step1 = (fun i j => raw25040step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25040step1 raw25040step0; decide +kernel
      have hl : raw25040step1Labels = raw25040step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25040step0 raw25040step0Labels permutation51 permutation7
    mixedMoment B raw25040step1 raw25040step1Labels = mixedMoment B raw25040step2 raw25040step2Labels := by
      have ha : raw25040step2 = -raw25040step1 := by apply Matrix.ext; change ∀ i j, raw25040step2 i j = -(raw25040step1 i j); unfold raw25040step2 raw25040step1; decide +kernel
      have hl : raw25040step2Labels = raw25040step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25040step2 raw25040step2Labels = mixedMoment B raw25040step3 raw25040step3Labels := by
      have ha : raw25040step3 = raw25040step2 := by apply Matrix.ext; unfold raw25040step3 raw25040step2; decide +kernel
      have hl : raw25040step2Labels = labelEmbedding1 ∘ raw25040step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25040step2 raw25040step2Labels raw25040step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1522 node1522Labels := by rfl

def raw25041 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25041Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25041step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25041step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25041step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25041step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25041step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw25041step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25041step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw25041step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25041 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25041 raw25041Labels = mixedMoment B node1734 node1734Labels := by
  calc
    mixedMoment B raw25041 raw25041Labels = mixedMoment B raw25041step0 raw25041step0Labels := by
      have hz : ∀ j, raw25041 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25041step0 = (fun i j => raw25041 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25041step0 raw25041; decide +kernel
      have hl : raw25041step0Labels = raw25041Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25041 raw25041Labels permutation346 hz
    mixedMoment B raw25041step0 raw25041step0Labels = mixedMoment B raw25041step1 raw25041step1Labels := by
      have ha : raw25041step1 = (fun i j => raw25041step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25041step1 raw25041step0; decide +kernel
      have hl : raw25041step1Labels = raw25041step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25041step0 raw25041step0Labels permutation51 permutation7
    mixedMoment B raw25041step1 raw25041step1Labels = mixedMoment B raw25041step2 raw25041step2Labels := by
      have ha : raw25041step2 = -raw25041step1 := by apply Matrix.ext; change ∀ i j, raw25041step2 i j = -(raw25041step1 i j); unfold raw25041step2 raw25041step1; decide +kernel
      have hl : raw25041step2Labels = raw25041step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25041step2 raw25041step2Labels = mixedMoment B raw25041step3 raw25041step3Labels := by
      have ha : raw25041step3 = raw25041step2 := by apply Matrix.ext; unfold raw25041step3 raw25041step2; decide +kernel
      have hl : raw25041step2Labels = labelEmbedding1 ∘ raw25041step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25041step2 raw25041step2Labels raw25041step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1734 node1734Labels := by rfl

def raw25042 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25042Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25042step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw25042step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25042step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25042step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25042step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25042step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25042 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25042 raw25042Labels = mixedMoment B node1678 node1678Labels := by
  calc
    mixedMoment B raw25042 raw25042Labels = mixedMoment B raw25042step0 raw25042step0Labels := by
      have ha : raw25042step0 = (fun i j => raw25042 (permutation195 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25042step0 raw25042; decide +kernel
      have hl : raw25042step0Labels = raw25042Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25042 raw25042Labels permutation195 permutation7
    mixedMoment B raw25042step0 raw25042step0Labels = mixedMoment B raw25042step1 raw25042step1Labels := by
      have ha : raw25042step1 = -raw25042step0 := by apply Matrix.ext; change ∀ i j, raw25042step1 i j = -(raw25042step0 i j); unfold raw25042step1 raw25042step0; decide +kernel
      have hl : raw25042step1Labels = raw25042step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25042step1 raw25042step1Labels = mixedMoment B raw25042step2 raw25042step2Labels := by
      have ha : raw25042step2 = raw25042step1 := by apply Matrix.ext; unfold raw25042step2 raw25042step1; decide +kernel
      have hl : raw25042step1Labels = labelEmbedding1 ∘ raw25042step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25042step1 raw25042step1Labels raw25042step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1678 node1678Labels := by rfl

def raw25043 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25043Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25043step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25043step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25043step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw25043step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25043step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25043step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25043step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25043step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25043 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25043 raw25043Labels = mixedMoment B node1736 node1736Labels := by
  calc
    mixedMoment B raw25043 raw25043Labels = mixedMoment B raw25043step0 raw25043step0Labels := by
      have hz : ∀ j, raw25043 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25043step0 = (fun i j => raw25043 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25043step0 raw25043; decide +kernel
      have hl : raw25043step0Labels = raw25043Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25043 raw25043Labels permutation346 hz
    mixedMoment B raw25043step0 raw25043step0Labels = mixedMoment B raw25043step1 raw25043step1Labels := by
      have ha : raw25043step1 = (fun i j => raw25043step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25043step1 raw25043step0; decide +kernel
      have hl : raw25043step1Labels = raw25043step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25043step0 raw25043step0Labels permutation51 permutation7
    mixedMoment B raw25043step1 raw25043step1Labels = mixedMoment B raw25043step2 raw25043step2Labels := by
      have ha : raw25043step2 = -raw25043step1 := by apply Matrix.ext; change ∀ i j, raw25043step2 i j = -(raw25043step1 i j); unfold raw25043step2 raw25043step1; decide +kernel
      have hl : raw25043step2Labels = raw25043step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25043step2 raw25043step2Labels = mixedMoment B raw25043step3 raw25043step3Labels := by
      have ha : raw25043step3 = raw25043step2 := by apply Matrix.ext; unfold raw25043step3 raw25043step2; decide +kernel
      have hl : raw25043step2Labels = labelEmbedding1 ∘ raw25043step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25043step2 raw25043step2Labels raw25043step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1736 node1736Labels := by rfl

def raw25044 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25044Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25044step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25044step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25044step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw25044step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25044step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25044step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25044step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25044step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25044 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25044 raw25044Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw25044 raw25044Labels = mixedMoment B raw25044step0 raw25044step0Labels := by
      have hz : ∀ j, raw25044 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25044step0 = (fun i j => raw25044 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25044step0 raw25044; decide +kernel
      have hl : raw25044step0Labels = raw25044Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25044 raw25044Labels permutation346 hz
    mixedMoment B raw25044step0 raw25044step0Labels = mixedMoment B raw25044step1 raw25044step1Labels := by
      have ha : raw25044step1 = (fun i j => raw25044step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25044step1 raw25044step0; decide +kernel
      have hl : raw25044step1Labels = raw25044step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25044step0 raw25044step0Labels permutation51 permutation7
    mixedMoment B raw25044step1 raw25044step1Labels = mixedMoment B raw25044step2 raw25044step2Labels := by
      have ha : raw25044step2 = -raw25044step1 := by apply Matrix.ext; change ∀ i j, raw25044step2 i j = -(raw25044step1 i j); unfold raw25044step2 raw25044step1; decide +kernel
      have hl : raw25044step2Labels = raw25044step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25044step2 raw25044step2Labels = mixedMoment B raw25044step3 raw25044step3Labels := by
      have ha : raw25044step3 = raw25044step2 := by apply Matrix.ext; unfold raw25044step3 raw25044step2; decide +kernel
      have hl : raw25044step2Labels = labelEmbedding1 ∘ raw25044step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25044step2 raw25044step2Labels raw25044step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1724 node1724Labels := by rfl

def raw25045 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25045Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25045step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25045step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25045step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw25045step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25045step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25045step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25045step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25045step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25045 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25045 raw25045Labels = mixedMoment B node1522 node1522Labels := by
  calc
    mixedMoment B raw25045 raw25045Labels = mixedMoment B raw25045step0 raw25045step0Labels := by
      have hz : ∀ j, raw25045 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25045step0 = (fun i j => raw25045 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25045step0 raw25045; decide +kernel
      have hl : raw25045step0Labels = raw25045Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25045 raw25045Labels permutation346 hz
    mixedMoment B raw25045step0 raw25045step0Labels = mixedMoment B raw25045step1 raw25045step1Labels := by
      have ha : raw25045step1 = (fun i j => raw25045step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25045step1 raw25045step0; decide +kernel
      have hl : raw25045step1Labels = raw25045step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25045step0 raw25045step0Labels permutation50 permutation7
    mixedMoment B raw25045step1 raw25045step1Labels = mixedMoment B raw25045step2 raw25045step2Labels := by
      have ha : raw25045step2 = -raw25045step1 := by apply Matrix.ext; change ∀ i j, raw25045step2 i j = -(raw25045step1 i j); unfold raw25045step2 raw25045step1; decide +kernel
      have hl : raw25045step2Labels = raw25045step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25045step2 raw25045step2Labels = mixedMoment B raw25045step3 raw25045step3Labels := by
      have ha : raw25045step3 = raw25045step2 := by apply Matrix.ext; unfold raw25045step3 raw25045step2; decide +kernel
      have hl : raw25045step2Labels = labelEmbedding1 ∘ raw25045step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25045step2 raw25045step2Labels raw25045step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1522 node1522Labels := by rfl

def raw25046 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25046Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25046step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25046step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25046step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw25046step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25046step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw25046step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25046step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw25046step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25046 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25046 raw25046Labels = mixedMoment B node1734 node1734Labels := by
  calc
    mixedMoment B raw25046 raw25046Labels = mixedMoment B raw25046step0 raw25046step0Labels := by
      have hz : ∀ j, raw25046 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25046step0 = (fun i j => raw25046 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25046step0 raw25046; decide +kernel
      have hl : raw25046step0Labels = raw25046Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25046 raw25046Labels permutation346 hz
    mixedMoment B raw25046step0 raw25046step0Labels = mixedMoment B raw25046step1 raw25046step1Labels := by
      have ha : raw25046step1 = (fun i j => raw25046step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25046step1 raw25046step0; decide +kernel
      have hl : raw25046step1Labels = raw25046step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25046step0 raw25046step0Labels permutation50 permutation7
    mixedMoment B raw25046step1 raw25046step1Labels = mixedMoment B raw25046step2 raw25046step2Labels := by
      have ha : raw25046step2 = -raw25046step1 := by apply Matrix.ext; change ∀ i j, raw25046step2 i j = -(raw25046step1 i j); unfold raw25046step2 raw25046step1; decide +kernel
      have hl : raw25046step2Labels = raw25046step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25046step2 raw25046step2Labels = mixedMoment B raw25046step3 raw25046step3Labels := by
      have ha : raw25046step3 = raw25046step2 := by apply Matrix.ext; unfold raw25046step3 raw25046step2; decide +kernel
      have hl : raw25046step2Labels = labelEmbedding1 ∘ raw25046step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25046step2 raw25046step2Labels raw25046step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1734 node1734Labels := by rfl

def raw25047 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25047Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25047step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw25047step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25047step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25047step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25047step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25047step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25047 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25047 raw25047Labels = mixedMoment B node1678 node1678Labels := by
  calc
    mixedMoment B raw25047 raw25047Labels = mixedMoment B raw25047step0 raw25047step0Labels := by
      have ha : raw25047step0 = (fun i j => raw25047 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25047step0 raw25047; decide +kernel
      have hl : raw25047step0Labels = raw25047Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25047 raw25047Labels permutation194 permutation7
    mixedMoment B raw25047step0 raw25047step0Labels = mixedMoment B raw25047step1 raw25047step1Labels := by
      have ha : raw25047step1 = -raw25047step0 := by apply Matrix.ext; change ∀ i j, raw25047step1 i j = -(raw25047step0 i j); unfold raw25047step1 raw25047step0; decide +kernel
      have hl : raw25047step1Labels = raw25047step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25047step1 raw25047step1Labels = mixedMoment B raw25047step2 raw25047step2Labels := by
      have ha : raw25047step2 = raw25047step1 := by apply Matrix.ext; unfold raw25047step2 raw25047step1; decide +kernel
      have hl : raw25047step1Labels = labelEmbedding1 ∘ raw25047step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25047step1 raw25047step1Labels raw25047step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1678 node1678Labels := by rfl

def raw25048 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25048Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25048step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25048step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25048step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw25048step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25048step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25048step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25048step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw25048step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25048 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25048 raw25048Labels = mixedMoment B node1736 node1736Labels := by
  calc
    mixedMoment B raw25048 raw25048Labels = mixedMoment B raw25048step0 raw25048step0Labels := by
      have hz : ∀ j, raw25048 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25048step0 = (fun i j => raw25048 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25048step0 raw25048; decide +kernel
      have hl : raw25048step0Labels = raw25048Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25048 raw25048Labels permutation346 hz
    mixedMoment B raw25048step0 raw25048step0Labels = mixedMoment B raw25048step1 raw25048step1Labels := by
      have ha : raw25048step1 = (fun i j => raw25048step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25048step1 raw25048step0; decide +kernel
      have hl : raw25048step1Labels = raw25048step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25048step0 raw25048step0Labels permutation50 permutation7
    mixedMoment B raw25048step1 raw25048step1Labels = mixedMoment B raw25048step2 raw25048step2Labels := by
      have ha : raw25048step2 = -raw25048step1 := by apply Matrix.ext; change ∀ i j, raw25048step2 i j = -(raw25048step1 i j); unfold raw25048step2 raw25048step1; decide +kernel
      have hl : raw25048step2Labels = raw25048step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25048step2 raw25048step2Labels = mixedMoment B raw25048step3 raw25048step3Labels := by
      have ha : raw25048step3 = raw25048step2 := by apply Matrix.ext; unfold raw25048step3 raw25048step2; decide +kernel
      have hl : raw25048step2Labels = labelEmbedding1 ∘ raw25048step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25048step2 raw25048step2Labels raw25048step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1736 node1736Labels := by rfl

def raw25049 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw25049Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25049step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw25049step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25049step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw25049step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25049step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25049step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25049step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw25049step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25049 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25049 raw25049Labels = mixedMoment B node1724 node1724Labels := by
  calc
    mixedMoment B raw25049 raw25049Labels = mixedMoment B raw25049step0 raw25049step0Labels := by
      have hz : ∀ j, raw25049 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25049step0 = (fun i j => raw25049 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25049step0 raw25049; decide +kernel
      have hl : raw25049step0Labels = raw25049Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25049 raw25049Labels permutation346 hz
    mixedMoment B raw25049step0 raw25049step0Labels = mixedMoment B raw25049step1 raw25049step1Labels := by
      have ha : raw25049step1 = (fun i j => raw25049step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25049step1 raw25049step0; decide +kernel
      have hl : raw25049step1Labels = raw25049step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25049step0 raw25049step0Labels permutation50 permutation7
    mixedMoment B raw25049step1 raw25049step1Labels = mixedMoment B raw25049step2 raw25049step2Labels := by
      have ha : raw25049step2 = -raw25049step1 := by apply Matrix.ext; change ∀ i j, raw25049step2 i j = -(raw25049step1 i j); unfold raw25049step2 raw25049step1; decide +kernel
      have hl : raw25049step2Labels = raw25049step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25049step2 raw25049step2Labels = mixedMoment B raw25049step3 raw25049step3Labels := by
      have ha : raw25049step3 = raw25049step2 := by apply Matrix.ext; unfold raw25049step3 raw25049step2; decide +kernel
      have hl : raw25049step2Labels = labelEmbedding1 ∘ raw25049step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25049step2 raw25049step2Labels raw25049step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1724 node1724Labels := by rfl

def raw25050 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25050Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25050step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25050step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25050step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -3, 3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw25050step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25050step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25050step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25050step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25050step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25050 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25050 raw25050Labels = mixedMoment B node1528 node1528Labels := by
  calc
    mixedMoment B raw25050 raw25050Labels = mixedMoment B raw25050step0 raw25050step0Labels := by
      have hz : ∀ j, raw25050 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25050step0 = (fun i j => raw25050 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25050step0 raw25050; decide +kernel
      have hl : raw25050step0Labels = raw25050Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25050 raw25050Labels permutation346 hz
    mixedMoment B raw25050step0 raw25050step0Labels = mixedMoment B raw25050step1 raw25050step1Labels := by
      have ha : raw25050step1 = (fun i j => raw25050step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25050step1 raw25050step0; decide +kernel
      have hl : raw25050step1Labels = raw25050step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25050step0 raw25050step0Labels permutation50 permutation7
    mixedMoment B raw25050step1 raw25050step1Labels = mixedMoment B raw25050step2 raw25050step2Labels := by
      have ha : raw25050step2 = -raw25050step1 := by apply Matrix.ext; change ∀ i j, raw25050step2 i j = -(raw25050step1 i j); unfold raw25050step2 raw25050step1; decide +kernel
      have hl : raw25050step2Labels = raw25050step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25050step2 raw25050step2Labels = mixedMoment B raw25050step3 raw25050step3Labels := by
      have ha : raw25050step3 = raw25050step2 := by apply Matrix.ext; unfold raw25050step3 raw25050step2; decide +kernel
      have hl : raw25050step2Labels = labelEmbedding1 ∘ raw25050step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25050step2 raw25050step2Labels raw25050step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1528 node1528Labels := by rfl

def raw25051 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25051Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25051step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25051step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25051step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw25051step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25051step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw25051step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25051step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw25051step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25051 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25051 raw25051Labels = mixedMoment B node1742 node1742Labels := by
  calc
    mixedMoment B raw25051 raw25051Labels = mixedMoment B raw25051step0 raw25051step0Labels := by
      have hz : ∀ j, raw25051 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25051step0 = (fun i j => raw25051 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25051step0 raw25051; decide +kernel
      have hl : raw25051step0Labels = raw25051Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25051 raw25051Labels permutation346 hz
    mixedMoment B raw25051step0 raw25051step0Labels = mixedMoment B raw25051step1 raw25051step1Labels := by
      have ha : raw25051step1 = (fun i j => raw25051step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25051step1 raw25051step0; decide +kernel
      have hl : raw25051step1Labels = raw25051step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25051step0 raw25051step0Labels permutation50 permutation7
    mixedMoment B raw25051step1 raw25051step1Labels = mixedMoment B raw25051step2 raw25051step2Labels := by
      have ha : raw25051step2 = -raw25051step1 := by apply Matrix.ext; change ∀ i j, raw25051step2 i j = -(raw25051step1 i j); unfold raw25051step2 raw25051step1; decide +kernel
      have hl : raw25051step2Labels = raw25051step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25051step2 raw25051step2Labels = mixedMoment B raw25051step3 raw25051step3Labels := by
      have ha : raw25051step3 = raw25051step2 := by apply Matrix.ext; unfold raw25051step3 raw25051step2; decide +kernel
      have hl : raw25051step2Labels = labelEmbedding1 ∘ raw25051step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25051step2 raw25051step2Labels raw25051step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1742 node1742Labels := by rfl

def raw25052 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25052Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25052step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 1, -1], ![0, -3, 3], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw25052step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25052step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25052step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25052step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw25052step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25052 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25052 raw25052Labels = mixedMoment B node1684 node1684Labels := by
  calc
    mixedMoment B raw25052 raw25052Labels = mixedMoment B raw25052step0 raw25052step0Labels := by
      have ha : raw25052step0 = (fun i j => raw25052 (permutation194 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25052step0 raw25052; decide +kernel
      have hl : raw25052step0Labels = raw25052Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25052 raw25052Labels permutation194 permutation7
    mixedMoment B raw25052step0 raw25052step0Labels = mixedMoment B raw25052step1 raw25052step1Labels := by
      have ha : raw25052step1 = -raw25052step0 := by apply Matrix.ext; change ∀ i j, raw25052step1 i j = -(raw25052step0 i j); unfold raw25052step1 raw25052step0; decide +kernel
      have hl : raw25052step1Labels = raw25052step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25052step1 raw25052step1Labels = mixedMoment B raw25052step2 raw25052step2Labels := by
      have ha : raw25052step2 = raw25052step1 := by apply Matrix.ext; unfold raw25052step2 raw25052step1; decide +kernel
      have hl : raw25052step1Labels = labelEmbedding1 ∘ raw25052step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25052step1 raw25052step1Labels raw25052step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1684 node1684Labels := by rfl

def raw25053 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25053Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25053step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25053step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25053step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw25053step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25053step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw25053step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25053step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw25053step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25053 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25053 raw25053Labels = mixedMoment B node1744 node1744Labels := by
  calc
    mixedMoment B raw25053 raw25053Labels = mixedMoment B raw25053step0 raw25053step0Labels := by
      have hz : ∀ j, raw25053 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25053step0 = (fun i j => raw25053 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25053step0 raw25053; decide +kernel
      have hl : raw25053step0Labels = raw25053Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25053 raw25053Labels permutation346 hz
    mixedMoment B raw25053step0 raw25053step0Labels = mixedMoment B raw25053step1 raw25053step1Labels := by
      have ha : raw25053step1 = (fun i j => raw25053step0 (permutation50 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25053step1 raw25053step0; decide +kernel
      have hl : raw25053step1Labels = raw25053step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25053step0 raw25053step0Labels permutation50 permutation7
    mixedMoment B raw25053step1 raw25053step1Labels = mixedMoment B raw25053step2 raw25053step2Labels := by
      have ha : raw25053step2 = -raw25053step1 := by apply Matrix.ext; change ∀ i j, raw25053step2 i j = -(raw25053step1 i j); unfold raw25053step2 raw25053step1; decide +kernel
      have hl : raw25053step2Labels = raw25053step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25053step2 raw25053step2Labels = mixedMoment B raw25053step3 raw25053step3Labels := by
      have ha : raw25053step3 = raw25053step2 := by apply Matrix.ext; unfold raw25053step3 raw25053step2; decide +kernel
      have hl : raw25053step2Labels = labelEmbedding1 ∘ raw25053step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25053step2 raw25053step2Labels raw25053step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1744 node1744Labels := by rfl

def raw25054 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw25054Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25054step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw25054step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw25054step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -3, 3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw25054step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25054step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw25054step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw25054step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw25054step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25054 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25054 raw25054Labels = mixedMoment B node1744 node1744Labels := by
  calc
    mixedMoment B raw25054 raw25054Labels = mixedMoment B raw25054step0 raw25054step0Labels := by
      have hz : ∀ j, raw25054 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25054step0 = (fun i j => raw25054 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25054step0 raw25054; decide +kernel
      have hl : raw25054step0Labels = raw25054Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25054 raw25054Labels permutation346 hz
    mixedMoment B raw25054step0 raw25054step0Labels = mixedMoment B raw25054step1 raw25054step1Labels := by
      have ha : raw25054step1 = (fun i j => raw25054step0 (permutation51 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25054step1 raw25054step0; decide +kernel
      have hl : raw25054step1Labels = raw25054step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25054step0 raw25054step0Labels permutation51 permutation7
    mixedMoment B raw25054step1 raw25054step1Labels = mixedMoment B raw25054step2 raw25054step2Labels := by
      have ha : raw25054step2 = -raw25054step1 := by apply Matrix.ext; change ∀ i j, raw25054step2 i j = -(raw25054step1 i j); unfold raw25054step2 raw25054step1; decide +kernel
      have hl : raw25054step2Labels = raw25054step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw25054step2 raw25054step2Labels = mixedMoment B raw25054step3 raw25054step3Labels := by
      have ha : raw25054step3 = raw25054step2 := by apply Matrix.ext; unfold raw25054step3 raw25054step2; decide +kernel
      have hl : raw25054step2Labels = labelEmbedding1 ∘ raw25054step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25054step2 raw25054step2Labels raw25054step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1744 node1744Labels := by rfl

def raw25055 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25055Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25055step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25055step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25055 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25055 raw25055Labels = mixedMoment B node610 node610Labels := by
  calc
    mixedMoment B raw25055 raw25055Labels = mixedMoment B raw25055step0 raw25055step0Labels := by
      have hz : ∀ j, raw25055 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25055step0 = (fun i j => raw25055 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25055step0 raw25055; decide +kernel
      have hl : raw25055step0Labels = raw25055Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25055 raw25055Labels permutation346 hz
    _ = mixedMoment B node610 node610Labels := by rfl

def raw25056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25056Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25056step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25056step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25056 raw25056Labels = mixedMoment B node1044 node1044Labels := by
  calc
    mixedMoment B raw25056 raw25056Labels = mixedMoment B raw25056step0 raw25056step0Labels := by
      have hz : ∀ j, raw25056 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25056step0 = (fun i j => raw25056 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25056step0 raw25056; decide +kernel
      have hl : raw25056step0Labels = raw25056Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25056 raw25056Labels permutation346 hz
    _ = mixedMoment B node1044 node1044Labels := by rfl

def raw25057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25057Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25057step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25057step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25057 raw25057Labels = mixedMoment B node929 node929Labels := by
  calc
    mixedMoment B raw25057 raw25057Labels = mixedMoment B raw25057step0 raw25057step0Labels := by
      have ha : raw25057step0 = (fun i j => raw25057 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25057step0 raw25057; decide +kernel
      have hl : raw25057step0Labels = raw25057Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25057 raw25057Labels permutation176 permutation2
    _ = mixedMoment B node929 node929Labels := by rfl

def raw25058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25058Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25058step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25058step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25058step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25058step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25058 raw25058Labels = mixedMoment B node1044 node1044Labels := by
  calc
    mixedMoment B raw25058 raw25058Labels = mixedMoment B raw25058step0 raw25058step0Labels := by
      have hz : ∀ j, raw25058 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25058step0 = (fun i j => raw25058 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25058step0 raw25058; decide +kernel
      have hl : raw25058step0Labels = raw25058Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25058 raw25058Labels permutation346 hz
    mixedMoment B raw25058step0 raw25058step0Labels = mixedMoment B raw25058step1 raw25058step1Labels := by
      have ha : raw25058step1 = (fun i j => raw25058step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25058step1 raw25058step0; decide +kernel
      have hl : raw25058step1Labels = raw25058step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25058step0 raw25058step0Labels permutation38 permutation2
    _ = mixedMoment B node1044 node1044Labels := by rfl

def raw25059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25059Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25059step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw25059step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25059step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25059step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25059 raw25059Labels = mixedMoment B node1044 node1044Labels := by
  calc
    mixedMoment B raw25059 raw25059Labels = mixedMoment B raw25059step0 raw25059step0Labels := by
      have hz : ∀ j, raw25059 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25059step0 = (fun i j => raw25059 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25059step0 raw25059; decide +kernel
      have hl : raw25059step0Labels = raw25059Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25059 raw25059Labels permutation346 hz
    mixedMoment B raw25059step0 raw25059step0Labels = mixedMoment B raw25059step1 raw25059step1Labels := by
      have ha : raw25059step1 = (fun i j => raw25059step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25059step1 raw25059step0; decide +kernel
      have hl : raw25059step1Labels = raw25059step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25059step0 raw25059step0Labels permutation44 permutation2
    _ = mixedMoment B node1044 node1044Labels := by rfl

def raw25060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25060Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25060step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw25060step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25060step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw25060step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25060 raw25060Labels = mixedMoment B node1081 node1081Labels := by
  calc
    mixedMoment B raw25060 raw25060Labels = mixedMoment B raw25060step0 raw25060step0Labels := by
      have hz : ∀ j, raw25060 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25060step0 = (fun i j => raw25060 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25060step0 raw25060; decide +kernel
      have hl : raw25060step0Labels = raw25060Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25060 raw25060Labels permutation346 hz
    mixedMoment B raw25060step0 raw25060step0Labels = mixedMoment B raw25060step1 raw25060step1Labels := by
      have ha : raw25060step1 = (fun i j => raw25060step0 (permutation50 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25060step1 raw25060step0; decide +kernel
      have hl : raw25060step1Labels = raw25060step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25060step0 raw25060step0Labels permutation50 permutation2
    _ = mixedMoment B node1081 node1081Labels := by rfl

def raw25061 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![1, -1], ![1, -1], ![0, 0]]
def raw25061Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25061step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![0, 0], ![1, -1], ![1, -1]]
def raw25061step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw25061step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw25061step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical25061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25061 raw25061Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw25061 raw25061Labels = mixedMoment B raw25061step0 raw25061step0Labels := by
      have hz : ∀ j, raw25061 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw25061step0 = (fun i j => raw25061 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw25061step0 raw25061; decide +kernel
      have hl : raw25061step0Labels = raw25061Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25061 raw25061Labels permutation590 hz
    mixedMoment B raw25061step0 raw25061step0Labels = mixedMoment B raw25061step1 raw25061step1Labels := by
      have hz : ∀ j, raw25061step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25061step1 = (fun i j => raw25061step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25061step1 raw25061step0; decide +kernel
      have hl : raw25061step1Labels = raw25061step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25061step0 raw25061step0Labels permutation80 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

def raw25062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25062Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25062step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25062step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25062 raw25062Labels = mixedMoment B node2110 node2110Labels := by
  calc
    mixedMoment B raw25062 raw25062Labels = mixedMoment B raw25062step0 raw25062step0Labels := by
      have hz : ∀ j, raw25062 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25062step0 = (fun i j => raw25062 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25062step0 raw25062; decide +kernel
      have hl : raw25062step0Labels = raw25062Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25062 raw25062Labels permutation346 hz
    _ = mixedMoment B node2110 node2110Labels := by rfl

def raw25063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25063Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25063 raw25063Labels = mixedMoment B node944 node944Labels := by
  calc
    _ = mixedMoment B node944 node944Labels := by rfl

def raw25064 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25064Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25064step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25064step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25064step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25064step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25064 raw25064Labels = mixedMoment B node950 node950Labels := by
  calc
    mixedMoment B raw25064 raw25064Labels = mixedMoment B raw25064step0 raw25064step0Labels := by
      have hz : ∀ j, raw25064 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25064step0 = (fun i j => raw25064 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25064step0 raw25064; decide +kernel
      have hl : raw25064step0Labels = raw25064Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25064 raw25064Labels permutation346 hz
    mixedMoment B raw25064step0 raw25064step0Labels = mixedMoment B raw25064step1 raw25064step1Labels := by
      have ha : raw25064step1 = (fun i j => raw25064step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25064step1 raw25064step0; decide +kernel
      have hl : raw25064step1Labels = raw25064step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25064step0 raw25064step0Labels permutation35 permutation2
    _ = mixedMoment B node950 node950Labels := by rfl

def raw25065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25065Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25065step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw25065step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25065step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw25065step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25065 raw25065Labels = mixedMoment B node950 node950Labels := by
  calc
    mixedMoment B raw25065 raw25065Labels = mixedMoment B raw25065step0 raw25065step0Labels := by
      have hz : ∀ j, raw25065 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25065step0 = (fun i j => raw25065 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25065step0 raw25065; decide +kernel
      have hl : raw25065step0Labels = raw25065Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25065 raw25065Labels permutation346 hz
    mixedMoment B raw25065step0 raw25065step0Labels = mixedMoment B raw25065step1 raw25065step1Labels := by
      have ha : raw25065step1 = (fun i j => raw25065step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw25065step1 raw25065step0; decide +kernel
      have hl : raw25065step1Labels = raw25065step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25065step0 raw25065step0Labels permutation33 permutation2
    _ = mixedMoment B node950 node950Labels := by rfl

def raw25066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25066Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw25066step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw25066step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25066 raw25066Labels = mixedMoment B node949 node949Labels := by
  calc
    mixedMoment B raw25066 raw25066Labels = mixedMoment B raw25066step0 raw25066step0Labels := by
      have hz : ∀ j, raw25066 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25066step0 = (fun i j => raw25066 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25066step0 raw25066; decide +kernel
      have hl : raw25066step0Labels = raw25066Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25066 raw25066Labels permutation346 hz
    _ = mixedMoment B node949 node949Labels := by rfl

def raw25067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25067Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25067step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25067step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25067step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25067step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25067step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25067step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25067 raw25067Labels = mixedMoment B node4126 node4126Labels := by
  calc
    mixedMoment B raw25067 raw25067Labels = mixedMoment B raw25067step0 raw25067step0Labels := by
      have hz : ∀ j, raw25067 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25067step0 = (fun i j => raw25067 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25067step0 raw25067; decide +kernel
      have hl : raw25067step0Labels = raw25067Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25067 raw25067Labels permutation346 hz
    mixedMoment B raw25067step0 raw25067step0Labels = mixedMoment B raw25067step1 raw25067step1Labels := by
      have ha : raw25067step1 = (fun i j => raw25067step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25067step1 raw25067step0; decide +kernel
      have hl : raw25067step1Labels = raw25067step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25067step0 raw25067step0Labels permutation40 permutation3
    mixedMoment B raw25067step1 raw25067step1Labels = mixedMoment B raw25067step2 raw25067step2Labels := by
      have ha : raw25067step2 = raw25067step1 := by apply Matrix.ext; unfold raw25067step2 raw25067step1; decide +kernel
      have hl : raw25067step1Labels = labelEmbedding6 ∘ raw25067step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25067step1 raw25067step1Labels raw25067step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4126 node4126Labels := by rfl

def raw25068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25068Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25068step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25068step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25068step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25068step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25068 raw25068Labels = mixedMoment B node4307 node4307Labels := by
  calc
    mixedMoment B raw25068 raw25068Labels = mixedMoment B raw25068step0 raw25068step0Labels := by
      have ha : raw25068step0 = (fun i j => raw25068 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25068step0 raw25068; decide +kernel
      have hl : raw25068step0Labels = raw25068Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25068 raw25068Labels permutation184 permutation3
    mixedMoment B raw25068step0 raw25068step0Labels = mixedMoment B raw25068step1 raw25068step1Labels := by
      have ha : raw25068step1 = raw25068step0 := by apply Matrix.ext; unfold raw25068step1 raw25068step0; decide +kernel
      have hl : raw25068step0Labels = labelEmbedding6 ∘ raw25068step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25068step0 raw25068step0Labels raw25068step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4307 node4307Labels := by rfl

def raw25069 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw25069Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25069step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25069step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25069step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25069step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25069step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25069step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25069step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25069step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25069 raw25069Labels = mixedMoment B node4503 node4503Labels := by
  calc
    mixedMoment B raw25069 raw25069Labels = mixedMoment B raw25069step0 raw25069step0Labels := by
      have hz : ∀ j, raw25069 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25069step0 = (fun i j => raw25069 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25069step0 raw25069; decide +kernel
      have hl : raw25069step0Labels = raw25069Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25069 raw25069Labels permutation520 hz
    mixedMoment B raw25069step0 raw25069step0Labels = mixedMoment B raw25069step1 raw25069step1Labels := by
      have hz : ∀ j, raw25069step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25069step1 = (fun i j => raw25069step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25069step1 raw25069step0; decide +kernel
      have hl : raw25069step1Labels = raw25069step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25069step0 raw25069step0Labels permutation80 hz
    mixedMoment B raw25069step1 raw25069step1Labels = mixedMoment B raw25069step2 raw25069step2Labels := by
      have ha : raw25069step2 = (fun i j => raw25069step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25069step2 raw25069step1; decide +kernel
      have hl : raw25069step2Labels = raw25069step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25069step1 raw25069step1Labels permutation10 permutation3
    mixedMoment B raw25069step2 raw25069step2Labels = mixedMoment B raw25069step3 raw25069step3Labels := by
      have ha : raw25069step3 = raw25069step2 := by apply Matrix.ext; unfold raw25069step3 raw25069step2; decide +kernel
      have hl : raw25069step2Labels = labelEmbedding6 ∘ raw25069step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25069step2 raw25069step2Labels raw25069step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4503 node4503Labels := by rfl

def raw25070 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25070Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25070step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25070step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25070step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25070step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25070 raw25070Labels = mixedMoment B node4104 node4104Labels := by
  calc
    mixedMoment B raw25070 raw25070Labels = mixedMoment B raw25070step0 raw25070step0Labels := by
      have ha : raw25070step0 = (fun i j => raw25070 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25070step0 raw25070; decide +kernel
      have hl : raw25070step0Labels = raw25070Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25070 raw25070Labels permutation152 permutation3
    mixedMoment B raw25070step0 raw25070step0Labels = mixedMoment B raw25070step1 raw25070step1Labels := by
      have ha : raw25070step1 = raw25070step0 := by apply Matrix.ext; unfold raw25070step1 raw25070step0; decide +kernel
      have hl : raw25070step0Labels = labelEmbedding6 ∘ raw25070step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25070step0 raw25070step0Labels raw25070step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4104 node4104Labels := by rfl

def raw25071 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25071Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25071step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25071step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25071step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25071step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25071 raw25071Labels = mixedMoment B node4351 node4351Labels := by
  calc
    mixedMoment B raw25071 raw25071Labels = mixedMoment B raw25071step0 raw25071step0Labels := by
      have ha : raw25071step0 = (fun i j => raw25071 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25071step0 raw25071; decide +kernel
      have hl : raw25071step0Labels = raw25071Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25071 raw25071Labels permutation152 permutation3
    mixedMoment B raw25071step0 raw25071step0Labels = mixedMoment B raw25071step1 raw25071step1Labels := by
      have ha : raw25071step1 = raw25071step0 := by apply Matrix.ext; unfold raw25071step1 raw25071step0; decide +kernel
      have hl : raw25071step0Labels = labelEmbedding6 ∘ raw25071step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25071step0 raw25071step0Labels raw25071step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4351 node4351Labels := by rfl

def raw25072 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw25072Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25072step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25072step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25072step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25072step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25072step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25072step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25072 raw25072Labels = mixedMoment B node4461 node4461Labels := by
  calc
    mixedMoment B raw25072 raw25072Labels = mixedMoment B raw25072step0 raw25072step0Labels := by
      have hz : ∀ j, raw25072 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25072step0 = (fun i j => raw25072 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25072step0 raw25072; decide +kernel
      have hl : raw25072step0Labels = raw25072Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25072 raw25072Labels permutation520 hz
    mixedMoment B raw25072step0 raw25072step0Labels = mixedMoment B raw25072step1 raw25072step1Labels := by
      have ha : raw25072step1 = (fun i j => raw25072step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25072step1 raw25072step0; decide +kernel
      have hl : raw25072step1Labels = raw25072step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25072step0 raw25072step0Labels permutation32 permutation3
    mixedMoment B raw25072step1 raw25072step1Labels = mixedMoment B raw25072step2 raw25072step2Labels := by
      have ha : raw25072step2 = raw25072step1 := by apply Matrix.ext; unfold raw25072step2 raw25072step1; decide +kernel
      have hl : raw25072step1Labels = labelEmbedding6 ∘ raw25072step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25072step1 raw25072step1Labels raw25072step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4461 node4461Labels := by rfl

def raw25073 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25073Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25073step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25073step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25073step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25073step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25073step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25073step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25073 raw25073Labels = mixedMoment B node4106 node4106Labels := by
  calc
    mixedMoment B raw25073 raw25073Labels = mixedMoment B raw25073step0 raw25073step0Labels := by
      have hz : ∀ j, raw25073 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25073step0 = (fun i j => raw25073 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25073step0 raw25073; decide +kernel
      have hl : raw25073step0Labels = raw25073Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25073 raw25073Labels permutation346 hz
    mixedMoment B raw25073step0 raw25073step0Labels = mixedMoment B raw25073step1 raw25073step1Labels := by
      have ha : raw25073step1 = (fun i j => raw25073step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25073step1 raw25073step0; decide +kernel
      have hl : raw25073step1Labels = raw25073step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25073step0 raw25073step0Labels permutation35 permutation3
    mixedMoment B raw25073step1 raw25073step1Labels = mixedMoment B raw25073step2 raw25073step2Labels := by
      have ha : raw25073step2 = raw25073step1 := by apply Matrix.ext; unfold raw25073step2 raw25073step1; decide +kernel
      have hl : raw25073step1Labels = labelEmbedding6 ∘ raw25073step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25073step1 raw25073step1Labels raw25073step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4106 node4106Labels := by rfl

def raw25074 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25074Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25074step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25074step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25074step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25074step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25074step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25074 raw25074Labels = mixedMoment B node4354 node4354Labels := by
  calc
    mixedMoment B raw25074 raw25074Labels = mixedMoment B raw25074step0 raw25074step0Labels := by
      have hz : ∀ j, raw25074 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25074step0 = (fun i j => raw25074 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25074step0 raw25074; decide +kernel
      have hl : raw25074step0Labels = raw25074Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25074 raw25074Labels permutation346 hz
    mixedMoment B raw25074step0 raw25074step0Labels = mixedMoment B raw25074step1 raw25074step1Labels := by
      have ha : raw25074step1 = (fun i j => raw25074step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25074step1 raw25074step0; decide +kernel
      have hl : raw25074step1Labels = raw25074step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25074step0 raw25074step0Labels permutation35 permutation3
    mixedMoment B raw25074step1 raw25074step1Labels = mixedMoment B raw25074step2 raw25074step2Labels := by
      have ha : raw25074step2 = raw25074step1 := by apply Matrix.ext; unfold raw25074step2 raw25074step1; decide +kernel
      have hl : raw25074step1Labels = labelEmbedding6 ∘ raw25074step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25074step1 raw25074step1Labels raw25074step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4354 node4354Labels := by rfl

def raw25075 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25075Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25075step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25075step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25075step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25075step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25075 raw25075Labels = mixedMoment B node4291 node4291Labels := by
  calc
    mixedMoment B raw25075 raw25075Labels = mixedMoment B raw25075step0 raw25075step0Labels := by
      have ha : raw25075step0 = (fun i j => raw25075 (permutation179 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25075step0 raw25075; decide +kernel
      have hl : raw25075step0Labels = raw25075Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25075 raw25075Labels permutation179 permutation3
    mixedMoment B raw25075step0 raw25075step0Labels = mixedMoment B raw25075step1 raw25075step1Labels := by
      have ha : raw25075step1 = raw25075step0 := by apply Matrix.ext; unfold raw25075step1 raw25075step0; decide +kernel
      have hl : raw25075step0Labels = labelEmbedding6 ∘ raw25075step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25075step0 raw25075step0Labels raw25075step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4291 node4291Labels := by rfl

def raw25076 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw25076Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25076step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25076step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw25076step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25076step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25076step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw25076step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25076step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25076 raw25076Labels = mixedMoment B node4466 node4466Labels := by
  calc
    mixedMoment B raw25076 raw25076Labels = mixedMoment B raw25076step0 raw25076step0Labels := by
      have hz : ∀ j, raw25076 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25076step0 = (fun i j => raw25076 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25076step0 raw25076; decide +kernel
      have hl : raw25076step0Labels = raw25076Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25076 raw25076Labels permutation520 hz
    mixedMoment B raw25076step0 raw25076step0Labels = mixedMoment B raw25076step1 raw25076step1Labels := by
      have hz : ∀ j, raw25076step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25076step1 = (fun i j => raw25076step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25076step1 raw25076step0; decide +kernel
      have hl : raw25076step1Labels = raw25076step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25076step0 raw25076step0Labels permutation80 hz
    mixedMoment B raw25076step1 raw25076step1Labels = mixedMoment B raw25076step2 raw25076step2Labels := by
      have ha : raw25076step2 = (fun i j => raw25076step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25076step2 raw25076step1; decide +kernel
      have hl : raw25076step2Labels = raw25076step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25076step1 raw25076step1Labels permutation9 permutation3
    mixedMoment B raw25076step2 raw25076step2Labels = mixedMoment B raw25076step3 raw25076step3Labels := by
      have ha : raw25076step3 = raw25076step2 := by apply Matrix.ext; unfold raw25076step3 raw25076step2; decide +kernel
      have hl : raw25076step2Labels = labelEmbedding6 ∘ raw25076step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25076step2 raw25076step2Labels raw25076step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4466 node4466Labels := by rfl

def raw25077 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25077Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25077step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25077step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25077step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25077 raw25077Labels = mixedMoment B node557 node557Labels := by
  calc
    mixedMoment B raw25077 raw25077Labels = mixedMoment B raw25077step0 raw25077step0Labels := by
      have hz : ∀ j, raw25077 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25077step0 = (fun i j => raw25077 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25077step0 raw25077; decide +kernel
      have hl : raw25077step0Labels = raw25077Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25077 raw25077Labels permutation346 hz
    mixedMoment B raw25077step0 raw25077step0Labels = mixedMoment B raw25077step1 raw25077step1Labels := by
      have ha : raw25077step1 = (fun i j => raw25077step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25077step1 raw25077step0; decide +kernel
      have hl : raw25077step1Labels = raw25077step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25077step0 raw25077step0Labels permutation40 permutation3
    _ = mixedMoment B node557 node557Labels := by rfl

def raw25078 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25078Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25078step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25078step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25078 raw25078Labels = mixedMoment B node885 node885Labels := by
  calc
    mixedMoment B raw25078 raw25078Labels = mixedMoment B raw25078step0 raw25078step0Labels := by
      have ha : raw25078step0 = (fun i j => raw25078 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25078step0 raw25078; decide +kernel
      have hl : raw25078step0Labels = raw25078Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25078 raw25078Labels permutation184 permutation3
    _ = mixedMoment B node885 node885Labels := by rfl

def raw25079 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw25079Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25079step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25079step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw25079step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25079step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw25079step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25079 raw25079Labels = mixedMoment B node1087 node1087Labels := by
  calc
    mixedMoment B raw25079 raw25079Labels = mixedMoment B raw25079step0 raw25079step0Labels := by
      have hz : ∀ j, raw25079 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25079step0 = (fun i j => raw25079 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25079step0 raw25079; decide +kernel
      have hl : raw25079step0Labels = raw25079Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25079 raw25079Labels permutation520 hz
    mixedMoment B raw25079step0 raw25079step0Labels = mixedMoment B raw25079step1 raw25079step1Labels := by
      have hz : ∀ j, raw25079step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25079step1 = (fun i j => raw25079step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25079step1 raw25079step0; decide +kernel
      have hl : raw25079step1Labels = raw25079step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25079step0 raw25079step0Labels permutation80 hz
    mixedMoment B raw25079step1 raw25079step1Labels = mixedMoment B raw25079step2 raw25079step2Labels := by
      have ha : raw25079step2 = (fun i j => raw25079step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25079step2 raw25079step1; decide +kernel
      have hl : raw25079step2Labels = raw25079step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25079step1 raw25079step1Labels permutation10 permutation3
    _ = mixedMoment B node1087 node1087Labels := by rfl

def raw25080 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25080Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25080step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25080step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25080 raw25080Labels = mixedMoment B node541 node541Labels := by
  calc
    mixedMoment B raw25080 raw25080Labels = mixedMoment B raw25080step0 raw25080step0Labels := by
      have ha : raw25080step0 = (fun i j => raw25080 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25080step0 raw25080; decide +kernel
      have hl : raw25080step0Labels = raw25080Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25080 raw25080Labels permutation152 permutation3
    _ = mixedMoment B node541 node541Labels := by rfl

def raw25081 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25081Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25081step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25081step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25081 raw25081Labels = mixedMoment B node929 node929Labels := by
  calc
    mixedMoment B raw25081 raw25081Labels = mixedMoment B raw25081step0 raw25081step0Labels := by
      have ha : raw25081step0 = (fun i j => raw25081 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25081step0 raw25081; decide +kernel
      have hl : raw25081step0Labels = raw25081Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25081 raw25081Labels permutation152 permutation3
    _ = mixedMoment B node929 node929Labels := by rfl

def raw25082 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw25082Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25082step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25082step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw25082step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25082 raw25082Labels = mixedMoment B node1044 node1044Labels := by
  calc
    mixedMoment B raw25082 raw25082Labels = mixedMoment B raw25082step0 raw25082step0Labels := by
      have hz : ∀ j, raw25082 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25082step0 = (fun i j => raw25082 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25082step0 raw25082; decide +kernel
      have hl : raw25082step0Labels = raw25082Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25082 raw25082Labels permutation520 hz
    mixedMoment B raw25082step0 raw25082step0Labels = mixedMoment B raw25082step1 raw25082step1Labels := by
      have ha : raw25082step1 = (fun i j => raw25082step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25082step1 raw25082step0; decide +kernel
      have hl : raw25082step1Labels = raw25082step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25082step0 raw25082step0Labels permutation32 permutation3
    _ = mixedMoment B node1044 node1044Labels := by rfl

def raw25083 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25083Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 4, 1], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25083step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25083step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 1, 4], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25083step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25083 raw25083Labels = mixedMoment B node543 node543Labels := by
  calc
    mixedMoment B raw25083 raw25083Labels = mixedMoment B raw25083step0 raw25083step0Labels := by
      have hz : ∀ j, raw25083 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25083step0 = (fun i j => raw25083 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25083step0 raw25083; decide +kernel
      have hl : raw25083step0Labels = raw25083Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25083 raw25083Labels permutation346 hz
    mixedMoment B raw25083step0 raw25083step0Labels = mixedMoment B raw25083step1 raw25083step1Labels := by
      have ha : raw25083step1 = (fun i j => raw25083step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25083step1 raw25083step0; decide +kernel
      have hl : raw25083step1Labels = raw25083step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25083step0 raw25083step0Labels permutation35 permutation3
    _ = mixedMoment B node543 node543Labels := by rfl

def raw25084 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25084Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25084step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25084step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25084step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25084 raw25084Labels = mixedMoment B node932 node932Labels := by
  calc
    mixedMoment B raw25084 raw25084Labels = mixedMoment B raw25084step0 raw25084step0Labels := by
      have hz : ∀ j, raw25084 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25084step0 = (fun i j => raw25084 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25084step0 raw25084; decide +kernel
      have hl : raw25084step0Labels = raw25084Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25084 raw25084Labels permutation346 hz
    mixedMoment B raw25084step0 raw25084step0Labels = mixedMoment B raw25084step1 raw25084step1Labels := by
      have ha : raw25084step1 = (fun i j => raw25084step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25084step1 raw25084step0; decide +kernel
      have hl : raw25084step1Labels = raw25084step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25084step0 raw25084step0Labels permutation35 permutation3
    _ = mixedMoment B node932 node932Labels := by rfl

def raw25085 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw25085Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25085step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25085step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25085 raw25085Labels = mixedMoment B node869 node869Labels := by
  calc
    mixedMoment B raw25085 raw25085Labels = mixedMoment B raw25085step0 raw25085step0Labels := by
      have ha : raw25085step0 = (fun i j => raw25085 (permutation179 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25085step0 raw25085; decide +kernel
      have hl : raw25085step0Labels = raw25085Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25085 raw25085Labels permutation179 permutation3
    _ = mixedMoment B node869 node869Labels := by rfl

def raw25086 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw25086Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25086step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw25086step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25086step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw25086step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw25086step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw25086step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical25086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25086 raw25086Labels = mixedMoment B node1049 node1049Labels := by
  calc
    mixedMoment B raw25086 raw25086Labels = mixedMoment B raw25086step0 raw25086step0Labels := by
      have hz : ∀ j, raw25086 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw25086step0 = (fun i j => raw25086 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw25086step0 raw25086; decide +kernel
      have hl : raw25086step0Labels = raw25086Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25086 raw25086Labels permutation520 hz
    mixedMoment B raw25086step0 raw25086step0Labels = mixedMoment B raw25086step1 raw25086step1Labels := by
      have hz : ∀ j, raw25086step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw25086step1 = (fun i j => raw25086step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw25086step1 raw25086step0; decide +kernel
      have hl : raw25086step1Labels = raw25086step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25086step0 raw25086step0Labels permutation80 hz
    mixedMoment B raw25086step1 raw25086step1Labels = mixedMoment B raw25086step2 raw25086step2Labels := by
      have ha : raw25086step2 = (fun i j => raw25086step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw25086step2 raw25086step1; decide +kernel
      have hl : raw25086step2Labels = raw25086step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25086step1 raw25086step1Labels permutation9 permutation3
    _ = mixedMoment B node1049 node1049Labels := by rfl

def raw25087 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25087Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25087step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw25087step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw25087step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25087step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw25087step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw25087step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical25087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw25087 raw25087Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw25087 raw25087Labels = mixedMoment B raw25087step0 raw25087step0Labels := by
      have hz : ∀ j, raw25087 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw25087step0 = (fun i j => raw25087 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw25087step0 raw25087; decide +kernel
      have hl : raw25087step0Labels = raw25087Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw25087 raw25087Labels permutation346 hz
    mixedMoment B raw25087step0 raw25087step0Labels = mixedMoment B raw25087step1 raw25087step1Labels := by
      have ha : raw25087step1 = (fun i j => raw25087step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw25087step1 raw25087step0; decide +kernel
      have hl : raw25087step1Labels = raw25087step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw25087step0 raw25087step0Labels permutation32 permutation7
    mixedMoment B raw25087step1 raw25087step1Labels = mixedMoment B raw25087step2 raw25087step2Labels := by
      have ha : raw25087step2 = raw25087step1 := by apply Matrix.ext; unfold raw25087step2 raw25087step1; decide +kernel
      have hl : raw25087step1Labels = labelEmbedding10 ∘ raw25087step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw25087step1 raw25087step1Labels raw25087step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4602 node4602Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
