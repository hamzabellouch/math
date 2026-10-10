import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw32256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw32256Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32256step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32256step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32256 raw32256Labels = mixedMoment B node2353 node2353Labels := by
  calc
    mixedMoment B raw32256 raw32256Labels = mixedMoment B raw32256step0 raw32256step0Labels := by
      have ha : raw32256step0 = (fun i j => raw32256 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32256step0 raw32256; decide +kernel
      have hl : raw32256step0Labels = raw32256Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32256 raw32256Labels permutation160 permutation2
    _ = mixedMoment B node2353 node2353Labels := by rfl

def raw32257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw32257Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32257step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32257step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32257 raw32257Labels = mixedMoment B node2553 node2553Labels := by
  calc
    mixedMoment B raw32257 raw32257Labels = mixedMoment B raw32257step0 raw32257step0Labels := by
      have ha : raw32257step0 = (fun i j => raw32257 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32257step0 raw32257; decide +kernel
      have hl : raw32257step0Labels = raw32257Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32257 raw32257Labels permutation160 permutation2
    _ = mixedMoment B node2553 node2553Labels := by rfl

def raw32258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw32258Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32258step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32258step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32258step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32258 raw32258Labels = mixedMoment B node2590 node2590Labels := by
  calc
    mixedMoment B raw32258 raw32258Labels = mixedMoment B raw32258step0 raw32258step0Labels := by
      have hz : ∀ j, raw32258 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32258step0 = (fun i j => raw32258 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32258step0 raw32258; decide +kernel
      have hl : raw32258step0Labels = raw32258Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32258 raw32258Labels permutation520 hz
    mixedMoment B raw32258step0 raw32258step0Labels = mixedMoment B raw32258step1 raw32258step1Labels := by
      have ha : raw32258step1 = (fun i j => raw32258step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32258step1 raw32258step0; decide +kernel
      have hl : raw32258step1Labels = raw32258step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32258step0 raw32258step0Labels permutation34 permutation2
    _ = mixedMoment B node2590 node2590Labels := by rfl

def raw32259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw32259Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32259step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32259step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32259 raw32259Labels = mixedMoment B node3964 node3964Labels := by
  calc
    mixedMoment B raw32259 raw32259Labels = mixedMoment B raw32259step0 raw32259step0Labels := by
      have ha : raw32259step0 = (fun i j => raw32259 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32259step0 raw32259; decide +kernel
      have hl : raw32259step0Labels = raw32259Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32259 raw32259Labels permutation154 permutation2
    _ = mixedMoment B node3964 node3964Labels := by rfl

def raw32260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -2, 0]]
def raw32260Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32260step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32260step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32260 raw32260Labels = mixedMoment B node2928 node2928Labels := by
  calc
    mixedMoment B raw32260 raw32260Labels = mixedMoment B raw32260step0 raw32260step0Labels := by
      have ha : raw32260step0 = (fun i j => raw32260 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32260step0 raw32260; decide +kernel
      have hl : raw32260step0Labels = raw32260Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32260 raw32260Labels permutation178 permutation2
    _ = mixedMoment B node2928 node2928Labels := by rfl

def raw32261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, 0, -2], ![1, 0, -1], ![2, -2, 0]]
def raw32261Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32261step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw32261step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32261 raw32261Labels = mixedMoment B node2896 node2896Labels := by
  calc
    mixedMoment B raw32261 raw32261Labels = mixedMoment B raw32261step0 raw32261step0Labels := by
      have ha : raw32261step0 = (fun i j => raw32261 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32261step0 raw32261; decide +kernel
      have hl : raw32261step0Labels = raw32261Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32261 raw32261Labels permutation155 permutation2
    _ = mixedMoment B node2896 node2896Labels := by rfl

def raw32262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -2, 0]]
def raw32262Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32262step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw32262step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32262 raw32262Labels = mixedMoment B node2898 node2898Labels := by
  calc
    mixedMoment B raw32262 raw32262Labels = mixedMoment B raw32262step0 raw32262step0Labels := by
      have ha : raw32262step0 = (fun i j => raw32262 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32262step0 raw32262; decide +kernel
      have hl : raw32262step0Labels = raw32262Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32262 raw32262Labels permutation153 permutation2
    _ = mixedMoment B node2898 node2898Labels := by rfl

def raw32263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![3, -3, 0]]
def raw32263Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32263step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw32263step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32263 raw32263Labels = mixedMoment B node2895 node2895Labels := by
  calc
    mixedMoment B raw32263 raw32263Labels = mixedMoment B raw32263step0 raw32263step0Labels := by
      have ha : raw32263step0 = (fun i j => raw32263 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32263step0 raw32263; decide +kernel
      have hl : raw32263step0Labels = raw32263Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32263 raw32263Labels permutation154 permutation2
    _ = mixedMoment B node2895 node2895Labels := by rfl

def raw32264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw32264Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32264step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32264step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32264 raw32264Labels = mixedMoment B node1158 node1158Labels := by
  calc
    mixedMoment B raw32264 raw32264Labels = mixedMoment B raw32264step0 raw32264step0Labels := by
      have ha : raw32264step0 = (fun i j => raw32264 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32264step0 raw32264; decide +kernel
      have hl : raw32264step0Labels = raw32264Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32264 raw32264Labels permutation158 permutation2
    _ = mixedMoment B node1158 node1158Labels := by rfl

def raw32265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw32265Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32265step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32265step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32265 raw32265Labels = mixedMoment B node2354 node2354Labels := by
  calc
    mixedMoment B raw32265 raw32265Labels = mixedMoment B raw32265step0 raw32265step0Labels := by
      have ha : raw32265step0 = (fun i j => raw32265 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32265step0 raw32265; decide +kernel
      have hl : raw32265step0Labels = raw32265Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32265 raw32265Labels permutation158 permutation2
    _ = mixedMoment B node2354 node2354Labels := by rfl

def raw32266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw32266Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32266 raw32266Labels = mixedMoment B node2567 node2567Labels := by
  calc
    _ = mixedMoment B node2567 node2567Labels := by rfl

def raw32267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw32267Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32267step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32267step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32267 raw32267Labels = mixedMoment B node2556 node2556Labels := by
  calc
    mixedMoment B raw32267 raw32267Labels = mixedMoment B raw32267step0 raw32267step0Labels := by
      have ha : raw32267step0 = (fun i j => raw32267 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32267step0 raw32267; decide +kernel
      have hl : raw32267step0Labels = raw32267Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32267 raw32267Labels permutation158 permutation2
    _ = mixedMoment B node2556 node2556Labels := by rfl

def raw32268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw32268Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32268step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw32268step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32268 raw32268Labels = mixedMoment B node2567 node2567Labels := by
  calc
    mixedMoment B raw32268 raw32268Labels = mixedMoment B raw32268step0 raw32268step0Labels := by
      have ha : raw32268step0 = (fun i j => raw32268 (permutation166 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32268step0 raw32268; decide +kernel
      have hl : raw32268step0Labels = raw32268Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32268 raw32268Labels permutation166 permutation2
    _ = mixedMoment B node2567 node2567Labels := by rfl

def raw32269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw32269Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32269step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32269step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32269 raw32269Labels = mixedMoment B node2589 node2589Labels := by
  calc
    mixedMoment B raw32269 raw32269Labels = mixedMoment B raw32269step0 raw32269step0Labels := by
      have ha : raw32269step0 = (fun i j => raw32269 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32269step0 raw32269; decide +kernel
      have hl : raw32269step0Labels = raw32269Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32269 raw32269Labels permutation158 permutation2
    _ = mixedMoment B node2589 node2589Labels := by rfl

def raw32270 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![-1, 1], ![1, -1], ![1, -1]]
def raw32270Labels : Fin 2 → Fin 2 := ![0, 1]

def raw32270step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![1, -1], ![1, -1]]
def raw32270step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw32270step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw32270step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical32270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32270 raw32270Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw32270 raw32270Labels = mixedMoment B raw32270step0 raw32270step0Labels := by
      have hz : ∀ j, raw32270 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw32270step0 = (fun i j => raw32270 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw32270step0 raw32270; decide +kernel
      have hl : raw32270step0Labels = raw32270Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32270 raw32270Labels permutation265 hz
    mixedMoment B raw32270step0 raw32270step0Labels = mixedMoment B raw32270step1 raw32270step1Labels := by
      have ha : raw32270step1 = (fun i j => raw32270step0 (permutation38 i) (permutation0 j)) := by apply Matrix.ext; unfold raw32270step1 raw32270step0; decide +kernel
      have hl : raw32270step1Labels = raw32270step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32270step0 raw32270step0Labels permutation38 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw32271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![2, -1, -1]]
def raw32271Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32271step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw32271step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32271 raw32271Labels = mixedMoment B node2925 node2925Labels := by
  calc
    mixedMoment B raw32271 raw32271Labels = mixedMoment B raw32271step0 raw32271step0Labels := by
      have ha : raw32271step0 = (fun i j => raw32271 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32271step0 raw32271; decide +kernel
      have hl : raw32271step0Labels = raw32271Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32271 raw32271Labels permutation178 permutation2
    _ = mixedMoment B node2925 node2925Labels := by rfl

def raw32272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![2, 0, -2], ![1, -1, 0], ![2, -1, -1]]
def raw32272Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32272step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw32272step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32272 raw32272Labels = mixedMoment B node2893 node2893Labels := by
  calc
    mixedMoment B raw32272 raw32272Labels = mixedMoment B raw32272step0 raw32272step0Labels := by
      have ha : raw32272step0 = (fun i j => raw32272 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32272step0 raw32272; decide +kernel
      have hl : raw32272step0Labels = raw32272Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32272 raw32272Labels permutation155 permutation2
    _ = mixedMoment B node2893 node2893Labels := by rfl

def raw32273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw32273Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32273 raw32273Labels = mixedMoment B node2898 node2898Labels := by
  calc
    _ = mixedMoment B node2898 node2898Labels := by rfl

def raw32274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![3, -2, -1]]
def raw32274Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32274step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw32274step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32274step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32274step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32274 raw32274Labels = mixedMoment B node2847 node2847Labels := by
  calc
    mixedMoment B raw32274 raw32274Labels = mixedMoment B raw32274step0 raw32274step0Labels := by
      have ha : raw32274step0 = (fun i j => raw32274 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32274step0 raw32274; decide +kernel
      have hl : raw32274step0Labels = raw32274Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32274 raw32274Labels permutation662 permutation2
    mixedMoment B raw32274step0 raw32274step0Labels = mixedMoment B raw32274step1 raw32274step1Labels := by
      have ha : raw32274step1 = -raw32274step0 := by apply Matrix.ext; change ∀ i j, raw32274step1 i j = -(raw32274step0 i j); unfold raw32274step1 raw32274step0; decide +kernel
      have hl : raw32274step1Labels = raw32274step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2847 node2847Labels := by rfl

def raw32275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1], ![2, 0, -2]]
def raw32275Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32275step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw32275step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32275 raw32275Labels = mixedMoment B node2922 node2922Labels := by
  calc
    mixedMoment B raw32275 raw32275Labels = mixedMoment B raw32275step0 raw32275step0Labels := by
      have ha : raw32275step0 = (fun i j => raw32275 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32275step0 raw32275; decide +kernel
      have hl : raw32275step0Labels = raw32275Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32275 raw32275Labels permutation154 permutation2
    _ = mixedMoment B node2922 node2922Labels := by rfl

def raw32276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1], ![2, 0, -2]]
def raw32276Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32276step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![1, -2, 1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw32276step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32276step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32276step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32276 raw32276Labels = mixedMoment B node3748 node3748Labels := by
  calc
    mixedMoment B raw32276 raw32276Labels = mixedMoment B raw32276step0 raw32276step0Labels := by
      have ha : raw32276step0 = (fun i j => raw32276 (permutation663 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32276step0 raw32276; decide +kernel
      have hl : raw32276step0Labels = raw32276Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32276 raw32276Labels permutation663 permutation2
    mixedMoment B raw32276step0 raw32276step0Labels = mixedMoment B raw32276step1 raw32276step1Labels := by
      have ha : raw32276step1 = -raw32276step0 := by apply Matrix.ext; change ∀ i j, raw32276step1 i j = -(raw32276step0 i j); unfold raw32276step1 raw32276step0; decide +kernel
      have hl : raw32276step1Labels = raw32276step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3748 node3748Labels := by rfl

def raw32277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![1, -2, 1], ![2, 0, -2]]
def raw32277Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32277step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw32277step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32277step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32277step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32277 raw32277Labels = mixedMoment B node3751 node3751Labels := by
  calc
    mixedMoment B raw32277 raw32277Labels = mixedMoment B raw32277step0 raw32277step0Labels := by
      have ha : raw32277step0 = (fun i j => raw32277 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32277step0 raw32277; decide +kernel
      have hl : raw32277step0Labels = raw32277Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32277 raw32277Labels permutation662 permutation2
    mixedMoment B raw32277step0 raw32277step0Labels = mixedMoment B raw32277step1 raw32277step1Labels := by
      have ha : raw32277step1 = -raw32277step0 := by apply Matrix.ext; change ∀ i j, raw32277step1 i j = -(raw32277step0 i j); unfold raw32277step1 raw32277step0; decide +kernel
      have hl : raw32277step1Labels = raw32277step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3751 node3751Labels := by rfl

def raw32278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw32278Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32278step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw32278step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32278step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32278step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32278 raw32278Labels = mixedMoment B node3866 node3866Labels := by
  calc
    mixedMoment B raw32278 raw32278Labels = mixedMoment B raw32278step0 raw32278step0Labels := by
      have ha : raw32278step0 = (fun i j => raw32278 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32278step0 raw32278; decide +kernel
      have hl : raw32278step0Labels = raw32278Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32278 raw32278Labels permutation688 permutation2
    mixedMoment B raw32278step0 raw32278step0Labels = mixedMoment B raw32278step1 raw32278step1Labels := by
      have ha : raw32278step1 = -raw32278step0 := by apply Matrix.ext; change ∀ i j, raw32278step1 i j = -(raw32278step0 i j); unfold raw32278step1 raw32278step0; decide +kernel
      have hl : raw32278step1Labels = raw32278step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3866 node3866Labels := by rfl

def raw32279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![0, -1, 1], ![2, 0, -2]]
def raw32279Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32279step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw32279step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32279step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32279step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32279 raw32279Labels = mixedMoment B node3758 node3758Labels := by
  calc
    mixedMoment B raw32279 raw32279Labels = mixedMoment B raw32279step0 raw32279step0Labels := by
      have ha : raw32279step0 = (fun i j => raw32279 (permutation658 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32279step0 raw32279; decide +kernel
      have hl : raw32279step0Labels = raw32279Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32279 raw32279Labels permutation658 permutation2
    mixedMoment B raw32279step0 raw32279step0Labels = mixedMoment B raw32279step1 raw32279step1Labels := by
      have ha : raw32279step1 = -raw32279step0 := by apply Matrix.ext; change ∀ i j, raw32279step1 i j = -(raw32279step0 i j); unfold raw32279step1 raw32279step0; decide +kernel
      have hl : raw32279step1Labels = raw32279step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3758 node3758Labels := by rfl

def raw32280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, -2, 1], ![1, 1, -2]]
def raw32280Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32280step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw32280step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32280 raw32280Labels = mixedMoment B node3973 node3973Labels := by
  calc
    mixedMoment B raw32280 raw32280Labels = mixedMoment B raw32280step0 raw32280step0Labels := by
      have ha : raw32280step0 = (fun i j => raw32280 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32280step0 raw32280; decide +kernel
      have hl : raw32280step0Labels = raw32280Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32280 raw32280Labels permutation154 permutation2
    _ = mixedMoment B node3973 node3973Labels := by rfl

def raw32281 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![-1, 1], ![2, -2]]
def raw32281Labels : Fin 2 → Fin 2 := ![0, 1]

def raw32281step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![2, -2], ![2, -2], ![-1, 1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw32281step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw32281step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw32281step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical32281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32281 raw32281Labels = mixedMoment B node4087 node4087Labels := by
  calc
    mixedMoment B raw32281 raw32281Labels = mixedMoment B raw32281step0 raw32281step0Labels := by
      have ha : raw32281step0 = (fun i j => raw32281 (permutation505 i) (permutation0 j)) := by apply Matrix.ext; unfold raw32281step0 raw32281; decide +kernel
      have hl : raw32281step0Labels = raw32281Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32281 raw32281Labels permutation505 permutation0
    mixedMoment B raw32281step0 raw32281step0Labels = mixedMoment B raw32281step1 raw32281step1Labels := by
      have ha : raw32281step1 = -raw32281step0 := by apply Matrix.ext; change ∀ i j, raw32281step1 i j = -(raw32281step0 i j); unfold raw32281step1 raw32281step0; decide +kernel
      have hl : raw32281step1Labels = raw32281step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4087 node4087Labels := by rfl

def raw32282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32282Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32282step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32282step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32282 raw32282Labels = mixedMoment B node4968 node4968Labels := by
  calc
    mixedMoment B raw32282 raw32282Labels = mixedMoment B raw32282step0 raw32282step0Labels := by
      have ha : raw32282step0 = (fun i j => raw32282 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32282step0 raw32282; decide +kernel
      have hl : raw32282step0Labels = raw32282Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32282 raw32282Labels permutation160 permutation2
    _ = mixedMoment B node4968 node4968Labels := by rfl

def raw32283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32283Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32283step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32283step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32283step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32283 raw32283Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw32283 raw32283Labels = mixedMoment B raw32283step0 raw32283step0Labels := by
      have hz : ∀ j, raw32283 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw32283step0 = (fun i j => raw32283 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw32283step0 raw32283; decide +kernel
      have hl : raw32283step0Labels = raw32283Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32283 raw32283Labels permutation434 hz
    mixedMoment B raw32283step0 raw32283step0Labels = mixedMoment B raw32283step1 raw32283step1Labels := by
      have ha : raw32283step1 = (fun i j => raw32283step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32283step1 raw32283step0; decide +kernel
      have hl : raw32283step1Labels = raw32283step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32283step0 raw32283step0Labels permutation34 permutation2
    _ = mixedMoment B node5169 node5169Labels := by rfl

def raw32284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw32284Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32284step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32284step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32284step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32284step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32284 raw32284Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw32284 raw32284Labels = mixedMoment B raw32284step0 raw32284step0Labels := by
      have hz : ∀ j, raw32284 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32284step0 = (fun i j => raw32284 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32284step0 raw32284; decide +kernel
      have hl : raw32284step0Labels = raw32284Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32284 raw32284Labels permutation520 hz
    mixedMoment B raw32284step0 raw32284step0Labels = mixedMoment B raw32284step1 raw32284step1Labels := by
      have ha : raw32284step1 = (fun i j => raw32284step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32284step1 raw32284step0; decide +kernel
      have hl : raw32284step1Labels = raw32284step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32284step0 raw32284step0Labels permutation34 permutation2
    _ = mixedMoment B node5169 node5169Labels := by rfl

def raw32285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32285Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32285step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw32285step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32285 raw32285Labels = mixedMoment B node4961 node4961Labels := by
  calc
    mixedMoment B raw32285 raw32285Labels = mixedMoment B raw32285step0 raw32285step0Labels := by
      have ha : raw32285step0 = (fun i j => raw32285 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32285step0 raw32285; decide +kernel
      have hl : raw32285step0Labels = raw32285Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32285 raw32285Labels permutation154 permutation2
    _ = mixedMoment B node4961 node4961Labels := by rfl

def raw32286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32286Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32286step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw32286step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32286 raw32286Labels = mixedMoment B node5119 node5119Labels := by
  calc
    mixedMoment B raw32286 raw32286Labels = mixedMoment B raw32286step0 raw32286step0Labels := by
      have ha : raw32286step0 = (fun i j => raw32286 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32286step0 raw32286; decide +kernel
      have hl : raw32286step0Labels = raw32286Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32286 raw32286Labels permutation154 permutation2
    _ = mixedMoment B node5119 node5119Labels := by rfl

def raw32287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![2, -1, -1]]
def raw32287Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32287step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32287 raw32287Labels = mixedMoment B node5152 node5152Labels := by
  calc
    mixedMoment B raw32287 raw32287Labels = mixedMoment B raw32287step0 raw32287step0Labels := by
      have hz : ∀ j, raw32287 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32287step0 = (fun i j => raw32287 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32287step0 raw32287; decide +kernel
      have hl : raw32287step0Labels = raw32287Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32287 raw32287Labels permutation520 hz
    _ = mixedMoment B node5152 node5152Labels := by rfl

def raw32288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw32288Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32288 raw32288Labels = mixedMoment B node4961 node4961Labels := by
  calc
    _ = mixedMoment B node4961 node4961Labels := by rfl

def raw32289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw32289Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32289 raw32289Labels = mixedMoment B node5119 node5119Labels := by
  calc
    _ = mixedMoment B node5119 node5119Labels := by rfl

def raw32290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw32290Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32290step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32290step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32290 raw32290Labels = mixedMoment B node5152 node5152Labels := by
  calc
    mixedMoment B raw32290 raw32290Labels = mixedMoment B raw32290step0 raw32290step0Labels := by
      have hz : ∀ j, raw32290 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw32290step0 = (fun i j => raw32290 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw32290step0 raw32290; decide +kernel
      have hl : raw32290step0Labels = raw32290Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32290 raw32290Labels permutation434 hz
    _ = mixedMoment B node5152 node5152Labels := by rfl

def raw32291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw32291Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32291 raw32291Labels = mixedMoment B node4960 node4960Labels := by
  calc
    _ = mixedMoment B node4960 node4960Labels := by rfl

def raw32292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw32292Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32292step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw32292step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32292step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw32292step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32292step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw32292step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32292 raw32292Labels = mixedMoment B node5027 node5027Labels := by
  calc
    mixedMoment B raw32292 raw32292Labels = mixedMoment B raw32292step0 raw32292step0Labels := by
      have ha : raw32292step0 = (fun i j => raw32292 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32292step0 raw32292; decide +kernel
      have hl : raw32292step0Labels = raw32292Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32292 raw32292Labels permutation662 permutation3
    mixedMoment B raw32292step0 raw32292step0Labels = mixedMoment B raw32292step1 raw32292step1Labels := by
      have ha : raw32292step1 = -raw32292step0 := by apply Matrix.ext; change ∀ i j, raw32292step1 i j = -(raw32292step0 i j); unfold raw32292step1 raw32292step0; decide +kernel
      have hl : raw32292step1Labels = raw32292step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32292step1 raw32292step1Labels = mixedMoment B raw32292step2 raw32292step2Labels := by
      have ha : raw32292step2 = raw32292step1 := by apply Matrix.ext; unfold raw32292step2 raw32292step1; decide +kernel
      have hl : raw32292step1Labels = labelEmbedding6 ∘ raw32292step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32292step1 raw32292step1Labels raw32292step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5027 node5027Labels := by rfl

def raw32293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw32293Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw32293step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32293step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw32293step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32293step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32293step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32293step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32293step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32293 raw32293Labels = mixedMoment B node5078 node5078Labels := by
  calc
    mixedMoment B raw32293 raw32293Labels = mixedMoment B raw32293step0 raw32293step0Labels := by
      have hz : ∀ j, raw32293 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw32293step0 = (fun i j => raw32293 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw32293step0 raw32293; decide +kernel
      have hl : raw32293step0Labels = raw32293Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32293 raw32293Labels permutation434 hz
    mixedMoment B raw32293step0 raw32293step0Labels = mixedMoment B raw32293step1 raw32293step1Labels := by
      have ha : raw32293step1 = (fun i j => raw32293step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32293step1 raw32293step0; decide +kernel
      have hl : raw32293step1Labels = raw32293step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32293step0 raw32293step0Labels permutation151 permutation3
    mixedMoment B raw32293step1 raw32293step1Labels = mixedMoment B raw32293step2 raw32293step2Labels := by
      have ha : raw32293step2 = -raw32293step1 := by apply Matrix.ext; change ∀ i j, raw32293step2 i j = -(raw32293step1 i j); unfold raw32293step2 raw32293step1; decide +kernel
      have hl : raw32293step2Labels = raw32293step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32293step2 raw32293step2Labels = mixedMoment B raw32293step3 raw32293step3Labels := by
      have ha : raw32293step3 = raw32293step2 := by apply Matrix.ext; unfold raw32293step3 raw32293step2; decide +kernel
      have hl : raw32293step2Labels = labelEmbedding6 ∘ raw32293step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32293step2 raw32293step2Labels raw32293step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5078 node5078Labels := by rfl

def raw32294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![3, -2, -1]]
def raw32294Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw32294step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32294step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw32294step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32294step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32294step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32294step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32294step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32294 raw32294Labels = mixedMoment B node5078 node5078Labels := by
  calc
    mixedMoment B raw32294 raw32294Labels = mixedMoment B raw32294step0 raw32294step0Labels := by
      have hz : ∀ j, raw32294 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32294step0 = (fun i j => raw32294 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32294step0 raw32294; decide +kernel
      have hl : raw32294step0Labels = raw32294Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32294 raw32294Labels permutation520 hz
    mixedMoment B raw32294step0 raw32294step0Labels = mixedMoment B raw32294step1 raw32294step1Labels := by
      have ha : raw32294step1 = (fun i j => raw32294step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32294step1 raw32294step0; decide +kernel
      have hl : raw32294step1Labels = raw32294step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32294step0 raw32294step0Labels permutation151 permutation3
    mixedMoment B raw32294step1 raw32294step1Labels = mixedMoment B raw32294step2 raw32294step2Labels := by
      have ha : raw32294step2 = -raw32294step1 := by apply Matrix.ext; change ∀ i j, raw32294step2 i j = -(raw32294step1 i j); unfold raw32294step2 raw32294step1; decide +kernel
      have hl : raw32294step2Labels = raw32294step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32294step2 raw32294step2Labels = mixedMoment B raw32294step3 raw32294step3Labels := by
      have ha : raw32294step3 = raw32294step2 := by apply Matrix.ext; unfold raw32294step3 raw32294step2; decide +kernel
      have hl : raw32294step2Labels = labelEmbedding6 ∘ raw32294step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32294step2 raw32294step2Labels raw32294step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5078 node5078Labels := by rfl

def raw32295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32295Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32295step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32295step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32295 raw32295Labels = mixedMoment B node3721 node3721Labels := by
  calc
    mixedMoment B raw32295 raw32295Labels = mixedMoment B raw32295step0 raw32295step0Labels := by
      have ha : raw32295step0 = (fun i j => raw32295 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32295step0 raw32295; decide +kernel
      have hl : raw32295step0Labels = raw32295Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32295 raw32295Labels permutation265 permutation3
    _ = mixedMoment B node3721 node3721Labels := by rfl

def raw32296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32296Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32296step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw32296step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32296step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32296step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32296 raw32296Labels = mixedMoment B node3964 node3964Labels := by
  calc
    mixedMoment B raw32296 raw32296Labels = mixedMoment B raw32296step0 raw32296step0Labels := by
      have ha : raw32296step0 = (fun i j => raw32296 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32296step0 raw32296; decide +kernel
      have hl : raw32296step0Labels = raw32296Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32296 raw32296Labels permutation662 permutation3
    mixedMoment B raw32296step0 raw32296step0Labels = mixedMoment B raw32296step1 raw32296step1Labels := by
      have ha : raw32296step1 = -raw32296step0 := by apply Matrix.ext; change ∀ i j, raw32296step1 i j = -(raw32296step0 i j); unfold raw32296step1 raw32296step0; decide +kernel
      have hl : raw32296step1Labels = raw32296step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3964 node3964Labels := by rfl

def raw32297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32297Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32297step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32297step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw32297step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32297step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32297step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32297 raw32297Labels = mixedMoment B node3982 node3982Labels := by
  calc
    mixedMoment B raw32297 raw32297Labels = mixedMoment B raw32297step0 raw32297step0Labels := by
      have hz : ∀ j, raw32297 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw32297step0 = (fun i j => raw32297 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw32297step0 raw32297; decide +kernel
      have hl : raw32297step0Labels = raw32297Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32297 raw32297Labels permutation434 hz
    mixedMoment B raw32297step0 raw32297step0Labels = mixedMoment B raw32297step1 raw32297step1Labels := by
      have ha : raw32297step1 = (fun i j => raw32297step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32297step1 raw32297step0; decide +kernel
      have hl : raw32297step1Labels = raw32297step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32297step0 raw32297step0Labels permutation151 permutation3
    mixedMoment B raw32297step1 raw32297step1Labels = mixedMoment B raw32297step2 raw32297step2Labels := by
      have ha : raw32297step2 = -raw32297step1 := by apply Matrix.ext; change ∀ i j, raw32297step2 i j = -(raw32297step1 i j); unfold raw32297step2 raw32297step1; decide +kernel
      have hl : raw32297step2Labels = raw32297step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3982 node3982Labels := by rfl

def raw32298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw32298Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32298step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32298step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw32298step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32298step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32298step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32298 raw32298Labels = mixedMoment B node3982 node3982Labels := by
  calc
    mixedMoment B raw32298 raw32298Labels = mixedMoment B raw32298step0 raw32298step0Labels := by
      have hz : ∀ j, raw32298 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32298step0 = (fun i j => raw32298 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32298step0 raw32298; decide +kernel
      have hl : raw32298step0Labels = raw32298Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32298 raw32298Labels permutation520 hz
    mixedMoment B raw32298step0 raw32298step0Labels = mixedMoment B raw32298step1 raw32298step1Labels := by
      have ha : raw32298step1 = (fun i j => raw32298step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32298step1 raw32298step0; decide +kernel
      have hl : raw32298step1Labels = raw32298step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32298step0 raw32298step0Labels permutation151 permutation3
    mixedMoment B raw32298step1 raw32298step1Labels = mixedMoment B raw32298step2 raw32298step2Labels := by
      have ha : raw32298step2 = -raw32298step1 := by apply Matrix.ext; change ∀ i j, raw32298step2 i j = -(raw32298step1 i j); unfold raw32298step2 raw32298step1; decide +kernel
      have hl : raw32298step2Labels = raw32298step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3982 node3982Labels := by rfl

def raw32299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32299Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32299step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32299step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32299 raw32299Labels = mixedMoment B node2809 node2809Labels := by
  calc
    mixedMoment B raw32299 raw32299Labels = mixedMoment B raw32299step0 raw32299step0Labels := by
      have ha : raw32299step0 = (fun i j => raw32299 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32299step0 raw32299; decide +kernel
      have hl : raw32299step0Labels = raw32299Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32299 raw32299Labels permutation152 permutation3
    _ = mixedMoment B node2809 node2809Labels := by rfl

def raw32300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32300Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32300step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32300step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32300step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32300 raw32300Labels = mixedMoment B node2960 node2960Labels := by
  calc
    mixedMoment B raw32300 raw32300Labels = mixedMoment B raw32300step0 raw32300step0Labels := by
      have hz : ∀ j, raw32300 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw32300step0 = (fun i j => raw32300 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw32300step0 raw32300; decide +kernel
      have hl : raw32300step0Labels = raw32300Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32300 raw32300Labels permutation434 hz
    mixedMoment B raw32300step0 raw32300step0Labels = mixedMoment B raw32300step1 raw32300step1Labels := by
      have ha : raw32300step1 = (fun i j => raw32300step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32300step1 raw32300step0; decide +kernel
      have hl : raw32300step1Labels = raw32300step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32300step0 raw32300step0Labels permutation32 permutation3
    _ = mixedMoment B node2960 node2960Labels := by rfl

def raw32301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw32301Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32301step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32301step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32301step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32301 raw32301Labels = mixedMoment B node2960 node2960Labels := by
  calc
    mixedMoment B raw32301 raw32301Labels = mixedMoment B raw32301step0 raw32301step0Labels := by
      have hz : ∀ j, raw32301 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32301step0 = (fun i j => raw32301 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32301step0 raw32301; decide +kernel
      have hl : raw32301step0Labels = raw32301Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32301 raw32301Labels permutation520 hz
    mixedMoment B raw32301step0 raw32301step0Labels = mixedMoment B raw32301step1 raw32301step1Labels := by
      have ha : raw32301step1 = (fun i j => raw32301step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32301step1 raw32301step0; decide +kernel
      have hl : raw32301step1Labels = raw32301step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32301step0 raw32301step0Labels permutation32 permutation3
    _ = mixedMoment B node2960 node2960Labels := by rfl

def raw32302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32302Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32302step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32302step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32302 raw32302Labels = mixedMoment B node2796 node2796Labels := by
  calc
    mixedMoment B raw32302 raw32302Labels = mixedMoment B raw32302step0 raw32302step0Labels := by
      have ha : raw32302step0 = (fun i j => raw32302 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32302step0 raw32302; decide +kernel
      have hl : raw32302step0Labels = raw32302Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32302 raw32302Labels permutation155 permutation3
    _ = mixedMoment B node2796 node2796Labels := by rfl

def raw32303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32303Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32303step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32303step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32303 raw32303Labels = mixedMoment B node2845 node2845Labels := by
  calc
    mixedMoment B raw32303 raw32303Labels = mixedMoment B raw32303step0 raw32303step0Labels := by
      have ha : raw32303step0 = (fun i j => raw32303 (permutation179 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32303step0 raw32303; decide +kernel
      have hl : raw32303step0Labels = raw32303Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32303 raw32303Labels permutation179 permutation3
    _ = mixedMoment B node2845 node2845Labels := by rfl

def raw32304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![2, -1, -1]]
def raw32304Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32304step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32304step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw32304step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32304 raw32304Labels = mixedMoment B node2931 node2931Labels := by
  calc
    mixedMoment B raw32304 raw32304Labels = mixedMoment B raw32304step0 raw32304step0Labels := by
      have hz : ∀ j, raw32304 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32304step0 = (fun i j => raw32304 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32304step0 raw32304; decide +kernel
      have hl : raw32304step0Labels = raw32304Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32304 raw32304Labels permutation520 hz
    mixedMoment B raw32304step0 raw32304step0Labels = mixedMoment B raw32304step1 raw32304step1Labels := by
      have ha : raw32304step1 = (fun i j => raw32304step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32304step1 raw32304step0; decide +kernel
      have hl : raw32304step1Labels = raw32304step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32304step0 raw32304step0Labels permutation33 permutation3
    _ = mixedMoment B node2931 node2931Labels := by rfl

def raw32305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw32305Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32305step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32305step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32305 raw32305Labels = mixedMoment B node2796 node2796Labels := by
  calc
    mixedMoment B raw32305 raw32305Labels = mixedMoment B raw32305step0 raw32305step0Labels := by
      have ha : raw32305step0 = (fun i j => raw32305 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32305step0 raw32305; decide +kernel
      have hl : raw32305step0Labels = raw32305Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32305 raw32305Labels permutation153 permutation3
    _ = mixedMoment B node2796 node2796Labels := by rfl

def raw32306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw32306Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32306step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32306step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32306 raw32306Labels = mixedMoment B node2845 node2845Labels := by
  calc
    mixedMoment B raw32306 raw32306Labels = mixedMoment B raw32306step0 raw32306step0Labels := by
      have ha : raw32306step0 = (fun i j => raw32306 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32306step0 raw32306; decide +kernel
      have hl : raw32306step0Labels = raw32306Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32306 raw32306Labels permutation177 permutation3
    _ = mixedMoment B node2845 node2845Labels := by rfl

def raw32307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw32307Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32307step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32307step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw32307step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32307 raw32307Labels = mixedMoment B node2931 node2931Labels := by
  calc
    mixedMoment B raw32307 raw32307Labels = mixedMoment B raw32307step0 raw32307step0Labels := by
      have hz : ∀ j, raw32307 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw32307step0 = (fun i j => raw32307 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw32307step0 raw32307; decide +kernel
      have hl : raw32307step0Labels = raw32307Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32307 raw32307Labels permutation434 hz
    mixedMoment B raw32307step0 raw32307step0Labels = mixedMoment B raw32307step1 raw32307step1Labels := by
      have ha : raw32307step1 = (fun i j => raw32307step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32307step1 raw32307step0; decide +kernel
      have hl : raw32307step1Labels = raw32307step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32307step0 raw32307step0Labels permutation33 permutation3
    _ = mixedMoment B node2931 node2931Labels := by rfl

def raw32308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw32308Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32308step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-2, 0, 2], ![-3, 2, 1]]
def raw32308step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32308step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw32308step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32308 raw32308Labels = mixedMoment B node2412 node2412Labels := by
  calc
    mixedMoment B raw32308 raw32308Labels = mixedMoment B raw32308step0 raw32308step0Labels := by
      have ha : raw32308step0 = (fun i j => raw32308 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32308step0 raw32308; decide +kernel
      have hl : raw32308step0Labels = raw32308Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32308 raw32308Labels permutation664 permutation3
    mixedMoment B raw32308step0 raw32308step0Labels = mixedMoment B raw32308step1 raw32308step1Labels := by
      have ha : raw32308step1 = -raw32308step0 := by apply Matrix.ext; change ∀ i j, raw32308step1 i j = -(raw32308step0 i j); unfold raw32308step1 raw32308step0; decide +kernel
      have hl : raw32308step1Labels = raw32308step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2412 node2412Labels := by rfl

def raw32309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw32309Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32309step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw32309step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32309step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw32309step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32309 raw32309Labels = mixedMoment B node2416 node2416Labels := by
  calc
    mixedMoment B raw32309 raw32309Labels = mixedMoment B raw32309step0 raw32309step0Labels := by
      have ha : raw32309step0 = (fun i j => raw32309 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32309step0 raw32309; decide +kernel
      have hl : raw32309step0Labels = raw32309Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32309 raw32309Labels permutation662 permutation3
    mixedMoment B raw32309step0 raw32309step0Labels = mixedMoment B raw32309step1 raw32309step1Labels := by
      have ha : raw32309step1 = -raw32309step0 := by apply Matrix.ext; change ∀ i j, raw32309step1 i j = -(raw32309step0 i j); unfold raw32309step1 raw32309step0; decide +kernel
      have hl : raw32309step1Labels = raw32309step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2416 node2416Labels := by rfl

def raw32310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, -2, -1]]
def raw32310Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw32310step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32310step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw32310step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32310step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32310step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32310 raw32310Labels = mixedMoment B node2485 node2485Labels := by
  calc
    mixedMoment B raw32310 raw32310Labels = mixedMoment B raw32310step0 raw32310step0Labels := by
      have hz : ∀ j, raw32310 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw32310step0 = (fun i j => raw32310 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw32310step0 raw32310; decide +kernel
      have hl : raw32310step0Labels = raw32310Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32310 raw32310Labels permutation434 hz
    mixedMoment B raw32310step0 raw32310step0Labels = mixedMoment B raw32310step1 raw32310step1Labels := by
      have ha : raw32310step1 = (fun i j => raw32310step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32310step1 raw32310step0; decide +kernel
      have hl : raw32310step1Labels = raw32310step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32310step0 raw32310step0Labels permutation151 permutation3
    mixedMoment B raw32310step1 raw32310step1Labels = mixedMoment B raw32310step2 raw32310step2Labels := by
      have ha : raw32310step2 = -raw32310step1 := by apply Matrix.ext; change ∀ i j, raw32310step2 i j = -(raw32310step1 i j); unfold raw32310step2 raw32310step1; decide +kernel
      have hl : raw32310step2Labels = raw32310step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2485 node2485Labels := by rfl

def raw32311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![3, -2, -1]]
def raw32311Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw32311step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32311step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw32311step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32311step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32311step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32311 raw32311Labels = mixedMoment B node2485 node2485Labels := by
  calc
    mixedMoment B raw32311 raw32311Labels = mixedMoment B raw32311step0 raw32311step0Labels := by
      have hz : ∀ j, raw32311 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32311step0 = (fun i j => raw32311 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32311step0 raw32311; decide +kernel
      have hl : raw32311step0Labels = raw32311Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32311 raw32311Labels permutation520 hz
    mixedMoment B raw32311step0 raw32311step0Labels = mixedMoment B raw32311step1 raw32311step1Labels := by
      have ha : raw32311step1 = (fun i j => raw32311step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32311step1 raw32311step0; decide +kernel
      have hl : raw32311step1Labels = raw32311step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32311step0 raw32311step0Labels permutation151 permutation3
    mixedMoment B raw32311step1 raw32311step1Labels = mixedMoment B raw32311step2 raw32311step2Labels := by
      have ha : raw32311step2 = -raw32311step1 := by apply Matrix.ext; change ∀ i j, raw32311step2 i j = -(raw32311step1 i j); unfold raw32311step2 raw32311step1; decide +kernel
      have hl : raw32311step2Labels = raw32311step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2485 node2485Labels := by rfl

def raw32312 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32312Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32312step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32312step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw32312step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32312step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32312 raw32312Labels = mixedMoment B node5137 node5137Labels := by
  calc
    mixedMoment B raw32312 raw32312Labels = mixedMoment B raw32312step0 raw32312step0Labels := by
      have ha : raw32312step0 = (fun i j => raw32312 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32312step0 raw32312; decide +kernel
      have hl : raw32312step0Labels = raw32312Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32312 raw32312Labels permutation152 permutation7
    mixedMoment B raw32312step0 raw32312step0Labels = mixedMoment B raw32312step1 raw32312step1Labels := by
      have ha : raw32312step1 = raw32312step0 := by apply Matrix.ext; unfold raw32312step1 raw32312step0; decide +kernel
      have hl : raw32312step0Labels = labelEmbedding10 ∘ raw32312step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32312step0 raw32312step0Labels raw32312step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5137 node5137Labels := by rfl

def raw32313 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32313Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32313step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32313step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32313step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw32313step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32313step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32313 raw32313Labels = mixedMoment B node5104 node5104Labels := by
  calc
    mixedMoment B raw32313 raw32313Labels = mixedMoment B raw32313step0 raw32313step0Labels := by
      have hz : ∀ j, raw32313 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32313step0 = (fun i j => raw32313 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32313step0 raw32313; decide +kernel
      have hl : raw32313step0Labels = raw32313Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32313 raw32313Labels permutation346 hz
    mixedMoment B raw32313step0 raw32313step0Labels = mixedMoment B raw32313step1 raw32313step1Labels := by
      have ha : raw32313step1 = (fun i j => raw32313step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32313step1 raw32313step0; decide +kernel
      have hl : raw32313step1Labels = raw32313step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32313step0 raw32313step0Labels permutation32 permutation7
    mixedMoment B raw32313step1 raw32313step1Labels = mixedMoment B raw32313step2 raw32313step2Labels := by
      have ha : raw32313step2 = raw32313step1 := by apply Matrix.ext; unfold raw32313step2 raw32313step1; decide +kernel
      have hl : raw32313step1Labels = labelEmbedding10 ∘ raw32313step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32313step1 raw32313step1Labels raw32313step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5104 node5104Labels := by rfl

def raw32314 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32314Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32314step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw32314step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw32314step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw32314step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32314 raw32314Labels = mixedMoment B node5059 node5059Labels := by
  calc
    mixedMoment B raw32314 raw32314Labels = mixedMoment B raw32314step0 raw32314step0Labels := by
      have ha : raw32314step0 = (fun i j => raw32314 (permutation154 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32314step0 raw32314; decide +kernel
      have hl : raw32314step0Labels = raw32314Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32314 raw32314Labels permutation154 permutation7
    mixedMoment B raw32314step0 raw32314step0Labels = mixedMoment B raw32314step1 raw32314step1Labels := by
      have ha : raw32314step1 = raw32314step0 := by apply Matrix.ext; unfold raw32314step1 raw32314step0; decide +kernel
      have hl : raw32314step0Labels = labelEmbedding10 ∘ raw32314step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32314step0 raw32314step0Labels raw32314step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5059 node5059Labels := by rfl

def raw32315 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw32315Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32315step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw32315step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw32315step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw32315step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32315 raw32315Labels = mixedMoment B node5059 node5059Labels := by
  calc
    mixedMoment B raw32315 raw32315Labels = mixedMoment B raw32315step0 raw32315step0Labels := by
      have ha : raw32315step0 = (fun i j => raw32315 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32315step0 raw32315; decide +kernel
      have hl : raw32315step0Labels = raw32315Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32315 raw32315Labels permutation152 permutation7
    mixedMoment B raw32315step0 raw32315step0Labels = mixedMoment B raw32315step1 raw32315step1Labels := by
      have ha : raw32315step1 = raw32315step0 := by apply Matrix.ext; unfold raw32315step1 raw32315step0; decide +kernel
      have hl : raw32315step0Labels = labelEmbedding10 ∘ raw32315step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32315step0 raw32315step0Labels raw32315step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5059 node5059Labels := by rfl

def raw32316 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw32316Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32316step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32316step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw32316step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32316step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32316 raw32316Labels = mixedMoment B node5058 node5058Labels := by
  calc
    mixedMoment B raw32316 raw32316Labels = mixedMoment B raw32316step0 raw32316step0Labels := by
      have ha : raw32316step0 = (fun i j => raw32316 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32316step0 raw32316; decide +kernel
      have hl : raw32316step0Labels = raw32316Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32316 raw32316Labels permutation152 permutation7
    mixedMoment B raw32316step0 raw32316step0Labels = mixedMoment B raw32316step1 raw32316step1Labels := by
      have ha : raw32316step1 = raw32316step0 := by apply Matrix.ext; unfold raw32316step1 raw32316step0; decide +kernel
      have hl : raw32316step0Labels = labelEmbedding10 ∘ raw32316step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32316step0 raw32316step0Labels raw32316step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5058 node5058Labels := by rfl

def raw32317 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32317Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32317step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32317step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32317step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32317step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32317 raw32317Labels = mixedMoment B node4851 node4851Labels := by
  calc
    mixedMoment B raw32317 raw32317Labels = mixedMoment B raw32317step0 raw32317step0Labels := by
      have ha : raw32317step0 = (fun i j => raw32317 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32317step0 raw32317; decide +kernel
      have hl : raw32317step0Labels = raw32317Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32317 raw32317Labels permutation152 permutation6
    mixedMoment B raw32317step0 raw32317step0Labels = mixedMoment B raw32317step1 raw32317step1Labels := by
      have ha : raw32317step1 = raw32317step0 := by apply Matrix.ext; unfold raw32317step1 raw32317step0; decide +kernel
      have hl : raw32317step0Labels = labelEmbedding9 ∘ raw32317step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32317step0 raw32317step0Labels raw32317step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4851 node4851Labels := by rfl

def raw32318 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32318Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32318step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32318step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32318step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32318step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32318step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32318 raw32318Labels = mixedMoment B node5203 node5203Labels := by
  calc
    mixedMoment B raw32318 raw32318Labels = mixedMoment B raw32318step0 raw32318step0Labels := by
      have hz : ∀ j, raw32318 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32318step0 = (fun i j => raw32318 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32318step0 raw32318; decide +kernel
      have hl : raw32318step0Labels = raw32318Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32318 raw32318Labels permutation346 hz
    mixedMoment B raw32318step0 raw32318step0Labels = mixedMoment B raw32318step1 raw32318step1Labels := by
      have ha : raw32318step1 = (fun i j => raw32318step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32318step1 raw32318step0; decide +kernel
      have hl : raw32318step1Labels = raw32318step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32318step0 raw32318step0Labels permutation32 permutation6
    mixedMoment B raw32318step1 raw32318step1Labels = mixedMoment B raw32318step2 raw32318step2Labels := by
      have ha : raw32318step2 = raw32318step1 := by apply Matrix.ext; unfold raw32318step2 raw32318step1; decide +kernel
      have hl : raw32318step1Labels = labelEmbedding9 ∘ raw32318step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32318step1 raw32318step1Labels raw32318step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5203 node5203Labels := by rfl

def raw32319 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32319Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32319step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw32319step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32319step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw32319step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32319 raw32319Labels = mixedMoment B node5190 node5190Labels := by
  calc
    mixedMoment B raw32319 raw32319Labels = mixedMoment B raw32319step0 raw32319step0Labels := by
      have ha : raw32319step0 = (fun i j => raw32319 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32319step0 raw32319; decide +kernel
      have hl : raw32319step0Labels = raw32319Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32319 raw32319Labels permutation152 permutation6
    mixedMoment B raw32319step0 raw32319step0Labels = mixedMoment B raw32319step1 raw32319step1Labels := by
      have ha : raw32319step1 = raw32319step0 := by apply Matrix.ext; unfold raw32319step1 raw32319step0; decide +kernel
      have hl : raw32319step0Labels = labelEmbedding9 ∘ raw32319step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32319step0 raw32319step0Labels raw32319step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5190 node5190Labels := by rfl

def raw32320 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw32320Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32320step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw32320step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32320step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw32320step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32320 raw32320Labels = mixedMoment B node5190 node5190Labels := by
  calc
    mixedMoment B raw32320 raw32320Labels = mixedMoment B raw32320step0 raw32320step0Labels := by
      have ha : raw32320step0 = (fun i j => raw32320 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32320step0 raw32320; decide +kernel
      have hl : raw32320step0Labels = raw32320Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32320 raw32320Labels permutation154 permutation6
    mixedMoment B raw32320step0 raw32320step0Labels = mixedMoment B raw32320step1 raw32320step1Labels := by
      have ha : raw32320step1 = raw32320step0 := by apply Matrix.ext; unfold raw32320step1 raw32320step0; decide +kernel
      have hl : raw32320step0Labels = labelEmbedding9 ∘ raw32320step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32320step0 raw32320step0Labels raw32320step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5190 node5190Labels := by rfl

def raw32321 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw32321Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32321step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw32321step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32321step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw32321step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32321 raw32321Labels = mixedMoment B node5192 node5192Labels := by
  calc
    mixedMoment B raw32321 raw32321Labels = mixedMoment B raw32321step0 raw32321step0Labels := by
      have ha : raw32321step0 = (fun i j => raw32321 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32321step0 raw32321; decide +kernel
      have hl : raw32321step0Labels = raw32321Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32321 raw32321Labels permutation152 permutation6
    mixedMoment B raw32321step0 raw32321step0Labels = mixedMoment B raw32321step1 raw32321step1Labels := by
      have ha : raw32321step1 = raw32321step0 := by apply Matrix.ext; unfold raw32321step1 raw32321step0; decide +kernel
      have hl : raw32321step0Labels = labelEmbedding9 ∘ raw32321step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32321step0 raw32321step0Labels raw32321step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5192 node5192Labels := by rfl

def raw32322 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32322Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32322step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32322step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32322step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32322step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32322 raw32322Labels = mixedMoment B node4815 node4815Labels := by
  calc
    mixedMoment B raw32322 raw32322Labels = mixedMoment B raw32322step0 raw32322step0Labels := by
      have ha : raw32322step0 = (fun i j => raw32322 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32322step0 raw32322; decide +kernel
      have hl : raw32322step0Labels = raw32322Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32322 raw32322Labels permutation152 permutation6
    mixedMoment B raw32322step0 raw32322step0Labels = mixedMoment B raw32322step1 raw32322step1Labels := by
      have ha : raw32322step1 = raw32322step0 := by apply Matrix.ext; unfold raw32322step1 raw32322step0; decide +kernel
      have hl : raw32322step0Labels = labelEmbedding9 ∘ raw32322step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32322step0 raw32322step0Labels raw32322step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4815 node4815Labels := by rfl

def raw32323 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32323Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32323step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32323step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32323step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32323step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32323 raw32323Labels = mixedMoment B node5085 node5085Labels := by
  calc
    mixedMoment B raw32323 raw32323Labels = mixedMoment B raw32323step0 raw32323step0Labels := by
      have ha : raw32323step0 = (fun i j => raw32323 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32323step0 raw32323; decide +kernel
      have hl : raw32323step0Labels = raw32323Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32323 raw32323Labels permutation152 permutation6
    mixedMoment B raw32323step0 raw32323step0Labels = mixedMoment B raw32323step1 raw32323step1Labels := by
      have ha : raw32323step1 = raw32323step0 := by apply Matrix.ext; unfold raw32323step1 raw32323step0; decide +kernel
      have hl : raw32323step0Labels = labelEmbedding9 ∘ raw32323step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32323step0 raw32323step0Labels raw32323step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5085 node5085Labels := by rfl

def raw32324 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32324Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32324step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw32324step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32324step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw32324step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32324 raw32324Labels = mixedMoment B node5153 node5153Labels := by
  calc
    mixedMoment B raw32324 raw32324Labels = mixedMoment B raw32324step0 raw32324step0Labels := by
      have ha : raw32324step0 = (fun i j => raw32324 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32324step0 raw32324; decide +kernel
      have hl : raw32324step0Labels = raw32324Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32324 raw32324Labels permutation152 permutation6
    mixedMoment B raw32324step0 raw32324step0Labels = mixedMoment B raw32324step1 raw32324step1Labels := by
      have ha : raw32324step1 = raw32324step0 := by apply Matrix.ext; unfold raw32324step1 raw32324step0; decide +kernel
      have hl : raw32324step0Labels = labelEmbedding9 ∘ raw32324step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32324step0 raw32324step0Labels raw32324step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5153 node5153Labels := by rfl

def raw32325 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw32325Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32325step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw32325step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32325step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw32325step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32325 raw32325Labels = mixedMoment B node5153 node5153Labels := by
  calc
    mixedMoment B raw32325 raw32325Labels = mixedMoment B raw32325step0 raw32325step0Labels := by
      have ha : raw32325step0 = (fun i j => raw32325 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32325step0 raw32325; decide +kernel
      have hl : raw32325step0Labels = raw32325Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32325 raw32325Labels permutation154 permutation6
    mixedMoment B raw32325step0 raw32325step0Labels = mixedMoment B raw32325step1 raw32325step1Labels := by
      have ha : raw32325step1 = raw32325step0 := by apply Matrix.ext; unfold raw32325step1 raw32325step0; decide +kernel
      have hl : raw32325step0Labels = labelEmbedding9 ∘ raw32325step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32325step0 raw32325step0Labels raw32325step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5153 node5153Labels := by rfl

def raw32326 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw32326Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32326step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw32326step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32326step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw32326step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32326 raw32326Labels = mixedMoment B node5155 node5155Labels := by
  calc
    mixedMoment B raw32326 raw32326Labels = mixedMoment B raw32326step0 raw32326step0Labels := by
      have ha : raw32326step0 = (fun i j => raw32326 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32326step0 raw32326; decide +kernel
      have hl : raw32326step0Labels = raw32326Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32326 raw32326Labels permutation152 permutation6
    mixedMoment B raw32326step0 raw32326step0Labels = mixedMoment B raw32326step1 raw32326step1Labels := by
      have ha : raw32326step1 = raw32326step0 := by apply Matrix.ext; unfold raw32326step1 raw32326step0; decide +kernel
      have hl : raw32326step0Labels = labelEmbedding9 ∘ raw32326step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32326step0 raw32326step0Labels raw32326step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5155 node5155Labels := by rfl

def raw32327 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32327Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32327step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32327step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32327step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32327step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32327 raw32327Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw32327 raw32327Labels = mixedMoment B raw32327step0 raw32327step0Labels := by
      have ha : raw32327step0 = (fun i j => raw32327 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32327step0 raw32327; decide +kernel
      have hl : raw32327step0Labels = raw32327Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32327 raw32327Labels permutation154 permutation6
    mixedMoment B raw32327step0 raw32327step0Labels = mixedMoment B raw32327step1 raw32327step1Labels := by
      have ha : raw32327step1 = raw32327step0 := by apply Matrix.ext; unfold raw32327step1 raw32327step0; decide +kernel
      have hl : raw32327step0Labels = labelEmbedding9 ∘ raw32327step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32327step0 raw32327step0Labels raw32327step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4802 node4802Labels := by rfl

def raw32328 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32328Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32328step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32328step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32328step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32328step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32328 raw32328Labels = mixedMoment B node5073 node5073Labels := by
  calc
    mixedMoment B raw32328 raw32328Labels = mixedMoment B raw32328step0 raw32328step0Labels := by
      have ha : raw32328step0 = (fun i j => raw32328 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32328step0 raw32328; decide +kernel
      have hl : raw32328step0Labels = raw32328Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32328 raw32328Labels permutation154 permutation6
    mixedMoment B raw32328step0 raw32328step0Labels = mixedMoment B raw32328step1 raw32328step1Labels := by
      have ha : raw32328step1 = raw32328step0 := by apply Matrix.ext; unfold raw32328step1 raw32328step0; decide +kernel
      have hl : raw32328step0Labels = labelEmbedding9 ∘ raw32328step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32328step0 raw32328step0Labels raw32328step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5073 node5073Labels := by rfl

def raw32329 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw32329Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32329step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw32329step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32329step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw32329step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32329 raw32329Labels = mixedMoment B node5145 node5145Labels := by
  calc
    mixedMoment B raw32329 raw32329Labels = mixedMoment B raw32329step0 raw32329step0Labels := by
      have ha : raw32329step0 = (fun i j => raw32329 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32329step0 raw32329; decide +kernel
      have hl : raw32329step0Labels = raw32329Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32329 raw32329Labels permutation154 permutation6
    mixedMoment B raw32329step0 raw32329step0Labels = mixedMoment B raw32329step1 raw32329step1Labels := by
      have ha : raw32329step1 = raw32329step0 := by apply Matrix.ext; unfold raw32329step1 raw32329step0; decide +kernel
      have hl : raw32329step0Labels = labelEmbedding9 ∘ raw32329step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32329step0 raw32329step0Labels raw32329step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5145 node5145Labels := by rfl

def raw32330 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw32330Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32330step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32330step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32330step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32330step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32330 raw32330Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw32330 raw32330Labels = mixedMoment B raw32330step0 raw32330step0Labels := by
      have ha : raw32330step0 = (fun i j => raw32330 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32330step0 raw32330; decide +kernel
      have hl : raw32330step0Labels = raw32330Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32330 raw32330Labels permutation152 permutation6
    mixedMoment B raw32330step0 raw32330step0Labels = mixedMoment B raw32330step1 raw32330step1Labels := by
      have ha : raw32330step1 = raw32330step0 := by apply Matrix.ext; unfold raw32330step1 raw32330step0; decide +kernel
      have hl : raw32330step0Labels = labelEmbedding9 ∘ raw32330step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32330step0 raw32330step0Labels raw32330step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4802 node4802Labels := by rfl

def raw32331 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw32331Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32331step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32331step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32331step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32331step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32331 raw32331Labels = mixedMoment B node5073 node5073Labels := by
  calc
    mixedMoment B raw32331 raw32331Labels = mixedMoment B raw32331step0 raw32331step0Labels := by
      have ha : raw32331step0 = (fun i j => raw32331 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32331step0 raw32331; decide +kernel
      have hl : raw32331step0Labels = raw32331Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32331 raw32331Labels permutation152 permutation6
    mixedMoment B raw32331step0 raw32331step0Labels = mixedMoment B raw32331step1 raw32331step1Labels := by
      have ha : raw32331step1 = raw32331step0 := by apply Matrix.ext; unfold raw32331step1 raw32331step0; decide +kernel
      have hl : raw32331step0Labels = labelEmbedding9 ∘ raw32331step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32331step0 raw32331step0Labels raw32331step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5073 node5073Labels := by rfl

def raw32332 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw32332Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32332step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw32332step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32332step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw32332step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32332 raw32332Labels = mixedMoment B node5145 node5145Labels := by
  calc
    mixedMoment B raw32332 raw32332Labels = mixedMoment B raw32332step0 raw32332step0Labels := by
      have ha : raw32332step0 = (fun i j => raw32332 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32332step0 raw32332; decide +kernel
      have hl : raw32332step0Labels = raw32332Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32332 raw32332Labels permutation152 permutation6
    mixedMoment B raw32332step0 raw32332step0Labels = mixedMoment B raw32332step1 raw32332step1Labels := by
      have ha : raw32332step1 = raw32332step0 := by apply Matrix.ext; unfold raw32332step1 raw32332step0; decide +kernel
      have hl : raw32332step0Labels = labelEmbedding9 ∘ raw32332step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32332step0 raw32332step0Labels raw32332step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5145 node5145Labels := by rfl

def raw32333 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw32333Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32333step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32333step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32333step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32333step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32333 raw32333Labels = mixedMoment B node4801 node4801Labels := by
  calc
    mixedMoment B raw32333 raw32333Labels = mixedMoment B raw32333step0 raw32333step0Labels := by
      have ha : raw32333step0 = (fun i j => raw32333 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32333step0 raw32333; decide +kernel
      have hl : raw32333step0Labels = raw32333Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32333 raw32333Labels permutation152 permutation6
    mixedMoment B raw32333step0 raw32333step0Labels = mixedMoment B raw32333step1 raw32333step1Labels := by
      have ha : raw32333step1 = raw32333step0 := by apply Matrix.ext; unfold raw32333step1 raw32333step0; decide +kernel
      have hl : raw32333step0Labels = labelEmbedding9 ∘ raw32333step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32333step0 raw32333step0Labels raw32333step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4801 node4801Labels := by rfl

def raw32334 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw32334Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32334step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32334step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32334step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32334step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32334 raw32334Labels = mixedMoment B node5072 node5072Labels := by
  calc
    mixedMoment B raw32334 raw32334Labels = mixedMoment B raw32334step0 raw32334step0Labels := by
      have ha : raw32334step0 = (fun i j => raw32334 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32334step0 raw32334; decide +kernel
      have hl : raw32334step0Labels = raw32334Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32334 raw32334Labels permutation152 permutation6
    mixedMoment B raw32334step0 raw32334step0Labels = mixedMoment B raw32334step1 raw32334step1Labels := by
      have ha : raw32334step1 = raw32334step0 := by apply Matrix.ext; unfold raw32334step1 raw32334step0; decide +kernel
      have hl : raw32334step0Labels = labelEmbedding9 ∘ raw32334step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32334step0 raw32334step0Labels raw32334step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5072 node5072Labels := by rfl

def raw32335 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw32335Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw32335step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32335step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32335step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32335step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32335step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32335 raw32335Labels = mixedMoment B node5168 node5168Labels := by
  calc
    mixedMoment B raw32335 raw32335Labels = mixedMoment B raw32335step0 raw32335step0Labels := by
      have hz : ∀ j, raw32335 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32335step0 = (fun i j => raw32335 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32335step0 raw32335; decide +kernel
      have hl : raw32335step0Labels = raw32335Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32335 raw32335Labels permutation346 hz
    mixedMoment B raw32335step0 raw32335step0Labels = mixedMoment B raw32335step1 raw32335step1Labels := by
      have ha : raw32335step1 = (fun i j => raw32335step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32335step1 raw32335step0; decide +kernel
      have hl : raw32335step1Labels = raw32335step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32335step0 raw32335step0Labels permutation32 permutation6
    mixedMoment B raw32335step1 raw32335step1Labels = mixedMoment B raw32335step2 raw32335step2Labels := by
      have ha : raw32335step2 = raw32335step1 := by apply Matrix.ext; unfold raw32335step2 raw32335step1; decide +kernel
      have hl : raw32335step1Labels = labelEmbedding9 ∘ raw32335step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32335step1 raw32335step1Labels raw32335step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5168 node5168Labels := by rfl

def raw32336 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw32336Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32336step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw32336step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32336step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw32336step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32336 raw32336Labels = mixedMoment B node5144 node5144Labels := by
  calc
    mixedMoment B raw32336 raw32336Labels = mixedMoment B raw32336step0 raw32336step0Labels := by
      have ha : raw32336step0 = (fun i j => raw32336 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32336step0 raw32336; decide +kernel
      have hl : raw32336step0Labels = raw32336Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32336 raw32336Labels permutation152 permutation6
    mixedMoment B raw32336step0 raw32336step0Labels = mixedMoment B raw32336step1 raw32336step1Labels := by
      have ha : raw32336step1 = raw32336step0 := by apply Matrix.ext; unfold raw32336step1 raw32336step0; decide +kernel
      have hl : raw32336step0Labels = labelEmbedding9 ∘ raw32336step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32336step0 raw32336step0Labels raw32336step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5144 node5144Labels := by rfl

def raw32337 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw32337Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32337step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw32337step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32337step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw32337step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32337 raw32337Labels = mixedMoment B node5144 node5144Labels := by
  calc
    mixedMoment B raw32337 raw32337Labels = mixedMoment B raw32337step0 raw32337step0Labels := by
      have ha : raw32337step0 = (fun i j => raw32337 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32337step0 raw32337; decide +kernel
      have hl : raw32337step0Labels = raw32337Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32337 raw32337Labels permutation154 permutation6
    mixedMoment B raw32337step0 raw32337step0Labels = mixedMoment B raw32337step1 raw32337step1Labels := by
      have ha : raw32337step1 = raw32337step0 := by apply Matrix.ext; unfold raw32337step1 raw32337step0; decide +kernel
      have hl : raw32337step0Labels = labelEmbedding9 ∘ raw32337step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32337step0 raw32337step0Labels raw32337step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5144 node5144Labels := by rfl

def raw32338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32338Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32338step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32338step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32338step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32338step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32338 raw32338Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw32338 raw32338Labels = mixedMoment B raw32338step0 raw32338step0Labels := by
      have ha : raw32338step0 = (fun i j => raw32338 (permutation267 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32338step0 raw32338; decide +kernel
      have hl : raw32338step0Labels = raw32338Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32338 raw32338Labels permutation267 permutation3
    mixedMoment B raw32338step0 raw32338step0Labels = mixedMoment B raw32338step1 raw32338step1Labels := by
      have ha : raw32338step1 = raw32338step0 := by apply Matrix.ext; unfold raw32338step1 raw32338step0; decide +kernel
      have hl : raw32338step0Labels = labelEmbedding6 ∘ raw32338step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32338step0 raw32338step0Labels raw32338step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

def raw32339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32339Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32339step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw32339step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32339step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32339step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32339step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32339step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32339 raw32339Labels = mixedMoment B node5397 node5397Labels := by
  calc
    mixedMoment B raw32339 raw32339Labels = mixedMoment B raw32339step0 raw32339step0Labels := by
      have ha : raw32339step0 = (fun i j => raw32339 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32339step0 raw32339; decide +kernel
      have hl : raw32339step0Labels = raw32339Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32339 raw32339Labels permutation662 permutation3
    mixedMoment B raw32339step0 raw32339step0Labels = mixedMoment B raw32339step1 raw32339step1Labels := by
      have ha : raw32339step1 = -raw32339step0 := by apply Matrix.ext; change ∀ i j, raw32339step1 i j = -(raw32339step0 i j); unfold raw32339step1 raw32339step0; decide +kernel
      have hl : raw32339step1Labels = raw32339step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32339step1 raw32339step1Labels = mixedMoment B raw32339step2 raw32339step2Labels := by
      have ha : raw32339step2 = raw32339step1 := by apply Matrix.ext; unfold raw32339step2 raw32339step1; decide +kernel
      have hl : raw32339step1Labels = labelEmbedding6 ∘ raw32339step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32339step1 raw32339step1Labels raw32339step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5397 node5397Labels := by rfl

def raw32340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32340Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32340step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32340 raw32340Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw32340 raw32340Labels = mixedMoment B raw32340step0 raw32340step0Labels := by
      have hz : ∀ j, raw32340 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw32340step0 = (fun i j => raw32340 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw32340step0 raw32340; decide +kernel
      have hl : raw32340step0Labels = raw32340Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32340 raw32340Labels permutation434 hz
    _ = mixedMoment B node5435 node5435Labels := by rfl

def raw32341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw32341Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32341step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw32341step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32341step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32341step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32341step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32341step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32341 raw32341Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw32341 raw32341Labels = mixedMoment B raw32341step0 raw32341step0Labels := by
      have ha : raw32341step0 = (fun i j => raw32341 (permutation658 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32341step0 raw32341; decide +kernel
      have hl : raw32341step0Labels = raw32341Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32341 raw32341Labels permutation658 permutation3
    mixedMoment B raw32341step0 raw32341step0Labels = mixedMoment B raw32341step1 raw32341step1Labels := by
      have ha : raw32341step1 = -raw32341step0 := by apply Matrix.ext; change ∀ i j, raw32341step1 i j = -(raw32341step0 i j); unfold raw32341step1 raw32341step0; decide +kernel
      have hl : raw32341step1Labels = raw32341step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32341step1 raw32341step1Labels = mixedMoment B raw32341step2 raw32341step2Labels := by
      have ha : raw32341step2 = raw32341step1 := by apply Matrix.ext; unfold raw32341step2 raw32341step1; decide +kernel
      have hl : raw32341step1Labels = labelEmbedding6 ∘ raw32341step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32341step1 raw32341step1Labels raw32341step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

def raw32342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw32342Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32342step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw32342step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32342 raw32342Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw32342 raw32342Labels = mixedMoment B raw32342step0 raw32342step0Labels := by
      have ha : raw32342step0 = (fun i j => raw32342 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32342step0 raw32342; decide +kernel
      have hl : raw32342step0Labels = raw32342Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32342 raw32342Labels permutation153 permutation2
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw32343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32343Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32343step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32343step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32343step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32343step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32343step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32343step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32343 raw32343Labels = mixedMoment B node4602 node4602Labels := by
  calc
    mixedMoment B raw32343 raw32343Labels = mixedMoment B raw32343step0 raw32343step0Labels := by
      have hz : ∀ j, raw32343 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw32343step0 = (fun i j => raw32343 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw32343step0 raw32343; decide +kernel
      have hl : raw32343step0Labels = raw32343Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32343 raw32343Labels permutation265 hz
    mixedMoment B raw32343step0 raw32343step0Labels = mixedMoment B raw32343step1 raw32343step1Labels := by
      have ha : raw32343step1 = (fun i j => raw32343step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32343step1 raw32343step0; decide +kernel
      have hl : raw32343step1Labels = raw32343step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32343step0 raw32343step0Labels permutation34 permutation3
    mixedMoment B raw32343step1 raw32343step1Labels = mixedMoment B raw32343step2 raw32343step2Labels := by
      have ha : raw32343step2 = raw32343step1 := by apply Matrix.ext; unfold raw32343step2 raw32343step1; decide +kernel
      have hl : raw32343step1Labels = labelEmbedding6 ∘ raw32343step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32343step1 raw32343step1Labels raw32343step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4602 node4602Labels := by rfl

def raw32344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32344Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32344step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32344step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32344 raw32344Labels = mixedMoment B node4971 node4971Labels := by
  calc
    mixedMoment B raw32344 raw32344Labels = mixedMoment B raw32344step0 raw32344step0Labels := by
      have ha : raw32344step0 = (fun i j => raw32344 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32344step0 raw32344; decide +kernel
      have hl : raw32344step0Labels = raw32344Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32344 raw32344Labels permutation158 permutation2
    _ = mixedMoment B node4971 node4971Labels := by rfl

def raw32345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32345Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32345step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32345 raw32345Labels = mixedMoment B node5172 node5172Labels := by
  calc
    mixedMoment B raw32345 raw32345Labels = mixedMoment B raw32345step0 raw32345step0Labels := by
      have hz : ∀ j, raw32345 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw32345step0 = (fun i j => raw32345 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw32345step0 raw32345; decide +kernel
      have hl : raw32345step0Labels = raw32345Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32345 raw32345Labels permutation434 hz
    _ = mixedMoment B node5172 node5172Labels := by rfl

def raw32346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw32346Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32346step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32346step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32346 raw32346Labels = mixedMoment B node5149 node5149Labels := by
  calc
    mixedMoment B raw32346 raw32346Labels = mixedMoment B raw32346step0 raw32346step0Labels := by
      have ha : raw32346step0 = (fun i j => raw32346 (permutation166 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32346step0 raw32346; decide +kernel
      have hl : raw32346step0Labels = raw32346Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32346 raw32346Labels permutation166 permutation2
    _ = mixedMoment B node5149 node5149Labels := by rfl

def raw32347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw32347Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32347step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw32347step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32347 raw32347Labels = mixedMoment B node5167 node5167Labels := by
  calc
    mixedMoment B raw32347 raw32347Labels = mixedMoment B raw32347step0 raw32347step0Labels := by
      have ha : raw32347step0 = (fun i j => raw32347 (permutation162 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32347step0 raw32347; decide +kernel
      have hl : raw32347step0Labels = raw32347Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32347 raw32347Labels permutation162 permutation2
    _ = mixedMoment B node5167 node5167Labels := by rfl

def raw32348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32348Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32348step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -2, 0]]
def raw32348step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32348 raw32348Labels = mixedMoment B node4962 node4962Labels := by
  calc
    mixedMoment B raw32348 raw32348Labels = mixedMoment B raw32348step0 raw32348step0Labels := by
      have ha : raw32348step0 = (fun i j => raw32348 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32348step0 raw32348; decide +kernel
      have hl : raw32348step0Labels = raw32348Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32348 raw32348Labels permutation154 permutation2
    _ = mixedMoment B node4962 node4962Labels := by rfl

def raw32349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32349Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32349step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -2, 0]]
def raw32349step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32349 raw32349Labels = mixedMoment B node5120 node5120Labels := by
  calc
    mixedMoment B raw32349 raw32349Labels = mixedMoment B raw32349step0 raw32349step0Labels := by
      have ha : raw32349step0 = (fun i j => raw32349 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32349step0 raw32349; decide +kernel
      have hl : raw32349step0Labels = raw32349Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32349 raw32349Labels permutation154 permutation2
    _ = mixedMoment B node5120 node5120Labels := by rfl

def raw32350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![0, 1, -1], ![2, -2, 0]]
def raw32350Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32350step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw32350step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32350 raw32350Labels = mixedMoment B node5142 node5142Labels := by
  calc
    mixedMoment B raw32350 raw32350Labels = mixedMoment B raw32350step0 raw32350step0Labels := by
      have ha : raw32350step0 = (fun i j => raw32350 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32350step0 raw32350; decide +kernel
      have hl : raw32350step0Labels = raw32350Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32350 raw32350Labels permutation154 permutation2
    _ = mixedMoment B node5142 node5142Labels := by rfl

def raw32351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1], ![1, -1, 0]]
def raw32351Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32351step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32351step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32351 raw32351Labels = mixedMoment B node5149 node5149Labels := by
  calc
    mixedMoment B raw32351 raw32351Labels = mixedMoment B raw32351step0 raw32351step0Labels := by
      have ha : raw32351step0 = (fun i j => raw32351 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32351step0 raw32351; decide +kernel
      have hl : raw32351step0Labels = raw32351Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32351 raw32351Labels permutation157 permutation2
    _ = mixedMoment B node5149 node5149Labels := by rfl

def raw32352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw32352Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32352step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw32352step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32352 raw32352Labels = mixedMoment B node4961 node4961Labels := by
  calc
    mixedMoment B raw32352 raw32352Labels = mixedMoment B raw32352step0 raw32352step0Labels := by
      have ha : raw32352step0 = (fun i j => raw32352 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32352step0 raw32352; decide +kernel
      have hl : raw32352step0Labels = raw32352Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32352 raw32352Labels permutation153 permutation2
    _ = mixedMoment B node4961 node4961Labels := by rfl

def raw32353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw32353Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32353step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw32353step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32353 raw32353Labels = mixedMoment B node5119 node5119Labels := by
  calc
    mixedMoment B raw32353 raw32353Labels = mixedMoment B raw32353step0 raw32353step0Labels := by
      have ha : raw32353step0 = (fun i j => raw32353 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32353step0 raw32353; decide +kernel
      have hl : raw32353step0Labels = raw32353Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32353 raw32353Labels permutation153 permutation2
    _ = mixedMoment B node5119 node5119Labels := by rfl

def raw32354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw32354Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32354step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw32354step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32354step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32354step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32354 raw32354Labels = mixedMoment B node5152 node5152Labels := by
  calc
    mixedMoment B raw32354 raw32354Labels = mixedMoment B raw32354step0 raw32354step0Labels := by
      have hz : ∀ j, raw32354 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw32354step0 = (fun i j => raw32354 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw32354step0 raw32354; decide +kernel
      have hl : raw32354step0Labels = raw32354Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32354 raw32354Labels permutation434 hz
    mixedMoment B raw32354step0 raw32354step0Labels = mixedMoment B raw32354step1 raw32354step1Labels := by
      have ha : raw32354step1 = (fun i j => raw32354step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32354step1 raw32354step0; decide +kernel
      have hl : raw32354step1Labels = raw32354step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32354step0 raw32354step0Labels permutation33 permutation2
    _ = mixedMoment B node5152 node5152Labels := by rfl

def raw32355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![1, -1, 0]]
def raw32355Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32355step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32355step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32355 raw32355Labels = mixedMoment B node5148 node5148Labels := by
  calc
    mixedMoment B raw32355 raw32355Labels = mixedMoment B raw32355step0 raw32355step0Labels := by
      have ha : raw32355step0 = (fun i j => raw32355 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32355step0 raw32355; decide +kernel
      have hl : raw32355step0Labels = raw32355Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32355 raw32355Labels permutation153 permutation2
    _ = mixedMoment B node5148 node5148Labels := by rfl

def raw32356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw32356Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32356step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2], ![-3, 2, 1]]
def raw32356step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32356step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw32356step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32356step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw32356step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32356 raw32356Labels = mixedMoment B node4707 node4707Labels := by
  calc
    mixedMoment B raw32356 raw32356Labels = mixedMoment B raw32356step0 raw32356step0Labels := by
      have ha : raw32356step0 = (fun i j => raw32356 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32356step0 raw32356; decide +kernel
      have hl : raw32356step0Labels = raw32356Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32356 raw32356Labels permutation664 permutation3
    mixedMoment B raw32356step0 raw32356step0Labels = mixedMoment B raw32356step1 raw32356step1Labels := by
      have ha : raw32356step1 = -raw32356step0 := by apply Matrix.ext; change ∀ i j, raw32356step1 i j = -(raw32356step0 i j); unfold raw32356step1 raw32356step0; decide +kernel
      have hl : raw32356step1Labels = raw32356step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32356step1 raw32356step1Labels = mixedMoment B raw32356step2 raw32356step2Labels := by
      have ha : raw32356step2 = raw32356step1 := by apply Matrix.ext; unfold raw32356step2 raw32356step1; decide +kernel
      have hl : raw32356step1Labels = labelEmbedding6 ∘ raw32356step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32356step1 raw32356step1Labels raw32356step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4707 node4707Labels := by rfl

def raw32357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw32357Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32357step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw32357step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32357step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw32357step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32357step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw32357step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32357 raw32357Labels = mixedMoment B node4713 node4713Labels := by
  calc
    mixedMoment B raw32357 raw32357Labels = mixedMoment B raw32357step0 raw32357step0Labels := by
      have ha : raw32357step0 = (fun i j => raw32357 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32357step0 raw32357; decide +kernel
      have hl : raw32357step0Labels = raw32357Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32357 raw32357Labels permutation662 permutation3
    mixedMoment B raw32357step0 raw32357step0Labels = mixedMoment B raw32357step1 raw32357step1Labels := by
      have ha : raw32357step1 = -raw32357step0 := by apply Matrix.ext; change ∀ i j, raw32357step1 i j = -(raw32357step0 i j); unfold raw32357step1 raw32357step0; decide +kernel
      have hl : raw32357step1Labels = raw32357step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32357step1 raw32357step1Labels = mixedMoment B raw32357step2 raw32357step2Labels := by
      have ha : raw32357step2 = raw32357step1 := by apply Matrix.ext; unfold raw32357step2 raw32357step1; decide +kernel
      have hl : raw32357step1Labels = labelEmbedding6 ∘ raw32357step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32357step1 raw32357step1Labels raw32357step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4713 node4713Labels := by rfl

def raw32358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw32358Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw32358step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32358step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw32358step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32358step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32358step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32358step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32358step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32358 raw32358Labels = mixedMoment B node4807 node4807Labels := by
  calc
    mixedMoment B raw32358 raw32358Labels = mixedMoment B raw32358step0 raw32358step0Labels := by
      have hz : ∀ j, raw32358 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw32358step0 = (fun i j => raw32358 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw32358step0 raw32358; decide +kernel
      have hl : raw32358step0Labels = raw32358Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32358 raw32358Labels permutation434 hz
    mixedMoment B raw32358step0 raw32358step0Labels = mixedMoment B raw32358step1 raw32358step1Labels := by
      have ha : raw32358step1 = (fun i j => raw32358step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32358step1 raw32358step0; decide +kernel
      have hl : raw32358step1Labels = raw32358step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32358step0 raw32358step0Labels permutation151 permutation3
    mixedMoment B raw32358step1 raw32358step1Labels = mixedMoment B raw32358step2 raw32358step2Labels := by
      have ha : raw32358step2 = -raw32358step1 := by apply Matrix.ext; change ∀ i j, raw32358step2 i j = -(raw32358step1 i j); unfold raw32358step2 raw32358step1; decide +kernel
      have hl : raw32358step2Labels = raw32358step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32358step2 raw32358step2Labels = mixedMoment B raw32358step3 raw32358step3Labels := by
      have ha : raw32358step3 = raw32358step2 := by apply Matrix.ext; unfold raw32358step3 raw32358step2; decide +kernel
      have hl : raw32358step2Labels = labelEmbedding6 ∘ raw32358step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32358step2 raw32358step2Labels raw32358step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4807 node4807Labels := by rfl

def raw32359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![3, -3, 0]]
def raw32359Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32359step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw32359step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32359step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32359step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32359step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32359step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32359 raw32359Labels = mixedMoment B node4729 node4729Labels := by
  calc
    mixedMoment B raw32359 raw32359Labels = mixedMoment B raw32359step0 raw32359step0Labels := by
      have ha : raw32359step0 = (fun i j => raw32359 (permutation658 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32359step0 raw32359; decide +kernel
      have hl : raw32359step0Labels = raw32359Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32359 raw32359Labels permutation658 permutation3
    mixedMoment B raw32359step0 raw32359step0Labels = mixedMoment B raw32359step1 raw32359step1Labels := by
      have ha : raw32359step1 = -raw32359step0 := by apply Matrix.ext; change ∀ i j, raw32359step1 i j = -(raw32359step0 i j); unfold raw32359step1 raw32359step0; decide +kernel
      have hl : raw32359step1Labels = raw32359step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32359step1 raw32359step1Labels = mixedMoment B raw32359step2 raw32359step2Labels := by
      have ha : raw32359step2 = raw32359step1 := by apply Matrix.ext; unfold raw32359step2 raw32359step1; decide +kernel
      have hl : raw32359step1Labels = labelEmbedding6 ∘ raw32359step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32359step1 raw32359step1Labels raw32359step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4729 node4729Labels := by rfl

def raw32360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32360Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32360step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32360step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32360 raw32360Labels = mixedMoment B node3719 node3719Labels := by
  calc
    mixedMoment B raw32360 raw32360Labels = mixedMoment B raw32360step0 raw32360step0Labels := by
      have ha : raw32360step0 = (fun i j => raw32360 (permutation267 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32360step0 raw32360; decide +kernel
      have hl : raw32360step0Labels = raw32360Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32360 raw32360Labels permutation267 permutation3
    _ = mixedMoment B node3719 node3719Labels := by rfl

def raw32361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32361Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32361step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw32361step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32361step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32361step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32361 raw32361Labels = mixedMoment B node3782 node3782Labels := by
  calc
    mixedMoment B raw32361 raw32361Labels = mixedMoment B raw32361step0 raw32361step0Labels := by
      have ha : raw32361step0 = (fun i j => raw32361 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32361step0 raw32361; decide +kernel
      have hl : raw32361step0Labels = raw32361Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32361 raw32361Labels permutation662 permutation3
    mixedMoment B raw32361step0 raw32361step0Labels = mixedMoment B raw32361step1 raw32361step1Labels := by
      have ha : raw32361step1 = -raw32361step0 := by apply Matrix.ext; change ∀ i j, raw32361step1 i j = -(raw32361step0 i j); unfold raw32361step1 raw32361step0; decide +kernel
      have hl : raw32361step1Labels = raw32361step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3782 node3782Labels := by rfl

def raw32362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32362Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32362step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32362step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32362step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw32362step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32362step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32362step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32362 raw32362Labels = mixedMoment B node3853 node3853Labels := by
  calc
    mixedMoment B raw32362 raw32362Labels = mixedMoment B raw32362step0 raw32362step0Labels := by
      have hz : ∀ j, raw32362 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw32362step0 = (fun i j => raw32362 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw32362step0 raw32362; decide +kernel
      have hl : raw32362step0Labels = raw32362Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32362 raw32362Labels permutation434 hz
    mixedMoment B raw32362step0 raw32362step0Labels = mixedMoment B raw32362step1 raw32362step1Labels := by
      have ha : raw32362step1 = (fun i j => raw32362step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32362step1 raw32362step0; decide +kernel
      have hl : raw32362step1Labels = raw32362step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32362step0 raw32362step0Labels permutation151 permutation3
    mixedMoment B raw32362step1 raw32362step1Labels = mixedMoment B raw32362step2 raw32362step2Labels := by
      have ha : raw32362step2 = -raw32362step1 := by apply Matrix.ext; change ∀ i j, raw32362step2 i j = -(raw32362step1 i j); unfold raw32362step2 raw32362step1; decide +kernel
      have hl : raw32362step2Labels = raw32362step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3853 node3853Labels := by rfl

def raw32363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw32363Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32363step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw32363step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32363step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32363step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32363 raw32363Labels = mixedMoment B node3801 node3801Labels := by
  calc
    mixedMoment B raw32363 raw32363Labels = mixedMoment B raw32363step0 raw32363step0Labels := by
      have ha : raw32363step0 = (fun i j => raw32363 (permutation658 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32363step0 raw32363; decide +kernel
      have hl : raw32363step0Labels = raw32363Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32363 raw32363Labels permutation658 permutation3
    mixedMoment B raw32363step0 raw32363step0Labels = mixedMoment B raw32363step1 raw32363step1Labels := by
      have ha : raw32363step1 = -raw32363step0 := by apply Matrix.ext; change ∀ i j, raw32363step1 i j = -(raw32363step0 i j); unfold raw32363step1 raw32363step0; decide +kernel
      have hl : raw32363step1Labels = raw32363step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3801 node3801Labels := by rfl

def raw32364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw32364Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32364step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw32364step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32364 raw32364Labels = mixedMoment B node4033 node4033Labels := by
  calc
    mixedMoment B raw32364 raw32364Labels = mixedMoment B raw32364step0 raw32364step0Labels := by
      have ha : raw32364step0 = (fun i j => raw32364 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32364step0 raw32364; decide +kernel
      have hl : raw32364step0Labels = raw32364Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32364 raw32364Labels permutation154 permutation3
    _ = mixedMoment B node4033 node4033Labels := by rfl

def raw32365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32365Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32365step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32365step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32365step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32365 raw32365Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw32365 raw32365Labels = mixedMoment B raw32365step0 raw32365step0Labels := by
      have hz : ∀ j, raw32365 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw32365step0 = (fun i j => raw32365 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw32365step0 raw32365; decide +kernel
      have hl : raw32365step0Labels = raw32365Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32365 raw32365Labels permutation265 hz
    mixedMoment B raw32365step0 raw32365step0Labels = mixedMoment B raw32365step1 raw32365step1Labels := by
      have ha : raw32365step1 = (fun i j => raw32365step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32365step1 raw32365step0; decide +kernel
      have hl : raw32365step1Labels = raw32365step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32365step0 raw32365step0Labels permutation34 permutation3
    _ = mixedMoment B node1236 node1236Labels := by rfl

def raw32366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32366Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32366step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32366step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32366 raw32366Labels = mixedMoment B node2807 node2807Labels := by
  calc
    mixedMoment B raw32366 raw32366Labels = mixedMoment B raw32366step0 raw32366step0Labels := by
      have ha : raw32366step0 = (fun i j => raw32366 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32366step0 raw32366; decide +kernel
      have hl : raw32366step0Labels = raw32366Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32366 raw32366Labels permutation154 permutation3
    _ = mixedMoment B node2807 node2807Labels := by rfl

def raw32367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32367Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw32367step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32367step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw32367step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32367 raw32367Labels = mixedMoment B node2959 node2959Labels := by
  calc
    mixedMoment B raw32367 raw32367Labels = mixedMoment B raw32367step0 raw32367step0Labels := by
      have hz : ∀ j, raw32367 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw32367step0 = (fun i j => raw32367 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw32367step0 raw32367; decide +kernel
      have hl : raw32367step0Labels = raw32367Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32367 raw32367Labels permutation434 hz
    mixedMoment B raw32367step0 raw32367step0Labels = mixedMoment B raw32367step1 raw32367step1Labels := by
      have ha : raw32367step1 = (fun i j => raw32367step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32367step1 raw32367step0; decide +kernel
      have hl : raw32367step1Labels = raw32367step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32367step0 raw32367step0Labels permutation32 permutation3
    _ = mixedMoment B node2959 node2959Labels := by rfl

def raw32368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![0, 1, -1], ![2, -2, 0]]
def raw32368Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32368step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32368step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32368 raw32368Labels = mixedMoment B node2924 node2924Labels := by
  calc
    mixedMoment B raw32368 raw32368Labels = mixedMoment B raw32368step0 raw32368step0Labels := by
      have ha : raw32368step0 = (fun i j => raw32368 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32368step0 raw32368; decide +kernel
      have hl : raw32368step0Labels = raw32368Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32368 raw32368Labels permutation164 permutation3
    _ = mixedMoment B node2924 node2924Labels := by rfl

def raw32369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw32369Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32369step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw32369step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32369 raw32369Labels = mixedMoment B node2958 node2958Labels := by
  calc
    mixedMoment B raw32369 raw32369Labels = mixedMoment B raw32369step0 raw32369step0Labels := by
      have ha : raw32369step0 = (fun i j => raw32369 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32369step0 raw32369; decide +kernel
      have hl : raw32369step0Labels = raw32369Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32369 raw32369Labels permutation154 permutation3
    _ = mixedMoment B node2958 node2958Labels := by rfl

def raw32370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32370Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32370step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw32370step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32370 raw32370Labels = mixedMoment B node2795 node2795Labels := by
  calc
    mixedMoment B raw32370 raw32370Labels = mixedMoment B raw32370step0 raw32370step0Labels := by
      have ha : raw32370step0 = (fun i j => raw32370 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32370step0 raw32370; decide +kernel
      have hl : raw32370step0Labels = raw32370Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32370 raw32370Labels permutation154 permutation3
    _ = mixedMoment B node2795 node2795Labels := by rfl

def raw32371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 2, -1], ![2, -2, 0], ![1, 0, -1], ![2, -2, 0]]
def raw32371Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32371step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw32371step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32371 raw32371Labels = mixedMoment B node2844 node2844Labels := by
  calc
    mixedMoment B raw32371 raw32371Labels = mixedMoment B raw32371step0 raw32371step0Labels := by
      have ha : raw32371step0 = (fun i j => raw32371 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32371step0 raw32371; decide +kernel
      have hl : raw32371step0Labels = raw32371Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32371 raw32371Labels permutation178 permutation3
    _ = mixedMoment B node2844 node2844Labels := by rfl

def raw32372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![0, 1, -1], ![2, -2, 0]]
def raw32372Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32372step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw32372step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32372 raw32372Labels = mixedMoment B node2913 node2913Labels := by
  calc
    mixedMoment B raw32372 raw32372Labels = mixedMoment B raw32372step0 raw32372step0Labels := by
      have ha : raw32372step0 = (fun i j => raw32372 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32372step0 raw32372; decide +kernel
      have hl : raw32372step0Labels = raw32372Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32372 raw32372Labels permutation154 permutation3
    _ = mixedMoment B node2913 node2913Labels := by rfl

def raw32373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1], ![1, -1, 0]]
def raw32373Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32373step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32373step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32373 raw32373Labels = mixedMoment B node2924 node2924Labels := by
  calc
    mixedMoment B raw32373 raw32373Labels = mixedMoment B raw32373step0 raw32373step0Labels := by
      have ha : raw32373step0 = (fun i j => raw32373 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32373step0 raw32373; decide +kernel
      have hl : raw32373step0Labels = raw32373Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32373 raw32373Labels permutation155 permutation3
    _ = mixedMoment B node2924 node2924Labels := by rfl

def raw32374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw32374Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32374step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32374step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32374 raw32374Labels = mixedMoment B node2796 node2796Labels := by
  calc
    mixedMoment B raw32374 raw32374Labels = mixedMoment B raw32374step0 raw32374step0Labels := by
      have ha : raw32374step0 = (fun i j => raw32374 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32374step0 raw32374; decide +kernel
      have hl : raw32374step0Labels = raw32374Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32374 raw32374Labels permutation152 permutation3
    _ = mixedMoment B node2796 node2796Labels := by rfl

def raw32375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -2, 0]]
def raw32375Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32375step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32375step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32375 raw32375Labels = mixedMoment B node2845 node2845Labels := by
  calc
    mixedMoment B raw32375 raw32375Labels = mixedMoment B raw32375step0 raw32375step0Labels := by
      have ha : raw32375step0 = (fun i j => raw32375 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32375step0 raw32375; decide +kernel
      have hl : raw32375step0Labels = raw32375Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32375 raw32375Labels permutation176 permutation3
    _ = mixedMoment B node2845 node2845Labels := by rfl

def raw32376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -2, 0]]
def raw32376Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw32376step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32376step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw32376step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32376 raw32376Labels = mixedMoment B node2931 node2931Labels := by
  calc
    mixedMoment B raw32376 raw32376Labels = mixedMoment B raw32376step0 raw32376step0Labels := by
      have hz : ∀ j, raw32376 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw32376step0 = (fun i j => raw32376 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw32376step0 raw32376; decide +kernel
      have hl : raw32376step0Labels = raw32376Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32376 raw32376Labels permutation434 hz
    mixedMoment B raw32376step0 raw32376step0Labels = mixedMoment B raw32376step1 raw32376step1Labels := by
      have ha : raw32376step1 = (fun i j => raw32376step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32376step1 raw32376step0; decide +kernel
      have hl : raw32376step1Labels = raw32376step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32376step0 raw32376step0Labels permutation32 permutation3
    _ = mixedMoment B node2931 node2931Labels := by rfl

def raw32377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![1, -1, 0]]
def raw32377Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32377step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32377step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32377 raw32377Labels = mixedMoment B node2927 node2927Labels := by
  calc
    mixedMoment B raw32377 raw32377Labels = mixedMoment B raw32377step0 raw32377step0Labels := by
      have ha : raw32377step0 = (fun i j => raw32377 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32377step0 raw32377; decide +kernel
      have hl : raw32377step0Labels = raw32377Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32377 raw32377Labels permutation153 permutation3
    _ = mixedMoment B node2927 node2927Labels := by rfl

def raw32378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw32378Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32378step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2], ![-3, 2, 1]]
def raw32378step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32378step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw32378step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32378 raw32378Labels = mixedMoment B node1861 node1861Labels := by
  calc
    mixedMoment B raw32378 raw32378Labels = mixedMoment B raw32378step0 raw32378step0Labels := by
      have ha : raw32378step0 = (fun i j => raw32378 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32378step0 raw32378; decide +kernel
      have hl : raw32378step0Labels = raw32378Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32378 raw32378Labels permutation664 permutation3
    mixedMoment B raw32378step0 raw32378step0Labels = mixedMoment B raw32378step1 raw32378step1Labels := by
      have ha : raw32378step1 = -raw32378step0 := by apply Matrix.ext; change ∀ i j, raw32378step1 i j = -(raw32378step0 i j); unfold raw32378step1 raw32378step0; decide +kernel
      have hl : raw32378step1Labels = raw32378step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1861 node1861Labels := by rfl

def raw32379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw32379Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32379step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw32379step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32379step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw32379step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32379 raw32379Labels = mixedMoment B node1867 node1867Labels := by
  calc
    mixedMoment B raw32379 raw32379Labels = mixedMoment B raw32379step0 raw32379step0Labels := by
      have ha : raw32379step0 = (fun i j => raw32379 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32379step0 raw32379; decide +kernel
      have hl : raw32379step0Labels = raw32379Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32379 raw32379Labels permutation662 permutation3
    mixedMoment B raw32379step0 raw32379step0Labels = mixedMoment B raw32379step1 raw32379step1Labels := by
      have ha : raw32379step1 = -raw32379step0 := by apply Matrix.ext; change ∀ i j, raw32379step1 i j = -(raw32379step0 i j); unfold raw32379step1 raw32379step0; decide +kernel
      have hl : raw32379step1Labels = raw32379step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1867 node1867Labels := by rfl

def raw32380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw32380Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32380step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw32380step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32380step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw32380step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32380step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32380step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32380 raw32380Labels = mixedMoment B node2025 node2025Labels := by
  calc
    mixedMoment B raw32380 raw32380Labels = mixedMoment B raw32380step0 raw32380step0Labels := by
      have hz : ∀ j, raw32380 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw32380step0 = (fun i j => raw32380 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw32380step0 raw32380; decide +kernel
      have hl : raw32380step0Labels = raw32380Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32380 raw32380Labels permutation434 hz
    mixedMoment B raw32380step0 raw32380step0Labels = mixedMoment B raw32380step1 raw32380step1Labels := by
      have ha : raw32380step1 = (fun i j => raw32380step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32380step1 raw32380step0; decide +kernel
      have hl : raw32380step1Labels = raw32380step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32380step0 raw32380step0Labels permutation151 permutation3
    mixedMoment B raw32380step1 raw32380step1Labels = mixedMoment B raw32380step2 raw32380step2Labels := by
      have ha : raw32380step2 = -raw32380step1 := by apply Matrix.ext; change ∀ i j, raw32380step2 i j = -(raw32380step1 i j); unfold raw32380step2 raw32380step1; decide +kernel
      have hl : raw32380step2Labels = raw32380step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2025 node2025Labels := by rfl

def raw32381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![3, -3, 0]]
def raw32381Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32381step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw32381step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32381step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32381step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32381 raw32381Labels = mixedMoment B node1898 node1898Labels := by
  calc
    mixedMoment B raw32381 raw32381Labels = mixedMoment B raw32381step0 raw32381step0Labels := by
      have ha : raw32381step0 = (fun i j => raw32381 (permutation658 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32381step0 raw32381; decide +kernel
      have hl : raw32381step0Labels = raw32381Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32381 raw32381Labels permutation658 permutation3
    mixedMoment B raw32381step0 raw32381step0Labels = mixedMoment B raw32381step1 raw32381step1Labels := by
      have ha : raw32381step1 = -raw32381step0 := by apply Matrix.ext; change ∀ i j, raw32381step1 i j = -(raw32381step0 i j); unfold raw32381step1 raw32381step0; decide +kernel
      have hl : raw32381step1Labels = raw32381step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1898 node1898Labels := by rfl

def raw32382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32382Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32382step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw32382step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32382step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32382step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32382 raw32382Labels = mixedMoment B node5393 node5393Labels := by
  calc
    mixedMoment B raw32382 raw32382Labels = mixedMoment B raw32382step0 raw32382step0Labels := by
      have ha : raw32382step0 = (fun i j => raw32382 (permutation663 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32382step0 raw32382; decide +kernel
      have hl : raw32382step0Labels = raw32382Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32382 raw32382Labels permutation663 permutation2
    mixedMoment B raw32382step0 raw32382step0Labels = mixedMoment B raw32382step1 raw32382step1Labels := by
      have ha : raw32382step1 = -raw32382step0 := by apply Matrix.ext; change ∀ i j, raw32382step1 i j = -(raw32382step0 i j); unfold raw32382step1 raw32382step0; decide +kernel
      have hl : raw32382step1Labels = raw32382step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5393 node5393Labels := by rfl

def raw32383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32383Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32383step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw32383step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32383step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32383step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32383 raw32383Labels = mixedMoment B node5396 node5396Labels := by
  calc
    mixedMoment B raw32383 raw32383Labels = mixedMoment B raw32383step0 raw32383step0Labels := by
      have ha : raw32383step0 = (fun i j => raw32383 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32383step0 raw32383; decide +kernel
      have hl : raw32383step0Labels = raw32383Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32383 raw32383Labels permutation662 permutation2
    mixedMoment B raw32383step0 raw32383step0Labels = mixedMoment B raw32383step1 raw32383step1Labels := by
      have ha : raw32383step1 = -raw32383step0 := by apply Matrix.ext; change ∀ i j, raw32383step1 i j = -(raw32383step0 i j); unfold raw32383step1 raw32383step0; decide +kernel
      have hl : raw32383step1Labels = raw32383step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5396 node5396Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
