import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes12
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw5248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5248Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5248step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw5248step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5248step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw5248step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5248 raw5248Labels = mixedMoment B node3016 node3016Labels := by
  calc
    mixedMoment B raw5248 raw5248Labels = mixedMoment B raw5248step0 raw5248step0Labels := by
      have ha : raw5248step0 = (fun i j => raw5248 (permutation260 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5248step0 raw5248; decide +kernel
      have hl : raw5248step0Labels = raw5248Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5248 raw5248Labels permutation260 permutation6
    mixedMoment B raw5248step0 raw5248step0Labels = mixedMoment B raw5248step1 raw5248step1Labels := by
      have ha : raw5248step1 = -raw5248step0 := by apply Matrix.ext; change ∀ i j, raw5248step1 i j = -(raw5248step0 i j); unfold raw5248step1 raw5248step0; decide +kernel
      have hl : raw5248step1Labels = raw5248step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3016 node3016Labels := by rfl

def raw5249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5249Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5249step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5249step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5249step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw5249step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5249step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw5249step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5249 raw5249Labels = mixedMoment B node3025 node3025Labels := by
  calc
    mixedMoment B raw5249 raw5249Labels = mixedMoment B raw5249step0 raw5249step0Labels := by
      have hz : ∀ j, raw5249 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5249step0 = (fun i j => raw5249 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5249step0 raw5249; decide +kernel
      have hl : raw5249step0Labels = raw5249Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5249 raw5249Labels permutation265 hz
    mixedMoment B raw5249step0 raw5249step0Labels = mixedMoment B raw5249step1 raw5249step1Labels := by
      have ha : raw5249step1 = (fun i j => raw5249step0 (permutation54 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5249step1 raw5249step0; decide +kernel
      have hl : raw5249step1Labels = raw5249step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5249step0 raw5249step0Labels permutation54 permutation6
    mixedMoment B raw5249step1 raw5249step1Labels = mixedMoment B raw5249step2 raw5249step2Labels := by
      have ha : raw5249step2 = -raw5249step1 := by apply Matrix.ext; change ∀ i j, raw5249step2 i j = -(raw5249step1 i j); unfold raw5249step2 raw5249step1; decide +kernel
      have hl : raw5249step2Labels = raw5249step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3025 node3025Labels := by rfl

def raw5250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5250Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5250step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5250step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, 1, -1], ![-1, 0, 1], ![-2, -1, 3]]
def raw5250step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5250step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw5250step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5250 raw5250Labels = mixedMoment B node3024 node3024Labels := by
  calc
    mixedMoment B raw5250 raw5250Labels = mixedMoment B raw5250step0 raw5250step0Labels := by
      have hz : ∀ j, raw5250 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5250step0 = (fun i j => raw5250 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5250step0 raw5250; decide +kernel
      have hl : raw5250step0Labels = raw5250Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5250 raw5250Labels permutation265 hz
    mixedMoment B raw5250step0 raw5250step0Labels = mixedMoment B raw5250step1 raw5250step1Labels := by
      have ha : raw5250step1 = (fun i j => raw5250step0 (permutation54 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5250step1 raw5250step0; decide +kernel
      have hl : raw5250step1Labels = raw5250step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5250step0 raw5250step0Labels permutation54 permutation6
    mixedMoment B raw5250step1 raw5250step1Labels = mixedMoment B raw5250step2 raw5250step2Labels := by
      have ha : raw5250step2 = -raw5250step1 := by apply Matrix.ext; change ∀ i j, raw5250step2 i j = -(raw5250step1 i j); unfold raw5250step2 raw5250step1; decide +kernel
      have hl : raw5250step2Labels = raw5250step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3024 node3024Labels := by rfl

def raw5251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]
def raw5251Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw5251step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5251step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw5251step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5251step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 0, 1], ![-2, 0, 2]]
def raw5251step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5251step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5251step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5251 raw5251Labels = mixedMoment B node3054 node3054Labels := by
  calc
    mixedMoment B raw5251 raw5251Labels = mixedMoment B raw5251step0 raw5251step0Labels := by
      have hz : ∀ j, raw5251 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5251step0 = (fun i j => raw5251 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5251step0 raw5251; decide +kernel
      have hl : raw5251step0Labels = raw5251Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5251 raw5251Labels permutation520 hz
    mixedMoment B raw5251step0 raw5251step0Labels = mixedMoment B raw5251step1 raw5251step1Labels := by
      have hz : ∀ j, raw5251step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5251step1 = (fun i j => raw5251step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5251step1 raw5251step0; decide +kernel
      have hl : raw5251step1Labels = raw5251step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5251step0 raw5251step0Labels permutation56 hz
    mixedMoment B raw5251step1 raw5251step1Labels = mixedMoment B raw5251step2 raw5251step2Labels := by
      have ha : raw5251step2 = (fun i j => raw5251step1 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5251step2 raw5251step1; decide +kernel
      have hl : raw5251step2Labels = raw5251step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5251step1 raw5251step1Labels permutation12 permutation6
    mixedMoment B raw5251step2 raw5251step2Labels = mixedMoment B raw5251step3 raw5251step3Labels := by
      have ha : raw5251step3 = -raw5251step2 := by apply Matrix.ext; change ∀ i j, raw5251step3 i j = -(raw5251step2 i j); unfold raw5251step3 raw5251step2; decide +kernel
      have hl : raw5251step3Labels = raw5251step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3054 node3054Labels := by rfl

def raw5252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw5252Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw5252step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5252step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw5252step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5252step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5252step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5252 raw5252Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw5252 raw5252Labels = mixedMoment B raw5252step0 raw5252step0Labels := by
      have hz : ∀ j, raw5252 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5252step0 = (fun i j => raw5252 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5252step0 raw5252; decide +kernel
      have hl : raw5252step0Labels = raw5252Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5252 raw5252Labels permutation265 hz
    mixedMoment B raw5252step0 raw5252step0Labels = mixedMoment B raw5252step1 raw5252step1Labels := by
      have ha : raw5252step1 = (fun i j => raw5252step0 (permutation48 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5252step1 raw5252step0; decide +kernel
      have hl : raw5252step1Labels = raw5252step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5252step0 raw5252step0Labels permutation48 permutation6
    mixedMoment B raw5252step1 raw5252step1Labels = mixedMoment B raw5252step2 raw5252step2Labels := by
      have ha : raw5252step2 = -raw5252step1 := by apply Matrix.ext; change ∀ i j, raw5252step2 i j = -(raw5252step1 i j); unfold raw5252step2 raw5252step1; decide +kernel
      have hl : raw5252step2Labels = raw5252step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3077 node3077Labels := by rfl

def raw5253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5253Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5253step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw5253step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5253 raw5253Labels = mixedMoment B node1354 node1354Labels := by
  calc
    mixedMoment B raw5253 raw5253Labels = mixedMoment B raw5253step0 raw5253step0Labels := by
      have ha : raw5253step0 = (fun i j => raw5253 (permutation206 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5253step0 raw5253; decide +kernel
      have hl : raw5253step0Labels = raw5253Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5253 raw5253Labels permutation206 permutation3
    _ = mixedMoment B node1354 node1354Labels := by rfl

def raw5254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5254Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5254step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw5254step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5254 raw5254Labels = mixedMoment B node3165 node3165Labels := by
  calc
    mixedMoment B raw5254 raw5254Labels = mixedMoment B raw5254step0 raw5254step0Labels := by
      have ha : raw5254step0 = (fun i j => raw5254 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5254step0 raw5254; decide +kernel
      have hl : raw5254step0Labels = raw5254Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5254 raw5254Labels permutation182 permutation3
    _ = mixedMoment B node3165 node3165Labels := by rfl

def raw5255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5255Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5255step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw5255step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5255 raw5255Labels = mixedMoment B node3146 node3146Labels := by
  calc
    mixedMoment B raw5255 raw5255Labels = mixedMoment B raw5255step0 raw5255step0Labels := by
      have ha : raw5255step0 = (fun i j => raw5255 (permutation206 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5255step0 raw5255; decide +kernel
      have hl : raw5255step0Labels = raw5255Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5255 raw5255Labels permutation206 permutation3
    _ = mixedMoment B node3146 node3146Labels := by rfl

def raw5256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]
def raw5256Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw5256step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5256step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5256step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5256 raw5256Labels = mixedMoment B node3222 node3222Labels := by
  calc
    mixedMoment B raw5256 raw5256Labels = mixedMoment B raw5256step0 raw5256step0Labels := by
      have hz : ∀ j, raw5256 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5256step0 = (fun i j => raw5256 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5256step0 raw5256; decide +kernel
      have hl : raw5256step0Labels = raw5256Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5256 raw5256Labels permutation520 hz
    mixedMoment B raw5256step0 raw5256step0Labels = mixedMoment B raw5256step1 raw5256step1Labels := by
      have ha : raw5256step1 = (fun i j => raw5256step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5256step1 raw5256step0; decide +kernel
      have hl : raw5256step1Labels = raw5256step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5256step0 raw5256step0Labels permutation46 permutation3
    _ = mixedMoment B node3222 node3222Labels := by rfl

def raw5257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw5257Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5257step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw5257step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5257 raw5257Labels = mixedMoment B node3221 node3221Labels := by
  calc
    mixedMoment B raw5257 raw5257Labels = mixedMoment B raw5257step0 raw5257step0Labels := by
      have ha : raw5257step0 = (fun i j => raw5257 (permutation206 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5257step0 raw5257; decide +kernel
      have hl : raw5257step0Labels = raw5257Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5257 raw5257Labels permutation206 permutation3
    _ = mixedMoment B node3221 node3221Labels := by rfl

def raw5258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5258Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5258step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5258step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw5258step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5258 raw5258Labels = mixedMoment B node1367 node1367Labels := by
  calc
    mixedMoment B raw5258 raw5258Labels = mixedMoment B raw5258step0 raw5258step0Labels := by
      have hz : ∀ j, raw5258 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5258step0 = (fun i j => raw5258 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5258step0 raw5258; decide +kernel
      have hl : raw5258step0Labels = raw5258Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5258 raw5258Labels permutation265 hz
    mixedMoment B raw5258step0 raw5258step0Labels = mixedMoment B raw5258step1 raw5258step1Labels := by
      have ha : raw5258step1 = (fun i j => raw5258step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5258step1 raw5258step0; decide +kernel
      have hl : raw5258step1Labels = raw5258step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5258step0 raw5258step0Labels permutation38 permutation3
    _ = mixedMoment B node1367 node1367Labels := by rfl

def raw5259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5259Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5259step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw5259step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5259 raw5259Labels = mixedMoment B node3196 node3196Labels := by
  calc
    mixedMoment B raw5259 raw5259Labels = mixedMoment B raw5259step0 raw5259step0Labels := by
      have ha : raw5259step0 = (fun i j => raw5259 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5259step0 raw5259; decide +kernel
      have hl : raw5259step0Labels = raw5259Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5259 raw5259Labels permutation158 permutation3
    _ = mixedMoment B node3196 node3196Labels := by rfl

def raw5260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5260Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5260step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5260step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw5260step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5260 raw5260Labels = mixedMoment B node3156 node3156Labels := by
  calc
    mixedMoment B raw5260 raw5260Labels = mixedMoment B raw5260step0 raw5260step0Labels := by
      have hz : ∀ j, raw5260 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5260step0 = (fun i j => raw5260 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5260step0 raw5260; decide +kernel
      have hl : raw5260step0Labels = raw5260Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5260 raw5260Labels permutation265 hz
    mixedMoment B raw5260step0 raw5260step0Labels = mixedMoment B raw5260step1 raw5260step1Labels := by
      have ha : raw5260step1 = (fun i j => raw5260step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5260step1 raw5260step0; decide +kernel
      have hl : raw5260step1Labels = raw5260step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5260step0 raw5260step0Labels permutation38 permutation3
    _ = mixedMoment B node3156 node3156Labels := by rfl

def raw5261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]
def raw5261Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw5261step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5261step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw5261step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5261step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw5261step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5261 raw5261Labels = mixedMoment B node3224 node3224Labels := by
  calc
    mixedMoment B raw5261 raw5261Labels = mixedMoment B raw5261step0 raw5261step0Labels := by
      have hz : ∀ j, raw5261 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5261step0 = (fun i j => raw5261 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5261step0 raw5261; decide +kernel
      have hl : raw5261step0Labels = raw5261Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5261 raw5261Labels permutation520 hz
    mixedMoment B raw5261step0 raw5261step0Labels = mixedMoment B raw5261step1 raw5261step1Labels := by
      have hz : ∀ j, raw5261step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5261step1 = (fun i j => raw5261step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5261step1 raw5261step0; decide +kernel
      have hl : raw5261step1Labels = raw5261step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5261step0 raw5261step0Labels permutation56 hz
    mixedMoment B raw5261step1 raw5261step1Labels = mixedMoment B raw5261step2 raw5261step2Labels := by
      have ha : raw5261step2 = (fun i j => raw5261step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5261step2 raw5261step1; decide +kernel
      have hl : raw5261step2Labels = raw5261step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5261step1 raw5261step1Labels permutation10 permutation3
    _ = mixedMoment B node3224 node3224Labels := by rfl

def raw5262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw5262Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5262step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw5262step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5262step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw5262step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5262 raw5262Labels = mixedMoment B node3223 node3223Labels := by
  calc
    mixedMoment B raw5262 raw5262Labels = mixedMoment B raw5262step0 raw5262step0Labels := by
      have hz : ∀ j, raw5262 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5262step0 = (fun i j => raw5262 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5262step0 raw5262; decide +kernel
      have hl : raw5262step0Labels = raw5262Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5262 raw5262Labels permutation265 hz
    mixedMoment B raw5262step0 raw5262step0Labels = mixedMoment B raw5262step1 raw5262step1Labels := by
      have ha : raw5262step1 = (fun i j => raw5262step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5262step1 raw5262step0; decide +kernel
      have hl : raw5262step1Labels = raw5262step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5262step0 raw5262step0Labels permutation38 permutation3
    _ = mixedMoment B node3223 node3223Labels := by rfl

def raw5263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5263Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5263step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5263step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5263step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5263 raw5263Labels = mixedMoment B node1406 node1406Labels := by
  calc
    mixedMoment B raw5263 raw5263Labels = mixedMoment B raw5263step0 raw5263step0Labels := by
      have hz : ∀ j, raw5263 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5263step0 = (fun i j => raw5263 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5263step0 raw5263; decide +kernel
      have hl : raw5263step0Labels = raw5263Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5263 raw5263Labels permutation265 hz
    mixedMoment B raw5263step0 raw5263step0Labels = mixedMoment B raw5263step1 raw5263step1Labels := by
      have ha : raw5263step1 = (fun i j => raw5263step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5263step1 raw5263step0; decide +kernel
      have hl : raw5263step1Labels = raw5263step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5263step0 raw5263step0Labels permutation32 permutation3
    _ = mixedMoment B node1406 node1406Labels := by rfl

def raw5264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5264Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5264step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5264step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5264 raw5264Labels = mixedMoment B node3202 node3202Labels := by
  calc
    mixedMoment B raw5264 raw5264Labels = mixedMoment B raw5264step0 raw5264step0Labels := by
      have ha : raw5264step0 = (fun i j => raw5264 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5264step0 raw5264; decide +kernel
      have hl : raw5264step0Labels = raw5264Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5264 raw5264Labels permutation152 permutation3
    _ = mixedMoment B node3202 node3202Labels := by rfl

def raw5265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5265Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5265step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5265step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5265step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5265step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5265 raw5265Labels = mixedMoment B node3180 node3180Labels := by
  calc
    mixedMoment B raw5265 raw5265Labels = mixedMoment B raw5265step0 raw5265step0Labels := by
      have hz : ∀ j, raw5265 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5265step0 = (fun i j => raw5265 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5265step0 raw5265; decide +kernel
      have hl : raw5265step0Labels = raw5265Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5265 raw5265Labels permutation265 hz
    mixedMoment B raw5265step0 raw5265step0Labels = mixedMoment B raw5265step1 raw5265step1Labels := by
      have ha : raw5265step1 = (fun i j => raw5265step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5265step1 raw5265step0; decide +kernel
      have hl : raw5265step1Labels = raw5265step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5265step0 raw5265step0Labels permutation32 permutation3
    _ = mixedMoment B node3180 node3180Labels := by rfl

def raw5266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![0, 0, 0], ![2, -2, 0]]
def raw5266Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5266step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw5266step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5266step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw5266step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5266step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 0, 1], ![-2, 1, 1]]
def raw5266step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5266step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw5266step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5266 raw5266Labels = mixedMoment B node3225 node3225Labels := by
  calc
    mixedMoment B raw5266 raw5266Labels = mixedMoment B raw5266step0 raw5266step0Labels := by
      have hz : ∀ j, raw5266 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5266step0 = (fun i j => raw5266 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5266step0 raw5266; decide +kernel
      have hl : raw5266step0Labels = raw5266Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5266 raw5266Labels permutation520 hz
    mixedMoment B raw5266step0 raw5266step0Labels = mixedMoment B raw5266step1 raw5266step1Labels := by
      have hz : ∀ j, raw5266step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5266step1 = (fun i j => raw5266step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5266step1 raw5266step0; decide +kernel
      have hl : raw5266step1Labels = raw5266step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5266step0 raw5266step0Labels permutation56 hz
    mixedMoment B raw5266step1 raw5266step1Labels = mixedMoment B raw5266step2 raw5266step2Labels := by
      have ha : raw5266step2 = (fun i j => raw5266step1 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5266step2 raw5266step1; decide +kernel
      have hl : raw5266step2Labels = raw5266step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5266step1 raw5266step1Labels permutation12 permutation6
    mixedMoment B raw5266step2 raw5266step2Labels = mixedMoment B raw5266step3 raw5266step3Labels := by
      have ha : raw5266step3 = -raw5266step2 := by apply Matrix.ext; change ∀ i j, raw5266step3 i j = -(raw5266step2 i j); unfold raw5266step3 raw5266step2; decide +kernel
      have hl : raw5266step3Labels = raw5266step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3225 node3225Labels := by rfl

def raw5267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw5267Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw5267step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5267step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw5267step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5267step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw5267step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5267 raw5267Labels = mixedMoment B node3227 node3227Labels := by
  calc
    mixedMoment B raw5267 raw5267Labels = mixedMoment B raw5267step0 raw5267step0Labels := by
      have hz : ∀ j, raw5267 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5267step0 = (fun i j => raw5267 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5267step0 raw5267; decide +kernel
      have hl : raw5267step0Labels = raw5267Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5267 raw5267Labels permutation265 hz
    mixedMoment B raw5267step0 raw5267step0Labels = mixedMoment B raw5267step1 raw5267step1Labels := by
      have ha : raw5267step1 = (fun i j => raw5267step0 (permutation48 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5267step1 raw5267step0; decide +kernel
      have hl : raw5267step1Labels = raw5267step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5267step0 raw5267step0Labels permutation48 permutation6
    mixedMoment B raw5267step1 raw5267step1Labels = mixedMoment B raw5267step2 raw5267step2Labels := by
      have ha : raw5267step2 = -raw5267step1 := by apply Matrix.ext; change ∀ i j, raw5267step2 i j = -(raw5267step1 i j); unfold raw5267step2 raw5267step1; decide +kernel
      have hl : raw5267step2Labels = raw5267step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3227 node3227Labels := by rfl

def raw5268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw5268Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw5268step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5268step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw5268step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5268 raw5268Labels = mixedMoment B node1356 node1356Labels := by
  calc
    mixedMoment B raw5268 raw5268Labels = mixedMoment B raw5268step0 raw5268step0Labels := by
      have hz : ∀ j, raw5268 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5268step0 = (fun i j => raw5268 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5268step0 raw5268; decide +kernel
      have hl : raw5268step0Labels = raw5268Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5268 raw5268Labels permutation265 hz
    mixedMoment B raw5268step0 raw5268step0Labels = mixedMoment B raw5268step1 raw5268step1Labels := by
      have ha : raw5268step1 = (fun i j => raw5268step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5268step1 raw5268step0; decide +kernel
      have hl : raw5268step1Labels = raw5268step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5268step0 raw5268step0Labels permutation38 permutation3
    _ = mixedMoment B node1356 node1356Labels := by rfl

def raw5269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw5269Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5269step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw5269step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5269 raw5269Labels = mixedMoment B node3193 node3193Labels := by
  calc
    mixedMoment B raw5269 raw5269Labels = mixedMoment B raw5269step0 raw5269step0Labels := by
      have ha : raw5269step0 = (fun i j => raw5269 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5269step0 raw5269; decide +kernel
      have hl : raw5269step0Labels = raw5269Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5269 raw5269Labels permutation158 permutation3
    _ = mixedMoment B node3193 node3193Labels := by rfl

def raw5270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw5270Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5270step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw5270step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5270step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw5270step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5270 raw5270Labels = mixedMoment B node3166 node3166Labels := by
  calc
    mixedMoment B raw5270 raw5270Labels = mixedMoment B raw5270step0 raw5270step0Labels := by
      have hz : ∀ j, raw5270 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5270step0 = (fun i j => raw5270 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5270step0 raw5270; decide +kernel
      have hl : raw5270step0Labels = raw5270Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5270 raw5270Labels permutation265 hz
    mixedMoment B raw5270step0 raw5270step0Labels = mixedMoment B raw5270step1 raw5270step1Labels := by
      have ha : raw5270step1 = (fun i j => raw5270step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5270step1 raw5270step0; decide +kernel
      have hl : raw5270step1Labels = raw5270step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5270step0 raw5270step0Labels permutation32 permutation3
    _ = mixedMoment B node3166 node3166Labels := by rfl

def raw5271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 3, -2], ![2, -2, 0], ![2, -2, 0]]
def raw5271Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5271step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 3, -2], ![2, -2, 0], ![2, -2, 0]]
def raw5271step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5271step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw5271step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5271 raw5271Labels = mixedMoment B node3147 node3147Labels := by
  calc
    mixedMoment B raw5271 raw5271Labels = mixedMoment B raw5271step0 raw5271step0Labels := by
      have hz : ∀ j, raw5271 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5271step0 = (fun i j => raw5271 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5271step0 raw5271; decide +kernel
      have hl : raw5271step0Labels = raw5271Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5271 raw5271Labels permutation265 hz
    mixedMoment B raw5271step0 raw5271step0Labels = mixedMoment B raw5271step1 raw5271step1Labels := by
      have ha : raw5271step1 = (fun i j => raw5271step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5271step1 raw5271step0; decide +kernel
      have hl : raw5271step1Labels = raw5271step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5271step0 raw5271step0Labels permutation38 permutation3
    _ = mixedMoment B node3147 node3147Labels := by rfl

def raw5272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0]]
def raw5272Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0]]
def raw5272step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5272step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw5272step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5272 raw5272Labels = mixedMoment B node3222 node3222Labels := by
  calc
    mixedMoment B raw5272 raw5272Labels = mixedMoment B raw5272step0 raw5272step0Labels := by
      have hz : ∀ j, raw5272 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5272step0 = (fun i j => raw5272 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5272step0 raw5272; decide +kernel
      have hl : raw5272step0Labels = raw5272Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5272 raw5272Labels permutation265 hz
    mixedMoment B raw5272step0 raw5272step0Labels = mixedMoment B raw5272step1 raw5272step1Labels := by
      have ha : raw5272step1 = (fun i j => raw5272step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5272step1 raw5272step0; decide +kernel
      have hl : raw5272step1Labels = raw5272step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5272step0 raw5272step0Labels permutation39 permutation3
    _ = mixedMoment B node3222 node3222Labels := by rfl

def raw5273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw5273Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw5273step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5273step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw5273step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5273 raw5273Labels = mixedMoment B node1355 node1355Labels := by
  calc
    mixedMoment B raw5273 raw5273Labels = mixedMoment B raw5273step0 raw5273step0Labels := by
      have hz : ∀ j, raw5273 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5273step0 = (fun i j => raw5273 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5273step0 raw5273; decide +kernel
      have hl : raw5273step0Labels = raw5273Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5273 raw5273Labels permutation265 hz
    mixedMoment B raw5273step0 raw5273step0Labels = mixedMoment B raw5273step1 raw5273step1Labels := by
      have ha : raw5273step1 = (fun i j => raw5273step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5273step1 raw5273step0; decide +kernel
      have hl : raw5273step1Labels = raw5273step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5273step0 raw5273step0Labels permutation38 permutation3
    _ = mixedMoment B node1355 node1355Labels := by rfl

def raw5274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw5274Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5274step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-3, 3, 0]]
def raw5274step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5274step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![3, -3, 0]]
def raw5274step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5274 raw5274Labels = mixedMoment B node1903 node1903Labels := by
  calc
    mixedMoment B raw5274 raw5274Labels = mixedMoment B raw5274step0 raw5274step0Labels := by
      have ha : raw5274step0 = (fun i j => raw5274 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5274step0 raw5274; decide +kernel
      have hl : raw5274step0Labels = raw5274Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5274 raw5274Labels permutation682 permutation3
    mixedMoment B raw5274step0 raw5274step0Labels = mixedMoment B raw5274step1 raw5274step1Labels := by
      have ha : raw5274step1 = -raw5274step0 := by apply Matrix.ext; change ∀ i j, raw5274step1 i j = -(raw5274step0 i j); unfold raw5274step1 raw5274step0; decide +kernel
      have hl : raw5274step1Labels = raw5274step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1903 node1903Labels := by rfl

def raw5275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw5275Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5275step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw5275step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5275step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![-3, 3, 0]]
def raw5275step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5275step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![3, -3, 0]]
def raw5275step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5275 raw5275Labels = mixedMoment B node1927 node1927Labels := by
  calc
    mixedMoment B raw5275 raw5275Labels = mixedMoment B raw5275step0 raw5275step0Labels := by
      have hz : ∀ j, raw5275 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5275step0 = (fun i j => raw5275 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5275step0 raw5275; decide +kernel
      have hl : raw5275step0Labels = raw5275Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5275 raw5275Labels permutation265 hz
    mixedMoment B raw5275step0 raw5275step0Labels = mixedMoment B raw5275step1 raw5275step1Labels := by
      have ha : raw5275step1 = (fun i j => raw5275step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5275step1 raw5275step0; decide +kernel
      have hl : raw5275step1Labels = raw5275step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5275step0 raw5275step0Labels permutation151 permutation3
    mixedMoment B raw5275step1 raw5275step1Labels = mixedMoment B raw5275step2 raw5275step2Labels := by
      have ha : raw5275step2 = -raw5275step1 := by apply Matrix.ext; change ∀ i j, raw5275step2 i j = -(raw5275step1 i j); unfold raw5275step2 raw5275step1; decide +kernel
      have hl : raw5275step2Labels = raw5275step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1927 node1927Labels := by rfl

def raw5276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 3, -2], ![1, -1, 0], ![3, -3, 0]]
def raw5276Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5276step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 3, -2], ![1, -1, 0], ![3, -3, 0]]
def raw5276step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5276step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -2, 3], ![-3, 3, 0]]
def raw5276step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5276step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![3, -3, 0]]
def raw5276step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5276 raw5276Labels = mixedMoment B node1916 node1916Labels := by
  calc
    mixedMoment B raw5276 raw5276Labels = mixedMoment B raw5276step0 raw5276step0Labels := by
      have hz : ∀ j, raw5276 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5276step0 = (fun i j => raw5276 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5276step0 raw5276; decide +kernel
      have hl : raw5276step0Labels = raw5276Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5276 raw5276Labels permutation265 hz
    mixedMoment B raw5276step0 raw5276step0Labels = mixedMoment B raw5276step1 raw5276step1Labels := by
      have ha : raw5276step1 = (fun i j => raw5276step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5276step1 raw5276step0; decide +kernel
      have hl : raw5276step1Labels = raw5276step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5276step0 raw5276step0Labels permutation149 permutation3
    mixedMoment B raw5276step1 raw5276step1Labels = mixedMoment B raw5276step2 raw5276step2Labels := by
      have ha : raw5276step2 = -raw5276step1 := by apply Matrix.ext; change ∀ i j, raw5276step2 i j = -(raw5276step1 i j); unfold raw5276step2 raw5276step1; decide +kernel
      have hl : raw5276step2Labels = raw5276step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1916 node1916Labels := by rfl

def raw5277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![0, 0, 0], ![3, -3, 0]]
def raw5277Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw5277step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5277step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw5277step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5277step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-3, 3, 0]]
def raw5277step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5277step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw5277step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5277 raw5277Labels = mixedMoment B node2255 node2255Labels := by
  calc
    mixedMoment B raw5277 raw5277Labels = mixedMoment B raw5277step0 raw5277step0Labels := by
      have hz : ∀ j, raw5277 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5277step0 = (fun i j => raw5277 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5277step0 raw5277; decide +kernel
      have hl : raw5277step0Labels = raw5277Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5277 raw5277Labels permutation520 hz
    mixedMoment B raw5277step0 raw5277step0Labels = mixedMoment B raw5277step1 raw5277step1Labels := by
      have hz : ∀ j, raw5277step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5277step1 = (fun i j => raw5277step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5277step1 raw5277step0; decide +kernel
      have hl : raw5277step1Labels = raw5277step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5277step0 raw5277step0Labels permutation56 hz
    mixedMoment B raw5277step1 raw5277step1Labels = mixedMoment B raw5277step2 raw5277step2Labels := by
      have ha : raw5277step2 = (fun i j => raw5277step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5277step2 raw5277step1; decide +kernel
      have hl : raw5277step2Labels = raw5277step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5277step1 raw5277step1Labels permutation29 permutation3
    mixedMoment B raw5277step2 raw5277step2Labels = mixedMoment B raw5277step3 raw5277step3Labels := by
      have ha : raw5277step3 = -raw5277step2 := by apply Matrix.ext; change ∀ i j, raw5277step3 i j = -(raw5277step2 i j); unfold raw5277step3 raw5277step2; decide +kernel
      have hl : raw5277step3Labels = raw5277step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2255 node2255Labels := by rfl

def raw5278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5278Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5278step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw5278step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5278step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5278step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5278step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5278step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5278 raw5278Labels = mixedMoment B node2714 node2714Labels := by
  calc
    mixedMoment B raw5278 raw5278Labels = mixedMoment B raw5278step0 raw5278step0Labels := by
      have ha : raw5278step0 = (fun i j => raw5278 (permutation168 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5278step0 raw5278; decide +kernel
      have hl : raw5278step0Labels = raw5278Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5278 raw5278Labels permutation168 permutation7
    mixedMoment B raw5278step0 raw5278step0Labels = mixedMoment B raw5278step1 raw5278step1Labels := by
      have ha : raw5278step1 = -raw5278step0 := by apply Matrix.ext; change ∀ i j, raw5278step1 i j = -(raw5278step0 i j); unfold raw5278step1 raw5278step0; decide +kernel
      have hl : raw5278step1Labels = raw5278step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5278step1 raw5278step1Labels = mixedMoment B raw5278step2 raw5278step2Labels := by
      have ha : raw5278step2 = raw5278step1 := by apply Matrix.ext; unfold raw5278step2 raw5278step1; decide +kernel
      have hl : raw5278step1Labels = labelEmbedding1 ∘ raw5278step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5278step1 raw5278step1Labels raw5278step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2714 node2714Labels := by rfl

def raw5279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5279Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5279step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5279step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5279step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 2, 0]]
def raw5279step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5279step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw5279step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5279step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw5279step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5279 raw5279Labels = mixedMoment B node2758 node2758Labels := by
  calc
    mixedMoment B raw5279 raw5279Labels = mixedMoment B raw5279step0 raw5279step0Labels := by
      have hz : ∀ j, raw5279 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5279step0 = (fun i j => raw5279 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5279step0 raw5279; decide +kernel
      have hl : raw5279step0Labels = raw5279Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5279 raw5279Labels permutation265 hz
    mixedMoment B raw5279step0 raw5279step0Labels = mixedMoment B raw5279step1 raw5279step1Labels := by
      have ha : raw5279step1 = (fun i j => raw5279step0 (permutation48 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5279step1 raw5279step0; decide +kernel
      have hl : raw5279step1Labels = raw5279step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5279step0 raw5279step0Labels permutation48 permutation7
    mixedMoment B raw5279step1 raw5279step1Labels = mixedMoment B raw5279step2 raw5279step2Labels := by
      have ha : raw5279step2 = -raw5279step1 := by apply Matrix.ext; change ∀ i j, raw5279step2 i j = -(raw5279step1 i j); unfold raw5279step2 raw5279step1; decide +kernel
      have hl : raw5279step2Labels = raw5279step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5279step2 raw5279step2Labels = mixedMoment B raw5279step3 raw5279step3Labels := by
      have ha : raw5279step3 = raw5279step2 := by apply Matrix.ext; unfold raw5279step3 raw5279step2; decide +kernel
      have hl : raw5279step2Labels = labelEmbedding1 ∘ raw5279step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5279step2 raw5279step2Labels raw5279step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2758 node2758Labels := by rfl

def raw5280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5280Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5280step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5280step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 3, -1]]
def raw5280step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5280step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -3, 1]]
def raw5280step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5280step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -3, 1]]
def raw5280step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5280 raw5280Labels = mixedMoment B node2759 node2759Labels := by
  calc
    mixedMoment B raw5280 raw5280Labels = mixedMoment B raw5280step0 raw5280step0Labels := by
      have hz : ∀ j, raw5280 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5280step0 = (fun i j => raw5280 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5280step0 raw5280; decide +kernel
      have hl : raw5280step0Labels = raw5280Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5280 raw5280Labels permutation265 hz
    mixedMoment B raw5280step0 raw5280step0Labels = mixedMoment B raw5280step1 raw5280step1Labels := by
      have ha : raw5280step1 = (fun i j => raw5280step0 (permutation48 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5280step1 raw5280step0; decide +kernel
      have hl : raw5280step1Labels = raw5280step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5280step0 raw5280step0Labels permutation48 permutation7
    mixedMoment B raw5280step1 raw5280step1Labels = mixedMoment B raw5280step2 raw5280step2Labels := by
      have ha : raw5280step2 = -raw5280step1 := by apply Matrix.ext; change ∀ i j, raw5280step2 i j = -(raw5280step1 i j); unfold raw5280step2 raw5280step1; decide +kernel
      have hl : raw5280step2Labels = raw5280step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5280step2 raw5280step2Labels = mixedMoment B raw5280step3 raw5280step3Labels := by
      have ha : raw5280step3 = raw5280step2 := by apply Matrix.ext; unfold raw5280step3 raw5280step2; decide +kernel
      have hl : raw5280step2Labels = labelEmbedding1 ∘ raw5280step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5280step2 raw5280step2Labels raw5280step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2759 node2759Labels := by rfl

def raw5281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]
def raw5281Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5281step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw5281step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5281step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw5281step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5281step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw5281step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5281step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5281step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5281step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5281step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5281 raw5281Labels = mixedMoment B node2776 node2776Labels := by
  calc
    mixedMoment B raw5281 raw5281Labels = mixedMoment B raw5281step0 raw5281step0Labels := by
      have hz : ∀ j, raw5281 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5281step0 = (fun i j => raw5281 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5281step0 raw5281; decide +kernel
      have hl : raw5281step0Labels = raw5281Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5281 raw5281Labels permutation520 hz
    mixedMoment B raw5281step0 raw5281step0Labels = mixedMoment B raw5281step1 raw5281step1Labels := by
      have hz : ∀ j, raw5281step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5281step1 = (fun i j => raw5281step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5281step1 raw5281step0; decide +kernel
      have hl : raw5281step1Labels = raw5281step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5281step0 raw5281step0Labels permutation56 hz
    mixedMoment B raw5281step1 raw5281step1Labels = mixedMoment B raw5281step2 raw5281step2Labels := by
      have ha : raw5281step2 = (fun i j => raw5281step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5281step2 raw5281step1; decide +kernel
      have hl : raw5281step2Labels = raw5281step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5281step1 raw5281step1Labels permutation12 permutation7
    mixedMoment B raw5281step2 raw5281step2Labels = mixedMoment B raw5281step3 raw5281step3Labels := by
      have ha : raw5281step3 = -raw5281step2 := by apply Matrix.ext; change ∀ i j, raw5281step3 i j = -(raw5281step2 i j); unfold raw5281step3 raw5281step2; decide +kernel
      have hl : raw5281step3Labels = raw5281step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5281step3 raw5281step3Labels = mixedMoment B raw5281step4 raw5281step4Labels := by
      have ha : raw5281step4 = raw5281step3 := by apply Matrix.ext; unfold raw5281step4 raw5281step3; decide +kernel
      have hl : raw5281step3Labels = labelEmbedding1 ∘ raw5281step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5281step3 raw5281step3Labels raw5281step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2776 node2776Labels := by rfl

def raw5282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw5282Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw5282step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5282step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw5282step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5282step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5282step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5282step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5282step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5282 raw5282Labels = mixedMoment B node2753 node2753Labels := by
  calc
    mixedMoment B raw5282 raw5282Labels = mixedMoment B raw5282step0 raw5282step0Labels := by
      have hz : ∀ j, raw5282 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5282step0 = (fun i j => raw5282 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5282step0 raw5282; decide +kernel
      have hl : raw5282step0Labels = raw5282Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5282 raw5282Labels permutation265 hz
    mixedMoment B raw5282step0 raw5282step0Labels = mixedMoment B raw5282step1 raw5282step1Labels := by
      have ha : raw5282step1 = (fun i j => raw5282step0 (permutation48 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5282step1 raw5282step0; decide +kernel
      have hl : raw5282step1Labels = raw5282step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5282step0 raw5282step0Labels permutation48 permutation7
    mixedMoment B raw5282step1 raw5282step1Labels = mixedMoment B raw5282step2 raw5282step2Labels := by
      have ha : raw5282step2 = -raw5282step1 := by apply Matrix.ext; change ∀ i j, raw5282step2 i j = -(raw5282step1 i j); unfold raw5282step2 raw5282step1; decide +kernel
      have hl : raw5282step2Labels = raw5282step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5282step2 raw5282step2Labels = mixedMoment B raw5282step3 raw5282step3Labels := by
      have ha : raw5282step3 = raw5282step2 := by apply Matrix.ext; unfold raw5282step3 raw5282step2; decide +kernel
      have hl : raw5282step2Labels = labelEmbedding1 ∘ raw5282step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5282step2 raw5282step2Labels raw5282step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2753 node2753Labels := by rfl

def raw5283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5283Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5283step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw5283step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5283step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5283step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5283step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5283step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5283 raw5283Labels = mixedMoment B node1701 node1701Labels := by
  calc
    mixedMoment B raw5283 raw5283Labels = mixedMoment B raw5283step0 raw5283step0Labels := by
      have ha : raw5283step0 = (fun i j => raw5283 (permutation168 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5283step0 raw5283; decide +kernel
      have hl : raw5283step0Labels = raw5283Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5283 raw5283Labels permutation168 permutation7
    mixedMoment B raw5283step0 raw5283step0Labels = mixedMoment B raw5283step1 raw5283step1Labels := by
      have ha : raw5283step1 = -raw5283step0 := by apply Matrix.ext; change ∀ i j, raw5283step1 i j = -(raw5283step0 i j); unfold raw5283step1 raw5283step0; decide +kernel
      have hl : raw5283step1Labels = raw5283step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5283step1 raw5283step1Labels = mixedMoment B raw5283step2 raw5283step2Labels := by
      have ha : raw5283step2 = raw5283step1 := by apply Matrix.ext; unfold raw5283step2 raw5283step1; decide +kernel
      have hl : raw5283step1Labels = labelEmbedding1 ∘ raw5283step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5283step1 raw5283step1Labels raw5283step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1701 node1701Labels := by rfl

def raw5284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5284Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5284step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 2, 0]]
def raw5284step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5284step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw5284step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5284step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw5284step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5284 raw5284Labels = mixedMoment B node2236 node2236Labels := by
  calc
    mixedMoment B raw5284 raw5284Labels = mixedMoment B raw5284step0 raw5284step0Labels := by
      have ha : raw5284step0 = (fun i j => raw5284 (permutation168 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5284step0 raw5284; decide +kernel
      have hl : raw5284step0Labels = raw5284Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5284 raw5284Labels permutation168 permutation7
    mixedMoment B raw5284step0 raw5284step0Labels = mixedMoment B raw5284step1 raw5284step1Labels := by
      have ha : raw5284step1 = -raw5284step0 := by apply Matrix.ext; change ∀ i j, raw5284step1 i j = -(raw5284step0 i j); unfold raw5284step1 raw5284step0; decide +kernel
      have hl : raw5284step1Labels = raw5284step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5284step1 raw5284step1Labels = mixedMoment B raw5284step2 raw5284step2Labels := by
      have ha : raw5284step2 = raw5284step1 := by apply Matrix.ext; unfold raw5284step2 raw5284step1; decide +kernel
      have hl : raw5284step1Labels = labelEmbedding1 ∘ raw5284step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5284step1 raw5284step1Labels raw5284step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2236 node2236Labels := by rfl

def raw5285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5285Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5285step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 3, -1]]
def raw5285step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5285step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -3, 1]]
def raw5285step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5285step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -3, 1]]
def raw5285step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5285 raw5285Labels = mixedMoment B node2237 node2237Labels := by
  calc
    mixedMoment B raw5285 raw5285Labels = mixedMoment B raw5285step0 raw5285step0Labels := by
      have ha : raw5285step0 = (fun i j => raw5285 (permutation168 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5285step0 raw5285; decide +kernel
      have hl : raw5285step0Labels = raw5285Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5285 raw5285Labels permutation168 permutation7
    mixedMoment B raw5285step0 raw5285step0Labels = mixedMoment B raw5285step1 raw5285step1Labels := by
      have ha : raw5285step1 = -raw5285step0 := by apply Matrix.ext; change ∀ i j, raw5285step1 i j = -(raw5285step0 i j); unfold raw5285step1 raw5285step0; decide +kernel
      have hl : raw5285step1Labels = raw5285step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5285step1 raw5285step1Labels = mixedMoment B raw5285step2 raw5285step2Labels := by
      have ha : raw5285step2 = raw5285step1 := by apply Matrix.ext; unfold raw5285step2 raw5285step1; decide +kernel
      have hl : raw5285step1Labels = labelEmbedding1 ∘ raw5285step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5285step1 raw5285step1Labels raw5285step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2237 node2237Labels := by rfl

def raw5286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]
def raw5286Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5286step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw5286step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5286step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw5286step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5286step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5286step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5286step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5286step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5286 raw5286Labels = mixedMoment B node2253 node2253Labels := by
  calc
    mixedMoment B raw5286 raw5286Labels = mixedMoment B raw5286step0 raw5286step0Labels := by
      have hz : ∀ j, raw5286 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5286step0 = (fun i j => raw5286 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5286step0 raw5286; decide +kernel
      have hl : raw5286step0Labels = raw5286Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5286 raw5286Labels permutation520 hz
    mixedMoment B raw5286step0 raw5286step0Labels = mixedMoment B raw5286step1 raw5286step1Labels := by
      have ha : raw5286step1 = (fun i j => raw5286step0 (permutation36 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5286step1 raw5286step0; decide +kernel
      have hl : raw5286step1Labels = raw5286step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5286step0 raw5286step0Labels permutation36 permutation7
    mixedMoment B raw5286step1 raw5286step1Labels = mixedMoment B raw5286step2 raw5286step2Labels := by
      have ha : raw5286step2 = -raw5286step1 := by apply Matrix.ext; change ∀ i j, raw5286step2 i j = -(raw5286step1 i j); unfold raw5286step2 raw5286step1; decide +kernel
      have hl : raw5286step2Labels = raw5286step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5286step2 raw5286step2Labels = mixedMoment B raw5286step3 raw5286step3Labels := by
      have ha : raw5286step3 = raw5286step2 := by apply Matrix.ext; unfold raw5286step3 raw5286step2; decide +kernel
      have hl : raw5286step2Labels = labelEmbedding1 ∘ raw5286step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5286step2 raw5286step2Labels raw5286step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2253 node2253Labels := by rfl

def raw5287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw5287Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5287step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw5287step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5287step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5287step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5287step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5287step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5287 raw5287Labels = mixedMoment B node2233 node2233Labels := by
  calc
    mixedMoment B raw5287 raw5287Labels = mixedMoment B raw5287step0 raw5287step0Labels := by
      have ha : raw5287step0 = (fun i j => raw5287 (permutation168 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5287step0 raw5287; decide +kernel
      have hl : raw5287step0Labels = raw5287Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5287 raw5287Labels permutation168 permutation7
    mixedMoment B raw5287step0 raw5287step0Labels = mixedMoment B raw5287step1 raw5287step1Labels := by
      have ha : raw5287step1 = -raw5287step0 := by apply Matrix.ext; change ∀ i j, raw5287step1 i j = -(raw5287step0 i j); unfold raw5287step1 raw5287step0; decide +kernel
      have hl : raw5287step1Labels = raw5287step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5287step1 raw5287step1Labels = mixedMoment B raw5287step2 raw5287step2Labels := by
      have ha : raw5287step2 = raw5287step1 := by apply Matrix.ext; unfold raw5287step2 raw5287step1; decide +kernel
      have hl : raw5287step1Labels = labelEmbedding1 ∘ raw5287step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5287step1 raw5287step1Labels raw5287step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2233 node2233Labels := by rfl

def raw5288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5288Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5288step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5288step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5288step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw5288step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5288step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw5288step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5288step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw5288step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5288 raw5288Labels = mixedMoment B node1715 node1715Labels := by
  calc
    mixedMoment B raw5288 raw5288Labels = mixedMoment B raw5288step0 raw5288step0Labels := by
      have hz : ∀ j, raw5288 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5288step0 = (fun i j => raw5288 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5288step0 raw5288; decide +kernel
      have hl : raw5288step0Labels = raw5288Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5288 raw5288Labels permutation265 hz
    mixedMoment B raw5288step0 raw5288step0Labels = mixedMoment B raw5288step1 raw5288step1Labels := by
      have ha : raw5288step1 = (fun i j => raw5288step0 (permutation48 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5288step1 raw5288step0; decide +kernel
      have hl : raw5288step1Labels = raw5288step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5288step0 raw5288step0Labels permutation48 permutation7
    mixedMoment B raw5288step1 raw5288step1Labels = mixedMoment B raw5288step2 raw5288step2Labels := by
      have ha : raw5288step2 = -raw5288step1 := by apply Matrix.ext; change ∀ i j, raw5288step2 i j = -(raw5288step1 i j); unfold raw5288step2 raw5288step1; decide +kernel
      have hl : raw5288step2Labels = raw5288step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5288step2 raw5288step2Labels = mixedMoment B raw5288step3 raw5288step3Labels := by
      have ha : raw5288step3 = raw5288step2 := by apply Matrix.ext; unfold raw5288step3 raw5288step2; decide +kernel
      have hl : raw5288step2Labels = labelEmbedding1 ∘ raw5288step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5288step2 raw5288step2Labels raw5288step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1715 node1715Labels := by rfl

def raw5289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5289Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5289step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw5289step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5289step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw5289step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5289step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw5289step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5289 raw5289Labels = mixedMoment B node2196 node2196Labels := by
  calc
    mixedMoment B raw5289 raw5289Labels = mixedMoment B raw5289step0 raw5289step0Labels := by
      have ha : raw5289step0 = (fun i j => raw5289 (permutation168 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5289step0 raw5289; decide +kernel
      have hl : raw5289step0Labels = raw5289Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5289 raw5289Labels permutation168 permutation7
    mixedMoment B raw5289step0 raw5289step0Labels = mixedMoment B raw5289step1 raw5289step1Labels := by
      have ha : raw5289step1 = -raw5289step0 := by apply Matrix.ext; change ∀ i j, raw5289step1 i j = -(raw5289step0 i j); unfold raw5289step1 raw5289step0; decide +kernel
      have hl : raw5289step1Labels = raw5289step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5289step1 raw5289step1Labels = mixedMoment B raw5289step2 raw5289step2Labels := by
      have ha : raw5289step2 = raw5289step1 := by apply Matrix.ext; unfold raw5289step2 raw5289step1; decide +kernel
      have hl : raw5289step1Labels = labelEmbedding1 ∘ raw5289step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5289step1 raw5289step1Labels raw5289step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2196 node2196Labels := by rfl

def raw5290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5290Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5290step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5290step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5290step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 3, -1]]
def raw5290step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5290step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw5290step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5290step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw5290step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5290 raw5290Labels = mixedMoment B node2254 node2254Labels := by
  calc
    mixedMoment B raw5290 raw5290Labels = mixedMoment B raw5290step0 raw5290step0Labels := by
      have hz : ∀ j, raw5290 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5290step0 = (fun i j => raw5290 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5290step0 raw5290; decide +kernel
      have hl : raw5290step0Labels = raw5290Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5290 raw5290Labels permutation265 hz
    mixedMoment B raw5290step0 raw5290step0Labels = mixedMoment B raw5290step1 raw5290step1Labels := by
      have ha : raw5290step1 = (fun i j => raw5290step0 (permutation48 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5290step1 raw5290step0; decide +kernel
      have hl : raw5290step1Labels = raw5290step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5290step0 raw5290step0Labels permutation48 permutation7
    mixedMoment B raw5290step1 raw5290step1Labels = mixedMoment B raw5290step2 raw5290step2Labels := by
      have ha : raw5290step2 = -raw5290step1 := by apply Matrix.ext; change ∀ i j, raw5290step2 i j = -(raw5290step1 i j); unfold raw5290step2 raw5290step1; decide +kernel
      have hl : raw5290step2Labels = raw5290step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5290step2 raw5290step2Labels = mixedMoment B raw5290step3 raw5290step3Labels := by
      have ha : raw5290step3 = raw5290step2 := by apply Matrix.ext; unfold raw5290step3 raw5290step2; decide +kernel
      have hl : raw5290step2Labels = labelEmbedding1 ∘ raw5290step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5290step2 raw5290step2Labels raw5290step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2254 node2254Labels := by rfl

def raw5291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]
def raw5291Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5291step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw5291step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5291step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw5291step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5291step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw5291step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5291step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw5291step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5291step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw5291step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5291 raw5291Labels = mixedMoment B node2279 node2279Labels := by
  calc
    mixedMoment B raw5291 raw5291Labels = mixedMoment B raw5291step0 raw5291step0Labels := by
      have hz : ∀ j, raw5291 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5291step0 = (fun i j => raw5291 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5291step0 raw5291; decide +kernel
      have hl : raw5291step0Labels = raw5291Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5291 raw5291Labels permutation520 hz
    mixedMoment B raw5291step0 raw5291step0Labels = mixedMoment B raw5291step1 raw5291step1Labels := by
      have hz : ∀ j, raw5291step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5291step1 = (fun i j => raw5291step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5291step1 raw5291step0; decide +kernel
      have hl : raw5291step1Labels = raw5291step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5291step0 raw5291step0Labels permutation56 hz
    mixedMoment B raw5291step1 raw5291step1Labels = mixedMoment B raw5291step2 raw5291step2Labels := by
      have ha : raw5291step2 = (fun i j => raw5291step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5291step2 raw5291step1; decide +kernel
      have hl : raw5291step2Labels = raw5291step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5291step1 raw5291step1Labels permutation12 permutation7
    mixedMoment B raw5291step2 raw5291step2Labels = mixedMoment B raw5291step3 raw5291step3Labels := by
      have ha : raw5291step3 = -raw5291step2 := by apply Matrix.ext; change ∀ i j, raw5291step3 i j = -(raw5291step2 i j); unfold raw5291step3 raw5291step2; decide +kernel
      have hl : raw5291step3Labels = raw5291step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5291step3 raw5291step3Labels = mixedMoment B raw5291step4 raw5291step4Labels := by
      have ha : raw5291step4 = raw5291step3 := by apply Matrix.ext; unfold raw5291step4 raw5291step3; decide +kernel
      have hl : raw5291step3Labels = labelEmbedding1 ∘ raw5291step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5291step3 raw5291step3Labels raw5291step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2279 node2279Labels := by rfl

def raw5292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw5292Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5292step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw5292step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5292step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw5292step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5292step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5292step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5292step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw5292step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5292 raw5292Labels = mixedMoment B node2245 node2245Labels := by
  calc
    mixedMoment B raw5292 raw5292Labels = mixedMoment B raw5292step0 raw5292step0Labels := by
      have hz : ∀ j, raw5292 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5292step0 = (fun i j => raw5292 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5292step0 raw5292; decide +kernel
      have hl : raw5292step0Labels = raw5292Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5292 raw5292Labels permutation265 hz
    mixedMoment B raw5292step0 raw5292step0Labels = mixedMoment B raw5292step1 raw5292step1Labels := by
      have ha : raw5292step1 = (fun i j => raw5292step0 (permutation48 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5292step1 raw5292step0; decide +kernel
      have hl : raw5292step1Labels = raw5292step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5292step0 raw5292step0Labels permutation48 permutation7
    mixedMoment B raw5292step1 raw5292step1Labels = mixedMoment B raw5292step2 raw5292step2Labels := by
      have ha : raw5292step2 = -raw5292step1 := by apply Matrix.ext; change ∀ i j, raw5292step2 i j = -(raw5292step1 i j); unfold raw5292step2 raw5292step1; decide +kernel
      have hl : raw5292step2Labels = raw5292step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5292step2 raw5292step2Labels = mixedMoment B raw5292step3 raw5292step3Labels := by
      have ha : raw5292step3 = raw5292step2 := by apply Matrix.ext; unfold raw5292step3 raw5292step2; decide +kernel
      have hl : raw5292step2Labels = labelEmbedding1 ∘ raw5292step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5292step2 raw5292step2Labels raw5292step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2245 node2245Labels := by rfl

def raw5293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5293Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5293step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5293step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw5293step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5293step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw5293step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5293step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw5293step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5293 raw5293Labels = mixedMoment B node1714 node1714Labels := by
  calc
    mixedMoment B raw5293 raw5293Labels = mixedMoment B raw5293step0 raw5293step0Labels := by
      have hz : ∀ j, raw5293 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5293step0 = (fun i j => raw5293 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5293step0 raw5293; decide +kernel
      have hl : raw5293step0Labels = raw5293Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5293 raw5293Labels permutation265 hz
    mixedMoment B raw5293step0 raw5293step0Labels = mixedMoment B raw5293step1 raw5293step1Labels := by
      have ha : raw5293step1 = (fun i j => raw5293step0 (permutation48 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5293step1 raw5293step0; decide +kernel
      have hl : raw5293step1Labels = raw5293step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5293step0 raw5293step0Labels permutation48 permutation7
    mixedMoment B raw5293step1 raw5293step1Labels = mixedMoment B raw5293step2 raw5293step2Labels := by
      have ha : raw5293step2 = -raw5293step1 := by apply Matrix.ext; change ∀ i j, raw5293step2 i j = -(raw5293step1 i j); unfold raw5293step2 raw5293step1; decide +kernel
      have hl : raw5293step2Labels = raw5293step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5293step2 raw5293step2Labels = mixedMoment B raw5293step3 raw5293step3Labels := by
      have ha : raw5293step3 = raw5293step2 := by apply Matrix.ext; unfold raw5293step3 raw5293step2; decide +kernel
      have hl : raw5293step2Labels = labelEmbedding1 ∘ raw5293step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5293step2 raw5293step2Labels raw5293step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1714 node1714Labels := by rfl

def raw5294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5294Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5294step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw5294step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5294step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw5294step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5294step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw5294step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5294 raw5294Labels = mixedMoment B node2195 node2195Labels := by
  calc
    mixedMoment B raw5294 raw5294Labels = mixedMoment B raw5294step0 raw5294step0Labels := by
      have ha : raw5294step0 = (fun i j => raw5294 (permutation168 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5294step0 raw5294; decide +kernel
      have hl : raw5294step0Labels = raw5294Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5294 raw5294Labels permutation168 permutation7
    mixedMoment B raw5294step0 raw5294step0Labels = mixedMoment B raw5294step1 raw5294step1Labels := by
      have ha : raw5294step1 = -raw5294step0 := by apply Matrix.ext; change ∀ i j, raw5294step1 i j = -(raw5294step0 i j); unfold raw5294step1 raw5294step0; decide +kernel
      have hl : raw5294step1Labels = raw5294step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5294step1 raw5294step1Labels = mixedMoment B raw5294step2 raw5294step2Labels := by
      have ha : raw5294step2 = raw5294step1 := by apply Matrix.ext; unfold raw5294step2 raw5294step1; decide +kernel
      have hl : raw5294step1Labels = labelEmbedding1 ∘ raw5294step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5294step1 raw5294step1Labels raw5294step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2195 node2195Labels := by rfl

def raw5295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5295Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5295step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5295step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5295step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw5295step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5295step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw5295step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5295step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw5295step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5295 raw5295Labels = mixedMoment B node2251 node2251Labels := by
  calc
    mixedMoment B raw5295 raw5295Labels = mixedMoment B raw5295step0 raw5295step0Labels := by
      have hz : ∀ j, raw5295 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5295step0 = (fun i j => raw5295 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5295step0 raw5295; decide +kernel
      have hl : raw5295step0Labels = raw5295Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5295 raw5295Labels permutation265 hz
    mixedMoment B raw5295step0 raw5295step0Labels = mixedMoment B raw5295step1 raw5295step1Labels := by
      have ha : raw5295step1 = (fun i j => raw5295step0 (permutation48 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5295step1 raw5295step0; decide +kernel
      have hl : raw5295step1Labels = raw5295step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5295step0 raw5295step0Labels permutation48 permutation7
    mixedMoment B raw5295step1 raw5295step1Labels = mixedMoment B raw5295step2 raw5295step2Labels := by
      have ha : raw5295step2 = -raw5295step1 := by apply Matrix.ext; change ∀ i j, raw5295step2 i j = -(raw5295step1 i j); unfold raw5295step2 raw5295step1; decide +kernel
      have hl : raw5295step2Labels = raw5295step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5295step2 raw5295step2Labels = mixedMoment B raw5295step3 raw5295step3Labels := by
      have ha : raw5295step3 = raw5295step2 := by apply Matrix.ext; unfold raw5295step3 raw5295step2; decide +kernel
      have hl : raw5295step2Labels = labelEmbedding1 ∘ raw5295step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5295step2 raw5295step2Labels raw5295step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2251 node2251Labels := by rfl

def raw5296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![0, 0, 0], ![2, -2, 0]]
def raw5296Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5296step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw5296step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5296step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw5296step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5296step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw5296step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5296step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw5296step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5296step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw5296step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5296 raw5296Labels = mixedMoment B node2278 node2278Labels := by
  calc
    mixedMoment B raw5296 raw5296Labels = mixedMoment B raw5296step0 raw5296step0Labels := by
      have hz : ∀ j, raw5296 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5296step0 = (fun i j => raw5296 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5296step0 raw5296; decide +kernel
      have hl : raw5296step0Labels = raw5296Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5296 raw5296Labels permutation520 hz
    mixedMoment B raw5296step0 raw5296step0Labels = mixedMoment B raw5296step1 raw5296step1Labels := by
      have hz : ∀ j, raw5296step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5296step1 = (fun i j => raw5296step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5296step1 raw5296step0; decide +kernel
      have hl : raw5296step1Labels = raw5296step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5296step0 raw5296step0Labels permutation56 hz
    mixedMoment B raw5296step1 raw5296step1Labels = mixedMoment B raw5296step2 raw5296step2Labels := by
      have ha : raw5296step2 = (fun i j => raw5296step1 (permutation12 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5296step2 raw5296step1; decide +kernel
      have hl : raw5296step2Labels = raw5296step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5296step1 raw5296step1Labels permutation12 permutation7
    mixedMoment B raw5296step2 raw5296step2Labels = mixedMoment B raw5296step3 raw5296step3Labels := by
      have ha : raw5296step3 = -raw5296step2 := by apply Matrix.ext; change ∀ i j, raw5296step3 i j = -(raw5296step2 i j); unfold raw5296step3 raw5296step2; decide +kernel
      have hl : raw5296step3Labels = raw5296step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5296step3 raw5296step3Labels = mixedMoment B raw5296step4 raw5296step4Labels := by
      have ha : raw5296step4 = raw5296step3 := by apply Matrix.ext; unfold raw5296step4 raw5296step3; decide +kernel
      have hl : raw5296step3Labels = labelEmbedding1 ∘ raw5296step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5296step3 raw5296step3Labels raw5296step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2278 node2278Labels := by rfl

def raw5297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw5297Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw5297step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5297step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw5297step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5297step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw5297step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5297step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw5297step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5297 raw5297Labels = mixedMoment B node2244 node2244Labels := by
  calc
    mixedMoment B raw5297 raw5297Labels = mixedMoment B raw5297step0 raw5297step0Labels := by
      have hz : ∀ j, raw5297 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5297step0 = (fun i j => raw5297 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5297step0 raw5297; decide +kernel
      have hl : raw5297step0Labels = raw5297Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5297 raw5297Labels permutation265 hz
    mixedMoment B raw5297step0 raw5297step0Labels = mixedMoment B raw5297step1 raw5297step1Labels := by
      have ha : raw5297step1 = (fun i j => raw5297step0 (permutation48 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5297step1 raw5297step0; decide +kernel
      have hl : raw5297step1Labels = raw5297step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5297step0 raw5297step0Labels permutation48 permutation7
    mixedMoment B raw5297step1 raw5297step1Labels = mixedMoment B raw5297step2 raw5297step2Labels := by
      have ha : raw5297step2 = -raw5297step1 := by apply Matrix.ext; change ∀ i j, raw5297step2 i j = -(raw5297step1 i j); unfold raw5297step2 raw5297step1; decide +kernel
      have hl : raw5297step2Labels = raw5297step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5297step2 raw5297step2Labels = mixedMoment B raw5297step3 raw5297step3Labels := by
      have ha : raw5297step3 = raw5297step2 := by apply Matrix.ext; unfold raw5297step3 raw5297step2; decide +kernel
      have hl : raw5297step2Labels = labelEmbedding1 ∘ raw5297step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5297step2 raw5297step2Labels raw5297step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2244 node2244Labels := by rfl

def raw5298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw5298Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw5298step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5298step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -2, 2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw5298step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5298step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5298step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5298step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5298step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5298 raw5298Labels = mixedMoment B node1732 node1732Labels := by
  calc
    mixedMoment B raw5298 raw5298Labels = mixedMoment B raw5298step0 raw5298step0Labels := by
      have hz : ∀ j, raw5298 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5298step0 = (fun i j => raw5298 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5298step0 raw5298; decide +kernel
      have hl : raw5298step0Labels = raw5298Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5298 raw5298Labels permutation265 hz
    mixedMoment B raw5298step0 raw5298step0Labels = mixedMoment B raw5298step1 raw5298step1Labels := by
      have ha : raw5298step1 = (fun i j => raw5298step0 (permutation48 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5298step1 raw5298step0; decide +kernel
      have hl : raw5298step1Labels = raw5298step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5298step0 raw5298step0Labels permutation48 permutation7
    mixedMoment B raw5298step1 raw5298step1Labels = mixedMoment B raw5298step2 raw5298step2Labels := by
      have ha : raw5298step2 = -raw5298step1 := by apply Matrix.ext; change ∀ i j, raw5298step2 i j = -(raw5298step1 i j); unfold raw5298step2 raw5298step1; decide +kernel
      have hl : raw5298step2Labels = raw5298step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5298step2 raw5298step2Labels = mixedMoment B raw5298step3 raw5298step3Labels := by
      have ha : raw5298step3 = raw5298step2 := by apply Matrix.ext; unfold raw5298step3 raw5298step2; decide +kernel
      have hl : raw5298step2Labels = labelEmbedding1 ∘ raw5298step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5298step2 raw5298step2Labels raw5298step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1732 node1732Labels := by rfl

def raw5299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw5299Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5299step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw5299step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5299step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5299step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5299step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5299step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5299 raw5299Labels = mixedMoment B node2209 node2209Labels := by
  calc
    mixedMoment B raw5299 raw5299Labels = mixedMoment B raw5299step0 raw5299step0Labels := by
      have ha : raw5299step0 = (fun i j => raw5299 (permutation168 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5299step0 raw5299; decide +kernel
      have hl : raw5299step0Labels = raw5299Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5299 raw5299Labels permutation168 permutation7
    mixedMoment B raw5299step0 raw5299step0Labels = mixedMoment B raw5299step1 raw5299step1Labels := by
      have ha : raw5299step1 = -raw5299step0 := by apply Matrix.ext; change ∀ i j, raw5299step1 i j = -(raw5299step0 i j); unfold raw5299step1 raw5299step0; decide +kernel
      have hl : raw5299step1Labels = raw5299step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5299step1 raw5299step1Labels = mixedMoment B raw5299step2 raw5299step2Labels := by
      have ha : raw5299step2 = raw5299step1 := by apply Matrix.ext; unfold raw5299step2 raw5299step1; decide +kernel
      have hl : raw5299step1Labels = labelEmbedding1 ∘ raw5299step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5299step1 raw5299step1Labels raw5299step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2209 node2209Labels := by rfl

def raw5300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw5300Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw5300step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5300step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![0, -2, 2], ![-1, 2, -1], ![-2, 2, 0]]
def raw5300step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5300step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw5300step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5300step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 2, -2], ![1, -2, 1], ![2, -2, 0]]
def raw5300step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5300 raw5300Labels = mixedMoment B node2270 node2270Labels := by
  calc
    mixedMoment B raw5300 raw5300Labels = mixedMoment B raw5300step0 raw5300step0Labels := by
      have hz : ∀ j, raw5300 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5300step0 = (fun i j => raw5300 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5300step0 raw5300; decide +kernel
      have hl : raw5300step0Labels = raw5300Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5300 raw5300Labels permutation265 hz
    mixedMoment B raw5300step0 raw5300step0Labels = mixedMoment B raw5300step1 raw5300step1Labels := by
      have ha : raw5300step1 = (fun i j => raw5300step0 (permutation48 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5300step1 raw5300step0; decide +kernel
      have hl : raw5300step1Labels = raw5300step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5300step0 raw5300step0Labels permutation48 permutation7
    mixedMoment B raw5300step1 raw5300step1Labels = mixedMoment B raw5300step2 raw5300step2Labels := by
      have ha : raw5300step2 = -raw5300step1 := by apply Matrix.ext; change ∀ i j, raw5300step2 i j = -(raw5300step1 i j); unfold raw5300step2 raw5300step1; decide +kernel
      have hl : raw5300step2Labels = raw5300step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5300step2 raw5300step2Labels = mixedMoment B raw5300step3 raw5300step3Labels := by
      have ha : raw5300step3 = raw5300step2 := by apply Matrix.ext; unfold raw5300step3 raw5300step2; decide +kernel
      have hl : raw5300step2Labels = labelEmbedding1 ∘ raw5300step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5300step2 raw5300step2Labels raw5300step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2270 node2270Labels := by rfl

def raw5301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 3, -2], ![2, -2, 0], ![2, -2, 0]]
def raw5301Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 3, -2], ![2, -2, 0], ![2, -2, 0]]
def raw5301step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5301step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -2, 2], ![0, -2, 2], ![-1, 1, 0], ![-2, 3, -1]]
def raw5301step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5301step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![2, -3, 1]]
def raw5301step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5301step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![2, -3, 1]]
def raw5301step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5301 raw5301Labels = mixedMoment B node2271 node2271Labels := by
  calc
    mixedMoment B raw5301 raw5301Labels = mixedMoment B raw5301step0 raw5301step0Labels := by
      have hz : ∀ j, raw5301 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5301step0 = (fun i j => raw5301 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5301step0 raw5301; decide +kernel
      have hl : raw5301step0Labels = raw5301Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5301 raw5301Labels permutation265 hz
    mixedMoment B raw5301step0 raw5301step0Labels = mixedMoment B raw5301step1 raw5301step1Labels := by
      have ha : raw5301step1 = (fun i j => raw5301step0 (permutation48 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5301step1 raw5301step0; decide +kernel
      have hl : raw5301step1Labels = raw5301step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5301step0 raw5301step0Labels permutation48 permutation7
    mixedMoment B raw5301step1 raw5301step1Labels = mixedMoment B raw5301step2 raw5301step2Labels := by
      have ha : raw5301step2 = -raw5301step1 := by apply Matrix.ext; change ∀ i j, raw5301step2 i j = -(raw5301step1 i j); unfold raw5301step2 raw5301step1; decide +kernel
      have hl : raw5301step2Labels = raw5301step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5301step2 raw5301step2Labels = mixedMoment B raw5301step3 raw5301step3Labels := by
      have ha : raw5301step3 = raw5301step2 := by apply Matrix.ext; unfold raw5301step3 raw5301step2; decide +kernel
      have hl : raw5301step2Labels = labelEmbedding1 ∘ raw5301step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5301step2 raw5301step2Labels raw5301step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2271 node2271Labels := by rfl

def raw5302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0]]
def raw5302Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0]]
def raw5302step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5302step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw5302step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5302step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5302step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5302step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5302step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5302 raw5302Labels = mixedMoment B node2253 node2253Labels := by
  calc
    mixedMoment B raw5302 raw5302Labels = mixedMoment B raw5302step0 raw5302step0Labels := by
      have hz : ∀ j, raw5302 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5302step0 = (fun i j => raw5302 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5302step0 raw5302; decide +kernel
      have hl : raw5302step0Labels = raw5302Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5302 raw5302Labels permutation265 hz
    mixedMoment B raw5302step0 raw5302step0Labels = mixedMoment B raw5302step1 raw5302step1Labels := by
      have ha : raw5302step1 = (fun i j => raw5302step0 (permutation54 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5302step1 raw5302step0; decide +kernel
      have hl : raw5302step1Labels = raw5302step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5302step0 raw5302step0Labels permutation54 permutation7
    mixedMoment B raw5302step1 raw5302step1Labels = mixedMoment B raw5302step2 raw5302step2Labels := by
      have ha : raw5302step2 = -raw5302step1 := by apply Matrix.ext; change ∀ i j, raw5302step2 i j = -(raw5302step1 i j); unfold raw5302step2 raw5302step1; decide +kernel
      have hl : raw5302step2Labels = raw5302step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5302step2 raw5302step2Labels = mixedMoment B raw5302step3 raw5302step3Labels := by
      have ha : raw5302step3 = raw5302step2 := by apply Matrix.ext; unfold raw5302step3 raw5302step2; decide +kernel
      have hl : raw5302step2Labels = labelEmbedding1 ∘ raw5302step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5302step2 raw5302step2Labels raw5302step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2253 node2253Labels := by rfl

def raw5303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw5303Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw5303step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5303step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -3, 3], ![-1, 1, 0], ![-2, 2, 0]]
def raw5303step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5303step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw5303step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5303step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw5303step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5303 raw5303Labels = mixedMoment B node1718 node1718Labels := by
  calc
    mixedMoment B raw5303 raw5303Labels = mixedMoment B raw5303step0 raw5303step0Labels := by
      have hz : ∀ j, raw5303 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5303step0 = (fun i j => raw5303 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5303step0 raw5303; decide +kernel
      have hl : raw5303step0Labels = raw5303Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5303 raw5303Labels permutation265 hz
    mixedMoment B raw5303step0 raw5303step0Labels = mixedMoment B raw5303step1 raw5303step1Labels := by
      have ha : raw5303step1 = (fun i j => raw5303step0 (permutation48 i) (permutation7 j)) := by apply Matrix.ext; unfold raw5303step1 raw5303step0; decide +kernel
      have hl : raw5303step1Labels = raw5303step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5303step0 raw5303step0Labels permutation48 permutation7
    mixedMoment B raw5303step1 raw5303step1Labels = mixedMoment B raw5303step2 raw5303step2Labels := by
      have ha : raw5303step2 = -raw5303step1 := by apply Matrix.ext; change ∀ i j, raw5303step2 i j = -(raw5303step1 i j); unfold raw5303step2 raw5303step1; decide +kernel
      have hl : raw5303step2Labels = raw5303step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5303step2 raw5303step2Labels = mixedMoment B raw5303step3 raw5303step3Labels := by
      have ha : raw5303step3 = raw5303step2 := by apply Matrix.ext; unfold raw5303step3 raw5303step2; decide +kernel
      have hl : raw5303step2Labels = labelEmbedding1 ∘ raw5303step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5303step2 raw5303step2Labels raw5303step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1718 node1718Labels := by rfl

def raw5304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw5304Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5304step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5304step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5304step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5304step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5304 raw5304Labels = mixedMoment B node1931 node1931Labels := by
  calc
    mixedMoment B raw5304 raw5304Labels = mixedMoment B raw5304step0 raw5304step0Labels := by
      have ha : raw5304step0 = (fun i j => raw5304 (permutation667 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5304step0 raw5304; decide +kernel
      have hl : raw5304step0Labels = raw5304Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5304 raw5304Labels permutation667 permutation5
    mixedMoment B raw5304step0 raw5304step0Labels = mixedMoment B raw5304step1 raw5304step1Labels := by
      have ha : raw5304step1 = raw5304step0 := by apply Matrix.ext; unfold raw5304step1 raw5304step0; decide +kernel
      have hl : raw5304step0Labels = labelEmbedding1 ∘ raw5304step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5304step0 raw5304step0Labels raw5304step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1931 node1931Labels := by rfl

def raw5305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw5305Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5305step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw5305step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5305step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![2, -2, 0], ![2, -1, -1]]
def raw5305step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5305step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![2, -2, 0], ![2, -1, -1]]
def raw5305step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5305 raw5305Labels = mixedMoment B node1934 node1934Labels := by
  calc
    mixedMoment B raw5305 raw5305Labels = mixedMoment B raw5305step0 raw5305step0Labels := by
      have hz : ∀ j, raw5305 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5305step0 = (fun i j => raw5305 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5305step0 raw5305; decide +kernel
      have hl : raw5305step0Labels = raw5305Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5305 raw5305Labels permutation265 hz
    mixedMoment B raw5305step0 raw5305step0Labels = mixedMoment B raw5305step1 raw5305step1Labels := by
      have ha : raw5305step1 = (fun i j => raw5305step0 (permutation147 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5305step1 raw5305step0; decide +kernel
      have hl : raw5305step1Labels = raw5305step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5305step0 raw5305step0Labels permutation147 permutation5
    mixedMoment B raw5305step1 raw5305step1Labels = mixedMoment B raw5305step2 raw5305step2Labels := by
      have ha : raw5305step2 = raw5305step1 := by apply Matrix.ext; unfold raw5305step2 raw5305step1; decide +kernel
      have hl : raw5305step1Labels = labelEmbedding1 ∘ raw5305step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5305step1 raw5305step1Labels raw5305step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1934 node1934Labels := by rfl

def raw5306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 3, -2], ![1, -1, 0], ![3, -3, 0]]
def raw5306Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 3, -2], ![1, -1, 0], ![3, -3, 0]]
def raw5306step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5306step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![3, -2, -1]]
def raw5306step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5306step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 3, -3], ![1, -1, 0], ![3, -2, -1]]
def raw5306step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5306 raw5306Labels = mixedMoment B node1932 node1932Labels := by
  calc
    mixedMoment B raw5306 raw5306Labels = mixedMoment B raw5306step0 raw5306step0Labels := by
      have hz : ∀ j, raw5306 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5306step0 = (fun i j => raw5306 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5306step0 raw5306; decide +kernel
      have hl : raw5306step0Labels = raw5306Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5306 raw5306Labels permutation265 hz
    mixedMoment B raw5306step0 raw5306step0Labels = mixedMoment B raw5306step1 raw5306step1Labels := by
      have ha : raw5306step1 = (fun i j => raw5306step0 (permutation146 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5306step1 raw5306step0; decide +kernel
      have hl : raw5306step1Labels = raw5306step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5306step0 raw5306step0Labels permutation146 permutation5
    mixedMoment B raw5306step1 raw5306step1Labels = mixedMoment B raw5306step2 raw5306step2Labels := by
      have ha : raw5306step2 = raw5306step1 := by apply Matrix.ext; unfold raw5306step2 raw5306step1; decide +kernel
      have hl : raw5306step1Labels = labelEmbedding1 ∘ raw5306step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5306step1 raw5306step1Labels raw5306step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1932 node1932Labels := by rfl

def raw5307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![0, 0, 0], ![3, -3, 0]]
def raw5307Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw5307step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5307step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw5307step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw5307step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw5307step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw5307step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 3, -3], ![1, -1, 0], ![2, -2, 0]]
def raw5307step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5307 raw5307Labels = mixedMoment B node2284 node2284Labels := by
  calc
    mixedMoment B raw5307 raw5307Labels = mixedMoment B raw5307step0 raw5307step0Labels := by
      have hz : ∀ j, raw5307 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5307step0 = (fun i j => raw5307 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5307step0 raw5307; decide +kernel
      have hl : raw5307step0Labels = raw5307Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5307 raw5307Labels permutation520 hz
    mixedMoment B raw5307step0 raw5307step0Labels = mixedMoment B raw5307step1 raw5307step1Labels := by
      have hz : ∀ j, raw5307step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5307step1 = (fun i j => raw5307step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5307step1 raw5307step0; decide +kernel
      have hl : raw5307step1Labels = raw5307step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5307step0 raw5307step0Labels permutation56 hz
    mixedMoment B raw5307step1 raw5307step1Labels = mixedMoment B raw5307step2 raw5307step2Labels := by
      have ha : raw5307step2 = (fun i j => raw5307step1 (permutation26 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5307step2 raw5307step1; decide +kernel
      have hl : raw5307step2Labels = raw5307step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5307step1 raw5307step1Labels permutation26 permutation5
    mixedMoment B raw5307step2 raw5307step2Labels = mixedMoment B raw5307step3 raw5307step3Labels := by
      have ha : raw5307step3 = raw5307step2 := by apply Matrix.ext; unfold raw5307step3 raw5307step2; decide +kernel
      have hl : raw5307step2Labels = labelEmbedding1 ∘ raw5307step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5307step2 raw5307step2Labels raw5307step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2284 node2284Labels := by rfl

def raw5308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5308Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5308step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5308 raw5308Labels = mixedMoment B node2253 node2253Labels := by
  calc
    mixedMoment B raw5308 raw5308Labels = mixedMoment B raw5308step0 raw5308step0Labels := by
      have hz : ∀ j, raw5308 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5308step0 = (fun i j => raw5308 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5308step0 raw5308; decide +kernel
      have hl : raw5308step0Labels = raw5308Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5308 raw5308Labels permutation265 hz
    _ = mixedMoment B node2253 node2253Labels := by rfl

def raw5309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5309Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5309 raw5309Labels = mixedMoment B node3528 node3528Labels := by
  calc
    _ = mixedMoment B node3528 node3528Labels := by rfl

def raw5310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5310Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5310step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5310 raw5310Labels = mixedMoment B node3577 node3577Labels := by
  calc
    mixedMoment B raw5310 raw5310Labels = mixedMoment B raw5310step0 raw5310step0Labels := by
      have hz : ∀ j, raw5310 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5310step0 = (fun i j => raw5310 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5310step0 raw5310; decide +kernel
      have hl : raw5310step0Labels = raw5310Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5310 raw5310Labels permutation265 hz
    _ = mixedMoment B node3577 node3577Labels := by rfl

def raw5311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5311Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5311step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5311step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 2, 0]]
def raw5311step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5311step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5311step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5311 raw5311Labels = mixedMoment B node2513 node2513Labels := by
  calc
    mixedMoment B raw5311 raw5311Labels = mixedMoment B raw5311step0 raw5311step0Labels := by
      have hz : ∀ j, raw5311 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5311step0 = (fun i j => raw5311 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5311step0 raw5311; decide +kernel
      have hl : raw5311step0Labels = raw5311Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5311 raw5311Labels permutation265 hz
    mixedMoment B raw5311step0 raw5311step0Labels = mixedMoment B raw5311step1 raw5311step1Labels := by
      have ha : raw5311step1 = (fun i j => raw5311step0 (permutation88 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5311step1 raw5311step0; decide +kernel
      have hl : raw5311step1Labels = raw5311step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5311step0 raw5311step0Labels permutation88 permutation4
    mixedMoment B raw5311step1 raw5311step1Labels = mixedMoment B raw5311step2 raw5311step2Labels := by
      have ha : raw5311step2 = -raw5311step1 := by apply Matrix.ext; change ∀ i j, raw5311step2 i j = -(raw5311step1 i j); unfold raw5311step2 raw5311step1; decide +kernel
      have hl : raw5311step2Labels = raw5311step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2513 node2513Labels := by rfl

def raw5312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]
def raw5312Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw5312step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5312step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw5312step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5312 raw5312Labels = mixedMoment B node3626 node3626Labels := by
  calc
    mixedMoment B raw5312 raw5312Labels = mixedMoment B raw5312step0 raw5312step0Labels := by
      have hz : ∀ j, raw5312 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5312step0 = (fun i j => raw5312 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5312step0 raw5312; decide +kernel
      have hl : raw5312step0Labels = raw5312Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5312 raw5312Labels permutation520 hz
    mixedMoment B raw5312step0 raw5312step0Labels = mixedMoment B raw5312step1 raw5312step1Labels := by
      have hz : ∀ j, raw5312step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5312step1 = (fun i j => raw5312step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5312step1 raw5312step0; decide +kernel
      have hl : raw5312step1Labels = raw5312step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5312step0 raw5312step0Labels permutation56 hz
    _ = mixedMoment B node3626 node3626Labels := by rfl

def raw5313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw5313Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw5313step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5313 raw5313Labels = mixedMoment B node3625 node3625Labels := by
  calc
    mixedMoment B raw5313 raw5313Labels = mixedMoment B raw5313step0 raw5313step0Labels := by
      have hz : ∀ j, raw5313 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5313step0 = (fun i j => raw5313 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5313step0 raw5313; decide +kernel
      have hl : raw5313step0Labels = raw5313Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5313 raw5313Labels permutation265 hz
    _ = mixedMoment B node3625 node3625Labels := by rfl

def raw5314 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![2, -2], ![0, 0], ![0, 0]]
def raw5314Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5314step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![2, -2], ![0, 0]]
def raw5314step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5314step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![0, 0], ![1, -1], ![2, -2]]
def raw5314step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw5314step2 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw5314step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical5314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5314 raw5314Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw5314 raw5314Labels = mixedMoment B raw5314step0 raw5314step0Labels := by
      have hz : ∀ j, raw5314 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw5314step0 = (fun i j => raw5314 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw5314step0 raw5314; decide +kernel
      have hl : raw5314step0Labels = raw5314Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5314 raw5314Labels permutation590 hz
    mixedMoment B raw5314step0 raw5314step0Labels = mixedMoment B raw5314step1 raw5314step1Labels := by
      have hz : ∀ j, raw5314step0 (permutation128 0) j = 0 := by decide +kernel
      have ha : raw5314step1 = (fun i j => raw5314step0 (permutation128 i.succ) j) := by apply Matrix.ext; unfold raw5314step1 raw5314step0; decide +kernel
      have hl : raw5314step1Labels = raw5314step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5314step0 raw5314step0Labels permutation128 hz
    mixedMoment B raw5314step1 raw5314step1Labels = mixedMoment B raw5314step2 raw5314step2Labels := by
      have hz : ∀ j, raw5314step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw5314step2 = (fun i j => raw5314step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw5314step2 raw5314step1; decide +kernel
      have hl : raw5314step2Labels = raw5314step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5314step1 raw5314step1Labels permutation14 hz
    _ = mixedMoment B node4084 node4084Labels := by rfl

def raw5315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5315Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5315step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw5315step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5315 raw5315Labels = mixedMoment B node1028 node1028Labels := by
  calc
    mixedMoment B raw5315 raw5315Labels = mixedMoment B raw5315step0 raw5315step0Labels := by
      have ha : raw5315step0 = (fun i j => raw5315 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5315step0 raw5315; decide +kernel
      have hl : raw5315step0Labels = raw5315Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5315 raw5315Labels permutation182 permutation2
    _ = mixedMoment B node1028 node1028Labels := by rfl

def raw5316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5316Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5316step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5316step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5316step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5316step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5316 raw5316Labels = mixedMoment B node1058 node1058Labels := by
  calc
    mixedMoment B raw5316 raw5316Labels = mixedMoment B raw5316step0 raw5316step0Labels := by
      have hz : ∀ j, raw5316 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5316step0 = (fun i j => raw5316 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5316step0 raw5316; decide +kernel
      have hl : raw5316step0Labels = raw5316Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5316 raw5316Labels permutation265 hz
    mixedMoment B raw5316step0 raw5316step0Labels = mixedMoment B raw5316step1 raw5316step1Labels := by
      have ha : raw5316step1 = (fun i j => raw5316step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5316step1 raw5316step0; decide +kernel
      have hl : raw5316step1Labels = raw5316step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5316step0 raw5316step0Labels permutation40 permutation2
    _ = mixedMoment B node1058 node1058Labels := by rfl

def raw5317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5317Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5317step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5317step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5317step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5317 raw5317Labels = mixedMoment B node1042 node1042Labels := by
  calc
    mixedMoment B raw5317 raw5317Labels = mixedMoment B raw5317step0 raw5317step0Labels := by
      have hz : ∀ j, raw5317 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5317step0 = (fun i j => raw5317 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5317step0 raw5317; decide +kernel
      have hl : raw5317step0Labels = raw5317Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5317 raw5317Labels permutation265 hz
    mixedMoment B raw5317step0 raw5317step0Labels = mixedMoment B raw5317step1 raw5317step1Labels := by
      have ha : raw5317step1 = (fun i j => raw5317step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5317step1 raw5317step0; decide +kernel
      have hl : raw5317step1Labels = raw5317step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5317step0 raw5317step0Labels permutation34 permutation2
    _ = mixedMoment B node1042 node1042Labels := by rfl

def raw5318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw5318Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw5318step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5318 raw5318Labels = mixedMoment B node1030 node1030Labels := by
  calc
    mixedMoment B raw5318 raw5318Labels = mixedMoment B raw5318step0 raw5318step0Labels := by
      have hz : ∀ j, raw5318 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5318step0 = (fun i j => raw5318 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5318step0 raw5318; decide +kernel
      have hl : raw5318step0Labels = raw5318Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5318 raw5318Labels permutation265 hz
    _ = mixedMoment B node1030 node1030Labels := by rfl

def raw5319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw5319Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw5319step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5319 raw5319Labels = mixedMoment B node1029 node1029Labels := by
  calc
    mixedMoment B raw5319 raw5319Labels = mixedMoment B raw5319step0 raw5319step0Labels := by
      have hz : ∀ j, raw5319 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5319step0 = (fun i j => raw5319 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5319step0 raw5319; decide +kernel
      have hl : raw5319step0Labels = raw5319Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5319 raw5319Labels permutation265 hz
    _ = mixedMoment B node1029 node1029Labels := by rfl

def raw5320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5320Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5320step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw5320step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5320 raw5320Labels = mixedMoment B node2095 node2095Labels := by
  calc
    mixedMoment B raw5320 raw5320Labels = mixedMoment B raw5320step0 raw5320step0Labels := by
      have ha : raw5320step0 = (fun i j => raw5320 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5320step0 raw5320; decide +kernel
      have hl : raw5320step0Labels = raw5320Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5320 raw5320Labels permutation182 permutation2
    _ = mixedMoment B node2095 node2095Labels := by rfl

def raw5321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5321Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5321step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw5321step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5321 raw5321Labels = mixedMoment B node2124 node2124Labels := by
  calc
    mixedMoment B raw5321 raw5321Labels = mixedMoment B raw5321step0 raw5321step0Labels := by
      have ha : raw5321step0 = (fun i j => raw5321 (permutation206 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5321step0 raw5321; decide +kernel
      have hl : raw5321step0Labels = raw5321Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5321 raw5321Labels permutation206 permutation2
    _ = mixedMoment B node2124 node2124Labels := by rfl

def raw5322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]
def raw5322Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5322step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw5322step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5322step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5322step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5322 raw5322Labels = mixedMoment B node2253 node2253Labels := by
  calc
    mixedMoment B raw5322 raw5322Labels = mixedMoment B raw5322step0 raw5322step0Labels := by
      have hz : ∀ j, raw5322 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5322step0 = (fun i j => raw5322 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5322step0 raw5322; decide +kernel
      have hl : raw5322step0Labels = raw5322Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5322 raw5322Labels permutation520 hz
    mixedMoment B raw5322step0 raw5322step0Labels = mixedMoment B raw5322step1 raw5322step1Labels := by
      have ha : raw5322step1 = (fun i j => raw5322step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5322step1 raw5322step0; decide +kernel
      have hl : raw5322step1Labels = raw5322step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5322step0 raw5322step0Labels permutation40 permutation2
    _ = mixedMoment B node2253 node2253Labels := by rfl

def raw5323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, -1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw5323Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5323step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw5323step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5323 raw5323Labels = mixedMoment B node2252 node2252Labels := by
  calc
    mixedMoment B raw5323 raw5323Labels = mixedMoment B raw5323step0 raw5323step0Labels := by
      have ha : raw5323step0 = (fun i j => raw5323 (permutation182 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5323step0 raw5323; decide +kernel
      have hl : raw5323step0Labels = raw5323Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5323 raw5323Labels permutation182 permutation2
    _ = mixedMoment B node2252 node2252Labels := by rfl

def raw5324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5324Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5324step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5324step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5324 raw5324Labels = mixedMoment B node2034 node2034Labels := by
  calc
    mixedMoment B raw5324 raw5324Labels = mixedMoment B raw5324step0 raw5324step0Labels := by
      have ha : raw5324step0 = (fun i j => raw5324 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5324step0 raw5324; decide +kernel
      have hl : raw5324step0Labels = raw5324Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5324 raw5324Labels permutation160 permutation2
    _ = mixedMoment B node2034 node2034Labels := by rfl

def raw5325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5325Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5325step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5325step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5325 raw5325Labels = mixedMoment B node2021 node2021Labels := by
  calc
    mixedMoment B raw5325 raw5325Labels = mixedMoment B raw5325step0 raw5325step0Labels := by
      have ha : raw5325step0 = (fun i j => raw5325 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5325step0 raw5325; decide +kernel
      have hl : raw5325step0Labels = raw5325Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5325 raw5325Labels permutation154 permutation2
    _ = mixedMoment B node2021 node2021Labels := by rfl

def raw5326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw5326Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5326 raw5326Labels = mixedMoment B node2014 node2014Labels := by
  calc
    _ = mixedMoment B node2014 node2014Labels := by rfl

def raw5327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw5327Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5327 raw5327Labels = mixedMoment B node2013 node2013Labels := by
  calc
    _ = mixedMoment B node2013 node2013Labels := by rfl

def raw5328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5328Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5328step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5328step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5328step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5328step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5328 raw5328Labels = mixedMoment B node2133 node2133Labels := by
  calc
    mixedMoment B raw5328 raw5328Labels = mixedMoment B raw5328step0 raw5328step0Labels := by
      have hz : ∀ j, raw5328 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5328step0 = (fun i j => raw5328 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5328step0 raw5328; decide +kernel
      have hl : raw5328step0Labels = raw5328Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5328 raw5328Labels permutation265 hz
    mixedMoment B raw5328step0 raw5328step0Labels = mixedMoment B raw5328step1 raw5328step1Labels := by
      have ha : raw5328step1 = (fun i j => raw5328step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5328step1 raw5328step0; decide +kernel
      have hl : raw5328step1Labels = raw5328step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5328step0 raw5328step0Labels permutation40 permutation2
    _ = mixedMoment B node2133 node2133Labels := by rfl

def raw5329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]
def raw5329Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw5329step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5329step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw5329step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5329step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw5329step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5329 raw5329Labels = mixedMoment B node2279 node2279Labels := by
  calc
    mixedMoment B raw5329 raw5329Labels = mixedMoment B raw5329step0 raw5329step0Labels := by
      have hz : ∀ j, raw5329 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5329step0 = (fun i j => raw5329 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5329step0 raw5329; decide +kernel
      have hl : raw5329step0Labels = raw5329Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5329 raw5329Labels permutation520 hz
    mixedMoment B raw5329step0 raw5329step0Labels = mixedMoment B raw5329step1 raw5329step1Labels := by
      have hz : ∀ j, raw5329step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5329step1 = (fun i j => raw5329step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5329step1 raw5329step0; decide +kernel
      have hl : raw5329step1Labels = raw5329step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5329step0 raw5329step0Labels permutation56 hz
    mixedMoment B raw5329step1 raw5329step1Labels = mixedMoment B raw5329step2 raw5329step2Labels := by
      have ha : raw5329step2 = (fun i j => raw5329step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5329step2 raw5329step1; decide +kernel
      have hl : raw5329step2Labels = raw5329step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5329step1 raw5329step1Labels permutation10 permutation2
    _ = mixedMoment B node2279 node2279Labels := by rfl

def raw5330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![1, 0, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw5330Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw5330step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5330step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw5330step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5330 raw5330Labels = mixedMoment B node2277 node2277Labels := by
  calc
    mixedMoment B raw5330 raw5330Labels = mixedMoment B raw5330step0 raw5330step0Labels := by
      have hz : ∀ j, raw5330 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5330step0 = (fun i j => raw5330 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5330step0 raw5330; decide +kernel
      have hl : raw5330step0Labels = raw5330Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5330 raw5330Labels permutation265 hz
    mixedMoment B raw5330step0 raw5330step0Labels = mixedMoment B raw5330step1 raw5330step1Labels := by
      have ha : raw5330step1 = (fun i j => raw5330step0 (permutation41 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5330step1 raw5330step0; decide +kernel
      have hl : raw5330step1Labels = raw5330step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5330step0 raw5330step0Labels permutation41 permutation2
    _ = mixedMoment B node2277 node2277Labels := by rfl

def raw5331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5331Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5331step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5331step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5331step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5331 raw5331Labels = mixedMoment B node2108 node2108Labels := by
  calc
    mixedMoment B raw5331 raw5331Labels = mixedMoment B raw5331step0 raw5331step0Labels := by
      have hz : ∀ j, raw5331 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5331step0 = (fun i j => raw5331 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5331step0 raw5331; decide +kernel
      have hl : raw5331step0Labels = raw5331Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5331 raw5331Labels permutation265 hz
    mixedMoment B raw5331step0 raw5331step0Labels = mixedMoment B raw5331step1 raw5331step1Labels := by
      have ha : raw5331step1 = (fun i j => raw5331step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5331step1 raw5331step0; decide +kernel
      have hl : raw5331step1Labels = raw5331step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5331step0 raw5331step0Labels permutation34 permutation2
    _ = mixedMoment B node2108 node2108Labels := by rfl

def raw5332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw5332Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5332step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw5332step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5332 raw5332Labels = mixedMoment B node2097 node2097Labels := by
  calc
    mixedMoment B raw5332 raw5332Labels = mixedMoment B raw5332step0 raw5332step0Labels := by
      have hz : ∀ j, raw5332 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5332step0 = (fun i j => raw5332 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5332step0 raw5332; decide +kernel
      have hl : raw5332step0Labels = raw5332Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5332 raw5332Labels permutation265 hz
    _ = mixedMoment B node2097 node2097Labels := by rfl

def raw5333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw5333Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5333step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw5333step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5333 raw5333Labels = mixedMoment B node2096 node2096Labels := by
  calc
    mixedMoment B raw5333 raw5333Labels = mixedMoment B raw5333step0 raw5333step0Labels := by
      have hz : ∀ j, raw5333 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5333step0 = (fun i j => raw5333 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5333step0 raw5333; decide +kernel
      have hl : raw5333step0Labels = raw5333Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5333 raw5333Labels permutation265 hz
    _ = mixedMoment B node2096 node2096Labels := by rfl

def raw5334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![0, 0, 0], ![2, -2, 0]]
def raw5334Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5334step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw5334step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5334step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw5334step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5334 raw5334Labels = mixedMoment B node2266 node2266Labels := by
  calc
    mixedMoment B raw5334 raw5334Labels = mixedMoment B raw5334step0 raw5334step0Labels := by
      have hz : ∀ j, raw5334 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw5334step0 = (fun i j => raw5334 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw5334step0 raw5334; decide +kernel
      have hl : raw5334step0Labels = raw5334Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5334 raw5334Labels permutation520 hz
    mixedMoment B raw5334step0 raw5334step0Labels = mixedMoment B raw5334step1 raw5334step1Labels := by
      have hz : ∀ j, raw5334step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw5334step1 = (fun i j => raw5334step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw5334step1 raw5334step0; decide +kernel
      have hl : raw5334step1Labels = raw5334step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5334step0 raw5334step0Labels permutation56 hz
    _ = mixedMoment B node2266 node2266Labels := by rfl

def raw5335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw5335Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw5335step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5335step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw5335step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5335 raw5335Labels = mixedMoment B node2262 node2262Labels := by
  calc
    mixedMoment B raw5335 raw5335Labels = mixedMoment B raw5335step0 raw5335step0Labels := by
      have hz : ∀ j, raw5335 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5335step0 = (fun i j => raw5335 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5335step0 raw5335; decide +kernel
      have hl : raw5335step0Labels = raw5335Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5335 raw5335Labels permutation265 hz
    mixedMoment B raw5335step0 raw5335step0Labels = mixedMoment B raw5335step1 raw5335step1Labels := by
      have ha : raw5335step1 = (fun i j => raw5335step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5335step1 raw5335step0; decide +kernel
      have hl : raw5335step1Labels = raw5335step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5335step0 raw5335step0Labels permutation35 permutation2
    _ = mixedMoment B node2262 node2262Labels := by rfl

def raw5336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 3, -2], ![2, -2, 0], ![2, -2, 0]]
def raw5336Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5336step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 3, -2], ![2, -2, 0], ![2, -2, 0]]
def raw5336step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5336step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 1, -1], ![2, -2, 0], ![2, -2, 0]]
def raw5336step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5336 raw5336Labels = mixedMoment B node2126 node2126Labels := by
  calc
    mixedMoment B raw5336 raw5336Labels = mixedMoment B raw5336step0 raw5336step0Labels := by
      have hz : ∀ j, raw5336 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5336step0 = (fun i j => raw5336 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5336step0 raw5336; decide +kernel
      have hl : raw5336step0Labels = raw5336Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5336 raw5336Labels permutation265 hz
    mixedMoment B raw5336step0 raw5336step0Labels = mixedMoment B raw5336step1 raw5336step1Labels := by
      have ha : raw5336step1 = (fun i j => raw5336step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5336step1 raw5336step0; decide +kernel
      have hl : raw5336step1Labels = raw5336step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5336step0 raw5336step0Labels permutation38 permutation2
    _ = mixedMoment B node2126 node2126Labels := by rfl

def raw5337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![-1, 3, -2], ![1, -1, 0], ![3, -3, 0]]
def raw5337Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 3, -2], ![1, -1, 0], ![3, -3, 0]]
def raw5337step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5337step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, 1, -1], ![1, -1, 0], ![3, -3, 0]]
def raw5337step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5337 raw5337Labels = mixedMoment B node2125 node2125Labels := by
  calc
    mixedMoment B raw5337 raw5337Labels = mixedMoment B raw5337step0 raw5337step0Labels := by
      have hz : ∀ j, raw5337 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5337step0 = (fun i j => raw5337 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5337step0 raw5337; decide +kernel
      have hl : raw5337step0Labels = raw5337Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5337 raw5337Labels permutation265 hz
    mixedMoment B raw5337step0 raw5337step0Labels = mixedMoment B raw5337step1 raw5337step1Labels := by
      have ha : raw5337step1 = (fun i j => raw5337step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5337step1 raw5337step0; decide +kernel
      have hl : raw5337step1Labels = raw5337step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5337step0 raw5337step0Labels permutation38 permutation2
    _ = mixedMoment B node2125 node2125Labels := by rfl

def raw5338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 0, 0], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0]]
def raw5338Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5338step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0]]
def raw5338step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5338step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5338step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5338 raw5338Labels = mixedMoment B node2253 node2253Labels := by
  calc
    mixedMoment B raw5338 raw5338Labels = mixedMoment B raw5338step0 raw5338step0Labels := by
      have hz : ∀ j, raw5338 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5338step0 = (fun i j => raw5338 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5338step0 raw5338; decide +kernel
      have hl : raw5338step0Labels = raw5338Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5338 raw5338Labels permutation265 hz
    mixedMoment B raw5338step0 raw5338step0Labels = mixedMoment B raw5338step1 raw5338step1Labels := by
      have ha : raw5338step1 = (fun i j => raw5338step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5338step1 raw5338step0; decide +kernel
      have hl : raw5338step1Labels = raw5338step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5338step0 raw5338step0Labels permutation33 permutation2
    _ = mixedMoment B node2253 node2253Labels := by rfl

def raw5339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5339Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5339step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw5339step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5339step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5339step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5339 raw5339Labels = mixedMoment B node5407 node5407Labels := by
  calc
    mixedMoment B raw5339 raw5339Labels = mixedMoment B raw5339step0 raw5339step0Labels := by
      have ha : raw5339step0 = (fun i j => raw5339 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5339step0 raw5339; decide +kernel
      have hl : raw5339step0Labels = raw5339Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5339 raw5339Labels permutation682 permutation2
    mixedMoment B raw5339step0 raw5339step0Labels = mixedMoment B raw5339step1 raw5339step1Labels := by
      have ha : raw5339step1 = -raw5339step0 := by apply Matrix.ext; change ∀ i j, raw5339step1 i j = -(raw5339step0 i j); unfold raw5339step1 raw5339step0; decide +kernel
      have hl : raw5339step1Labels = raw5339step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5407 node5407Labels := by rfl

def raw5340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5340Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5340step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5340step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw5340step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5340step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw5340step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5340 raw5340Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw5340 raw5340Labels = mixedMoment B raw5340step0 raw5340step0Labels := by
      have hz : ∀ j, raw5340 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5340step0 = (fun i j => raw5340 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5340step0 raw5340; decide +kernel
      have hl : raw5340step0Labels = raw5340Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5340 raw5340Labels permutation265 hz
    mixedMoment B raw5340step0 raw5340step0Labels = mixedMoment B raw5340step1 raw5340step1Labels := by
      have ha : raw5340step1 = (fun i j => raw5340step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5340step1 raw5340step0; decide +kernel
      have hl : raw5340step1Labels = raw5340step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5340step0 raw5340step0Labels permutation151 permutation2
    mixedMoment B raw5340step1 raw5340step1Labels = mixedMoment B raw5340step2 raw5340step2Labels := by
      have ha : raw5340step2 = -raw5340step1 := by apply Matrix.ext; change ∀ i j, raw5340step2 i j = -(raw5340step1 i j); unfold raw5340step2 raw5340step1; decide +kernel
      have hl : raw5340step2Labels = raw5340step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5412 node5412Labels := by rfl

def raw5341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5341Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5341step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5341step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5341step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw5341step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5341step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw5341step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5341 raw5341Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw5341 raw5341Labels = mixedMoment B raw5341step0 raw5341step0Labels := by
      have hz : ∀ j, raw5341 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5341step0 = (fun i j => raw5341 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5341step0 raw5341; decide +kernel
      have hl : raw5341step0Labels = raw5341Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5341 raw5341Labels permutation265 hz
    mixedMoment B raw5341step0 raw5341step0Labels = mixedMoment B raw5341step1 raw5341step1Labels := by
      have ha : raw5341step1 = (fun i j => raw5341step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw5341step1 raw5341step0; decide +kernel
      have hl : raw5341step1Labels = raw5341step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5341step0 raw5341step0Labels permutation149 permutation2
    mixedMoment B raw5341step1 raw5341step1Labels = mixedMoment B raw5341step2 raw5341step2Labels := by
      have ha : raw5341step2 = -raw5341step1 := by apply Matrix.ext; change ∀ i j, raw5341step2 i j = -(raw5341step1 i j); unfold raw5341step2 raw5341step1; decide +kernel
      have hl : raw5341step2Labels = raw5341step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw5342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw5342Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5342step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw5342step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5342step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw5342step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5342step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw5342step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5342 raw5342Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw5342 raw5342Labels = mixedMoment B raw5342step0 raw5342step0Labels := by
      have hz : ∀ j, raw5342 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5342step0 = (fun i j => raw5342 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5342step0 raw5342; decide +kernel
      have hl : raw5342step0Labels = raw5342Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5342 raw5342Labels permutation265 hz
    mixedMoment B raw5342step0 raw5342step0Labels = mixedMoment B raw5342step1 raw5342step1Labels := by
      have ha : raw5342step1 = (fun i j => raw5342step0 (permutation91 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5342step1 raw5342step0; decide +kernel
      have hl : raw5342step1Labels = raw5342step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5342step0 raw5342step0Labels permutation91 permutation4
    mixedMoment B raw5342step1 raw5342step1Labels = mixedMoment B raw5342step2 raw5342step2Labels := by
      have ha : raw5342step2 = raw5342step1 := by apply Matrix.ext; unfold raw5342step2 raw5342step1; decide +kernel
      have hl : raw5342step1Labels = labelEmbedding7 ∘ raw5342step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5342step1 raw5342step1Labels raw5342step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

def raw5343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw5343Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5343step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw5343step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5343step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw5343step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw5343step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw5343step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5343 raw5343Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw5343 raw5343Labels = mixedMoment B raw5343step0 raw5343step0Labels := by
      have hz : ∀ j, raw5343 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5343step0 = (fun i j => raw5343 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5343step0 raw5343; decide +kernel
      have hl : raw5343step0Labels = raw5343Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5343 raw5343Labels permutation265 hz
    mixedMoment B raw5343step0 raw5343step0Labels = mixedMoment B raw5343step1 raw5343step1Labels := by
      have ha : raw5343step1 = (fun i j => raw5343step0 (permutation89 i) (permutation4 j)) := by apply Matrix.ext; unfold raw5343step1 raw5343step0; decide +kernel
      have hl : raw5343step1Labels = raw5343step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5343step0 raw5343step0Labels permutation89 permutation4
    mixedMoment B raw5343step1 raw5343step1Labels = mixedMoment B raw5343step2 raw5343step2Labels := by
      have ha : raw5343step2 = raw5343step1 := by apply Matrix.ext; unfold raw5343step2 raw5343step1; decide +kernel
      have hl : raw5343step1Labels = labelEmbedding7 ∘ raw5343step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5343step1 raw5343step1Labels raw5343step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw5344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5344Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5344step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5344step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5344step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5344step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5344 raw5344Labels = mixedMoment B node4258 node4258Labels := by
  calc
    mixedMoment B raw5344 raw5344Labels = mixedMoment B raw5344step0 raw5344step0Labels := by
      have ha : raw5344step0 = (fun i j => raw5344 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5344step0 raw5344; decide +kernel
      have hl : raw5344step0Labels = raw5344Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5344 raw5344Labels permutation184 permutation3
    mixedMoment B raw5344step0 raw5344step0Labels = mixedMoment B raw5344step1 raw5344step1Labels := by
      have ha : raw5344step1 = raw5344step0 := by apply Matrix.ext; unfold raw5344step1 raw5344step0; decide +kernel
      have hl : raw5344step0Labels = labelEmbedding6 ∘ raw5344step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5344step0 raw5344step0Labels raw5344step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4258 node4258Labels := by rfl

def raw5345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5345Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5345step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5345step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5345step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5345step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5345 raw5345Labels = mixedMoment B node4816 node4816Labels := by
  calc
    mixedMoment B raw5345 raw5345Labels = mixedMoment B raw5345step0 raw5345step0Labels := by
      have ha : raw5345step0 = (fun i j => raw5345 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5345step0 raw5345; decide +kernel
      have hl : raw5345step0Labels = raw5345Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5345 raw5345Labels permutation184 permutation3
    mixedMoment B raw5345step0 raw5345step0Labels = mixedMoment B raw5345step1 raw5345step1Labels := by
      have ha : raw5345step1 = raw5345step0 := by apply Matrix.ext; unfold raw5345step1 raw5345step0; decide +kernel
      have hl : raw5345step0Labels = labelEmbedding6 ∘ raw5345step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5345step0 raw5345step0Labels raw5345step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4816 node4816Labels := by rfl

def raw5346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5346Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5346step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5346step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5346step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5346step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5346 raw5346Labels = mixedMoment B node4852 node4852Labels := by
  calc
    mixedMoment B raw5346 raw5346Labels = mixedMoment B raw5346step0 raw5346step0Labels := by
      have ha : raw5346step0 = (fun i j => raw5346 (permutation208 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5346step0 raw5346; decide +kernel
      have hl : raw5346step0Labels = raw5346Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5346 raw5346Labels permutation208 permutation3
    mixedMoment B raw5346step0 raw5346step0Labels = mixedMoment B raw5346step1 raw5346step1Labels := by
      have ha : raw5346step1 = raw5346step0 := by apply Matrix.ext; unfold raw5346step1 raw5346step0; decide +kernel
      have hl : raw5346step0Labels = labelEmbedding6 ∘ raw5346step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5346step0 raw5346step0Labels raw5346step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4852 node4852Labels := by rfl

def raw5347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw5347Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5347step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw5347step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5347step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5347step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5347step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5347step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5347 raw5347Labels = mixedMoment B node4816 node4816Labels := by
  calc
    mixedMoment B raw5347 raw5347Labels = mixedMoment B raw5347step0 raw5347step0Labels := by
      have ha : raw5347step0 = (fun i j => raw5347 (permutation242 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5347step0 raw5347; decide +kernel
      have hl : raw5347step0Labels = raw5347Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5347 raw5347Labels permutation242 permutation5
    mixedMoment B raw5347step0 raw5347step0Labels = mixedMoment B raw5347step1 raw5347step1Labels := by
      have ha : raw5347step1 = -raw5347step0 := by apply Matrix.ext; change ∀ i j, raw5347step1 i j = -(raw5347step0 i j); unfold raw5347step1 raw5347step0; decide +kernel
      have hl : raw5347step1Labels = raw5347step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5347step1 raw5347step1Labels = mixedMoment B raw5347step2 raw5347step2Labels := by
      have ha : raw5347step2 = raw5347step1 := by apply Matrix.ext; unfold raw5347step2 raw5347step1; decide +kernel
      have hl : raw5347step1Labels = labelEmbedding8 ∘ raw5347step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5347step1 raw5347step1Labels raw5347step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4816 node4816Labels := by rfl

def raw5348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw5348Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5348step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw5348step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5348step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5348step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5348step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5348step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5348 raw5348Labels = mixedMoment B node4852 node4852Labels := by
  calc
    mixedMoment B raw5348 raw5348Labels = mixedMoment B raw5348step0 raw5348step0Labels := by
      have ha : raw5348step0 = (fun i j => raw5348 (permutation262 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5348step0 raw5348; decide +kernel
      have hl : raw5348step0Labels = raw5348Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5348 raw5348Labels permutation262 permutation5
    mixedMoment B raw5348step0 raw5348step0Labels = mixedMoment B raw5348step1 raw5348step1Labels := by
      have ha : raw5348step1 = -raw5348step0 := by apply Matrix.ext; change ∀ i j, raw5348step1 i j = -(raw5348step0 i j); unfold raw5348step1 raw5348step0; decide +kernel
      have hl : raw5348step1Labels = raw5348step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5348step1 raw5348step1Labels = mixedMoment B raw5348step2 raw5348step2Labels := by
      have ha : raw5348step2 = raw5348step1 := by apply Matrix.ext; unfold raw5348step2 raw5348step1; decide +kernel
      have hl : raw5348step1Labels = labelEmbedding8 ∘ raw5348step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5348step1 raw5348step1Labels raw5348step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4852 node4852Labels := by rfl

def raw5349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5349Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5349step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5349step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw5349step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5349step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw5349step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5349step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw5349step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5349 raw5349Labels = mixedMoment B node4261 node4261Labels := by
  calc
    mixedMoment B raw5349 raw5349Labels = mixedMoment B raw5349step0 raw5349step0Labels := by
      have hz : ∀ j, raw5349 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5349step0 = (fun i j => raw5349 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5349step0 raw5349; decide +kernel
      have hl : raw5349step0Labels = raw5349Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5349 raw5349Labels permutation265 hz
    mixedMoment B raw5349step0 raw5349step0Labels = mixedMoment B raw5349step1 raw5349step1Labels := by
      have ha : raw5349step1 = (fun i j => raw5349step0 (permutation49 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5349step1 raw5349step0; decide +kernel
      have hl : raw5349step1Labels = raw5349step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5349step0 raw5349step0Labels permutation49 permutation5
    mixedMoment B raw5349step1 raw5349step1Labels = mixedMoment B raw5349step2 raw5349step2Labels := by
      have ha : raw5349step2 = -raw5349step1 := by apply Matrix.ext; change ∀ i j, raw5349step2 i j = -(raw5349step1 i j); unfold raw5349step2 raw5349step1; decide +kernel
      have hl : raw5349step2Labels = raw5349step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5349step2 raw5349step2Labels = mixedMoment B raw5349step3 raw5349step3Labels := by
      have ha : raw5349step3 = raw5349step2 := by apply Matrix.ext; unfold raw5349step3 raw5349step2; decide +kernel
      have hl : raw5349step2Labels = labelEmbedding8 ∘ raw5349step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5349step2 raw5349step2Labels raw5349step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4261 node4261Labels := by rfl

def raw5350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5350Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5350step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw5350step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5350step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw5350step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5350step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw5350step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5350 raw5350Labels = mixedMoment B node4735 node4735Labels := by
  calc
    mixedMoment B raw5350 raw5350Labels = mixedMoment B raw5350step0 raw5350step0Labels := by
      have ha : raw5350step0 = (fun i j => raw5350 (permutation169 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5350step0 raw5350; decide +kernel
      have hl : raw5350step0Labels = raw5350Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5350 raw5350Labels permutation169 permutation5
    mixedMoment B raw5350step0 raw5350step0Labels = mixedMoment B raw5350step1 raw5350step1Labels := by
      have ha : raw5350step1 = -raw5350step0 := by apply Matrix.ext; change ∀ i j, raw5350step1 i j = -(raw5350step0 i j); unfold raw5350step1 raw5350step0; decide +kernel
      have hl : raw5350step1Labels = raw5350step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5350step1 raw5350step1Labels = mixedMoment B raw5350step2 raw5350step2Labels := by
      have ha : raw5350step2 = raw5350step1 := by apply Matrix.ext; unfold raw5350step2 raw5350step1; decide +kernel
      have hl : raw5350step1Labels = labelEmbedding8 ∘ raw5350step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5350step1 raw5350step1Labels raw5350step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4735 node4735Labels := by rfl

def raw5351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5351Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5351step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5351step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5351step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5351step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5351step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5351step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5351 raw5351Labels = mixedMoment B node4867 node4867Labels := by
  calc
    mixedMoment B raw5351 raw5351Labels = mixedMoment B raw5351step0 raw5351step0Labels := by
      have hz : ∀ j, raw5351 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5351step0 = (fun i j => raw5351 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5351step0 raw5351; decide +kernel
      have hl : raw5351step0Labels = raw5351Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5351 raw5351Labels permutation265 hz
    mixedMoment B raw5351step0 raw5351step0Labels = mixedMoment B raw5351step1 raw5351step1Labels := by
      have ha : raw5351step1 = (fun i j => raw5351step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5351step1 raw5351step0; decide +kernel
      have hl : raw5351step1Labels = raw5351step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5351step0 raw5351step0Labels permutation40 permutation3
    mixedMoment B raw5351step1 raw5351step1Labels = mixedMoment B raw5351step2 raw5351step2Labels := by
      have ha : raw5351step2 = raw5351step1 := by apply Matrix.ext; unfold raw5351step2 raw5351step1; decide +kernel
      have hl : raw5351step1Labels = labelEmbedding6 ∘ raw5351step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5351step1 raw5351step1Labels raw5351step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4867 node4867Labels := by rfl

def raw5352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -2, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw5352Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5352step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw5352step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5352step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw5352step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5352step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw5352step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5352step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw5352step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5352 raw5352Labels = mixedMoment B node4821 node4821Labels := by
  calc
    mixedMoment B raw5352 raw5352Labels = mixedMoment B raw5352step0 raw5352step0Labels := by
      have hz : ∀ j, raw5352 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5352step0 = (fun i j => raw5352 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5352step0 raw5352; decide +kernel
      have hl : raw5352step0Labels = raw5352Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5352 raw5352Labels permutation265 hz
    mixedMoment B raw5352step0 raw5352step0Labels = mixedMoment B raw5352step1 raw5352step1Labels := by
      have ha : raw5352step1 = (fun i j => raw5352step0 (permutation49 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5352step1 raw5352step0; decide +kernel
      have hl : raw5352step1Labels = raw5352step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5352step0 raw5352step0Labels permutation49 permutation5
    mixedMoment B raw5352step1 raw5352step1Labels = mixedMoment B raw5352step2 raw5352step2Labels := by
      have ha : raw5352step2 = -raw5352step1 := by apply Matrix.ext; change ∀ i j, raw5352step2 i j = -(raw5352step1 i j); unfold raw5352step2 raw5352step1; decide +kernel
      have hl : raw5352step2Labels = raw5352step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5352step2 raw5352step2Labels = mixedMoment B raw5352step3 raw5352step3Labels := by
      have ha : raw5352step3 = raw5352step2 := by apply Matrix.ext; unfold raw5352step3 raw5352step2; decide +kernel
      have hl : raw5352step2Labels = labelEmbedding8 ∘ raw5352step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5352step2 raw5352step2Labels raw5352step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4821 node4821Labels := by rfl

def raw5353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw5353Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5353step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw5353step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5353step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw5353step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5353step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw5353step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5353step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw5353step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5353 raw5353Labels = mixedMoment B node4856 node4856Labels := by
  calc
    mixedMoment B raw5353 raw5353Labels = mixedMoment B raw5353step0 raw5353step0Labels := by
      have hz : ∀ j, raw5353 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5353step0 = (fun i j => raw5353 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5353step0 raw5353; decide +kernel
      have hl : raw5353step0Labels = raw5353Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5353 raw5353Labels permutation265 hz
    mixedMoment B raw5353step0 raw5353step0Labels = mixedMoment B raw5353step1 raw5353step1Labels := by
      have ha : raw5353step1 = (fun i j => raw5353step0 (permutation55 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5353step1 raw5353step0; decide +kernel
      have hl : raw5353step1Labels = raw5353step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5353step0 raw5353step0Labels permutation55 permutation5
    mixedMoment B raw5353step1 raw5353step1Labels = mixedMoment B raw5353step2 raw5353step2Labels := by
      have ha : raw5353step2 = -raw5353step1 := by apply Matrix.ext; change ∀ i j, raw5353step2 i j = -(raw5353step1 i j); unfold raw5353step2 raw5353step1; decide +kernel
      have hl : raw5353step2Labels = raw5353step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5353step2 raw5353step2Labels = mixedMoment B raw5353step3 raw5353step3Labels := by
      have ha : raw5353step3 = raw5353step2 := by apply Matrix.ext; unfold raw5353step3 raw5353step2; decide +kernel
      have hl : raw5353step2Labels = labelEmbedding8 ∘ raw5353step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5353step2 raw5353step2Labels raw5353step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4856 node4856Labels := by rfl

def raw5354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, -1, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5354Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5354step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5354step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5354step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, 0, -4], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw5354step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5354step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw5354step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5354step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw5354step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5354 raw5354Labels = mixedMoment B node4259 node4259Labels := by
  calc
    mixedMoment B raw5354 raw5354Labels = mixedMoment B raw5354step0 raw5354step0Labels := by
      have hz : ∀ j, raw5354 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5354step0 = (fun i j => raw5354 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5354step0 raw5354; decide +kernel
      have hl : raw5354step0Labels = raw5354Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5354 raw5354Labels permutation265 hz
    mixedMoment B raw5354step0 raw5354step0Labels = mixedMoment B raw5354step1 raw5354step1Labels := by
      have ha : raw5354step1 = (fun i j => raw5354step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5354step1 raw5354step0; decide +kernel
      have hl : raw5354step1Labels = raw5354step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5354step0 raw5354step0Labels permutation48 permutation5
    mixedMoment B raw5354step1 raw5354step1Labels = mixedMoment B raw5354step2 raw5354step2Labels := by
      have ha : raw5354step2 = -raw5354step1 := by apply Matrix.ext; change ∀ i j, raw5354step2 i j = -(raw5354step1 i j); unfold raw5354step2 raw5354step1; decide +kernel
      have hl : raw5354step2Labels = raw5354step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5354step2 raw5354step2Labels = mixedMoment B raw5354step3 raw5354step3Labels := by
      have ha : raw5354step3 = raw5354step2 := by apply Matrix.ext; unfold raw5354step3 raw5354step2; decide +kernel
      have hl : raw5354step2Labels = labelEmbedding8 ∘ raw5354step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5354step2 raw5354step2Labels raw5354step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4259 node4259Labels := by rfl

def raw5355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5355Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5355step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw5355step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5355step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw5355step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5355step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw5355step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5355 raw5355Labels = mixedMoment B node4733 node4733Labels := by
  calc
    mixedMoment B raw5355 raw5355Labels = mixedMoment B raw5355step0 raw5355step0Labels := by
      have ha : raw5355step0 = (fun i j => raw5355 (permutation168 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5355step0 raw5355; decide +kernel
      have hl : raw5355step0Labels = raw5355Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5355 raw5355Labels permutation168 permutation5
    mixedMoment B raw5355step0 raw5355step0Labels = mixedMoment B raw5355step1 raw5355step1Labels := by
      have ha : raw5355step1 = -raw5355step0 := by apply Matrix.ext; change ∀ i j, raw5355step1 i j = -(raw5355step0 i j); unfold raw5355step1 raw5355step0; decide +kernel
      have hl : raw5355step1Labels = raw5355step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5355step1 raw5355step1Labels = mixedMoment B raw5355step2 raw5355step2Labels := by
      have ha : raw5355step2 = raw5355step1 := by apply Matrix.ext; unfold raw5355step2 raw5355step1; decide +kernel
      have hl : raw5355step1Labels = labelEmbedding8 ∘ raw5355step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5355step1 raw5355step1Labels raw5355step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4733 node4733Labels := by rfl

def raw5356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5356Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5356step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5356step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5356step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5356step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5356step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5356step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5356 raw5356Labels = mixedMoment B node4836 node4836Labels := by
  calc
    mixedMoment B raw5356 raw5356Labels = mixedMoment B raw5356step0 raw5356step0Labels := by
      have hz : ∀ j, raw5356 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5356step0 = (fun i j => raw5356 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5356step0 raw5356; decide +kernel
      have hl : raw5356step0Labels = raw5356Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5356 raw5356Labels permutation265 hz
    mixedMoment B raw5356step0 raw5356step0Labels = mixedMoment B raw5356step1 raw5356step1Labels := by
      have ha : raw5356step1 = (fun i j => raw5356step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5356step1 raw5356step0; decide +kernel
      have hl : raw5356step1Labels = raw5356step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5356step0 raw5356step0Labels permutation34 permutation3
    mixedMoment B raw5356step1 raw5356step1Labels = mixedMoment B raw5356step2 raw5356step2Labels := by
      have ha : raw5356step2 = raw5356step1 := by apply Matrix.ext; unfold raw5356step2 raw5356step1; decide +kernel
      have hl : raw5356step1Labels = labelEmbedding6 ∘ raw5356step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5356step1 raw5356step1Labels raw5356step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4836 node4836Labels := by rfl

def raw5357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![1, -3, 2], ![0, 1, -1], ![2, 0, -2]]
def raw5357Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5357step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -3, 2], ![0, 1, -1], ![2, 0, -2]]
def raw5357step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5357step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw5357step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5357step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw5357step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5357step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw5357step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5357 raw5357Labels = mixedMoment B node4817 node4817Labels := by
  calc
    mixedMoment B raw5357 raw5357Labels = mixedMoment B raw5357step0 raw5357step0Labels := by
      have hz : ∀ j, raw5357 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5357step0 = (fun i j => raw5357 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5357step0 raw5357; decide +kernel
      have hl : raw5357step0Labels = raw5357Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5357 raw5357Labels permutation265 hz
    mixedMoment B raw5357step0 raw5357step0Labels = mixedMoment B raw5357step1 raw5357step1Labels := by
      have ha : raw5357step1 = (fun i j => raw5357step0 (permutation48 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5357step1 raw5357step0; decide +kernel
      have hl : raw5357step1Labels = raw5357step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5357step0 raw5357step0Labels permutation48 permutation5
    mixedMoment B raw5357step1 raw5357step1Labels = mixedMoment B raw5357step2 raw5357step2Labels := by
      have ha : raw5357step2 = -raw5357step1 := by apply Matrix.ext; change ∀ i j, raw5357step2 i j = -(raw5357step1 i j); unfold raw5357step2 raw5357step1; decide +kernel
      have hl : raw5357step2Labels = raw5357step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5357step2 raw5357step2Labels = mixedMoment B raw5357step3 raw5357step3Labels := by
      have ha : raw5357step3 = raw5357step2 := by apply Matrix.ext; unfold raw5357step3 raw5357step2; decide +kernel
      have hl : raw5357step2Labels = labelEmbedding8 ∘ raw5357step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5357step2 raw5357step2Labels raw5357step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4817 node4817Labels := by rfl

def raw5358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw5358Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw5358step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5358step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-3, 2, 1]]
def raw5358step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5358step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw5358step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5358step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw5358step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5358 raw5358Labels = mixedMoment B node4853 node4853Labels := by
  calc
    mixedMoment B raw5358 raw5358Labels = mixedMoment B raw5358step0 raw5358step0Labels := by
      have hz : ∀ j, raw5358 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5358step0 = (fun i j => raw5358 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5358step0 raw5358; decide +kernel
      have hl : raw5358step0Labels = raw5358Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5358 raw5358Labels permutation265 hz
    mixedMoment B raw5358step0 raw5358step0Labels = mixedMoment B raw5358step1 raw5358step1Labels := by
      have ha : raw5358step1 = (fun i j => raw5358step0 (permutation54 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5358step1 raw5358step0; decide +kernel
      have hl : raw5358step1Labels = raw5358step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5358step0 raw5358step0Labels permutation54 permutation5
    mixedMoment B raw5358step1 raw5358step1Labels = mixedMoment B raw5358step2 raw5358step2Labels := by
      have ha : raw5358step2 = -raw5358step1 := by apply Matrix.ext; change ∀ i j, raw5358step2 i j = -(raw5358step1 i j); unfold raw5358step2 raw5358step1; decide +kernel
      have hl : raw5358step2Labels = raw5358step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5358step2 raw5358step2Labels = mixedMoment B raw5358step3 raw5358step3Labels := by
      have ha : raw5358step3 = raw5358step2 := by apply Matrix.ext; unfold raw5358step3 raw5358step2; decide +kernel
      have hl : raw5358step2Labels = labelEmbedding8 ∘ raw5358step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5358step2 raw5358step2Labels raw5358step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4853 node4853Labels := by rfl

def raw5359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw5359Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5359step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw5359step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5359step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw5359step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5359step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw5359step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5359 raw5359Labels = mixedMoment B node4261 node4261Labels := by
  calc
    mixedMoment B raw5359 raw5359Labels = mixedMoment B raw5359step0 raw5359step0Labels := by
      have hz : ∀ j, raw5359 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5359step0 = (fun i j => raw5359 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5359step0 raw5359; decide +kernel
      have hl : raw5359step0Labels = raw5359Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5359 raw5359Labels permutation265 hz
    mixedMoment B raw5359step0 raw5359step0Labels = mixedMoment B raw5359step1 raw5359step1Labels := by
      have ha : raw5359step1 = (fun i j => raw5359step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5359step1 raw5359step0; decide +kernel
      have hl : raw5359step1Labels = raw5359step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5359step0 raw5359step0Labels permutation33 permutation3
    mixedMoment B raw5359step1 raw5359step1Labels = mixedMoment B raw5359step2 raw5359step2Labels := by
      have ha : raw5359step2 = raw5359step1 := by apply Matrix.ext; unfold raw5359step2 raw5359step1; decide +kernel
      have hl : raw5359step1Labels = labelEmbedding6 ∘ raw5359step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5359step1 raw5359step1Labels raw5359step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4261 node4261Labels := by rfl

def raw5360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw5360Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5360step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw5360step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5360step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw5360step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5360 raw5360Labels = mixedMoment B node4735 node4735Labels := by
  calc
    mixedMoment B raw5360 raw5360Labels = mixedMoment B raw5360step0 raw5360step0Labels := by
      have ha : raw5360step0 = (fun i j => raw5360 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5360step0 raw5360; decide +kernel
      have hl : raw5360step0Labels = raw5360Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5360 raw5360Labels permutation153 permutation3
    mixedMoment B raw5360step0 raw5360step0Labels = mixedMoment B raw5360step1 raw5360step1Labels := by
      have ha : raw5360step1 = raw5360step0 := by apply Matrix.ext; unfold raw5360step1 raw5360step0; decide +kernel
      have hl : raw5360step0Labels = labelEmbedding6 ∘ raw5360step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5360step0 raw5360step0Labels raw5360step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4735 node4735Labels := by rfl

def raw5361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw5361Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5361step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![2, 0, -2]]
def raw5361step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5361step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw5361step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5361step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw5361step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5361 raw5361Labels = mixedMoment B node4821 node4821Labels := by
  calc
    mixedMoment B raw5361 raw5361Labels = mixedMoment B raw5361step0 raw5361step0Labels := by
      have hz : ∀ j, raw5361 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5361step0 = (fun i j => raw5361 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5361step0 raw5361; decide +kernel
      have hl : raw5361step0Labels = raw5361Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5361 raw5361Labels permutation265 hz
    mixedMoment B raw5361step0 raw5361step0Labels = mixedMoment B raw5361step1 raw5361step1Labels := by
      have ha : raw5361step1 = (fun i j => raw5361step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5361step1 raw5361step0; decide +kernel
      have hl : raw5361step1Labels = raw5361step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5361step0 raw5361step0Labels permutation33 permutation3
    mixedMoment B raw5361step1 raw5361step1Labels = mixedMoment B raw5361step2 raw5361step2Labels := by
      have ha : raw5361step2 = raw5361step1 := by apply Matrix.ext; unfold raw5361step2 raw5361step1; decide +kernel
      have hl : raw5361step1Labels = labelEmbedding6 ∘ raw5361step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5361step1 raw5361step1Labels raw5361step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4821 node4821Labels := by rfl

def raw5362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw5362Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5362step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, -1, 2], ![2, -1, -1], ![2, 0, -2]]
def raw5362step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5362step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw5362step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5362step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw5362step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5362 raw5362Labels = mixedMoment B node4856 node4856Labels := by
  calc
    mixedMoment B raw5362 raw5362Labels = mixedMoment B raw5362step0 raw5362step0Labels := by
      have hz : ∀ j, raw5362 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5362step0 = (fun i j => raw5362 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5362step0 raw5362; decide +kernel
      have hl : raw5362step0Labels = raw5362Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5362 raw5362Labels permutation265 hz
    mixedMoment B raw5362step0 raw5362step0Labels = mixedMoment B raw5362step1 raw5362step1Labels := by
      have ha : raw5362step1 = (fun i j => raw5362step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5362step1 raw5362step0; decide +kernel
      have hl : raw5362step1Labels = raw5362step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5362step0 raw5362step0Labels permutation39 permutation3
    mixedMoment B raw5362step1 raw5362step1Labels = mixedMoment B raw5362step2 raw5362step2Labels := by
      have ha : raw5362step2 = raw5362step1 := by apply Matrix.ext; unfold raw5362step2 raw5362step1; decide +kernel
      have hl : raw5362step1Labels = labelEmbedding6 ∘ raw5362step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5362step1 raw5362step1Labels raw5362step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4856 node4856Labels := by rfl

def raw5363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![2, -1, -1], ![1, 1, -2]]
def raw5363Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -2, 2], ![2, -1, -1], ![1, 1, -2]]
def raw5363step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5363step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw5363step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5363step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5363step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5363step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw5363step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5363 raw5363Labels = mixedMoment B node4867 node4867Labels := by
  calc
    mixedMoment B raw5363 raw5363Labels = mixedMoment B raw5363step0 raw5363step0Labels := by
      have hz : ∀ j, raw5363 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5363step0 = (fun i j => raw5363 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5363step0 raw5363; decide +kernel
      have hl : raw5363step0Labels = raw5363Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5363 raw5363Labels permutation265 hz
    mixedMoment B raw5363step0 raw5363step0Labels = mixedMoment B raw5363step1 raw5363step1Labels := by
      have ha : raw5363step1 = (fun i j => raw5363step0 (permutation51 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5363step1 raw5363step0; decide +kernel
      have hl : raw5363step1Labels = raw5363step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5363step0 raw5363step0Labels permutation51 permutation5
    mixedMoment B raw5363step1 raw5363step1Labels = mixedMoment B raw5363step2 raw5363step2Labels := by
      have ha : raw5363step2 = -raw5363step1 := by apply Matrix.ext; change ∀ i j, raw5363step2 i j = -(raw5363step1 i j); unfold raw5363step2 raw5363step1; decide +kernel
      have hl : raw5363step2Labels = raw5363step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5363step2 raw5363step2Labels = mixedMoment B raw5363step3 raw5363step3Labels := by
      have ha : raw5363step3 = raw5363step2 := by apply Matrix.ext; unfold raw5363step3 raw5363step2; decide +kernel
      have hl : raw5363step2Labels = labelEmbedding8 ∘ raw5363step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5363step2 raw5363step2Labels raw5363step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4867 node4867Labels := by rfl

def raw5364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw5364Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw5364step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5364step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw5364step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5364step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw5364step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5364 raw5364Labels = mixedMoment B node4259 node4259Labels := by
  calc
    mixedMoment B raw5364 raw5364Labels = mixedMoment B raw5364step0 raw5364step0Labels := by
      have hz : ∀ j, raw5364 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5364step0 = (fun i j => raw5364 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5364step0 raw5364; decide +kernel
      have hl : raw5364step0Labels = raw5364Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5364 raw5364Labels permutation265 hz
    mixedMoment B raw5364step0 raw5364step0Labels = mixedMoment B raw5364step1 raw5364step1Labels := by
      have ha : raw5364step1 = (fun i j => raw5364step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5364step1 raw5364step0; decide +kernel
      have hl : raw5364step1Labels = raw5364step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5364step0 raw5364step0Labels permutation32 permutation3
    mixedMoment B raw5364step1 raw5364step1Labels = mixedMoment B raw5364step2 raw5364step2Labels := by
      have ha : raw5364step2 = raw5364step1 := by apply Matrix.ext; unfold raw5364step2 raw5364step1; decide +kernel
      have hl : raw5364step1Labels = labelEmbedding6 ∘ raw5364step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5364step1 raw5364step1Labels raw5364step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4259 node4259Labels := by rfl

def raw5365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw5365Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5365step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw5365step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5365step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw5365step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5365 raw5365Labels = mixedMoment B node4733 node4733Labels := by
  calc
    mixedMoment B raw5365 raw5365Labels = mixedMoment B raw5365step0 raw5365step0Labels := by
      have ha : raw5365step0 = (fun i j => raw5365 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5365step0 raw5365; decide +kernel
      have hl : raw5365step0Labels = raw5365Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5365 raw5365Labels permutation152 permutation3
    mixedMoment B raw5365step0 raw5365step0Labels = mixedMoment B raw5365step1 raw5365step1Labels := by
      have ha : raw5365step1 = raw5365step0 := by apply Matrix.ext; unfold raw5365step1 raw5365step0; decide +kernel
      have hl : raw5365step0Labels = labelEmbedding6 ∘ raw5365step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5365step0 raw5365step0Labels raw5365step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4733 node4733Labels := by rfl

def raw5366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw5366Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![3, -1, -2]]
def raw5366step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5366step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw5366step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5366step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw5366step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5366 raw5366Labels = mixedMoment B node4817 node4817Labels := by
  calc
    mixedMoment B raw5366 raw5366Labels = mixedMoment B raw5366step0 raw5366step0Labels := by
      have hz : ∀ j, raw5366 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5366step0 = (fun i j => raw5366 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5366step0 raw5366; decide +kernel
      have hl : raw5366step0Labels = raw5366Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5366 raw5366Labels permutation265 hz
    mixedMoment B raw5366step0 raw5366step0Labels = mixedMoment B raw5366step1 raw5366step1Labels := by
      have ha : raw5366step1 = (fun i j => raw5366step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5366step1 raw5366step0; decide +kernel
      have hl : raw5366step1Labels = raw5366step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5366step0 raw5366step0Labels permutation32 permutation3
    mixedMoment B raw5366step1 raw5366step1Labels = mixedMoment B raw5366step2 raw5366step2Labels := by
      have ha : raw5366step2 = raw5366step1 := by apply Matrix.ext; unfold raw5366step2 raw5366step1; decide +kernel
      have hl : raw5366step1Labels = labelEmbedding6 ∘ raw5366step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5366step1 raw5366step1Labels raw5366step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4817 node4817Labels := by rfl

def raw5367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw5367Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![3, -1, -2]]
def raw5367step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5367step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw5367step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw5367step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw5367step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5367 raw5367Labels = mixedMoment B node4853 node4853Labels := by
  calc
    mixedMoment B raw5367 raw5367Labels = mixedMoment B raw5367step0 raw5367step0Labels := by
      have hz : ∀ j, raw5367 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5367step0 = (fun i j => raw5367 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5367step0 raw5367; decide +kernel
      have hl : raw5367step0Labels = raw5367Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5367 raw5367Labels permutation265 hz
    mixedMoment B raw5367step0 raw5367step0Labels = mixedMoment B raw5367step1 raw5367step1Labels := by
      have ha : raw5367step1 = (fun i j => raw5367step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5367step1 raw5367step0; decide +kernel
      have hl : raw5367step1Labels = raw5367step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5367step0 raw5367step0Labels permutation38 permutation3
    mixedMoment B raw5367step1 raw5367step1Labels = mixedMoment B raw5367step2 raw5367step2Labels := by
      have ha : raw5367step2 = raw5367step1 := by apply Matrix.ext; unfold raw5367step2 raw5367step1; decide +kernel
      have hl : raw5367step1Labels = labelEmbedding6 ∘ raw5367step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5367step1 raw5367step1Labels raw5367step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4853 node4853Labels := by rfl

def raw5368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![3, -1, -2]]
def raw5368Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![3, -1, -2]]
def raw5368step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw5368step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, -2, 3], ![-2, 2, 0]]
def raw5368step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5368step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5368step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw5368step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw5368step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical5368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5368 raw5368Labels = mixedMoment B node4836 node4836Labels := by
  calc
    mixedMoment B raw5368 raw5368Labels = mixedMoment B raw5368step0 raw5368step0Labels := by
      have hz : ∀ j, raw5368 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5368step0 = (fun i j => raw5368 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5368step0 raw5368; decide +kernel
      have hl : raw5368step0Labels = raw5368Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5368 raw5368Labels permutation265 hz
    mixedMoment B raw5368step0 raw5368step0Labels = mixedMoment B raw5368step1 raw5368step1Labels := by
      have ha : raw5368step1 = (fun i j => raw5368step0 (permutation45 i) (permutation5 j)) := by apply Matrix.ext; unfold raw5368step1 raw5368step0; decide +kernel
      have hl : raw5368step1Labels = raw5368step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5368step0 raw5368step0Labels permutation45 permutation5
    mixedMoment B raw5368step1 raw5368step1Labels = mixedMoment B raw5368step2 raw5368step2Labels := by
      have ha : raw5368step2 = -raw5368step1 := by apply Matrix.ext; change ∀ i j, raw5368step2 i j = -(raw5368step1 i j); unfold raw5368step2 raw5368step1; decide +kernel
      have hl : raw5368step2Labels = raw5368step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw5368step2 raw5368step2Labels = mixedMoment B raw5368step3 raw5368step3Labels := by
      have ha : raw5368step3 = raw5368step2 := by apply Matrix.ext; unfold raw5368step3 raw5368step2; decide +kernel
      have hl : raw5368step2Labels = labelEmbedding8 ∘ raw5368step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw5368step2 raw5368step2Labels raw5368step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4836 node4836Labels := by rfl

def raw5369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5369Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5369step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5369step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5369 raw5369Labels = mixedMoment B node3803 node3803Labels := by
  calc
    mixedMoment B raw5369 raw5369Labels = mixedMoment B raw5369step0 raw5369step0Labels := by
      have ha : raw5369step0 = (fun i j => raw5369 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5369step0 raw5369; decide +kernel
      have hl : raw5369step0Labels = raw5369Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5369 raw5369Labels permutation152 permutation3
    _ = mixedMoment B node3803 node3803Labels := by rfl

def raw5370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5370Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5370step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5370step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5370step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw5370step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5370 raw5370Labels = mixedMoment B node3856 node3856Labels := by
  calc
    mixedMoment B raw5370 raw5370Labels = mixedMoment B raw5370step0 raw5370step0Labels := by
      have hz : ∀ j, raw5370 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5370step0 = (fun i j => raw5370 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5370step0 raw5370; decide +kernel
      have hl : raw5370step0Labels = raw5370Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5370 raw5370Labels permutation265 hz
    mixedMoment B raw5370step0 raw5370step0Labels = mixedMoment B raw5370step1 raw5370step1Labels := by
      have ha : raw5370step1 = (fun i j => raw5370step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5370step1 raw5370step0; decide +kernel
      have hl : raw5370step1Labels = raw5370step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5370step0 raw5370step0Labels permutation32 permutation3
    _ = mixedMoment B node3856 node3856Labels := by rfl

def raw5371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5371Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5371step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5371step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw5371step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5371 raw5371Labels = mixedMoment B node3883 node3883Labels := by
  calc
    mixedMoment B raw5371 raw5371Labels = mixedMoment B raw5371step0 raw5371step0Labels := by
      have hz : ∀ j, raw5371 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5371step0 = (fun i j => raw5371 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5371step0 raw5371; decide +kernel
      have hl : raw5371step0Labels = raw5371Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5371 raw5371Labels permutation265 hz
    mixedMoment B raw5371step0 raw5371step0Labels = mixedMoment B raw5371step1 raw5371step1Labels := by
      have ha : raw5371step1 = (fun i j => raw5371step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5371step1 raw5371step0; decide +kernel
      have hl : raw5371step1Labels = raw5371step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5371step0 raw5371step0Labels permutation38 permutation3
    _ = mixedMoment B node3883 node3883Labels := by rfl

def raw5372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw5372Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![2, 0, -2]]
def raw5372step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5372step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw5372step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5372step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw5372step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5372 raw5372Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw5372 raw5372Labels = mixedMoment B raw5372step0 raw5372step0Labels := by
      have hz : ∀ j, raw5372 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5372step0 = (fun i j => raw5372 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5372step0 raw5372; decide +kernel
      have hl : raw5372step0Labels = raw5372Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5372 raw5372Labels permutation265 hz
    mixedMoment B raw5372step0 raw5372step0Labels = mixedMoment B raw5372step1 raw5372step1Labels := by
      have ha : raw5372step1 = (fun i j => raw5372step0 (permutation86 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5372step1 raw5372step0; decide +kernel
      have hl : raw5372step1Labels = raw5372step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5372step0 raw5372step0Labels permutation86 permutation6
    mixedMoment B raw5372step1 raw5372step1Labels = mixedMoment B raw5372step2 raw5372step2Labels := by
      have ha : raw5372step2 = -raw5372step1 := by apply Matrix.ext; change ∀ i j, raw5372step2 i j = -(raw5372step1 i j); unfold raw5372step2 raw5372step1; decide +kernel
      have hl : raw5372step2Labels = raw5372step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3814 node3814Labels := by rfl

def raw5373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw5373Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2]]
def raw5373step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5373step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw5373step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw5373step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw5373step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5373 raw5373Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw5373 raw5373Labels = mixedMoment B raw5373step0 raw5373step0Labels := by
      have hz : ∀ j, raw5373 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw5373step0 = (fun i j => raw5373 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw5373step0 raw5373; decide +kernel
      have hl : raw5373step0Labels = raw5373Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw5373 raw5373Labels permutation265 hz
    mixedMoment B raw5373step0 raw5373step0Labels = mixedMoment B raw5373step1 raw5373step1Labels := by
      have ha : raw5373step1 = (fun i j => raw5373step0 (permutation86 i) (permutation6 j)) := by apply Matrix.ext; unfold raw5373step1 raw5373step0; decide +kernel
      have hl : raw5373step1Labels = raw5373step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5373step0 raw5373step0Labels permutation86 permutation6
    mixedMoment B raw5373step1 raw5373step1Labels = mixedMoment B raw5373step2 raw5373step2Labels := by
      have ha : raw5373step2 = -raw5373step1 := by apply Matrix.ext; change ∀ i j, raw5373step2 i j = -(raw5373step1 i j); unfold raw5373step2 raw5373step1; decide +kernel
      have hl : raw5373step2Labels = raw5373step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3813 node3813Labels := by rfl

def raw5374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5374Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5374step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 0, 4], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5374step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5374 raw5374Labels = mixedMoment B node793 node793Labels := by
  calc
    mixedMoment B raw5374 raw5374Labels = mixedMoment B raw5374step0 raw5374step0Labels := by
      have ha : raw5374step0 = (fun i j => raw5374 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5374step0 raw5374; decide +kernel
      have hl : raw5374step0Labels = raw5374Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5374 raw5374Labels permutation184 permutation3
    _ = mixedMoment B node793 node793Labels := by rfl

def raw5375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![2, 0, -2]]
def raw5375Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw5375step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw5375step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical5375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw5375 raw5375Labels = mixedMoment B node2034 node2034Labels := by
  calc
    mixedMoment B raw5375 raw5375Labels = mixedMoment B raw5375step0 raw5375step0Labels := by
      have ha : raw5375step0 = (fun i j => raw5375 (permutation184 i) (permutation3 j)) := by apply Matrix.ext; unfold raw5375step0 raw5375; decide +kernel
      have hl : raw5375step0Labels = raw5375Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw5375 raw5375Labels permutation184 permutation3
    _ = mixedMoment B node2034 node2034Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
