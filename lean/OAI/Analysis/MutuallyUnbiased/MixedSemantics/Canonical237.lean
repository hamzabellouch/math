import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes13
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw30336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw30336Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30336step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw30336step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30336step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw30336step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30336step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw30336step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30336 raw30336Labels = mixedMoment B node2604 node2604Labels := by
  calc
    mixedMoment B raw30336 raw30336Labels = mixedMoment B raw30336step0 raw30336step0Labels := by
      have hz : ∀ j, raw30336 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30336step0 = (fun i j => raw30336 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30336step0 raw30336; decide +kernel
      have hl : raw30336step0Labels = raw30336Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30336 raw30336Labels permutation434 hz
    mixedMoment B raw30336step0 raw30336step0Labels = mixedMoment B raw30336step1 raw30336step1Labels := by
      have hz : ∀ j, raw30336step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw30336step1 = (fun i j => raw30336step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw30336step1 raw30336step0; decide +kernel
      have hl : raw30336step1Labels = raw30336step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30336step0 raw30336step0Labels permutation56 hz
    mixedMoment B raw30336step1 raw30336step1Labels = mixedMoment B raw30336step2 raw30336step2Labels := by
      have ha : raw30336step2 = (fun i j => raw30336step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30336step2 raw30336step1; decide +kernel
      have hl : raw30336step2Labels = raw30336step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30336step1 raw30336step1Labels permutation9 permutation3
    _ = mixedMoment B node2604 node2604Labels := by rfl

def raw30337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw30337Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw30337step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30337step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30337step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30337 raw30337Labels = mixedMoment B node2488 node2488Labels := by
  calc
    mixedMoment B raw30337 raw30337Labels = mixedMoment B raw30337step0 raw30337step0Labels := by
      have hz : ∀ j, raw30337 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw30337step0 = (fun i j => raw30337 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw30337step0 raw30337; decide +kernel
      have hl : raw30337step0Labels = raw30337Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30337 raw30337Labels permutation265 hz
    mixedMoment B raw30337step0 raw30337step0Labels = mixedMoment B raw30337step1 raw30337step1Labels := by
      have ha : raw30337step1 = (fun i j => raw30337step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30337step1 raw30337step0; decide +kernel
      have hl : raw30337step1Labels = raw30337step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30337step0 raw30337step0Labels permutation39 permutation3
    _ = mixedMoment B node2488 node2488Labels := by rfl

def raw30338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw30338Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30338step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw30338step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30338step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw30338step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30338step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw30338step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30338 raw30338Labels = mixedMoment B node2768 node2768Labels := by
  calc
    mixedMoment B raw30338 raw30338Labels = mixedMoment B raw30338step0 raw30338step0Labels := by
      have hz : ∀ j, raw30338 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30338step0 = (fun i j => raw30338 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30338step0 raw30338; decide +kernel
      have hl : raw30338step0Labels = raw30338Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30338 raw30338Labels permutation434 hz
    mixedMoment B raw30338step0 raw30338step0Labels = mixedMoment B raw30338step1 raw30338step1Labels := by
      have hz : ∀ j, raw30338step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw30338step1 = (fun i j => raw30338step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw30338step1 raw30338step0; decide +kernel
      have hl : raw30338step1Labels = raw30338step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30338step0 raw30338step0Labels permutation56 hz
    mixedMoment B raw30338step1 raw30338step1Labels = mixedMoment B raw30338step2 raw30338step2Labels := by
      have ha : raw30338step2 = (fun i j => raw30338step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30338step2 raw30338step1; decide +kernel
      have hl : raw30338step2Labels = raw30338step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30338step1 raw30338step1Labels permutation8 permutation3
    _ = mixedMoment B node2768 node2768Labels := by rfl

def raw30339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw30339Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw30339step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30339step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw30339step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30339step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw30339step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30339 raw30339Labels = mixedMoment B node2765 node2765Labels := by
  calc
    mixedMoment B raw30339 raw30339Labels = mixedMoment B raw30339step0 raw30339step0Labels := by
      have hz : ∀ j, raw30339 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30339step0 = (fun i j => raw30339 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30339step0 raw30339; decide +kernel
      have hl : raw30339step0Labels = raw30339Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30339 raw30339Labels permutation434 hz
    mixedMoment B raw30339step0 raw30339step0Labels = mixedMoment B raw30339step1 raw30339step1Labels := by
      have hz : ∀ j, raw30339step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw30339step1 = (fun i j => raw30339step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw30339step1 raw30339step0; decide +kernel
      have hl : raw30339step1Labels = raw30339step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30339step0 raw30339step0Labels permutation56 hz
    mixedMoment B raw30339step1 raw30339step1Labels = mixedMoment B raw30339step2 raw30339step2Labels := by
      have ha : raw30339step2 = (fun i j => raw30339step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30339step2 raw30339step1; decide +kernel
      have hl : raw30339step2Labels = raw30339step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30339step1 raw30339step1Labels permutation9 permutation3
    _ = mixedMoment B node2765 node2765Labels := by rfl

def raw30340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw30340Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![1, -2, 1], ![2, -2, 0], ![2, 0, -2]]
def raw30340step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30340step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw30340step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30340 raw30340Labels = mixedMoment B node891 node891Labels := by
  calc
    mixedMoment B raw30340 raw30340Labels = mixedMoment B raw30340step0 raw30340step0Labels := by
      have hz : ∀ j, raw30340 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30340step0 = (fun i j => raw30340 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30340step0 raw30340; decide +kernel
      have hl : raw30340step0Labels = raw30340Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30340 raw30340Labels permutation434 hz
    mixedMoment B raw30340step0 raw30340step0Labels = mixedMoment B raw30340step1 raw30340step1Labels := by
      have ha : raw30340step1 = (fun i j => raw30340step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30340step1 raw30340step0; decide +kernel
      have hl : raw30340step1Labels = raw30340step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30340step0 raw30340step0Labels permutation33 permutation3
    _ = mixedMoment B node891 node891Labels := by rfl

def raw30341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![1, -2, 1], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw30341Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30341step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![1, -2, 1], ![2, -2, 0], ![2, 0, -2]]
def raw30341step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30341step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw30341step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30341 raw30341Labels = mixedMoment B node2313 node2313Labels := by
  calc
    mixedMoment B raw30341 raw30341Labels = mixedMoment B raw30341step0 raw30341step0Labels := by
      have hz : ∀ j, raw30341 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30341step0 = (fun i j => raw30341 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30341step0 raw30341; decide +kernel
      have hl : raw30341step0Labels = raw30341Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30341 raw30341Labels permutation434 hz
    mixedMoment B raw30341step0 raw30341step0Labels = mixedMoment B raw30341step1 raw30341step1Labels := by
      have ha : raw30341step1 = (fun i j => raw30341step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30341step1 raw30341step0; decide +kernel
      have hl : raw30341step1Labels = raw30341step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30341step0 raw30341step0Labels permutation33 permutation3
    _ = mixedMoment B node2313 node2313Labels := by rfl

def raw30342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw30342Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30342step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw30342step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30342 raw30342Labels = mixedMoment B node2419 node2419Labels := by
  calc
    mixedMoment B raw30342 raw30342Labels = mixedMoment B raw30342step0 raw30342step0Labels := by
      have ha : raw30342step0 = (fun i j => raw30342 (permutation159 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30342step0 raw30342; decide +kernel
      have hl : raw30342step0Labels = raw30342Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30342 raw30342Labels permutation159 permutation3
    _ = mixedMoment B node2419 node2419Labels := by rfl

def raw30343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw30343Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30343step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw30343step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30343step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw30343step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30343 raw30343Labels = mixedMoment B node2515 node2515Labels := by
  calc
    mixedMoment B raw30343 raw30343Labels = mixedMoment B raw30343step0 raw30343step0Labels := by
      have hz : ∀ j, raw30343 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30343step0 = (fun i j => raw30343 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30343step0 raw30343; decide +kernel
      have hl : raw30343step0Labels = raw30343Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30343 raw30343Labels permutation434 hz
    mixedMoment B raw30343step0 raw30343step0Labels = mixedMoment B raw30343step1 raw30343step1Labels := by
      have ha : raw30343step1 = (fun i j => raw30343step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30343step1 raw30343step0; decide +kernel
      have hl : raw30343step1Labels = raw30343step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30343step0 raw30343step0Labels permutation34 permutation3
    _ = mixedMoment B node2515 node2515Labels := by rfl

def raw30344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw30344Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![2, -2, 0], ![1, 1, -2]]
def raw30344step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30344step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw30344step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30344 raw30344Labels = mixedMoment B node2505 node2505Labels := by
  calc
    mixedMoment B raw30344 raw30344Labels = mixedMoment B raw30344step0 raw30344step0Labels := by
      have hz : ∀ j, raw30344 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30344step0 = (fun i j => raw30344 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30344step0 raw30344; decide +kernel
      have hl : raw30344step0Labels = raw30344Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30344 raw30344Labels permutation434 hz
    mixedMoment B raw30344step0 raw30344step0Labels = mixedMoment B raw30344step1 raw30344step1Labels := by
      have ha : raw30344step1 = (fun i j => raw30344step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30344step1 raw30344step0; decide +kernel
      have hl : raw30344step1Labels = raw30344step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30344step0 raw30344step0Labels permutation36 permutation3
    _ = mixedMoment B node2505 node2505Labels := by rfl

def raw30345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw30345Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30345step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30345step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30345 raw30345Labels = mixedMoment B node869 node869Labels := by
  calc
    mixedMoment B raw30345 raw30345Labels = mixedMoment B raw30345step0 raw30345step0Labels := by
      have ha : raw30345step0 = (fun i j => raw30345 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30345step0 raw30345; decide +kernel
      have hl : raw30345step0Labels = raw30345Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30345 raw30345Labels permutation153 permutation3
    _ = mixedMoment B node869 node869Labels := by rfl

def raw30346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw30346Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30346step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30346step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30346 raw30346Labels = mixedMoment B node2298 node2298Labels := by
  calc
    mixedMoment B raw30346 raw30346Labels = mixedMoment B raw30346step0 raw30346step0Labels := by
      have ha : raw30346step0 = (fun i j => raw30346 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30346step0 raw30346; decide +kernel
      have hl : raw30346step0Labels = raw30346Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30346 raw30346Labels permutation153 permutation3
    _ = mixedMoment B node2298 node2298Labels := by rfl

def raw30347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw30347Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30347step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30347step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30347 raw30347Labels = mixedMoment B node2431 node2431Labels := by
  calc
    mixedMoment B raw30347 raw30347Labels = mixedMoment B raw30347step0 raw30347step0Labels := by
      have ha : raw30347step0 = (fun i j => raw30347 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30347step0 raw30347; decide +kernel
      have hl : raw30347step0Labels = raw30347Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30347 raw30347Labels permutation153 permutation3
    _ = mixedMoment B node2431 node2431Labels := by rfl

def raw30348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw30348Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30348step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, -1, 1], ![3, -3, 0], ![2, 0, -2]]
def raw30348step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30348step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw30348step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30348 raw30348Labels = mixedMoment B node872 node872Labels := by
  calc
    mixedMoment B raw30348 raw30348Labels = mixedMoment B raw30348step0 raw30348step0Labels := by
      have hz : ∀ j, raw30348 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30348step0 = (fun i j => raw30348 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30348step0 raw30348; decide +kernel
      have hl : raw30348step0Labels = raw30348Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30348 raw30348Labels permutation434 hz
    mixedMoment B raw30348step0 raw30348step0Labels = mixedMoment B raw30348step1 raw30348step1Labels := by
      have ha : raw30348step1 = (fun i j => raw30348step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30348step1 raw30348step0; decide +kernel
      have hl : raw30348step1Labels = raw30348step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30348step0 raw30348step0Labels permutation33 permutation3
    _ = mixedMoment B node872 node872Labels := by rfl

def raw30349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw30349Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, -1, 1], ![3, -3, 0], ![2, 0, -2]]
def raw30349step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30349step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, 1, -1], ![-2, 0, 2], ![-3, 1, 2]]
def raw30349step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30349step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw30349step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30349 raw30349Labels = mixedMoment B node1788 node1788Labels := by
  calc
    mixedMoment B raw30349 raw30349Labels = mixedMoment B raw30349step0 raw30349step0Labels := by
      have hz : ∀ j, raw30349 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30349step0 = (fun i j => raw30349 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30349step0 raw30349; decide +kernel
      have hl : raw30349step0Labels = raw30349Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30349 raw30349Labels permutation434 hz
    mixedMoment B raw30349step0 raw30349step0Labels = mixedMoment B raw30349step1 raw30349step1Labels := by
      have ha : raw30349step1 = (fun i j => raw30349step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30349step1 raw30349step0; decide +kernel
      have hl : raw30349step1Labels = raw30349step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30349step0 raw30349step0Labels permutation127 permutation3
    mixedMoment B raw30349step1 raw30349step1Labels = mixedMoment B raw30349step2 raw30349step2Labels := by
      have ha : raw30349step2 = -raw30349step1 := by apply Matrix.ext; change ∀ i j, raw30349step2 i j = -(raw30349step1 i j); unfold raw30349step2 raw30349step1; decide +kernel
      have hl : raw30349step2Labels = raw30349step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1788 node1788Labels := by rfl

def raw30350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![3, -3, 0], ![2, 0, -2]]
def raw30350Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 0, 1], ![3, -3, 0], ![2, 0, -2]]
def raw30350step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30350step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw30350step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30350step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw30350step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30350 raw30350Labels = mixedMoment B node1807 node1807Labels := by
  calc
    mixedMoment B raw30350 raw30350Labels = mixedMoment B raw30350step0 raw30350step0Labels := by
      have hz : ∀ j, raw30350 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30350step0 = (fun i j => raw30350 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30350step0 raw30350; decide +kernel
      have hl : raw30350step0Labels = raw30350Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30350 raw30350Labels permutation434 hz
    mixedMoment B raw30350step0 raw30350step0Labels = mixedMoment B raw30350step1 raw30350step1Labels := by
      have ha : raw30350step1 = (fun i j => raw30350step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30350step1 raw30350step0; decide +kernel
      have hl : raw30350step1Labels = raw30350step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30350step0 raw30350step0Labels permutation127 permutation3
    mixedMoment B raw30350step1 raw30350step1Labels = mixedMoment B raw30350step2 raw30350step2Labels := by
      have ha : raw30350step2 = -raw30350step1 := by apply Matrix.ext; change ∀ i j, raw30350step2 i j = -(raw30350step1 i j); unfold raw30350step2 raw30350step1; decide +kernel
      have hl : raw30350step2Labels = raw30350step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1807 node1807Labels := by rfl

def raw30351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 1, 0], ![3, -3, 0], ![2, 0, -2]]
def raw30351Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30351step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw30351step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30351step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw30351step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30351 raw30351Labels = mixedMoment B node1786 node1786Labels := by
  calc
    mixedMoment B raw30351 raw30351Labels = mixedMoment B raw30351step0 raw30351step0Labels := by
      have ha : raw30351step0 = (fun i j => raw30351 (permutation582 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30351step0 raw30351; decide +kernel
      have hl : raw30351step0Labels = raw30351Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30351 raw30351Labels permutation582 permutation3
    mixedMoment B raw30351step0 raw30351step0Labels = mixedMoment B raw30351step1 raw30351step1Labels := by
      have ha : raw30351step1 = -raw30351step0 := by apply Matrix.ext; change ∀ i j, raw30351step1 i j = -(raw30351step0 i j); unfold raw30351step1 raw30351step0; decide +kernel
      have hl : raw30351step1Labels = raw30351step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1786 node1786Labels := by rfl

def raw30352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![3, -3, 0], ![1, 1, -2]]
def raw30352Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30352step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![3, -3, 0], ![1, 1, -2]]
def raw30352step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30352step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw30352step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw30352step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw30352step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30352 raw30352Labels = mixedMoment B node2079 node2079Labels := by
  calc
    mixedMoment B raw30352 raw30352Labels = mixedMoment B raw30352step0 raw30352step0Labels := by
      have hz : ∀ j, raw30352 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30352step0 = (fun i j => raw30352 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30352step0 raw30352; decide +kernel
      have hl : raw30352step0Labels = raw30352Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30352 raw30352Labels permutation434 hz
    mixedMoment B raw30352step0 raw30352step0Labels = mixedMoment B raw30352step1 raw30352step1Labels := by
      have ha : raw30352step1 = (fun i j => raw30352step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30352step1 raw30352step0; decide +kernel
      have hl : raw30352step1Labels = raw30352step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30352step0 raw30352step0Labels permutation127 permutation3
    mixedMoment B raw30352step1 raw30352step1Labels = mixedMoment B raw30352step2 raw30352step2Labels := by
      have ha : raw30352step2 = -raw30352step1 := by apply Matrix.ext; change ∀ i j, raw30352step2 i j = -(raw30352step1 i j); unfold raw30352step2 raw30352step1; decide +kernel
      have hl : raw30352step2Labels = raw30352step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2079 node2079Labels := by rfl

def raw30353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw30353Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30353step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![3, -1, -2]]
def raw30353step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30353step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw30353step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30353 raw30353Labels = mixedMoment B node874 node874Labels := by
  calc
    mixedMoment B raw30353 raw30353Labels = mixedMoment B raw30353step0 raw30353step0Labels := by
      have hz : ∀ j, raw30353 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30353step0 = (fun i j => raw30353 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30353step0 raw30353; decide +kernel
      have hl : raw30353step0Labels = raw30353Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30353 raw30353Labels permutation434 hz
    mixedMoment B raw30353step0 raw30353step0Labels = mixedMoment B raw30353step1 raw30353step1Labels := by
      have ha : raw30353step1 = (fun i j => raw30353step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30353step1 raw30353step0; decide +kernel
      have hl : raw30353step1Labels = raw30353step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30353step0 raw30353step0Labels permutation32 permutation3
    _ = mixedMoment B node874 node874Labels := by rfl

def raw30354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw30354Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30354step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, -1, 1], ![2, -2, 0], ![3, -1, -2]]
def raw30354step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30354step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw30354step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30354 raw30354Labels = mixedMoment B node2301 node2301Labels := by
  calc
    mixedMoment B raw30354 raw30354Labels = mixedMoment B raw30354step0 raw30354step0Labels := by
      have hz : ∀ j, raw30354 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30354step0 = (fun i j => raw30354 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30354step0 raw30354; decide +kernel
      have hl : raw30354step0Labels = raw30354Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30354 raw30354Labels permutation434 hz
    mixedMoment B raw30354step0 raw30354step0Labels = mixedMoment B raw30354step1 raw30354step1Labels := by
      have ha : raw30354step1 = (fun i j => raw30354step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30354step1 raw30354step0; decide +kernel
      have hl : raw30354step1Labels = raw30354step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30354step0 raw30354step0Labels permutation32 permutation3
    _ = mixedMoment B node2301 node2301Labels := by rfl

def raw30355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw30355Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 0, 1], ![2, -2, 0], ![3, -1, -2]]
def raw30355step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30355step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -2, -1]]
def raw30355step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30355 raw30355Labels = mixedMoment B node2434 node2434Labels := by
  calc
    mixedMoment B raw30355 raw30355Labels = mixedMoment B raw30355step0 raw30355step0Labels := by
      have hz : ∀ j, raw30355 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30355step0 = (fun i j => raw30355 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30355step0 raw30355; decide +kernel
      have hl : raw30355step0Labels = raw30355Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30355 raw30355Labels permutation434 hz
    mixedMoment B raw30355step0 raw30355step0Labels = mixedMoment B raw30355step1 raw30355step1Labels := by
      have ha : raw30355step1 = (fun i j => raw30355step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30355step1 raw30355step0; decide +kernel
      have hl : raw30355step1Labels = raw30355step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30355step0 raw30355step0Labels permutation32 permutation3
    _ = mixedMoment B node2434 node2434Labels := by rfl

def raw30356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw30356Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30356step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![2, 0, -2], ![3, -2, -1]]
def raw30356step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30356 raw30356Labels = mixedMoment B node2412 node2412Labels := by
  calc
    mixedMoment B raw30356 raw30356Labels = mixedMoment B raw30356step0 raw30356step0Labels := by
      have ha : raw30356step0 = (fun i j => raw30356 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30356step0 raw30356; decide +kernel
      have hl : raw30356step0Labels = raw30356Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30356 raw30356Labels permutation158 permutation3
    _ = mixedMoment B node2412 node2412Labels := by rfl

def raw30357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw30357Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30357step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw30357step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30357step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw30357step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30357 raw30357Labels = mixedMoment B node2485 node2485Labels := by
  calc
    mixedMoment B raw30357 raw30357Labels = mixedMoment B raw30357step0 raw30357step0Labels := by
      have hz : ∀ j, raw30357 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30357step0 = (fun i j => raw30357 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30357step0 raw30357; decide +kernel
      have hl : raw30357step0Labels = raw30357Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30357 raw30357Labels permutation434 hz
    mixedMoment B raw30357step0 raw30357step0Labels = mixedMoment B raw30357step1 raw30357step1Labels := by
      have ha : raw30357step1 = (fun i j => raw30357step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30357step1 raw30357step0; decide +kernel
      have hl : raw30357step1Labels = raw30357step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30357step0 raw30357step0Labels permutation32 permutation3
    _ = mixedMoment B node2485 node2485Labels := by rfl

def raw30358 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30358Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30358step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30358step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw30358step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30358step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw30358step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30358 raw30358Labels = mixedMoment B node5188 node5188Labels := by
  calc
    mixedMoment B raw30358 raw30358Labels = mixedMoment B raw30358step0 raw30358step0Labels := by
      have hz : ∀ j, raw30358 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30358step0 = (fun i j => raw30358 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30358step0 raw30358; decide +kernel
      have hl : raw30358step0Labels = raw30358Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30358 raw30358Labels permutation434 hz
    mixedMoment B raw30358step0 raw30358step0Labels = mixedMoment B raw30358step1 raw30358step1Labels := by
      have ha : raw30358step1 = (fun i j => raw30358step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30358step1 raw30358step0; decide +kernel
      have hl : raw30358step1Labels = raw30358step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30358step0 raw30358step0Labels permutation32 permutation7
    mixedMoment B raw30358step1 raw30358step1Labels = mixedMoment B raw30358step2 raw30358step2Labels := by
      have ha : raw30358step2 = raw30358step1 := by apply Matrix.ext; unfold raw30358step2 raw30358step1; decide +kernel
      have hl : raw30358step1Labels = labelEmbedding10 ∘ raw30358step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30358step1 raw30358step1Labels raw30358step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5188 node5188Labels := by rfl

def raw30359 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30359Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30359step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30359step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30359step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![-2, 0, 2]]
def raw30359step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30359step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw30359step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30359step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw30359step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30359 raw30359Labels = mixedMoment B node5176 node5176Labels := by
  calc
    mixedMoment B raw30359 raw30359Labels = mixedMoment B raw30359step0 raw30359step0Labels := by
      have hz : ∀ j, raw30359 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30359step0 = (fun i j => raw30359 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30359step0 raw30359; decide +kernel
      have hl : raw30359step0Labels = raw30359Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30359 raw30359Labels permutation434 hz
    mixedMoment B raw30359step0 raw30359step0Labels = mixedMoment B raw30359step1 raw30359step1Labels := by
      have hz : ∀ j, raw30359step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30359step1 = (fun i j => raw30359step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30359step1 raw30359step0; decide +kernel
      have hl : raw30359step1Labels = raw30359step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30359step0 raw30359step0Labels permutation80 hz
    mixedMoment B raw30359step1 raw30359step1Labels = mixedMoment B raw30359step2 raw30359step2Labels := by
      have ha : raw30359step2 = (fun i j => raw30359step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30359step2 raw30359step1; decide +kernel
      have hl : raw30359step2Labels = raw30359step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30359step1 raw30359step1Labels permutation8 permutation7
    mixedMoment B raw30359step2 raw30359step2Labels = mixedMoment B raw30359step3 raw30359step3Labels := by
      have ha : raw30359step3 = raw30359step2 := by apply Matrix.ext; unfold raw30359step3 raw30359step2; decide +kernel
      have hl : raw30359step2Labels = labelEmbedding10 ∘ raw30359step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30359step2 raw30359step2Labels raw30359step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5176 node5176Labels := by rfl

def raw30360 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30360Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30360step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30360step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30360step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30360step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30360 raw30360Labels = mixedMoment B node5129 node5129Labels := by
  calc
    mixedMoment B raw30360 raw30360Labels = mixedMoment B raw30360step0 raw30360step0Labels := by
      have ha : raw30360step0 = (fun i j => raw30360 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30360step0 raw30360; decide +kernel
      have hl : raw30360step0Labels = raw30360Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30360 raw30360Labels permutation152 permutation7
    mixedMoment B raw30360step0 raw30360step0Labels = mixedMoment B raw30360step1 raw30360step1Labels := by
      have ha : raw30360step1 = raw30360step0 := by apply Matrix.ext; unfold raw30360step1 raw30360step0; decide +kernel
      have hl : raw30360step0Labels = labelEmbedding10 ∘ raw30360step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30360step0 raw30360step0Labels raw30360step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5129 node5129Labels := by rfl

def raw30361 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw30361Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30361step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw30361step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30361step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw30361step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30361step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw30361step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30361 raw30361Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw30361 raw30361Labels = mixedMoment B raw30361step0 raw30361step0Labels := by
      have hz : ∀ j, raw30361 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30361step0 = (fun i j => raw30361 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30361step0 raw30361; decide +kernel
      have hl : raw30361step0Labels = raw30361Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30361 raw30361Labels permutation434 hz
    mixedMoment B raw30361step0 raw30361step0Labels = mixedMoment B raw30361step1 raw30361step1Labels := by
      have ha : raw30361step1 = (fun i j => raw30361step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30361step1 raw30361step0; decide +kernel
      have hl : raw30361step1Labels = raw30361step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30361step0 raw30361step0Labels permutation32 permutation7
    mixedMoment B raw30361step1 raw30361step1Labels = mixedMoment B raw30361step2 raw30361step2Labels := by
      have ha : raw30361step2 = raw30361step1 := by apply Matrix.ext; unfold raw30361step2 raw30361step1; decide +kernel
      have hl : raw30361step1Labels = labelEmbedding10 ∘ raw30361step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30361step1 raw30361step1Labels raw30361step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5141 node5141Labels := by rfl

def raw30362 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw30362Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30362step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw30362step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30362step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw30362step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw30362step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw30362step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30362 raw30362Labels = mixedMoment B node5140 node5140Labels := by
  calc
    mixedMoment B raw30362 raw30362Labels = mixedMoment B raw30362step0 raw30362step0Labels := by
      have hz : ∀ j, raw30362 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30362step0 = (fun i j => raw30362 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30362step0 raw30362; decide +kernel
      have hl : raw30362step0Labels = raw30362Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30362 raw30362Labels permutation434 hz
    mixedMoment B raw30362step0 raw30362step0Labels = mixedMoment B raw30362step1 raw30362step1Labels := by
      have ha : raw30362step1 = (fun i j => raw30362step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30362step1 raw30362step0; decide +kernel
      have hl : raw30362step1Labels = raw30362step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30362step0 raw30362step0Labels permutation32 permutation7
    mixedMoment B raw30362step1 raw30362step1Labels = mixedMoment B raw30362step2 raw30362step2Labels := by
      have ha : raw30362step2 = raw30362step1 := by apply Matrix.ext; unfold raw30362step2 raw30362step1; decide +kernel
      have hl : raw30362step1Labels = labelEmbedding10 ∘ raw30362step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30362step1 raw30362step1Labels raw30362step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5140 node5140Labels := by rfl

def raw30363 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30363Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30363step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30363step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30363step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30363step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30363step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30363 raw30363Labels = mixedMoment B node4810 node4810Labels := by
  calc
    mixedMoment B raw30363 raw30363Labels = mixedMoment B raw30363step0 raw30363step0Labels := by
      have hz : ∀ j, raw30363 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30363step0 = (fun i j => raw30363 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30363step0 raw30363; decide +kernel
      have hl : raw30363step0Labels = raw30363Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30363 raw30363Labels permutation434 hz
    mixedMoment B raw30363step0 raw30363step0Labels = mixedMoment B raw30363step1 raw30363step1Labels := by
      have ha : raw30363step1 = (fun i j => raw30363step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30363step1 raw30363step0; decide +kernel
      have hl : raw30363step1Labels = raw30363step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30363step0 raw30363step0Labels permutation33 permutation6
    mixedMoment B raw30363step1 raw30363step1Labels = mixedMoment B raw30363step2 raw30363step2Labels := by
      have ha : raw30363step2 = raw30363step1 := by apply Matrix.ext; unfold raw30363step2 raw30363step1; decide +kernel
      have hl : raw30363step1Labels = labelEmbedding9 ∘ raw30363step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30363step1 raw30363step1Labels raw30363step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4810 node4810Labels := by rfl

def raw30364 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw30364Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw30364step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30364step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw30364step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30364step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw30364step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30364 raw30364Labels = mixedMoment B node5151 node5151Labels := by
  calc
    mixedMoment B raw30364 raw30364Labels = mixedMoment B raw30364step0 raw30364step0Labels := by
      have hz : ∀ j, raw30364 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30364step0 = (fun i j => raw30364 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30364step0 raw30364; decide +kernel
      have hl : raw30364step0Labels = raw30364Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30364 raw30364Labels permutation434 hz
    mixedMoment B raw30364step0 raw30364step0Labels = mixedMoment B raw30364step1 raw30364step1Labels := by
      have ha : raw30364step1 = (fun i j => raw30364step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30364step1 raw30364step0; decide +kernel
      have hl : raw30364step1Labels = raw30364step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30364step0 raw30364step0Labels permutation33 permutation6
    mixedMoment B raw30364step1 raw30364step1Labels = mixedMoment B raw30364step2 raw30364step2Labels := by
      have ha : raw30364step2 = raw30364step1 := by apply Matrix.ext; unfold raw30364step2 raw30364step1; decide +kernel
      have hl : raw30364step1Labels = labelEmbedding9 ∘ raw30364step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30364step1 raw30364step1Labels raw30364step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5151 node5151Labels := by rfl

def raw30365 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30365Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -2, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30365step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30365step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-2, 2, 0], ![-2, 0, 2]]
def raw30365step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30365step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw30365step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw30365step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw30365step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30365 raw30365Labels = mixedMoment B node4749 node4749Labels := by
  calc
    mixedMoment B raw30365 raw30365Labels = mixedMoment B raw30365step0 raw30365step0Labels := by
      have hz : ∀ j, raw30365 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30365step0 = (fun i j => raw30365 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30365step0 raw30365; decide +kernel
      have hl : raw30365step0Labels = raw30365Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30365 raw30365Labels permutation434 hz
    mixedMoment B raw30365step0 raw30365step0Labels = mixedMoment B raw30365step1 raw30365step1Labels := by
      have ha : raw30365step1 = (fun i j => raw30365step0 (permutation36 i) (permutation4 j)) := by apply Matrix.ext; unfold raw30365step1 raw30365step0; decide +kernel
      have hl : raw30365step1Labels = raw30365step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30365step0 raw30365step0Labels permutation36 permutation4
    mixedMoment B raw30365step1 raw30365step1Labels = mixedMoment B raw30365step2 raw30365step2Labels := by
      have ha : raw30365step2 = -raw30365step1 := by apply Matrix.ext; change ∀ i j, raw30365step2 i j = -(raw30365step1 i j); unfold raw30365step2 raw30365step1; decide +kernel
      have hl : raw30365step2Labels = raw30365step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30365step2 raw30365step2Labels = mixedMoment B raw30365step3 raw30365step3Labels := by
      have ha : raw30365step3 = raw30365step2 := by apply Matrix.ext; unfold raw30365step3 raw30365step2; decide +kernel
      have hl : raw30365step2Labels = labelEmbedding7 ∘ raw30365step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30365step2 raw30365step2Labels raw30365step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4749 node4749Labels := by rfl

def raw30366 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![2, -2, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30366Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![2, -2, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30366step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30366step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw30366step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30366step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw30366step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30366 raw30366Labels = mixedMoment B node5009 node5009Labels := by
  calc
    mixedMoment B raw30366 raw30366Labels = mixedMoment B raw30366step0 raw30366step0Labels := by
      have hz : ∀ j, raw30366 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30366step0 = (fun i j => raw30366 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30366step0 raw30366; decide +kernel
      have hl : raw30366step0Labels = raw30366Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30366 raw30366Labels permutation434 hz
    mixedMoment B raw30366step0 raw30366step0Labels = mixedMoment B raw30366step1 raw30366step1Labels := by
      have ha : raw30366step1 = (fun i j => raw30366step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30366step1 raw30366step0; decide +kernel
      have hl : raw30366step1Labels = raw30366step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30366step0 raw30366step0Labels permutation33 permutation6
    mixedMoment B raw30366step1 raw30366step1Labels = mixedMoment B raw30366step2 raw30366step2Labels := by
      have ha : raw30366step2 = raw30366step1 := by apply Matrix.ext; unfold raw30366step2 raw30366step1; decide +kernel
      have hl : raw30366step1Labels = labelEmbedding9 ∘ raw30366step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30366step1 raw30366step1Labels raw30366step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5009 node5009Labels := by rfl

def raw30367 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![2, -2, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30367Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30367step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw30367step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30367step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw30367step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30367 raw30367Labels = mixedMoment B node5053 node5053Labels := by
  calc
    mixedMoment B raw30367 raw30367Labels = mixedMoment B raw30367step0 raw30367step0Labels := by
      have ha : raw30367step0 = (fun i j => raw30367 (permutation159 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30367step0 raw30367; decide +kernel
      have hl : raw30367step0Labels = raw30367Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30367 raw30367Labels permutation159 permutation6
    mixedMoment B raw30367step0 raw30367step0Labels = mixedMoment B raw30367step1 raw30367step1Labels := by
      have ha : raw30367step1 = raw30367step0 := by apply Matrix.ext; unfold raw30367step1 raw30367step0; decide +kernel
      have hl : raw30367step0Labels = labelEmbedding9 ∘ raw30367step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30367step0 raw30367step0Labels raw30367step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5053 node5053Labels := by rfl

def raw30368 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw30368Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![2, -2, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw30368step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30368step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw30368step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30368step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw30368step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30368 raw30368Labels = mixedMoment B node5090 node5090Labels := by
  calc
    mixedMoment B raw30368 raw30368Labels = mixedMoment B raw30368step0 raw30368step0Labels := by
      have hz : ∀ j, raw30368 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30368step0 = (fun i j => raw30368 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30368step0 raw30368; decide +kernel
      have hl : raw30368step0Labels = raw30368Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30368 raw30368Labels permutation434 hz
    mixedMoment B raw30368step0 raw30368step0Labels = mixedMoment B raw30368step1 raw30368step1Labels := by
      have ha : raw30368step1 = (fun i j => raw30368step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30368step1 raw30368step0; decide +kernel
      have hl : raw30368step1Labels = raw30368step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30368step0 raw30368step0Labels permutation33 permutation6
    mixedMoment B raw30368step1 raw30368step1Labels = mixedMoment B raw30368step2 raw30368step2Labels := by
      have ha : raw30368step2 = raw30368step1 := by apply Matrix.ext; unfold raw30368step2 raw30368step1; decide +kernel
      have hl : raw30368step1Labels = labelEmbedding9 ∘ raw30368step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30368step1 raw30368step1Labels raw30368step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5090 node5090Labels := by rfl

def raw30369 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw30369Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30369step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![2, -2, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw30369step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30369step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw30369step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30369step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw30369step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30369 raw30369Labels = mixedMoment B node5089 node5089Labels := by
  calc
    mixedMoment B raw30369 raw30369Labels = mixedMoment B raw30369step0 raw30369step0Labels := by
      have hz : ∀ j, raw30369 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30369step0 = (fun i j => raw30369 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30369step0 raw30369; decide +kernel
      have hl : raw30369step0Labels = raw30369Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30369 raw30369Labels permutation434 hz
    mixedMoment B raw30369step0 raw30369step0Labels = mixedMoment B raw30369step1 raw30369step1Labels := by
      have ha : raw30369step1 = (fun i j => raw30369step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30369step1 raw30369step0; decide +kernel
      have hl : raw30369step1Labels = raw30369step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30369step0 raw30369step0Labels permutation33 permutation6
    mixedMoment B raw30369step1 raw30369step1Labels = mixedMoment B raw30369step2 raw30369step2Labels := by
      have ha : raw30369step2 = raw30369step1 := by apply Matrix.ext; unfold raw30369step2 raw30369step1; decide +kernel
      have hl : raw30369step1Labels = labelEmbedding9 ∘ raw30369step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30369step1 raw30369step1Labels raw30369step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5089 node5089Labels := by rfl

def raw30370 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30370Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30370step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30370step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30370step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30370step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30370 raw30370Labels = mixedMoment B node4731 node4731Labels := by
  calc
    mixedMoment B raw30370 raw30370Labels = mixedMoment B raw30370step0 raw30370step0Labels := by
      have ha : raw30370step0 = (fun i j => raw30370 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30370step0 raw30370; decide +kernel
      have hl : raw30370step0Labels = raw30370Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30370 raw30370Labels permutation153 permutation6
    mixedMoment B raw30370step0 raw30370step0Labels = mixedMoment B raw30370step1 raw30370step1Labels := by
      have ha : raw30370step1 = raw30370step0 := by apply Matrix.ext; unfold raw30370step1 raw30370step0; decide +kernel
      have hl : raw30370step0Labels = labelEmbedding9 ∘ raw30370step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30370step0 raw30370step0Labels raw30370step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4731 node4731Labels := by rfl

def raw30371 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30371Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30371step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30371step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30371step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30371step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30371 raw30371Labels = mixedMoment B node4993 node4993Labels := by
  calc
    mixedMoment B raw30371 raw30371Labels = mixedMoment B raw30371step0 raw30371step0Labels := by
      have ha : raw30371step0 = (fun i j => raw30371 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30371step0 raw30371; decide +kernel
      have hl : raw30371step0Labels = raw30371Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30371 raw30371Labels permutation153 permutation6
    mixedMoment B raw30371step0 raw30371step0Labels = mixedMoment B raw30371step1 raw30371step1Labels := by
      have ha : raw30371step1 = raw30371step0 := by apply Matrix.ext; unfold raw30371step1 raw30371step0; decide +kernel
      have hl : raw30371step0Labels = labelEmbedding9 ∘ raw30371step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30371step0 raw30371step0Labels raw30371step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4993 node4993Labels := by rfl

def raw30372 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30372Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30372step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30372step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30372step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30372step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30372step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30372 raw30372Labels = mixedMoment B node5080 node5080Labels := by
  calc
    mixedMoment B raw30372 raw30372Labels = mixedMoment B raw30372step0 raw30372step0Labels := by
      have hz : ∀ j, raw30372 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30372step0 = (fun i j => raw30372 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30372step0 raw30372; decide +kernel
      have hl : raw30372step0Labels = raw30372Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30372 raw30372Labels permutation346 hz
    mixedMoment B raw30372step0 raw30372step0Labels = mixedMoment B raw30372step1 raw30372step1Labels := by
      have ha : raw30372step1 = (fun i j => raw30372step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30372step1 raw30372step0; decide +kernel
      have hl : raw30372step1Labels = raw30372step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30372step0 raw30372step0Labels permutation33 permutation6
    mixedMoment B raw30372step1 raw30372step1Labels = mixedMoment B raw30372step2 raw30372step2Labels := by
      have ha : raw30372step2 = raw30372step1 := by apply Matrix.ext; unfold raw30372step2 raw30372step1; decide +kernel
      have hl : raw30372step1Labels = labelEmbedding9 ∘ raw30372step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30372step1 raw30372step1Labels raw30372step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5080 node5080Labels := by rfl

def raw30373 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw30373Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30373step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30373step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30373step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30373step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30373 raw30373Labels = mixedMoment B node5067 node5067Labels := by
  calc
    mixedMoment B raw30373 raw30373Labels = mixedMoment B raw30373step0 raw30373step0Labels := by
      have ha : raw30373step0 = (fun i j => raw30373 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30373step0 raw30373; decide +kernel
      have hl : raw30373step0Labels = raw30373Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30373 raw30373Labels permutation153 permutation6
    mixedMoment B raw30373step0 raw30373step0Labels = mixedMoment B raw30373step1 raw30373step1Labels := by
      have ha : raw30373step1 = raw30373step0 := by apply Matrix.ext; unfold raw30373step1 raw30373step0; decide +kernel
      have hl : raw30373step0Labels = labelEmbedding9 ∘ raw30373step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30373step0 raw30373step0Labels raw30373step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5067 node5067Labels := by rfl

def raw30374 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw30374Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30374step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw30374step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30374step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw30374step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30374 raw30374Labels = mixedMoment B node5066 node5066Labels := by
  calc
    mixedMoment B raw30374 raw30374Labels = mixedMoment B raw30374step0 raw30374step0Labels := by
      have ha : raw30374step0 = (fun i j => raw30374 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30374step0 raw30374; decide +kernel
      have hl : raw30374step0Labels = raw30374Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30374 raw30374Labels permutation153 permutation6
    mixedMoment B raw30374step0 raw30374step0Labels = mixedMoment B raw30374step1 raw30374step1Labels := by
      have ha : raw30374step1 = raw30374step0 := by apply Matrix.ext; unfold raw30374step1 raw30374step0; decide +kernel
      have hl : raw30374step0Labels = labelEmbedding9 ∘ raw30374step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30374step0 raw30374step0Labels raw30374step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5066 node5066Labels := by rfl

def raw30375 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw30375Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw30375step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30375step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw30375step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30375step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw30375step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30375 raw30375Labels = mixedMoment B node4744 node4744Labels := by
  calc
    mixedMoment B raw30375 raw30375Labels = mixedMoment B raw30375step0 raw30375step0Labels := by
      have hz : ∀ j, raw30375 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30375step0 = (fun i j => raw30375 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30375step0 raw30375; decide +kernel
      have hl : raw30375step0Labels = raw30375Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30375 raw30375Labels permutation434 hz
    mixedMoment B raw30375step0 raw30375step0Labels = mixedMoment B raw30375step1 raw30375step1Labels := by
      have ha : raw30375step1 = (fun i j => raw30375step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30375step1 raw30375step0; decide +kernel
      have hl : raw30375step1Labels = raw30375step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30375step0 raw30375step0Labels permutation33 permutation6
    mixedMoment B raw30375step1 raw30375step1Labels = mixedMoment B raw30375step2 raw30375step2Labels := by
      have ha : raw30375step2 = raw30375step1 := by apply Matrix.ext; unfold raw30375step2 raw30375step1; decide +kernel
      have hl : raw30375step1Labels = labelEmbedding9 ∘ raw30375step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30375step1 raw30375step1Labels raw30375step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4744 node4744Labels := by rfl

def raw30376 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw30376Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw30376step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30376step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw30376step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30376step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw30376step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30376 raw30376Labels = mixedMoment B node5002 node5002Labels := by
  calc
    mixedMoment B raw30376 raw30376Labels = mixedMoment B raw30376step0 raw30376step0Labels := by
      have hz : ∀ j, raw30376 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30376step0 = (fun i j => raw30376 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30376step0 raw30376; decide +kernel
      have hl : raw30376step0Labels = raw30376Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30376 raw30376Labels permutation434 hz
    mixedMoment B raw30376step0 raw30376step0Labels = mixedMoment B raw30376step1 raw30376step1Labels := by
      have ha : raw30376step1 = (fun i j => raw30376step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30376step1 raw30376step0; decide +kernel
      have hl : raw30376step1Labels = raw30376step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30376step0 raw30376step0Labels permutation33 permutation6
    mixedMoment B raw30376step1 raw30376step1Labels = mixedMoment B raw30376step2 raw30376step2Labels := by
      have ha : raw30376step2 = raw30376step1 := by apply Matrix.ext; unfold raw30376step2 raw30376step1; decide +kernel
      have hl : raw30376step1Labels = labelEmbedding9 ∘ raw30376step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30376step1 raw30376step1Labels raw30376step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5002 node5002Labels := by rfl

def raw30377 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw30377Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30377step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw30377step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30377step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -3, 2], ![-2, 0, 2]]
def raw30377step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30377step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw30377step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30377step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw30377step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30377 raw30377Labels = mixedMoment B node5110 node5110Labels := by
  calc
    mixedMoment B raw30377 raw30377Labels = mixedMoment B raw30377step0 raw30377step0Labels := by
      have hz : ∀ j, raw30377 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30377step0 = (fun i j => raw30377 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30377step0 raw30377; decide +kernel
      have hl : raw30377step0Labels = raw30377Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30377 raw30377Labels permutation434 hz
    mixedMoment B raw30377step0 raw30377step0Labels = mixedMoment B raw30377step1 raw30377step1Labels := by
      have hz : ∀ j, raw30377step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30377step1 = (fun i j => raw30377step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30377step1 raw30377step0; decide +kernel
      have hl : raw30377step1Labels = raw30377step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30377step0 raw30377step0Labels permutation80 hz
    mixedMoment B raw30377step1 raw30377step1Labels = mixedMoment B raw30377step2 raw30377step2Labels := by
      have ha : raw30377step2 = (fun i j => raw30377step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30377step2 raw30377step1; decide +kernel
      have hl : raw30377step2Labels = raw30377step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30377step1 raw30377step1Labels permutation9 permutation6
    mixedMoment B raw30377step2 raw30377step2Labels = mixedMoment B raw30377step3 raw30377step3Labels := by
      have ha : raw30377step3 = raw30377step2 := by apply Matrix.ext; unfold raw30377step3 raw30377step2; decide +kernel
      have hl : raw30377step2Labels = labelEmbedding9 ∘ raw30377step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30377step2 raw30377step2Labels raw30377step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5110 node5110Labels := by rfl

def raw30378 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw30378Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30378step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw30378step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30378step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw30378step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30378 raw30378Labels = mixedMoment B node5049 node5049Labels := by
  calc
    mixedMoment B raw30378 raw30378Labels = mixedMoment B raw30378step0 raw30378step0Labels := by
      have ha : raw30378step0 = (fun i j => raw30378 (permutation159 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30378step0 raw30378; decide +kernel
      have hl : raw30378step0Labels = raw30378Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30378 raw30378Labels permutation159 permutation6
    mixedMoment B raw30378step0 raw30378step0Labels = mixedMoment B raw30378step1 raw30378step1Labels := by
      have ha : raw30378step1 = raw30378step0 := by apply Matrix.ext; unfold raw30378step1 raw30378step0; decide +kernel
      have hl : raw30378step0Labels = labelEmbedding9 ∘ raw30378step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30378step0 raw30378step0Labels raw30378step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5049 node5049Labels := by rfl

def raw30379 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw30379Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30379step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw30379step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30379step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw30379step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30379step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw30379step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30379 raw30379Labels = mixedMoment B node5079 node5079Labels := by
  calc
    mixedMoment B raw30379 raw30379Labels = mixedMoment B raw30379step0 raw30379step0Labels := by
      have hz : ∀ j, raw30379 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30379step0 = (fun i j => raw30379 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30379step0 raw30379; decide +kernel
      have hl : raw30379step0Labels = raw30379Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30379 raw30379Labels permutation434 hz
    mixedMoment B raw30379step0 raw30379step0Labels = mixedMoment B raw30379step1 raw30379step1Labels := by
      have ha : raw30379step1 = (fun i j => raw30379step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30379step1 raw30379step0; decide +kernel
      have hl : raw30379step1Labels = raw30379step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30379step0 raw30379step0Labels permutation33 permutation6
    mixedMoment B raw30379step1 raw30379step1Labels = mixedMoment B raw30379step2 raw30379step2Labels := by
      have ha : raw30379step2 = raw30379step1 := by apply Matrix.ext; unfold raw30379step2 raw30379step1; decide +kernel
      have hl : raw30379step1Labels = labelEmbedding9 ∘ raw30379step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30379step1 raw30379step1Labels raw30379step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5079 node5079Labels := by rfl

def raw30380 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw30380Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30380step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw30380step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30380step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30380step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30380step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30380step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30380 raw30380Labels = mixedMoment B node4745 node4745Labels := by
  calc
    mixedMoment B raw30380 raw30380Labels = mixedMoment B raw30380step0 raw30380step0Labels := by
      have hz : ∀ j, raw30380 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30380step0 = (fun i j => raw30380 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30380step0 raw30380; decide +kernel
      have hl : raw30380step0Labels = raw30380Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30380 raw30380Labels permutation434 hz
    mixedMoment B raw30380step0 raw30380step0Labels = mixedMoment B raw30380step1 raw30380step1Labels := by
      have ha : raw30380step1 = (fun i j => raw30380step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30380step1 raw30380step0; decide +kernel
      have hl : raw30380step1Labels = raw30380step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30380step0 raw30380step0Labels permutation33 permutation6
    mixedMoment B raw30380step1 raw30380step1Labels = mixedMoment B raw30380step2 raw30380step2Labels := by
      have ha : raw30380step2 = raw30380step1 := by apply Matrix.ext; unfold raw30380step2 raw30380step1; decide +kernel
      have hl : raw30380step1Labels = labelEmbedding9 ∘ raw30380step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30380step1 raw30380step1Labels raw30380step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4745 node4745Labels := by rfl

def raw30381 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw30381Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw30381step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30381step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30381step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw30381step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30381step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30381 raw30381Labels = mixedMoment B node5003 node5003Labels := by
  calc
    mixedMoment B raw30381 raw30381Labels = mixedMoment B raw30381step0 raw30381step0Labels := by
      have hz : ∀ j, raw30381 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30381step0 = (fun i j => raw30381 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30381step0 raw30381; decide +kernel
      have hl : raw30381step0Labels = raw30381Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30381 raw30381Labels permutation434 hz
    mixedMoment B raw30381step0 raw30381step0Labels = mixedMoment B raw30381step1 raw30381step1Labels := by
      have ha : raw30381step1 = (fun i j => raw30381step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30381step1 raw30381step0; decide +kernel
      have hl : raw30381step1Labels = raw30381step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30381step0 raw30381step0Labels permutation33 permutation6
    mixedMoment B raw30381step1 raw30381step1Labels = mixedMoment B raw30381step2 raw30381step2Labels := by
      have ha : raw30381step2 = raw30381step1 := by apply Matrix.ext; unfold raw30381step2 raw30381step1; decide +kernel
      have hl : raw30381step1Labels = labelEmbedding9 ∘ raw30381step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30381step1 raw30381step1Labels raw30381step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5003 node5003Labels := by rfl

def raw30382 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30382Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30382step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30382step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30382step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30382step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30382 raw30382Labels = mixedMoment B node2867 node2867Labels := by
  calc
    mixedMoment B raw30382 raw30382Labels = mixedMoment B raw30382step0 raw30382step0Labels := by
      have hz : ∀ j, raw30382 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30382step0 = (fun i j => raw30382 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30382step0 raw30382; decide +kernel
      have hl : raw30382step0Labels = raw30382Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30382 raw30382Labels permutation434 hz
    mixedMoment B raw30382step0 raw30382step0Labels = mixedMoment B raw30382step1 raw30382step1Labels := by
      have ha : raw30382step1 = (fun i j => raw30382step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30382step1 raw30382step0; decide +kernel
      have hl : raw30382step1Labels = raw30382step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30382step0 raw30382step0Labels permutation33 permutation6
    _ = mixedMoment B node2867 node2867Labels := by rfl

def raw30383 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30383Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30383step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30383step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30383step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -2, 2], ![-2, 0, 2]]
def raw30383step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30383step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw30383step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30383 raw30383Labels = mixedMoment B node2968 node2968Labels := by
  calc
    mixedMoment B raw30383 raw30383Labels = mixedMoment B raw30383step0 raw30383step0Labels := by
      have hz : ∀ j, raw30383 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30383step0 = (fun i j => raw30383 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30383step0 raw30383; decide +kernel
      have hl : raw30383step0Labels = raw30383Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30383 raw30383Labels permutation434 hz
    mixedMoment B raw30383step0 raw30383step0Labels = mixedMoment B raw30383step1 raw30383step1Labels := by
      have hz : ∀ j, raw30383step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30383step1 = (fun i j => raw30383step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30383step1 raw30383step0; decide +kernel
      have hl : raw30383step1Labels = raw30383step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30383step0 raw30383step0Labels permutation80 hz
    mixedMoment B raw30383step1 raw30383step1Labels = mixedMoment B raw30383step2 raw30383step2Labels := by
      have ha : raw30383step2 = (fun i j => raw30383step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30383step2 raw30383step1; decide +kernel
      have hl : raw30383step2Labels = raw30383step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30383step1 raw30383step1Labels permutation9 permutation6
    _ = mixedMoment B node2968 node2968Labels := by rfl

def raw30384 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30384Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30384step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30384step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30384 raw30384Labels = mixedMoment B node2916 node2916Labels := by
  calc
    mixedMoment B raw30384 raw30384Labels = mixedMoment B raw30384step0 raw30384step0Labels := by
      have ha : raw30384step0 = (fun i j => raw30384 (permutation159 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30384step0 raw30384; decide +kernel
      have hl : raw30384step0Labels = raw30384Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30384 raw30384Labels permutation159 permutation6
    _ = mixedMoment B node2916 node2916Labels := by rfl

def raw30385 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw30385Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw30385step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30385step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30385step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30385 raw30385Labels = mixedMoment B node2943 node2943Labels := by
  calc
    mixedMoment B raw30385 raw30385Labels = mixedMoment B raw30385step0 raw30385step0Labels := by
      have hz : ∀ j, raw30385 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30385step0 = (fun i j => raw30385 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30385step0 raw30385; decide +kernel
      have hl : raw30385step0Labels = raw30385Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30385 raw30385Labels permutation434 hz
    mixedMoment B raw30385step0 raw30385step0Labels = mixedMoment B raw30385step1 raw30385step1Labels := by
      have ha : raw30385step1 = (fun i j => raw30385step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30385step1 raw30385step0; decide +kernel
      have hl : raw30385step1Labels = raw30385step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30385step0 raw30385step0Labels permutation33 permutation6
    _ = mixedMoment B node2943 node2943Labels := by rfl

def raw30386 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw30386Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw30386step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30386step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw30386step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30386 raw30386Labels = mixedMoment B node2942 node2942Labels := by
  calc
    mixedMoment B raw30386 raw30386Labels = mixedMoment B raw30386step0 raw30386step0Labels := by
      have hz : ∀ j, raw30386 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30386step0 = (fun i j => raw30386 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30386step0 raw30386; decide +kernel
      have hl : raw30386step0Labels = raw30386Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30386 raw30386Labels permutation434 hz
    mixedMoment B raw30386step0 raw30386step0Labels = mixedMoment B raw30386step1 raw30386step1Labels := by
      have ha : raw30386step1 = (fun i j => raw30386step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30386step1 raw30386step0; decide +kernel
      have hl : raw30386step1Labels = raw30386step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30386step0 raw30386step0Labels permutation33 permutation6
    _ = mixedMoment B node2942 node2942Labels := by rfl

def raw30387 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30387Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30387step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30387step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30387step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30387step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30387 raw30387Labels = mixedMoment B node2028 node2028Labels := by
  calc
    mixedMoment B raw30387 raw30387Labels = mixedMoment B raw30387step0 raw30387step0Labels := by
      have hz : ∀ j, raw30387 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30387step0 = (fun i j => raw30387 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30387step0 raw30387; decide +kernel
      have hl : raw30387step0Labels = raw30387Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30387 raw30387Labels permutation434 hz
    mixedMoment B raw30387step0 raw30387step0Labels = mixedMoment B raw30387step1 raw30387step1Labels := by
      have ha : raw30387step1 = (fun i j => raw30387step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30387step1 raw30387step0; decide +kernel
      have hl : raw30387step1Labels = raw30387step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30387step0 raw30387step0Labels permutation33 permutation6
    _ = mixedMoment B node2028 node2028Labels := by rfl

def raw30388 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30388Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30388step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30388step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, -2, 2], ![-2, 0, 2]]
def raw30388step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30388step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw30388step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30388 raw30388Labels = mixedMoment B node2604 node2604Labels := by
  calc
    mixedMoment B raw30388 raw30388Labels = mixedMoment B raw30388step0 raw30388step0Labels := by
      have hz : ∀ j, raw30388 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30388step0 = (fun i j => raw30388 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30388step0 raw30388; decide +kernel
      have hl : raw30388step0Labels = raw30388Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30388 raw30388Labels permutation434 hz
    mixedMoment B raw30388step0 raw30388step0Labels = mixedMoment B raw30388step1 raw30388step1Labels := by
      have hz : ∀ j, raw30388step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30388step1 = (fun i j => raw30388step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30388step1 raw30388step0; decide +kernel
      have hl : raw30388step1Labels = raw30388step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30388step0 raw30388step0Labels permutation80 hz
    mixedMoment B raw30388step1 raw30388step1Labels = mixedMoment B raw30388step2 raw30388step2Labels := by
      have ha : raw30388step2 = (fun i j => raw30388step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30388step2 raw30388step1; decide +kernel
      have hl : raw30388step2Labels = raw30388step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30388step1 raw30388step1Labels permutation9 permutation6
    _ = mixedMoment B node2604 node2604Labels := by rfl

def raw30389 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30389Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30389step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30389step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30389 raw30389Labels = mixedMoment B node2545 node2545Labels := by
  calc
    mixedMoment B raw30389 raw30389Labels = mixedMoment B raw30389step0 raw30389step0Labels := by
      have ha : raw30389step0 = (fun i j => raw30389 (permutation159 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30389step0 raw30389; decide +kernel
      have hl : raw30389step0Labels = raw30389Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30389 raw30389Labels permutation159 permutation6
    _ = mixedMoment B node2545 node2545Labels := by rfl

def raw30390 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw30390Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30390step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw30390step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30390step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30390step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30390 raw30390Labels = mixedMoment B node2576 node2576Labels := by
  calc
    mixedMoment B raw30390 raw30390Labels = mixedMoment B raw30390step0 raw30390step0Labels := by
      have hz : ∀ j, raw30390 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30390step0 = (fun i j => raw30390 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30390step0 raw30390; decide +kernel
      have hl : raw30390step0Labels = raw30390Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30390 raw30390Labels permutation434 hz
    mixedMoment B raw30390step0 raw30390step0Labels = mixedMoment B raw30390step1 raw30390step1Labels := by
      have ha : raw30390step1 = (fun i j => raw30390step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30390step1 raw30390step0; decide +kernel
      have hl : raw30390step1Labels = raw30390step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30390step0 raw30390step0Labels permutation33 permutation6
    _ = mixedMoment B node2576 node2576Labels := by rfl

def raw30391 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw30391Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30391step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw30391step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30391step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw30391step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30391 raw30391Labels = mixedMoment B node2575 node2575Labels := by
  calc
    mixedMoment B raw30391 raw30391Labels = mixedMoment B raw30391step0 raw30391step0Labels := by
      have hz : ∀ j, raw30391 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30391step0 = (fun i j => raw30391 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30391step0 raw30391; decide +kernel
      have hl : raw30391step0Labels = raw30391Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30391 raw30391Labels permutation434 hz
    mixedMoment B raw30391step0 raw30391step0Labels = mixedMoment B raw30391step1 raw30391step1Labels := by
      have ha : raw30391step1 = (fun i j => raw30391step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30391step1 raw30391step0; decide +kernel
      have hl : raw30391step1Labels = raw30391step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30391step0 raw30391step0Labels permutation33 permutation6
    _ = mixedMoment B node2575 node2575Labels := by rfl

def raw30392 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30392Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30392step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![2, -2, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30392step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30392step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw30392step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30392 raw30392Labels = mixedMoment B node1928 node1928Labels := by
  calc
    mixedMoment B raw30392 raw30392Labels = mixedMoment B raw30392step0 raw30392step0Labels := by
      have hz : ∀ j, raw30392 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30392step0 = (fun i j => raw30392 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30392step0 raw30392; decide +kernel
      have hl : raw30392step0Labels = raw30392Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30392 raw30392Labels permutation434 hz
    mixedMoment B raw30392step0 raw30392step0Labels = mixedMoment B raw30392step1 raw30392step1Labels := by
      have ha : raw30392step1 = (fun i j => raw30392step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30392step1 raw30392step0; decide +kernel
      have hl : raw30392step1Labels = raw30392step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30392step0 raw30392step0Labels permutation33 permutation6
    _ = mixedMoment B node1928 node1928Labels := by rfl

def raw30393 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![2, -2, 0], ![0, 0, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30393Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30393step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![2, -2, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30393step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30393step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw30393step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30393 raw30393Labels = mixedMoment B node2394 node2394Labels := by
  calc
    mixedMoment B raw30393 raw30393Labels = mixedMoment B raw30393step0 raw30393step0Labels := by
      have hz : ∀ j, raw30393 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30393step0 = (fun i j => raw30393 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30393step0 raw30393; decide +kernel
      have hl : raw30393step0Labels = raw30393Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30393 raw30393Labels permutation434 hz
    mixedMoment B raw30393step0 raw30393step0Labels = mixedMoment B raw30393step1 raw30393step1Labels := by
      have ha : raw30393step1 = (fun i j => raw30393step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30393step1 raw30393step0; decide +kernel
      have hl : raw30393step1Labels = raw30393step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30393step0 raw30393step0Labels permutation33 permutation6
    _ = mixedMoment B node2394 node2394Labels := by rfl

def raw30394 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![2, -2, 0], ![-1, 1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30394Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30394step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0], ![2, 0, -2]]
def raw30394step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30394 raw30394Labels = mixedMoment B node2455 node2455Labels := by
  calc
    mixedMoment B raw30394 raw30394Labels = mixedMoment B raw30394step0 raw30394step0Labels := by
      have ha : raw30394step0 = (fun i j => raw30394 (permutation159 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30394step0 raw30394; decide +kernel
      have hl : raw30394step0Labels = raw30394Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30394 raw30394Labels permutation159 permutation6
    _ = mixedMoment B node2455 node2455Labels := by rfl

def raw30395 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw30395Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![2, -2, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw30395step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30395step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw30395step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30395 raw30395Labels = mixedMoment B node2499 node2499Labels := by
  calc
    mixedMoment B raw30395 raw30395Labels = mixedMoment B raw30395step0 raw30395step0Labels := by
      have hz : ∀ j, raw30395 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30395step0 = (fun i j => raw30395 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30395step0 raw30395; decide +kernel
      have hl : raw30395step0Labels = raw30395Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30395 raw30395Labels permutation434 hz
    mixedMoment B raw30395step0 raw30395step0Labels = mixedMoment B raw30395step1 raw30395step1Labels := by
      have ha : raw30395step1 = (fun i j => raw30395step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30395step1 raw30395step0; decide +kernel
      have hl : raw30395step1Labels = raw30395step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30395step0 raw30395step0Labels permutation33 permutation6
    _ = mixedMoment B node2499 node2499Labels := by rfl

def raw30396 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw30396Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30396step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![2, -2, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw30396step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30396step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![2, -3, 1], ![2, 0, -2]]
def raw30396step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30396 raw30396Labels = mixedMoment B node2498 node2498Labels := by
  calc
    mixedMoment B raw30396 raw30396Labels = mixedMoment B raw30396step0 raw30396step0Labels := by
      have hz : ∀ j, raw30396 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30396step0 = (fun i j => raw30396 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30396step0 raw30396; decide +kernel
      have hl : raw30396step0Labels = raw30396Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30396 raw30396Labels permutation434 hz
    mixedMoment B raw30396step0 raw30396step0Labels = mixedMoment B raw30396step1 raw30396step1Labels := by
      have ha : raw30396step1 = (fun i j => raw30396step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30396step1 raw30396step0; decide +kernel
      have hl : raw30396step1Labels = raw30396step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30396step0 raw30396step0Labels permutation33 permutation6
    _ = mixedMoment B node2498 node2498Labels := by rfl

def raw30397 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30397Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30397step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30397step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30397 raw30397Labels = mixedMoment B node1900 node1900Labels := by
  calc
    mixedMoment B raw30397 raw30397Labels = mixedMoment B raw30397step0 raw30397step0Labels := by
      have ha : raw30397step0 = (fun i j => raw30397 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30397step0 raw30397; decide +kernel
      have hl : raw30397step0Labels = raw30397Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30397 raw30397Labels permutation153 permutation6
    _ = mixedMoment B node1900 node1900Labels := by rfl

def raw30398 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30398Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30398step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30398step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30398 raw30398Labels = mixedMoment B node2379 node2379Labels := by
  calc
    mixedMoment B raw30398 raw30398Labels = mixedMoment B raw30398step0 raw30398step0Labels := by
      have ha : raw30398step0 = (fun i j => raw30398 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30398step0 raw30398; decide +kernel
      have hl : raw30398step0Labels = raw30398Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30398 raw30398Labels permutation153 permutation6
    _ = mixedMoment B node2379 node2379Labels := by rfl

def raw30399 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30399Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 0, 2]]
def raw30399step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30399step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw30399step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30399 raw30399Labels = mixedMoment B node2488 node2488Labels := by
  calc
    mixedMoment B raw30399 raw30399Labels = mixedMoment B raw30399step0 raw30399step0Labels := by
      have hz : ∀ j, raw30399 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw30399step0 = (fun i j => raw30399 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw30399step0 raw30399; decide +kernel
      have hl : raw30399step0Labels = raw30399Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30399 raw30399Labels permutation346 hz
    mixedMoment B raw30399step0 raw30399step0Labels = mixedMoment B raw30399step1 raw30399step1Labels := by
      have ha : raw30399step1 = (fun i j => raw30399step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30399step1 raw30399step0; decide +kernel
      have hl : raw30399step1Labels = raw30399step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30399step0 raw30399step0Labels permutation33 permutation6
    _ = mixedMoment B node2488 node2488Labels := by rfl

def raw30400 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw30400Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30400step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw30400step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30400 raw30400Labels = mixedMoment B node2473 node2473Labels := by
  calc
    mixedMoment B raw30400 raw30400Labels = mixedMoment B raw30400step0 raw30400step0Labels := by
      have ha : raw30400step0 = (fun i j => raw30400 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30400step0 raw30400; decide +kernel
      have hl : raw30400step0Labels = raw30400Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30400 raw30400Labels permutation153 permutation6
    _ = mixedMoment B node2473 node2473Labels := by rfl

def raw30401 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, -2, 2], ![-3, 1, 2]]
def raw30401Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30401step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw30401step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30401 raw30401Labels = mixedMoment B node2472 node2472Labels := by
  calc
    mixedMoment B raw30401 raw30401Labels = mixedMoment B raw30401step0 raw30401step0Labels := by
      have ha : raw30401step0 = (fun i j => raw30401 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30401step0 raw30401; decide +kernel
      have hl : raw30401step0Labels = raw30401Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30401 raw30401Labels permutation153 permutation6
    _ = mixedMoment B node2472 node2472Labels := by rfl

def raw30402 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw30402Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30402step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw30402step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30402step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw30402step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30402 raw30402Labels = mixedMoment B node1917 node1917Labels := by
  calc
    mixedMoment B raw30402 raw30402Labels = mixedMoment B raw30402step0 raw30402step0Labels := by
      have hz : ∀ j, raw30402 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30402step0 = (fun i j => raw30402 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30402step0 raw30402; decide +kernel
      have hl : raw30402step0Labels = raw30402Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30402 raw30402Labels permutation434 hz
    mixedMoment B raw30402step0 raw30402step0Labels = mixedMoment B raw30402step1 raw30402step1Labels := by
      have ha : raw30402step1 = (fun i j => raw30402step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30402step1 raw30402step0; decide +kernel
      have hl : raw30402step1Labels = raw30402step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30402step0 raw30402step0Labels permutation33 permutation6
    _ = mixedMoment B node1917 node1917Labels := by rfl

def raw30403 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw30403Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw30403step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30403step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw30403step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30403 raw30403Labels = mixedMoment B node2387 node2387Labels := by
  calc
    mixedMoment B raw30403 raw30403Labels = mixedMoment B raw30403step0 raw30403step0Labels := by
      have hz : ∀ j, raw30403 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30403step0 = (fun i j => raw30403 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30403step0 raw30403; decide +kernel
      have hl : raw30403step0Labels = raw30403Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30403 raw30403Labels permutation434 hz
    mixedMoment B raw30403step0 raw30403step0Labels = mixedMoment B raw30403step1 raw30403step1Labels := by
      have ha : raw30403step1 = (fun i j => raw30403step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30403step1 raw30403step0; decide +kernel
      have hl : raw30403step1Labels = raw30403step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30403step0 raw30403step0Labels permutation33 permutation6
    _ = mixedMoment B node2387 node2387Labels := by rfl

def raw30404 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw30404Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw30404step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30404step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -3, 2], ![-2, 0, 2]]
def raw30404step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30404step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw30404step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30404 raw30404Labels = mixedMoment B node2522 node2522Labels := by
  calc
    mixedMoment B raw30404 raw30404Labels = mixedMoment B raw30404step0 raw30404step0Labels := by
      have hz : ∀ j, raw30404 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30404step0 = (fun i j => raw30404 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30404step0 raw30404; decide +kernel
      have hl : raw30404step0Labels = raw30404Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30404 raw30404Labels permutation434 hz
    mixedMoment B raw30404step0 raw30404step0Labels = mixedMoment B raw30404step1 raw30404step1Labels := by
      have hz : ∀ j, raw30404step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30404step1 = (fun i j => raw30404step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30404step1 raw30404step0; decide +kernel
      have hl : raw30404step1Labels = raw30404step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30404step0 raw30404step0Labels permutation80 hz
    mixedMoment B raw30404step1 raw30404step1Labels = mixedMoment B raw30404step2 raw30404step2Labels := by
      have ha : raw30404step2 = (fun i j => raw30404step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30404step2 raw30404step1; decide +kernel
      have hl : raw30404step2Labels = raw30404step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30404step1 raw30404step1Labels permutation9 permutation6
    _ = mixedMoment B node2522 node2522Labels := by rfl

def raw30405 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -3, 2], ![-2, 0, 2]]
def raw30405Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30405step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw30405step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30405 raw30405Labels = mixedMoment B node2451 node2451Labels := by
  calc
    mixedMoment B raw30405 raw30405Labels = mixedMoment B raw30405step0 raw30405step0Labels := by
      have ha : raw30405step0 = (fun i j => raw30405 (permutation159 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30405step0 raw30405; decide +kernel
      have hl : raw30405step0Labels = raw30405Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30405 raw30405Labels permutation159 permutation6
    _ = mixedMoment B node2451 node2451Labels := by rfl

def raw30406 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw30406Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![1, -3, 2], ![-3, 1, 2]]
def raw30406step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30406step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw30406step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30406 raw30406Labels = mixedMoment B node2487 node2487Labels := by
  calc
    mixedMoment B raw30406 raw30406Labels = mixedMoment B raw30406step0 raw30406step0Labels := by
      have hz : ∀ j, raw30406 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30406step0 = (fun i j => raw30406 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30406step0 raw30406; decide +kernel
      have hl : raw30406step0Labels = raw30406Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30406 raw30406Labels permutation434 hz
    mixedMoment B raw30406step0 raw30406step0Labels = mixedMoment B raw30406step1 raw30406step1Labels := by
      have ha : raw30406step1 = (fun i j => raw30406step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30406step1 raw30406step0; decide +kernel
      have hl : raw30406step1Labels = raw30406step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30406step0 raw30406step0Labels permutation33 permutation6
    _ = mixedMoment B node2487 node2487Labels := by rfl

def raw30407 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw30407Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30407step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw30407step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30407step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30407step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30407 raw30407Labels = mixedMoment B node1918 node1918Labels := by
  calc
    mixedMoment B raw30407 raw30407Labels = mixedMoment B raw30407step0 raw30407step0Labels := by
      have hz : ∀ j, raw30407 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30407step0 = (fun i j => raw30407 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30407step0 raw30407; decide +kernel
      have hl : raw30407step0Labels = raw30407Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30407 raw30407Labels permutation434 hz
    mixedMoment B raw30407step0 raw30407step0Labels = mixedMoment B raw30407step1 raw30407step1Labels := by
      have ha : raw30407step1 = (fun i j => raw30407step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30407step1 raw30407step0; decide +kernel
      have hl : raw30407step1Labels = raw30407step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30407step0 raw30407step0Labels permutation33 permutation6
    _ = mixedMoment B node1918 node1918Labels := by rfl

def raw30408 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw30408Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw30408step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30408step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30408step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30408 raw30408Labels = mixedMoment B node2388 node2388Labels := by
  calc
    mixedMoment B raw30408 raw30408Labels = mixedMoment B raw30408step0 raw30408step0Labels := by
      have hz : ∀ j, raw30408 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30408step0 = (fun i j => raw30408 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30408step0 raw30408; decide +kernel
      have hl : raw30408step0Labels = raw30408Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30408 raw30408Labels permutation434 hz
    mixedMoment B raw30408step0 raw30408step0Labels = mixedMoment B raw30408step1 raw30408step1Labels := by
      have ha : raw30408step1 = (fun i j => raw30408step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30408step1 raw30408step0; decide +kernel
      have hl : raw30408step1Labels = raw30408step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30408step0 raw30408step0Labels permutation33 permutation6
    _ = mixedMoment B node2388 node2388Labels := by rfl

def raw30409 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw30409Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw30409step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30409step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, -2, 2], ![-1, -1, 2]]
def raw30409step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30409step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -1, -1], ![2, 0, -2]]
def raw30409step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30409 raw30409Labels = mixedMoment B node2523 node2523Labels := by
  calc
    mixedMoment B raw30409 raw30409Labels = mixedMoment B raw30409step0 raw30409step0Labels := by
      have hz : ∀ j, raw30409 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30409step0 = (fun i j => raw30409 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30409step0 raw30409; decide +kernel
      have hl : raw30409step0Labels = raw30409Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30409 raw30409Labels permutation434 hz
    mixedMoment B raw30409step0 raw30409step0Labels = mixedMoment B raw30409step1 raw30409step1Labels := by
      have hz : ∀ j, raw30409step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw30409step1 = (fun i j => raw30409step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw30409step1 raw30409step0; decide +kernel
      have hl : raw30409step1Labels = raw30409step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30409step0 raw30409step0Labels permutation80 hz
    mixedMoment B raw30409step1 raw30409step1Labels = mixedMoment B raw30409step2 raw30409step2Labels := by
      have ha : raw30409step2 = (fun i j => raw30409step1 (permutation9 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30409step2 raw30409step1; decide +kernel
      have hl : raw30409step2Labels = raw30409step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30409step1 raw30409step1Labels permutation9 permutation6
    _ = mixedMoment B node2523 node2523Labels := by rfl

def raw30410 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -2, 2], ![-1, -1, 2]]
def raw30410Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30410step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw30410step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30410 raw30410Labels = mixedMoment B node2452 node2452Labels := by
  calc
    mixedMoment B raw30410 raw30410Labels = mixedMoment B raw30410step0 raw30410step0Labels := by
      have ha : raw30410step0 = (fun i j => raw30410 (permutation159 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30410step0 raw30410; decide +kernel
      have hl : raw30410step0Labels = raw30410Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30410 raw30410Labels permutation159 permutation6
    _ = mixedMoment B node2452 node2452Labels := by rfl

def raw30411 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw30411Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30411step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw30411step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw30411step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30411step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30411 raw30411Labels = mixedMoment B node2489 node2489Labels := by
  calc
    mixedMoment B raw30411 raw30411Labels = mixedMoment B raw30411step0 raw30411step0Labels := by
      have hz : ∀ j, raw30411 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30411step0 = (fun i j => raw30411 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30411step0 raw30411; decide +kernel
      have hl : raw30411step0Labels = raw30411Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30411 raw30411Labels permutation434 hz
    mixedMoment B raw30411step0 raw30411step0Labels = mixedMoment B raw30411step1 raw30411step1Labels := by
      have ha : raw30411step1 = (fun i j => raw30411step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw30411step1 raw30411step0; decide +kernel
      have hl : raw30411step1Labels = raw30411step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30411step0 raw30411step0Labels permutation32 permutation6
    _ = mixedMoment B node2489 node2489Labels := by rfl

def raw30412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30412Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30412step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30412step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30412 raw30412Labels = mixedMoment B node5356 node5356Labels := by
  calc
    mixedMoment B raw30412 raw30412Labels = mixedMoment B raw30412step0 raw30412step0Labels := by
      have hz : ∀ j, raw30412 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30412step0 = (fun i j => raw30412 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30412step0 raw30412; decide +kernel
      have hl : raw30412step0Labels = raw30412Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30412 raw30412Labels permutation434 hz
    _ = mixedMoment B node5356 node5356Labels := by rfl

def raw30413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30413Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30413step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30413 raw30413Labels = mixedMoment B node5404 node5404Labels := by
  calc
    mixedMoment B raw30413 raw30413Labels = mixedMoment B raw30413step0 raw30413step0Labels := by
      have hz : ∀ j, raw30413 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30413step0 = (fun i j => raw30413 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30413step0 raw30413; decide +kernel
      have hl : raw30413step0Labels = raw30413Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30413 raw30413Labels permutation434 hz
    _ = mixedMoment B node5404 node5404Labels := by rfl

def raw30414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30414Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30414step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30414step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30414 raw30414Labels = mixedMoment B node5393 node5393Labels := by
  calc
    mixedMoment B raw30414 raw30414Labels = mixedMoment B raw30414step0 raw30414step0Labels := by
      have ha : raw30414step0 = (fun i j => raw30414 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30414step0 raw30414; decide +kernel
      have hl : raw30414step0Labels = raw30414Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30414 raw30414Labels permutation158 permutation2
    _ = mixedMoment B node5393 node5393Labels := by rfl

def raw30415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw30415Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30415step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw30415step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30415 raw30415Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw30415 raw30415Labels = mixedMoment B raw30415step0 raw30415step0Labels := by
      have hz : ∀ j, raw30415 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30415step0 = (fun i j => raw30415 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30415step0 raw30415; decide +kernel
      have hl : raw30415step0Labels = raw30415Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30415 raw30415Labels permutation434 hz
    _ = mixedMoment B node5410 node5410Labels := by rfl

def raw30416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw30416Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw30416step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30416step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw30416step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30416 raw30416Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw30416 raw30416Labels = mixedMoment B raw30416step0 raw30416step0Labels := by
      have hz : ∀ j, raw30416 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30416step0 = (fun i j => raw30416 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30416step0 raw30416; decide +kernel
      have hl : raw30416step0Labels = raw30416Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30416 raw30416Labels permutation434 hz
    mixedMoment B raw30416step0 raw30416step0Labels = mixedMoment B raw30416step1 raw30416step1Labels := by
      have ha : raw30416step1 = (fun i j => raw30416step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30416step1 raw30416step0; decide +kernel
      have hl : raw30416step1Labels = raw30416step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30416step0 raw30416step0Labels permutation33 permutation2
    _ = mixedMoment B node5410 node5410Labels := by rfl

def raw30417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30417Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30417step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30417 raw30417Labels = mixedMoment B node4593 node4593Labels := by
  calc
    mixedMoment B raw30417 raw30417Labels = mixedMoment B raw30417step0 raw30417step0Labels := by
      have hz : ∀ j, raw30417 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30417step0 = (fun i j => raw30417 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30417step0 raw30417; decide +kernel
      have hl : raw30417step0Labels = raw30417Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30417 raw30417Labels permutation434 hz
    _ = mixedMoment B node4593 node4593Labels := by rfl

def raw30418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30418Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30418step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30418step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw30418step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30418 raw30418Labels = mixedMoment B node5189 node5189Labels := by
  calc
    mixedMoment B raw30418 raw30418Labels = mixedMoment B raw30418step0 raw30418step0Labels := by
      have hz : ∀ j, raw30418 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30418step0 = (fun i j => raw30418 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30418step0 raw30418; decide +kernel
      have hl : raw30418step0Labels = raw30418Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30418 raw30418Labels permutation434 hz
    mixedMoment B raw30418step0 raw30418step0Labels = mixedMoment B raw30418step1 raw30418step1Labels := by
      have ha : raw30418step1 = (fun i j => raw30418step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30418step1 raw30418step0; decide +kernel
      have hl : raw30418step1Labels = raw30418step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30418step0 raw30418step0Labels permutation38 permutation2
    _ = mixedMoment B node5189 node5189Labels := by rfl

def raw30419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30419Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30419step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30419step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30419 raw30419Labels = mixedMoment B node5130 node5130Labels := by
  calc
    mixedMoment B raw30419 raw30419Labels = mixedMoment B raw30419step0 raw30419step0Labels := by
      have ha : raw30419step0 = (fun i j => raw30419 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30419step0 raw30419; decide +kernel
      have hl : raw30419step0Labels = raw30419Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30419 raw30419Labels permutation200 permutation2
    _ = mixedMoment B node5130 node5130Labels := by rfl

def raw30420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw30420Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw30420step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30420 raw30420Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw30420 raw30420Labels = mixedMoment B raw30420step0 raw30420step0Labels := by
      have hz : ∀ j, raw30420 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30420step0 = (fun i j => raw30420 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30420step0 raw30420; decide +kernel
      have hl : raw30420step0Labels = raw30420Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30420 raw30420Labels permutation434 hz
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw30421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw30421Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30421step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw30421step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30421step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw30421step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30421 raw30421Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw30421 raw30421Labels = mixedMoment B raw30421step0 raw30421step0Labels := by
      have hz : ∀ j, raw30421 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30421step0 = (fun i j => raw30421 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30421step0 raw30421; decide +kernel
      have hl : raw30421step0Labels = raw30421Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30421 raw30421Labels permutation434 hz
    mixedMoment B raw30421step0 raw30421step0Labels = mixedMoment B raw30421step1 raw30421step1Labels := by
      have ha : raw30421step1 = (fun i j => raw30421step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30421step1 raw30421step0; decide +kernel
      have hl : raw30421step1Labels = raw30421step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30421step0 raw30421step0Labels permutation33 permutation2
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw30422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30422Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30422step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30422step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30422 raw30422Labels = mixedMoment B node4554 node4554Labels := by
  calc
    mixedMoment B raw30422 raw30422Labels = mixedMoment B raw30422step0 raw30422step0Labels := by
      have hz : ∀ j, raw30422 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30422step0 = (fun i j => raw30422 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30422step0 raw30422; decide +kernel
      have hl : raw30422step0Labels = raw30422Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30422 raw30422Labels permutation434 hz
    _ = mixedMoment B node4554 node4554Labels := by rfl

def raw30423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30423Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30423step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30423step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30423 raw30423Labels = mixedMoment B node4950 node4950Labels := by
  calc
    mixedMoment B raw30423 raw30423Labels = mixedMoment B raw30423step0 raw30423step0Labels := by
      have hz : ∀ j, raw30423 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30423step0 = (fun i j => raw30423 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30423step0 raw30423; decide +kernel
      have hl : raw30423step0Labels = raw30423Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30423 raw30423Labels permutation434 hz
    _ = mixedMoment B node4950 node4950Labels := by rfl

def raw30424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30424Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30424step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30424step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30424 raw30424Labels = mixedMoment B node5039 node5039Labels := by
  calc
    mixedMoment B raw30424 raw30424Labels = mixedMoment B raw30424step0 raw30424step0Labels := by
      have ha : raw30424step0 = (fun i j => raw30424 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30424step0 raw30424; decide +kernel
      have hl : raw30424step0Labels = raw30424Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30424 raw30424Labels permutation158 permutation2
    _ = mixedMoment B node5039 node5039Labels := by rfl

def raw30425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw30425Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw30425step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30425 raw30425Labels = mixedMoment B node5104 node5104Labels := by
  calc
    mixedMoment B raw30425 raw30425Labels = mixedMoment B raw30425step0 raw30425step0Labels := by
      have hz : ∀ j, raw30425 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30425step0 = (fun i j => raw30425 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30425step0 raw30425; decide +kernel
      have hl : raw30425step0Labels = raw30425Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30425 raw30425Labels permutation434 hz
    _ = mixedMoment B node5104 node5104Labels := by rfl

def raw30426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw30426Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30426step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw30426step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30426step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw30426step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30426 raw30426Labels = mixedMoment B node5104 node5104Labels := by
  calc
    mixedMoment B raw30426 raw30426Labels = mixedMoment B raw30426step0 raw30426step0Labels := by
      have hz : ∀ j, raw30426 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30426step0 = (fun i j => raw30426 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30426step0 raw30426; decide +kernel
      have hl : raw30426step0Labels = raw30426Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30426 raw30426Labels permutation434 hz
    mixedMoment B raw30426step0 raw30426step0Labels = mixedMoment B raw30426step1 raw30426step1Labels := by
      have ha : raw30426step1 = (fun i j => raw30426step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30426step1 raw30426step0; decide +kernel
      have hl : raw30426step1Labels = raw30426step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30426step0 raw30426step0Labels permutation33 permutation2
    _ = mixedMoment B node5104 node5104Labels := by rfl

def raw30427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30427Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30427 raw30427Labels = mixedMoment B node4530 node4530Labels := by
  calc
    _ = mixedMoment B node4530 node4530Labels := by rfl

def raw30428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30428Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30428 raw30428Labels = mixedMoment B node4932 node4932Labels := by
  calc
    _ = mixedMoment B node4932 node4932Labels := by rfl

def raw30429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30429Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30429 raw30429Labels = mixedMoment B node5043 node5043Labels := by
  calc
    _ = mixedMoment B node5043 node5043Labels := by rfl

def raw30430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw30430Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30430 raw30430Labels = mixedMoment B node5073 node5073Labels := by
  calc
    _ = mixedMoment B node5073 node5073Labels := by rfl

def raw30431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw30431Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30431step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw30431step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30431 raw30431Labels = mixedMoment B node5073 node5073Labels := by
  calc
    mixedMoment B raw30431 raw30431Labels = mixedMoment B raw30431step0 raw30431step0Labels := by
      have ha : raw30431step0 = (fun i j => raw30431 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30431step0 raw30431; decide +kernel
      have hl : raw30431step0Labels = raw30431Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30431 raw30431Labels permutation153 permutation2
    _ = mixedMoment B node5073 node5073Labels := by rfl

def raw30432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw30432Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30432step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![3, -2, -1], ![2, -1, -1]]
def raw30432step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30432step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw30432step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30432 raw30432Labels = mixedMoment B node4535 node4535Labels := by
  calc
    mixedMoment B raw30432 raw30432Labels = mixedMoment B raw30432step0 raw30432step0Labels := by
      have hz : ∀ j, raw30432 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30432step0 = (fun i j => raw30432 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30432step0 raw30432; decide +kernel
      have hl : raw30432step0Labels = raw30432Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30432 raw30432Labels permutation434 hz
    mixedMoment B raw30432step0 raw30432step0Labels = mixedMoment B raw30432step1 raw30432step1Labels := by
      have ha : raw30432step1 = (fun i j => raw30432step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30432step1 raw30432step0; decide +kernel
      have hl : raw30432step1Labels = raw30432step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30432step0 raw30432step0Labels permutation33 permutation2
    _ = mixedMoment B node4535 node4535Labels := by rfl

def raw30433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw30433Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30433step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![3, -2, -1], ![2, -1, -1]]
def raw30433step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30433step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw30433step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30433 raw30433Labels = mixedMoment B node4935 node4935Labels := by
  calc
    mixedMoment B raw30433 raw30433Labels = mixedMoment B raw30433step0 raw30433step0Labels := by
      have hz : ∀ j, raw30433 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30433step0 = (fun i j => raw30433 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30433step0 raw30433; decide +kernel
      have hl : raw30433step0Labels = raw30433Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30433 raw30433Labels permutation434 hz
    mixedMoment B raw30433step0 raw30433step0Labels = mixedMoment B raw30433step1 raw30433step1Labels := by
      have ha : raw30433step1 = (fun i j => raw30433step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30433step1 raw30433step0; decide +kernel
      have hl : raw30433step1Labels = raw30433step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30433step0 raw30433step0Labels permutation33 permutation2
    _ = mixedMoment B node4935 node4935Labels := by rfl

def raw30434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw30434Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30434step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![3, -2, -1], ![2, -1, -1]]
def raw30434step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30434step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw30434step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30434step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw30434step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30434step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw30434step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30434 raw30434Labels = mixedMoment B node4944 node4944Labels := by
  calc
    mixedMoment B raw30434 raw30434Labels = mixedMoment B raw30434step0 raw30434step0Labels := by
      have hz : ∀ j, raw30434 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30434step0 = (fun i j => raw30434 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30434step0 raw30434; decide +kernel
      have hl : raw30434step0Labels = raw30434Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30434 raw30434Labels permutation434 hz
    mixedMoment B raw30434step0 raw30434step0Labels = mixedMoment B raw30434step1 raw30434step1Labels := by
      have ha : raw30434step1 = (fun i j => raw30434step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30434step1 raw30434step0; decide +kernel
      have hl : raw30434step1Labels = raw30434step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30434step0 raw30434step0Labels permutation125 permutation3
    mixedMoment B raw30434step1 raw30434step1Labels = mixedMoment B raw30434step2 raw30434step2Labels := by
      have ha : raw30434step2 = -raw30434step1 := by apply Matrix.ext; change ∀ i j, raw30434step2 i j = -(raw30434step1 i j); unfold raw30434step2 raw30434step1; decide +kernel
      have hl : raw30434step2Labels = raw30434step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30434step2 raw30434step2Labels = mixedMoment B raw30434step3 raw30434step3Labels := by
      have ha : raw30434step3 = raw30434step2 := by apply Matrix.ext; unfold raw30434step3 raw30434step2; decide +kernel
      have hl : raw30434step2Labels = labelEmbedding6 ∘ raw30434step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30434step2 raw30434step2Labels raw30434step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4944 node4944Labels := by rfl

def raw30435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![3, -2, -1], ![2, -1, -1]]
def raw30435Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30435step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw30435step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30435step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw30435step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30435step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw30435step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30435 raw30435Labels = mixedMoment B node4930 node4930Labels := by
  calc
    mixedMoment B raw30435 raw30435Labels = mixedMoment B raw30435step0 raw30435step0Labels := by
      have ha : raw30435step0 = (fun i j => raw30435 (permutation582 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30435step0 raw30435; decide +kernel
      have hl : raw30435step0Labels = raw30435Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30435 raw30435Labels permutation582 permutation3
    mixedMoment B raw30435step0 raw30435step0Labels = mixedMoment B raw30435step1 raw30435step1Labels := by
      have ha : raw30435step1 = -raw30435step0 := by apply Matrix.ext; change ∀ i j, raw30435step1 i j = -(raw30435step0 i j); unfold raw30435step1 raw30435step0; decide +kernel
      have hl : raw30435step1Labels = raw30435step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30435step1 raw30435step1Labels = mixedMoment B raw30435step2 raw30435step2Labels := by
      have ha : raw30435step2 = raw30435step1 := by apply Matrix.ext; unfold raw30435step2 raw30435step1; decide +kernel
      have hl : raw30435step1Labels = labelEmbedding6 ∘ raw30435step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30435step1 raw30435step1Labels raw30435step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4930 node4930Labels := by rfl

def raw30436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![1, 0, -1]]
def raw30436Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30436step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![3, -2, -1], ![1, 0, -1]]
def raw30436step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30436step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw30436step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30436 raw30436Labels = mixedMoment B node5078 node5078Labels := by
  calc
    mixedMoment B raw30436 raw30436Labels = mixedMoment B raw30436step0 raw30436step0Labels := by
      have hz : ∀ j, raw30436 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30436step0 = (fun i j => raw30436 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30436step0 raw30436; decide +kernel
      have hl : raw30436step0Labels = raw30436Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30436 raw30436Labels permutation434 hz
    mixedMoment B raw30436step0 raw30436step0Labels = mixedMoment B raw30436step1 raw30436step1Labels := by
      have ha : raw30436step1 = (fun i j => raw30436step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw30436step1 raw30436step0; decide +kernel
      have hl : raw30436step1Labels = raw30436step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30436step0 raw30436step0Labels permutation33 permutation2
    _ = mixedMoment B node5078 node5078Labels := by rfl

def raw30437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw30437Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30437step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw30437step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30437 raw30437Labels = mixedMoment B node4535 node4535Labels := by
  calc
    mixedMoment B raw30437 raw30437Labels = mixedMoment B raw30437step0 raw30437step0Labels := by
      have hz : ∀ j, raw30437 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30437step0 = (fun i j => raw30437 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30437step0 raw30437; decide +kernel
      have hl : raw30437step0Labels = raw30437Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30437 raw30437Labels permutation434 hz
    _ = mixedMoment B node4535 node4535Labels := by rfl

def raw30438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw30438Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30438step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw30438step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30438 raw30438Labels = mixedMoment B node4935 node4935Labels := by
  calc
    mixedMoment B raw30438 raw30438Labels = mixedMoment B raw30438step0 raw30438step0Labels := by
      have hz : ∀ j, raw30438 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30438step0 = (fun i j => raw30438 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30438step0 raw30438; decide +kernel
      have hl : raw30438step0Labels = raw30438Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30438 raw30438Labels permutation434 hz
    _ = mixedMoment B node4935 node4935Labels := by rfl

def raw30439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw30439Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30439step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![3, -2, -1]]
def raw30439step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30439step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw30439step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30439step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw30439step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30439step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw30439step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30439 raw30439Labels = mixedMoment B node4944 node4944Labels := by
  calc
    mixedMoment B raw30439 raw30439Labels = mixedMoment B raw30439step0 raw30439step0Labels := by
      have hz : ∀ j, raw30439 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30439step0 = (fun i j => raw30439 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30439step0 raw30439; decide +kernel
      have hl : raw30439step0Labels = raw30439Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30439 raw30439Labels permutation434 hz
    mixedMoment B raw30439step0 raw30439step0Labels = mixedMoment B raw30439step1 raw30439step1Labels := by
      have ha : raw30439step1 = (fun i j => raw30439step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30439step1 raw30439step0; decide +kernel
      have hl : raw30439step1Labels = raw30439step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30439step0 raw30439step0Labels permutation149 permutation3
    mixedMoment B raw30439step1 raw30439step1Labels = mixedMoment B raw30439step2 raw30439step2Labels := by
      have ha : raw30439step2 = -raw30439step1 := by apply Matrix.ext; change ∀ i j, raw30439step2 i j = -(raw30439step1 i j); unfold raw30439step2 raw30439step1; decide +kernel
      have hl : raw30439step2Labels = raw30439step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30439step2 raw30439step2Labels = mixedMoment B raw30439step3 raw30439step3Labels := by
      have ha : raw30439step3 = raw30439step2 := by apply Matrix.ext; unfold raw30439step3 raw30439step2; decide +kernel
      have hl : raw30439step2Labels = labelEmbedding6 ∘ raw30439step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30439step2 raw30439step2Labels raw30439step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4944 node4944Labels := by rfl

def raw30440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw30440Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30440step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 2, 1]]
def raw30440step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30440step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw30440step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw30440step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw30440step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30440 raw30440Labels = mixedMoment B node4930 node4930Labels := by
  calc
    mixedMoment B raw30440 raw30440Labels = mixedMoment B raw30440step0 raw30440step0Labels := by
      have ha : raw30440step0 = (fun i j => raw30440 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw30440step0 raw30440; decide +kernel
      have hl : raw30440step0Labels = raw30440Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30440 raw30440Labels permutation680 permutation3
    mixedMoment B raw30440step0 raw30440step0Labels = mixedMoment B raw30440step1 raw30440step1Labels := by
      have ha : raw30440step1 = -raw30440step0 := by apply Matrix.ext; change ∀ i j, raw30440step1 i j = -(raw30440step0 i j); unfold raw30440step1 raw30440step0; decide +kernel
      have hl : raw30440step1Labels = raw30440step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30440step1 raw30440step1Labels = mixedMoment B raw30440step2 raw30440step2Labels := by
      have ha : raw30440step2 = raw30440step1 := by apply Matrix.ext; unfold raw30440step2 raw30440step1; decide +kernel
      have hl : raw30440step1Labels = labelEmbedding6 ∘ raw30440step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30440step1 raw30440step1Labels raw30440step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4930 node4930Labels := by rfl

def raw30441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw30441Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw30441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw30441step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical30441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30441 raw30441Labels = mixedMoment B node5078 node5078Labels := by
  calc
    mixedMoment B raw30441 raw30441Labels = mixedMoment B raw30441step0 raw30441step0Labels := by
      have hz : ∀ j, raw30441 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30441step0 = (fun i j => raw30441 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30441step0 raw30441; decide +kernel
      have hl : raw30441step0Labels = raw30441Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30441 raw30441Labels permutation434 hz
    _ = mixedMoment B node5078 node5078Labels := by rfl

def raw30442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30442Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30442step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30442step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw30442step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30442step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw30442step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30442step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw30442step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30442 raw30442Labels = mixedMoment B node3773 node3773Labels := by
  calc
    mixedMoment B raw30442 raw30442Labels = mixedMoment B raw30442step0 raw30442step0Labels := by
      have hz : ∀ j, raw30442 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30442step0 = (fun i j => raw30442 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30442step0 raw30442; decide +kernel
      have hl : raw30442step0Labels = raw30442Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30442 raw30442Labels permutation434 hz
    mixedMoment B raw30442step0 raw30442step0Labels = mixedMoment B raw30442step1 raw30442step1Labels := by
      have ha : raw30442step1 = (fun i j => raw30442step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30442step1 raw30442step0; decide +kernel
      have hl : raw30442step1Labels = raw30442step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30442step0 raw30442step0Labels permutation32 permutation7
    mixedMoment B raw30442step1 raw30442step1Labels = mixedMoment B raw30442step2 raw30442step2Labels := by
      have ha : raw30442step2 = -raw30442step1 := by apply Matrix.ext; change ∀ i j, raw30442step2 i j = -(raw30442step1 i j); unfold raw30442step2 raw30442step1; decide +kernel
      have hl : raw30442step2Labels = raw30442step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30442step2 raw30442step2Labels = mixedMoment B raw30442step3 raw30442step3Labels := by
      have ha : raw30442step3 = raw30442step2 := by apply Matrix.ext; unfold raw30442step3 raw30442step2; decide +kernel
      have hl : raw30442step2Labels = labelEmbedding1 ∘ raw30442step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30442step2 raw30442step2Labels raw30442step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3773 node3773Labels := by rfl

def raw30443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30443Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30443step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30443step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw30443step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30443step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw30443step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30443step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw30443step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30443 raw30443Labels = mixedMoment B node3815 node3815Labels := by
  calc
    mixedMoment B raw30443 raw30443Labels = mixedMoment B raw30443step0 raw30443step0Labels := by
      have hz : ∀ j, raw30443 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30443step0 = (fun i j => raw30443 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30443step0 raw30443; decide +kernel
      have hl : raw30443step0Labels = raw30443Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30443 raw30443Labels permutation434 hz
    mixedMoment B raw30443step0 raw30443step0Labels = mixedMoment B raw30443step1 raw30443step1Labels := by
      have ha : raw30443step1 = (fun i j => raw30443step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30443step1 raw30443step0; decide +kernel
      have hl : raw30443step1Labels = raw30443step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30443step0 raw30443step0Labels permutation32 permutation7
    mixedMoment B raw30443step1 raw30443step1Labels = mixedMoment B raw30443step2 raw30443step2Labels := by
      have ha : raw30443step2 = -raw30443step1 := by apply Matrix.ext; change ∀ i j, raw30443step2 i j = -(raw30443step1 i j); unfold raw30443step2 raw30443step1; decide +kernel
      have hl : raw30443step2Labels = raw30443step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30443step2 raw30443step2Labels = mixedMoment B raw30443step3 raw30443step3Labels := by
      have ha : raw30443step3 = raw30443step2 := by apply Matrix.ext; unfold raw30443step3 raw30443step2; decide +kernel
      have hl : raw30443step2Labels = labelEmbedding1 ∘ raw30443step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30443step2 raw30443step2Labels raw30443step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3815 node3815Labels := by rfl

def raw30444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30444Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30444step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw30444step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30444step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw30444step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30444step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw30444step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30444 raw30444Labels = mixedMoment B node3797 node3797Labels := by
  calc
    mixedMoment B raw30444 raw30444Labels = mixedMoment B raw30444step0 raw30444step0Labels := by
      have ha : raw30444step0 = (fun i j => raw30444 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30444step0 raw30444; decide +kernel
      have hl : raw30444step0Labels = raw30444Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30444 raw30444Labels permutation158 permutation7
    mixedMoment B raw30444step0 raw30444step0Labels = mixedMoment B raw30444step1 raw30444step1Labels := by
      have ha : raw30444step1 = -raw30444step0 := by apply Matrix.ext; change ∀ i j, raw30444step1 i j = -(raw30444step0 i j); unfold raw30444step1 raw30444step0; decide +kernel
      have hl : raw30444step1Labels = raw30444step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30444step1 raw30444step1Labels = mixedMoment B raw30444step2 raw30444step2Labels := by
      have ha : raw30444step2 = raw30444step1 := by apply Matrix.ext; unfold raw30444step2 raw30444step1; decide +kernel
      have hl : raw30444step1Labels = labelEmbedding1 ∘ raw30444step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30444step1 raw30444step1Labels raw30444step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3797 node3797Labels := by rfl

def raw30445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw30445Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw30445step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30445step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw30445step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30445step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw30445step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30445step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw30445step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30445 raw30445Labels = mixedMoment B node3816 node3816Labels := by
  calc
    mixedMoment B raw30445 raw30445Labels = mixedMoment B raw30445step0 raw30445step0Labels := by
      have hz : ∀ j, raw30445 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30445step0 = (fun i j => raw30445 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30445step0 raw30445; decide +kernel
      have hl : raw30445step0Labels = raw30445Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30445 raw30445Labels permutation434 hz
    mixedMoment B raw30445step0 raw30445step0Labels = mixedMoment B raw30445step1 raw30445step1Labels := by
      have ha : raw30445step1 = (fun i j => raw30445step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30445step1 raw30445step0; decide +kernel
      have hl : raw30445step1Labels = raw30445step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30445step0 raw30445step0Labels permutation32 permutation7
    mixedMoment B raw30445step1 raw30445step1Labels = mixedMoment B raw30445step2 raw30445step2Labels := by
      have ha : raw30445step2 = -raw30445step1 := by apply Matrix.ext; change ∀ i j, raw30445step2 i j = -(raw30445step1 i j); unfold raw30445step2 raw30445step1; decide +kernel
      have hl : raw30445step2Labels = raw30445step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30445step2 raw30445step2Labels = mixedMoment B raw30445step3 raw30445step3Labels := by
      have ha : raw30445step3 = raw30445step2 := by apply Matrix.ext; unfold raw30445step3 raw30445step2; decide +kernel
      have hl : raw30445step2Labels = labelEmbedding1 ∘ raw30445step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30445step2 raw30445step2Labels raw30445step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3816 node3816Labels := by rfl

def raw30446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw30446Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw30446step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30446step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw30446step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30446step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw30446step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30446step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw30446step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30446 raw30446Labels = mixedMoment B node3816 node3816Labels := by
  calc
    mixedMoment B raw30446 raw30446Labels = mixedMoment B raw30446step0 raw30446step0Labels := by
      have hz : ∀ j, raw30446 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30446step0 = (fun i j => raw30446 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30446step0 raw30446; decide +kernel
      have hl : raw30446step0Labels = raw30446Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30446 raw30446Labels permutation434 hz
    mixedMoment B raw30446step0 raw30446step0Labels = mixedMoment B raw30446step1 raw30446step1Labels := by
      have ha : raw30446step1 = (fun i j => raw30446step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30446step1 raw30446step0; decide +kernel
      have hl : raw30446step1Labels = raw30446step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30446step0 raw30446step0Labels permutation33 permutation7
    mixedMoment B raw30446step1 raw30446step1Labels = mixedMoment B raw30446step2 raw30446step2Labels := by
      have ha : raw30446step2 = -raw30446step1 := by apply Matrix.ext; change ∀ i j, raw30446step2 i j = -(raw30446step1 i j); unfold raw30446step2 raw30446step1; decide +kernel
      have hl : raw30446step2Labels = raw30446step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30446step2 raw30446step2Labels = mixedMoment B raw30446step3 raw30446step3Labels := by
      have ha : raw30446step3 = raw30446step2 := by apply Matrix.ext; unfold raw30446step3 raw30446step2; decide +kernel
      have hl : raw30446step2Labels = labelEmbedding1 ∘ raw30446step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30446step2 raw30446step2Labels raw30446step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3816 node3816Labels := by rfl

def raw30447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30447Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30447step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30447step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30447step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw30447step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30447step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw30447step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30447step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw30447step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30447 raw30447Labels = mixedMoment B node3297 node3297Labels := by
  calc
    mixedMoment B raw30447 raw30447Labels = mixedMoment B raw30447step0 raw30447step0Labels := by
      have hz : ∀ j, raw30447 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30447step0 = (fun i j => raw30447 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30447step0 raw30447; decide +kernel
      have hl : raw30447step0Labels = raw30447Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30447 raw30447Labels permutation434 hz
    mixedMoment B raw30447step0 raw30447step0Labels = mixedMoment B raw30447step1 raw30447step1Labels := by
      have ha : raw30447step1 = (fun i j => raw30447step0 (permutation38 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30447step1 raw30447step0; decide +kernel
      have hl : raw30447step1Labels = raw30447step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30447step0 raw30447step0Labels permutation38 permutation5
    mixedMoment B raw30447step1 raw30447step1Labels = mixedMoment B raw30447step2 raw30447step2Labels := by
      have ha : raw30447step2 = -raw30447step1 := by apply Matrix.ext; change ∀ i j, raw30447step2 i j = -(raw30447step1 i j); unfold raw30447step2 raw30447step1; decide +kernel
      have hl : raw30447step2Labels = raw30447step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30447step2 raw30447step2Labels = mixedMoment B raw30447step3 raw30447step3Labels := by
      have ha : raw30447step3 = raw30447step2 := by apply Matrix.ext; unfold raw30447step3 raw30447step2; decide +kernel
      have hl : raw30447step2Labels = labelEmbedding1 ∘ raw30447step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30447step2 raw30447step2Labels raw30447step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3297 node3297Labels := by rfl

def raw30448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30448Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30448step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30448step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30448step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw30448step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30448step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw30448step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30448step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw30448step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30448 raw30448Labels = mixedMoment B node3542 node3542Labels := by
  calc
    mixedMoment B raw30448 raw30448Labels = mixedMoment B raw30448step0 raw30448step0Labels := by
      have hz : ∀ j, raw30448 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30448step0 = (fun i j => raw30448 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30448step0 raw30448; decide +kernel
      have hl : raw30448step0Labels = raw30448Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30448 raw30448Labels permutation434 hz
    mixedMoment B raw30448step0 raw30448step0Labels = mixedMoment B raw30448step1 raw30448step1Labels := by
      have ha : raw30448step1 = (fun i j => raw30448step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30448step1 raw30448step0; decide +kernel
      have hl : raw30448step1Labels = raw30448step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30448step0 raw30448step0Labels permutation32 permutation7
    mixedMoment B raw30448step1 raw30448step1Labels = mixedMoment B raw30448step2 raw30448step2Labels := by
      have ha : raw30448step2 = -raw30448step1 := by apply Matrix.ext; change ∀ i j, raw30448step2 i j = -(raw30448step1 i j); unfold raw30448step2 raw30448step1; decide +kernel
      have hl : raw30448step2Labels = raw30448step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30448step2 raw30448step2Labels = mixedMoment B raw30448step3 raw30448step3Labels := by
      have ha : raw30448step3 = raw30448step2 := by apply Matrix.ext; unfold raw30448step3 raw30448step2; decide +kernel
      have hl : raw30448step2Labels = labelEmbedding1 ∘ raw30448step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30448step2 raw30448step2Labels raw30448step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3542 node3542Labels := by rfl

def raw30449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30449Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30449step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw30449step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30449step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw30449step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30449step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw30449step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30449 raw30449Labels = mixedMoment B node3520 node3520Labels := by
  calc
    mixedMoment B raw30449 raw30449Labels = mixedMoment B raw30449step0 raw30449step0Labels := by
      have ha : raw30449step0 = (fun i j => raw30449 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30449step0 raw30449; decide +kernel
      have hl : raw30449step0Labels = raw30449Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30449 raw30449Labels permutation158 permutation7
    mixedMoment B raw30449step0 raw30449step0Labels = mixedMoment B raw30449step1 raw30449step1Labels := by
      have ha : raw30449step1 = -raw30449step0 := by apply Matrix.ext; change ∀ i j, raw30449step1 i j = -(raw30449step0 i j); unfold raw30449step1 raw30449step0; decide +kernel
      have hl : raw30449step1Labels = raw30449step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30449step1 raw30449step1Labels = mixedMoment B raw30449step2 raw30449step2Labels := by
      have ha : raw30449step2 = raw30449step1 := by apply Matrix.ext; unfold raw30449step2 raw30449step1; decide +kernel
      have hl : raw30449step1Labels = labelEmbedding1 ∘ raw30449step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30449step1 raw30449step1Labels raw30449step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3520 node3520Labels := by rfl

def raw30450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw30450Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw30450step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30450step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw30450step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30450step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw30450step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30450step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw30450step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30450 raw30450Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw30450 raw30450Labels = mixedMoment B raw30450step0 raw30450step0Labels := by
      have hz : ∀ j, raw30450 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30450step0 = (fun i j => raw30450 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30450step0 raw30450; decide +kernel
      have hl : raw30450step0Labels = raw30450Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30450 raw30450Labels permutation434 hz
    mixedMoment B raw30450step0 raw30450step0Labels = mixedMoment B raw30450step1 raw30450step1Labels := by
      have ha : raw30450step1 = (fun i j => raw30450step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30450step1 raw30450step0; decide +kernel
      have hl : raw30450step1Labels = raw30450step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30450step0 raw30450step0Labels permutation32 permutation7
    mixedMoment B raw30450step1 raw30450step1Labels = mixedMoment B raw30450step2 raw30450step2Labels := by
      have ha : raw30450step2 = -raw30450step1 := by apply Matrix.ext; change ∀ i j, raw30450step2 i j = -(raw30450step1 i j); unfold raw30450step2 raw30450step1; decide +kernel
      have hl : raw30450step2Labels = raw30450step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30450step2 raw30450step2Labels = mixedMoment B raw30450step3 raw30450step3Labels := by
      have ha : raw30450step3 = raw30450step2 := by apply Matrix.ext; unfold raw30450step3 raw30450step2; decide +kernel
      have hl : raw30450step2Labels = labelEmbedding1 ∘ raw30450step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30450step2 raw30450step2Labels raw30450step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3544 node3544Labels := by rfl

def raw30451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw30451Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30451step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw30451step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30451step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw30451step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30451step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw30451step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30451step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw30451step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30451 raw30451Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw30451 raw30451Labels = mixedMoment B raw30451step0 raw30451step0Labels := by
      have hz : ∀ j, raw30451 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30451step0 = (fun i j => raw30451 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30451step0 raw30451; decide +kernel
      have hl : raw30451step0Labels = raw30451Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30451 raw30451Labels permutation434 hz
    mixedMoment B raw30451step0 raw30451step0Labels = mixedMoment B raw30451step1 raw30451step1Labels := by
      have ha : raw30451step1 = (fun i j => raw30451step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30451step1 raw30451step0; decide +kernel
      have hl : raw30451step1Labels = raw30451step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30451step0 raw30451step0Labels permutation33 permutation7
    mixedMoment B raw30451step1 raw30451step1Labels = mixedMoment B raw30451step2 raw30451step2Labels := by
      have ha : raw30451step2 = -raw30451step1 := by apply Matrix.ext; change ∀ i j, raw30451step2 i j = -(raw30451step1 i j); unfold raw30451step2 raw30451step1; decide +kernel
      have hl : raw30451step2Labels = raw30451step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30451step2 raw30451step2Labels = mixedMoment B raw30451step3 raw30451step3Labels := by
      have ha : raw30451step3 = raw30451step2 := by apply Matrix.ext; unfold raw30451step3 raw30451step2; decide +kernel
      have hl : raw30451step2Labels = labelEmbedding1 ∘ raw30451step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30451step2 raw30451step2Labels raw30451step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3544 node3544Labels := by rfl

def raw30452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30452Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30452step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30452step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30452step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw30452step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30452step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw30452step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30452step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw30452step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30452 raw30452Labels = mixedMoment B node3274 node3274Labels := by
  calc
    mixedMoment B raw30452 raw30452Labels = mixedMoment B raw30452step0 raw30452step0Labels := by
      have hz : ∀ j, raw30452 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30452step0 = (fun i j => raw30452 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30452step0 raw30452; decide +kernel
      have hl : raw30452step0Labels = raw30452Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30452 raw30452Labels permutation434 hz
    mixedMoment B raw30452step0 raw30452step0Labels = mixedMoment B raw30452step1 raw30452step1Labels := by
      have ha : raw30452step1 = (fun i j => raw30452step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30452step1 raw30452step0; decide +kernel
      have hl : raw30452step1Labels = raw30452step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30452step0 raw30452step0Labels permutation32 permutation7
    mixedMoment B raw30452step1 raw30452step1Labels = mixedMoment B raw30452step2 raw30452step2Labels := by
      have ha : raw30452step2 = -raw30452step1 := by apply Matrix.ext; change ∀ i j, raw30452step2 i j = -(raw30452step1 i j); unfold raw30452step2 raw30452step1; decide +kernel
      have hl : raw30452step2Labels = raw30452step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30452step2 raw30452step2Labels = mixedMoment B raw30452step3 raw30452step3Labels := by
      have ha : raw30452step3 = raw30452step2 := by apply Matrix.ext; unfold raw30452step3 raw30452step2; decide +kernel
      have hl : raw30452step2Labels = labelEmbedding1 ∘ raw30452step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30452step2 raw30452step2Labels raw30452step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3274 node3274Labels := by rfl

def raw30453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30453Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw30453step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30453step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw30453step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30453step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw30453step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30453step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw30453step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30453 raw30453Labels = mixedMoment B node3421 node3421Labels := by
  calc
    mixedMoment B raw30453 raw30453Labels = mixedMoment B raw30453step0 raw30453step0Labels := by
      have hz : ∀ j, raw30453 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30453step0 = (fun i j => raw30453 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30453step0 raw30453; decide +kernel
      have hl : raw30453step0Labels = raw30453Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30453 raw30453Labels permutation434 hz
    mixedMoment B raw30453step0 raw30453step0Labels = mixedMoment B raw30453step1 raw30453step1Labels := by
      have ha : raw30453step1 = (fun i j => raw30453step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30453step1 raw30453step0; decide +kernel
      have hl : raw30453step1Labels = raw30453step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30453step0 raw30453step0Labels permutation32 permutation7
    mixedMoment B raw30453step1 raw30453step1Labels = mixedMoment B raw30453step2 raw30453step2Labels := by
      have ha : raw30453step2 = -raw30453step1 := by apply Matrix.ext; change ∀ i j, raw30453step2 i j = -(raw30453step1 i j); unfold raw30453step2 raw30453step1; decide +kernel
      have hl : raw30453step2Labels = raw30453step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30453step2 raw30453step2Labels = mixedMoment B raw30453step3 raw30453step3Labels := by
      have ha : raw30453step3 = raw30453step2 := by apply Matrix.ext; unfold raw30453step3 raw30453step2; decide +kernel
      have hl : raw30453step2Labels = labelEmbedding1 ∘ raw30453step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30453step2 raw30453step2Labels raw30453step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3421 node3421Labels := by rfl

def raw30454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30454Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30454step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw30454step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30454step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw30454step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30454step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw30454step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30454 raw30454Labels = mixedMoment B node3456 node3456Labels := by
  calc
    mixedMoment B raw30454 raw30454Labels = mixedMoment B raw30454step0 raw30454step0Labels := by
      have ha : raw30454step0 = (fun i j => raw30454 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30454step0 raw30454; decide +kernel
      have hl : raw30454step0Labels = raw30454Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30454 raw30454Labels permutation158 permutation7
    mixedMoment B raw30454step0 raw30454step0Labels = mixedMoment B raw30454step1 raw30454step1Labels := by
      have ha : raw30454step1 = -raw30454step0 := by apply Matrix.ext; change ∀ i j, raw30454step1 i j = -(raw30454step0 i j); unfold raw30454step1 raw30454step0; decide +kernel
      have hl : raw30454step1Labels = raw30454step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30454step1 raw30454step1Labels = mixedMoment B raw30454step2 raw30454step2Labels := by
      have ha : raw30454step2 = raw30454step1 := by apply Matrix.ext; unfold raw30454step2 raw30454step1; decide +kernel
      have hl : raw30454step1Labels = labelEmbedding1 ∘ raw30454step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30454step1 raw30454step1Labels raw30454step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3456 node3456Labels := by rfl

def raw30455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw30455Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30455step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw30455step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30455step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw30455step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30455step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw30455step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30455step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw30455step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30455 raw30455Labels = mixedMoment B node3483 node3483Labels := by
  calc
    mixedMoment B raw30455 raw30455Labels = mixedMoment B raw30455step0 raw30455step0Labels := by
      have hz : ∀ j, raw30455 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30455step0 = (fun i j => raw30455 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30455step0 raw30455; decide +kernel
      have hl : raw30455step0Labels = raw30455Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30455 raw30455Labels permutation434 hz
    mixedMoment B raw30455step0 raw30455step0Labels = mixedMoment B raw30455step1 raw30455step1Labels := by
      have ha : raw30455step1 = (fun i j => raw30455step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30455step1 raw30455step0; decide +kernel
      have hl : raw30455step1Labels = raw30455step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30455step0 raw30455step0Labels permutation32 permutation7
    mixedMoment B raw30455step1 raw30455step1Labels = mixedMoment B raw30455step2 raw30455step2Labels := by
      have ha : raw30455step2 = -raw30455step1 := by apply Matrix.ext; change ∀ i j, raw30455step2 i j = -(raw30455step1 i j); unfold raw30455step2 raw30455step1; decide +kernel
      have hl : raw30455step2Labels = raw30455step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30455step2 raw30455step2Labels = mixedMoment B raw30455step3 raw30455step3Labels := by
      have ha : raw30455step3 = raw30455step2 := by apply Matrix.ext; unfold raw30455step3 raw30455step2; decide +kernel
      have hl : raw30455step2Labels = labelEmbedding1 ∘ raw30455step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30455step2 raw30455step2Labels raw30455step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3483 node3483Labels := by rfl

def raw30456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw30456Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw30456step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30456step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw30456step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30456step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw30456step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30456step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw30456step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30456 raw30456Labels = mixedMoment B node3483 node3483Labels := by
  calc
    mixedMoment B raw30456 raw30456Labels = mixedMoment B raw30456step0 raw30456step0Labels := by
      have hz : ∀ j, raw30456 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30456step0 = (fun i j => raw30456 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30456step0 raw30456; decide +kernel
      have hl : raw30456step0Labels = raw30456Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30456 raw30456Labels permutation434 hz
    mixedMoment B raw30456step0 raw30456step0Labels = mixedMoment B raw30456step1 raw30456step1Labels := by
      have ha : raw30456step1 = (fun i j => raw30456step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30456step1 raw30456step0; decide +kernel
      have hl : raw30456step1Labels = raw30456step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30456step0 raw30456step0Labels permutation33 permutation7
    mixedMoment B raw30456step1 raw30456step1Labels = mixedMoment B raw30456step2 raw30456step2Labels := by
      have ha : raw30456step2 = -raw30456step1 := by apply Matrix.ext; change ∀ i j, raw30456step2 i j = -(raw30456step1 i j); unfold raw30456step2 raw30456step1; decide +kernel
      have hl : raw30456step2Labels = raw30456step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30456step2 raw30456step2Labels = mixedMoment B raw30456step3 raw30456step3Labels := by
      have ha : raw30456step3 = raw30456step2 := by apply Matrix.ext; unfold raw30456step3 raw30456step2; decide +kernel
      have hl : raw30456step2Labels = labelEmbedding1 ∘ raw30456step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30456step2 raw30456step2Labels raw30456step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3483 node3483Labels := by rfl

def raw30457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30457Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30457step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw30457step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30457step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw30457step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30457step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw30457step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30457 raw30457Labels = mixedMoment B node3261 node3261Labels := by
  calc
    mixedMoment B raw30457 raw30457Labels = mixedMoment B raw30457step0 raw30457step0Labels := by
      have ha : raw30457step0 = (fun i j => raw30457 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30457step0 raw30457; decide +kernel
      have hl : raw30457step0Labels = raw30457Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30457 raw30457Labels permutation158 permutation7
    mixedMoment B raw30457step0 raw30457step0Labels = mixedMoment B raw30457step1 raw30457step1Labels := by
      have ha : raw30457step1 = -raw30457step0 := by apply Matrix.ext; change ∀ i j, raw30457step1 i j = -(raw30457step0 i j); unfold raw30457step1 raw30457step0; decide +kernel
      have hl : raw30457step1Labels = raw30457step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30457step1 raw30457step1Labels = mixedMoment B raw30457step2 raw30457step2Labels := by
      have ha : raw30457step2 = raw30457step1 := by apply Matrix.ext; unfold raw30457step2 raw30457step1; decide +kernel
      have hl : raw30457step1Labels = labelEmbedding1 ∘ raw30457step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30457step1 raw30457step1Labels raw30457step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3261 node3261Labels := by rfl

def raw30458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30458Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30458step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw30458step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30458step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw30458step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30458step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw30458step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30458 raw30458Labels = mixedMoment B node3409 node3409Labels := by
  calc
    mixedMoment B raw30458 raw30458Labels = mixedMoment B raw30458step0 raw30458step0Labels := by
      have ha : raw30458step0 = (fun i j => raw30458 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30458step0 raw30458; decide +kernel
      have hl : raw30458step0Labels = raw30458Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30458 raw30458Labels permutation158 permutation7
    mixedMoment B raw30458step0 raw30458step0Labels = mixedMoment B raw30458step1 raw30458step1Labels := by
      have ha : raw30458step1 = -raw30458step0 := by apply Matrix.ext; change ∀ i j, raw30458step1 i j = -(raw30458step0 i j); unfold raw30458step1 raw30458step0; decide +kernel
      have hl : raw30458step1Labels = raw30458step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30458step1 raw30458step1Labels = mixedMoment B raw30458step2 raw30458step2Labels := by
      have ha : raw30458step2 = raw30458step1 := by apply Matrix.ext; unfold raw30458step2 raw30458step1; decide +kernel
      have hl : raw30458step1Labels = labelEmbedding1 ∘ raw30458step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30458step1 raw30458step1Labels raw30458step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3409 node3409Labels := by rfl

def raw30459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw30459Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30459step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw30459step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30459step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw30459step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30459step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw30459step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30459 raw30459Labels = mixedMoment B node3465 node3465Labels := by
  calc
    mixedMoment B raw30459 raw30459Labels = mixedMoment B raw30459step0 raw30459step0Labels := by
      have ha : raw30459step0 = (fun i j => raw30459 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30459step0 raw30459; decide +kernel
      have hl : raw30459step0Labels = raw30459Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30459 raw30459Labels permutation158 permutation7
    mixedMoment B raw30459step0 raw30459step0Labels = mixedMoment B raw30459step1 raw30459step1Labels := by
      have ha : raw30459step1 = -raw30459step0 := by apply Matrix.ext; change ∀ i j, raw30459step1 i j = -(raw30459step0 i j); unfold raw30459step1 raw30459step0; decide +kernel
      have hl : raw30459step1Labels = raw30459step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30459step1 raw30459step1Labels = mixedMoment B raw30459step2 raw30459step2Labels := by
      have ha : raw30459step2 = raw30459step1 := by apply Matrix.ext; unfold raw30459step2 raw30459step1; decide +kernel
      have hl : raw30459step1Labels = labelEmbedding1 ∘ raw30459step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30459step1 raw30459step1Labels raw30459step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3465 node3465Labels := by rfl

def raw30460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw30460Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30460step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw30460step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30460step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw30460step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30460step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw30460step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30460 raw30460Labels = mixedMoment B node3467 node3467Labels := by
  calc
    mixedMoment B raw30460 raw30460Labels = mixedMoment B raw30460step0 raw30460step0Labels := by
      have ha : raw30460step0 = (fun i j => raw30460 (permutation158 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30460step0 raw30460; decide +kernel
      have hl : raw30460step0Labels = raw30460Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30460 raw30460Labels permutation158 permutation7
    mixedMoment B raw30460step0 raw30460step0Labels = mixedMoment B raw30460step1 raw30460step1Labels := by
      have ha : raw30460step1 = -raw30460step0 := by apply Matrix.ext; change ∀ i j, raw30460step1 i j = -(raw30460step0 i j); unfold raw30460step1 raw30460step0; decide +kernel
      have hl : raw30460step1Labels = raw30460step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30460step1 raw30460step1Labels = mixedMoment B raw30460step2 raw30460step2Labels := by
      have ha : raw30460step2 = raw30460step1 := by apply Matrix.ext; unfold raw30460step2 raw30460step1; decide +kernel
      have hl : raw30460step1Labels = labelEmbedding1 ∘ raw30460step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30460step1 raw30460step1Labels raw30460step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3467 node3467Labels := by rfl

def raw30461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw30461Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30461step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw30461step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30461step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw30461step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30461step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw30461step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30461 raw30461Labels = mixedMoment B node3467 node3467Labels := by
  calc
    mixedMoment B raw30461 raw30461Labels = mixedMoment B raw30461step0 raw30461step0Labels := by
      have ha : raw30461step0 = (fun i j => raw30461 (permutation159 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30461step0 raw30461; decide +kernel
      have hl : raw30461step0Labels = raw30461Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30461 raw30461Labels permutation159 permutation7
    mixedMoment B raw30461step0 raw30461step0Labels = mixedMoment B raw30461step1 raw30461step1Labels := by
      have ha : raw30461step1 = -raw30461step0 := by apply Matrix.ext; change ∀ i j, raw30461step1 i j = -(raw30461step0 i j); unfold raw30461step1 raw30461step0; decide +kernel
      have hl : raw30461step1Labels = raw30461step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30461step1 raw30461step1Labels = mixedMoment B raw30461step2 raw30461step2Labels := by
      have ha : raw30461step2 = raw30461step1 := by apply Matrix.ext; unfold raw30461step2 raw30461step1; decide +kernel
      have hl : raw30461step1Labels = labelEmbedding1 ∘ raw30461step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30461step1 raw30461step1Labels raw30461step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3467 node3467Labels := by rfl

def raw30462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw30462Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30462step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 1, -1], ![3, -2, -1], ![2, -1, -1]]
def raw30462step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30462step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -2, 3]]
def raw30462step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30462step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw30462step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30462step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw30462step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30462 raw30462Labels = mixedMoment B node3272 node3272Labels := by
  calc
    mixedMoment B raw30462 raw30462Labels = mixedMoment B raw30462step0 raw30462step0Labels := by
      have hz : ∀ j, raw30462 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30462step0 = (fun i j => raw30462 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30462step0 raw30462; decide +kernel
      have hl : raw30462step0Labels = raw30462Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30462 raw30462Labels permutation434 hz
    mixedMoment B raw30462step0 raw30462step0Labels = mixedMoment B raw30462step1 raw30462step1Labels := by
      have ha : raw30462step1 = (fun i j => raw30462step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw30462step1 raw30462step0; decide +kernel
      have hl : raw30462step1Labels = raw30462step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30462step0 raw30462step0Labels permutation33 permutation7
    mixedMoment B raw30462step1 raw30462step1Labels = mixedMoment B raw30462step2 raw30462step2Labels := by
      have ha : raw30462step2 = -raw30462step1 := by apply Matrix.ext; change ∀ i j, raw30462step2 i j = -(raw30462step1 i j); unfold raw30462step2 raw30462step1; decide +kernel
      have hl : raw30462step2Labels = raw30462step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw30462step2 raw30462step2Labels = mixedMoment B raw30462step3 raw30462step3Labels := by
      have ha : raw30462step3 = raw30462step2 := by apply Matrix.ext; unfold raw30462step3 raw30462step2; decide +kernel
      have hl : raw30462step2Labels = labelEmbedding1 ∘ raw30462step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30462step2 raw30462step2Labels raw30462step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3272 node3272Labels := by rfl

def raw30463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1], ![2, -1, -1]]
def raw30463Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30463step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![3, -2, -1], ![2, -1, -1]]
def raw30463step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw30463step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw30463step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw30463step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw30463step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical30463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw30463 raw30463Labels = mixedMoment B node3419 node3419Labels := by
  calc
    mixedMoment B raw30463 raw30463Labels = mixedMoment B raw30463step0 raw30463step0Labels := by
      have hz : ∀ j, raw30463 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw30463step0 = (fun i j => raw30463 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw30463step0 raw30463; decide +kernel
      have hl : raw30463step0Labels = raw30463Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw30463 raw30463Labels permutation434 hz
    mixedMoment B raw30463step0 raw30463step0Labels = mixedMoment B raw30463step1 raw30463step1Labels := by
      have ha : raw30463step1 = (fun i j => raw30463step0 (permutation127 i) (permutation5 j)) := by apply Matrix.ext; unfold raw30463step1 raw30463step0; decide +kernel
      have hl : raw30463step1Labels = raw30463step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw30463step0 raw30463step0Labels permutation127 permutation5
    mixedMoment B raw30463step1 raw30463step1Labels = mixedMoment B raw30463step2 raw30463step2Labels := by
      have ha : raw30463step2 = raw30463step1 := by apply Matrix.ext; unfold raw30463step2 raw30463step1; decide +kernel
      have hl : raw30463step1Labels = labelEmbedding1 ∘ raw30463step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw30463step1 raw30463step1Labels raw30463step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3419 node3419Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
