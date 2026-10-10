import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw14336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14336Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14336step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw14336step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14336 raw14336Labels = mixedMoment B node4833 node4833Labels := by
  calc
    mixedMoment B raw14336 raw14336Labels = mixedMoment B raw14336step0 raw14336step0Labels := by
      have ha : raw14336step0 = (fun i j => raw14336 (permutation194 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14336step0 raw14336; decide +kernel
      have hl : raw14336step0Labels = raw14336Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14336 raw14336Labels permutation194 permutation2
    _ = mixedMoment B node4833 node4833Labels := by rfl

def raw14337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14337Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14337step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14337step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14337step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14337 raw14337Labels = mixedMoment B node4893 node4893Labels := by
  calc
    mixedMoment B raw14337 raw14337Labels = mixedMoment B raw14337step0 raw14337step0Labels := by
      have hz : ∀ j, raw14337 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14337step0 = (fun i j => raw14337 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14337step0 raw14337; decide +kernel
      have hl : raw14337step0Labels = raw14337Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14337 raw14337Labels permutation346 hz
    mixedMoment B raw14337step0 raw14337step0Labels = mixedMoment B raw14337step1 raw14337step1Labels := by
      have ha : raw14337step1 = (fun i j => raw14337step0 (permutation42 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14337step1 raw14337step0; decide +kernel
      have hl : raw14337step1Labels = raw14337step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14337step0 raw14337step0Labels permutation42 permutation2
    _ = mixedMoment B node4893 node4893Labels := by rfl

def raw14338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw14338Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14338step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw14338step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14338step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14338step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14338 raw14338Labels = mixedMoment B node4893 node4893Labels := by
  calc
    mixedMoment B raw14338 raw14338Labels = mixedMoment B raw14338step0 raw14338step0Labels := by
      have hz : ∀ j, raw14338 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14338step0 = (fun i j => raw14338 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14338step0 raw14338; decide +kernel
      have hl : raw14338step0Labels = raw14338Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14338 raw14338Labels permutation346 hz
    mixedMoment B raw14338step0 raw14338step0Labels = mixedMoment B raw14338step1 raw14338step1Labels := by
      have ha : raw14338step1 = (fun i j => raw14338step0 (permutation48 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14338step1 raw14338step0; decide +kernel
      have hl : raw14338step1Labels = raw14338step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14338step0 raw14338step0Labels permutation48 permutation2
    _ = mixedMoment B node4893 node4893Labels := by rfl

def raw14339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw14339Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14339step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14339step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw14339step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14339step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw14339step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw14339step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw14339step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical14339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14339 raw14339Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw14339 raw14339Labels = mixedMoment B raw14339step0 raw14339step0Labels := by
      have hz : ∀ j, raw14339 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14339step0 = (fun i j => raw14339 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14339step0 raw14339; decide +kernel
      have hl : raw14339step0Labels = raw14339Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14339 raw14339Labels permutation590 hz
    mixedMoment B raw14339step0 raw14339step0Labels = mixedMoment B raw14339step1 raw14339step1Labels := by
      have hz : ∀ j, raw14339step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14339step1 = (fun i j => raw14339step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14339step1 raw14339step0; decide +kernel
      have hl : raw14339step1Labels = raw14339step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14339step0 raw14339step0Labels permutation80 hz
    mixedMoment B raw14339step1 raw14339step1Labels = mixedMoment B raw14339step2 raw14339step2Labels := by
      have hz : ∀ i, raw14339step1 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw14339step2 = (fun i j => raw14339step1 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw14339step2 raw14339step1; decide +kernel
      have hl : raw14339step2Labels = (fun j => raw14339step1Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw14339step1 raw14339step1Labels permutation4 hz
    mixedMoment B raw14339step2 raw14339step2Labels = mixedMoment B raw14339step3 raw14339step3Labels := by
      have ha : raw14339step3 = raw14339step2 := by apply Matrix.ext; unfold raw14339step3 raw14339step2; decide +kernel
      have hl : raw14339step2Labels = labelEmbedding2 ∘ raw14339step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14339step2 raw14339step2Labels raw14339step3Labels labelEmbedding2 hl
    _ = mixedMoment B node4083 node4083Labels := by rfl

def raw14340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14340Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14340step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14340step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14340 raw14340Labels = mixedMoment B node4456 node4456Labels := by
  calc
    mixedMoment B raw14340 raw14340Labels = mixedMoment B raw14340step0 raw14340step0Labels := by
      have ha : raw14340step0 = (fun i j => raw14340 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14340step0 raw14340; decide +kernel
      have hl : raw14340step0Labels = raw14340Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14340 raw14340Labels permutation156 permutation2
    _ = mixedMoment B node4456 node4456Labels := by rfl

def raw14341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14341Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14341step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14341step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14341 raw14341Labels = mixedMoment B node4864 node4864Labels := by
  calc
    mixedMoment B raw14341 raw14341Labels = mixedMoment B raw14341step0 raw14341step0Labels := by
      have ha : raw14341step0 = (fun i j => raw14341 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14341step0 raw14341; decide +kernel
      have hl : raw14341step0Labels = raw14341Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14341 raw14341Labels permutation156 permutation2
    _ = mixedMoment B node4864 node4864Labels := by rfl

def raw14342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14342Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14342step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14342step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14342 raw14342Labels = mixedMoment B node4887 node4887Labels := by
  calc
    mixedMoment B raw14342 raw14342Labels = mixedMoment B raw14342step0 raw14342step0Labels := by
      have ha : raw14342step0 = (fun i j => raw14342 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14342step0 raw14342; decide +kernel
      have hl : raw14342step0Labels = raw14342Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14342 raw14342Labels permutation159 permutation2
    _ = mixedMoment B node4887 node4887Labels := by rfl

def raw14343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw14343Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14343step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14343step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14343 raw14343Labels = mixedMoment B node4887 node4887Labels := by
  calc
    mixedMoment B raw14343 raw14343Labels = mixedMoment B raw14343step0 raw14343step0Labels := by
      have ha : raw14343step0 = (fun i j => raw14343 (permutation165 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14343step0 raw14343; decide +kernel
      have hl : raw14343step0Labels = raw14343Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14343 raw14343Labels permutation165 permutation2
    _ = mixedMoment B node4887 node4887Labels := by rfl

def raw14344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw14344Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw14344step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14344 raw14344Labels = mixedMoment B node4893 node4893Labels := by
  calc
    mixedMoment B raw14344 raw14344Labels = mixedMoment B raw14344step0 raw14344step0Labels := by
      have hz : ∀ j, raw14344 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14344step0 = (fun i j => raw14344 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14344step0 raw14344; decide +kernel
      have hl : raw14344step0Labels = raw14344Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14344 raw14344Labels permutation590 hz
    _ = mixedMoment B node4893 node4893Labels := by rfl

def raw14345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14345Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14345step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14345step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14345step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14345 raw14345Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw14345 raw14345Labels = mixedMoment B raw14345step0 raw14345step0Labels := by
      have hz : ∀ j, raw14345 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14345step0 = (fun i j => raw14345 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14345step0 raw14345; decide +kernel
      have hl : raw14345step0Labels = raw14345Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14345 raw14345Labels permutation346 hz
    mixedMoment B raw14345step0 raw14345step0Labels = mixedMoment B raw14345step1 raw14345step1Labels := by
      have ha : raw14345step1 = (fun i j => raw14345step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14345step1 raw14345step0; decide +kernel
      have hl : raw14345step1Labels = raw14345step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14345step0 raw14345step0Labels permutation37 permutation2
    _ = mixedMoment B node4458 node4458Labels := by rfl

def raw14346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14346Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14346step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14346step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14346step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14346step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14346 raw14346Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw14346 raw14346Labels = mixedMoment B raw14346step0 raw14346step0Labels := by
      have hz : ∀ j, raw14346 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14346step0 = (fun i j => raw14346 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14346step0 raw14346; decide +kernel
      have hl : raw14346step0Labels = raw14346Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14346 raw14346Labels permutation346 hz
    mixedMoment B raw14346step0 raw14346step0Labels = mixedMoment B raw14346step1 raw14346step1Labels := by
      have ha : raw14346step1 = (fun i j => raw14346step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14346step1 raw14346step0; decide +kernel
      have hl : raw14346step1Labels = raw14346step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14346step0 raw14346step0Labels permutation37 permutation2
    _ = mixedMoment B node4866 node4866Labels := by rfl

def raw14347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw14347Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14347step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14347step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14347 raw14347Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw14347 raw14347Labels = mixedMoment B raw14347step0 raw14347step0Labels := by
      have ha : raw14347step0 = (fun i j => raw14347 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14347step0 raw14347; decide +kernel
      have hl : raw14347step0Labels = raw14347Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14347 raw14347Labels permutation181 permutation2
    _ = mixedMoment B node4802 node4802Labels := by rfl

def raw14348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw14348Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14348step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw14348step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14348step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14348step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14348 raw14348Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw14348 raw14348Labels = mixedMoment B raw14348step0 raw14348step0Labels := by
      have hz : ∀ j, raw14348 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14348step0 = (fun i j => raw14348 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14348step0 raw14348; decide +kernel
      have hl : raw14348step0Labels = raw14348Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14348 raw14348Labels permutation346 hz
    mixedMoment B raw14348step0 raw14348step0Labels = mixedMoment B raw14348step1 raw14348step1Labels := by
      have ha : raw14348step1 = (fun i j => raw14348step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14348step1 raw14348step0; decide +kernel
      have hl : raw14348step1Labels = raw14348step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14348step0 raw14348step0Labels permutation35 permutation2
    _ = mixedMoment B node4888 node4888Labels := by rfl

def raw14349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw14349Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw14349step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14349step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw14349step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14349step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14349step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14349 raw14349Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw14349 raw14349Labels = mixedMoment B raw14349step0 raw14349step0Labels := by
      have hz : ∀ j, raw14349 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14349step0 = (fun i j => raw14349 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14349step0 raw14349; decide +kernel
      have hl : raw14349step0Labels = raw14349Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14349 raw14349Labels permutation590 hz
    mixedMoment B raw14349step0 raw14349step0Labels = mixedMoment B raw14349step1 raw14349step1Labels := by
      have hz : ∀ j, raw14349step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14349step1 = (fun i j => raw14349step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14349step1 raw14349step0; decide +kernel
      have hl : raw14349step1Labels = raw14349step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14349step0 raw14349step0Labels permutation80 hz
    mixedMoment B raw14349step1 raw14349step1Labels = mixedMoment B raw14349step2 raw14349step2Labels := by
      have ha : raw14349step2 = (fun i j => raw14349step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14349step2 raw14349step1; decide +kernel
      have hl : raw14349step2Labels = raw14349step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14349step1 raw14349step1Labels permutation9 permutation2
    _ = mixedMoment B node4895 node4895Labels := by rfl

def raw14350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw14350Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw14350step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14350step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14350step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14350 raw14350Labels = mixedMoment B node4458 node4458Labels := by
  calc
    mixedMoment B raw14350 raw14350Labels = mixedMoment B raw14350step0 raw14350step0Labels := by
      have hz : ∀ j, raw14350 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14350step0 = (fun i j => raw14350 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14350step0 raw14350; decide +kernel
      have hl : raw14350step0Labels = raw14350Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14350 raw14350Labels permutation346 hz
    mixedMoment B raw14350step0 raw14350step0Labels = mixedMoment B raw14350step1 raw14350step1Labels := by
      have ha : raw14350step1 = (fun i j => raw14350step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14350step1 raw14350step0; decide +kernel
      have hl : raw14350step1Labels = raw14350step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14350step0 raw14350step0Labels permutation36 permutation2
    _ = mixedMoment B node4458 node4458Labels := by rfl

def raw14351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw14351Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14351step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw14351step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14351step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14351step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14351 raw14351Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw14351 raw14351Labels = mixedMoment B raw14351step0 raw14351step0Labels := by
      have hz : ∀ j, raw14351 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14351step0 = (fun i j => raw14351 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14351step0 raw14351; decide +kernel
      have hl : raw14351step0Labels = raw14351Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14351 raw14351Labels permutation346 hz
    mixedMoment B raw14351step0 raw14351step0Labels = mixedMoment B raw14351step1 raw14351step1Labels := by
      have ha : raw14351step1 = (fun i j => raw14351step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14351step1 raw14351step0; decide +kernel
      have hl : raw14351step1Labels = raw14351step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14351step0 raw14351step0Labels permutation36 permutation2
    _ = mixedMoment B node4866 node4866Labels := by rfl

def raw14352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw14352Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14352step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14352step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14352 raw14352Labels = mixedMoment B node4802 node4802Labels := by
  calc
    mixedMoment B raw14352 raw14352Labels = mixedMoment B raw14352step0 raw14352step0Labels := by
      have ha : raw14352step0 = (fun i j => raw14352 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14352step0 raw14352; decide +kernel
      have hl : raw14352step0Labels = raw14352Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14352 raw14352Labels permutation180 permutation2
    _ = mixedMoment B node4802 node4802Labels := by rfl

def raw14353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw14353Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14353step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw14353step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14353step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14353step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14353 raw14353Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw14353 raw14353Labels = mixedMoment B raw14353step0 raw14353step0Labels := by
      have hz : ∀ j, raw14353 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14353step0 = (fun i j => raw14353 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14353step0 raw14353; decide +kernel
      have hl : raw14353step0Labels = raw14353Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14353 raw14353Labels permutation346 hz
    mixedMoment B raw14353step0 raw14353step0Labels = mixedMoment B raw14353step1 raw14353step1Labels := by
      have ha : raw14353step1 = (fun i j => raw14353step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14353step1 raw14353step0; decide +kernel
      have hl : raw14353step1Labels = raw14353step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14353step0 raw14353step0Labels permutation33 permutation2
    _ = mixedMoment B node4888 node4888Labels := by rfl

def raw14354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw14354Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14354step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw14354step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14354step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw14354step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14354 raw14354Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw14354 raw14354Labels = mixedMoment B raw14354step0 raw14354step0Labels := by
      have hz : ∀ j, raw14354 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14354step0 = (fun i j => raw14354 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14354step0 raw14354; decide +kernel
      have hl : raw14354step0Labels = raw14354Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14354 raw14354Labels permutation590 hz
    mixedMoment B raw14354step0 raw14354step0Labels = mixedMoment B raw14354step1 raw14354step1Labels := by
      have hz : ∀ j, raw14354step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14354step1 = (fun i j => raw14354step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14354step1 raw14354step0; decide +kernel
      have hl : raw14354step1Labels = raw14354step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14354step0 raw14354step0Labels permutation80 hz
    _ = mixedMoment B node4895 node4895Labels := by rfl

def raw14355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14355Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14355step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14355 raw14355Labels = mixedMoment B node4461 node4461Labels := by
  calc
    mixedMoment B raw14355 raw14355Labels = mixedMoment B raw14355step0 raw14355step0Labels := by
      have hz : ∀ j, raw14355 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14355step0 = (fun i j => raw14355 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14355step0 raw14355; decide +kernel
      have hl : raw14355step0Labels = raw14355Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14355 raw14355Labels permutation346 hz
    _ = mixedMoment B node4461 node4461Labels := by rfl

def raw14356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14356Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14356step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14356step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14356 raw14356Labels = mixedMoment B node4869 node4869Labels := by
  calc
    mixedMoment B raw14356 raw14356Labels = mixedMoment B raw14356step0 raw14356step0Labels := by
      have hz : ∀ j, raw14356 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14356step0 = (fun i j => raw14356 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14356step0 raw14356; decide +kernel
      have hl : raw14356step0Labels = raw14356Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14356 raw14356Labels permutation346 hz
    _ = mixedMoment B node4869 node4869Labels := by rfl

def raw14357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14357Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14357step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14357step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14357 raw14357Labels = mixedMoment B node4805 node4805Labels := by
  calc
    mixedMoment B raw14357 raw14357Labels = mixedMoment B raw14357step0 raw14357step0Labels := by
      have ha : raw14357step0 = (fun i j => raw14357 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14357step0 raw14357; decide +kernel
      have hl : raw14357step0Labels = raw14357Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14357 raw14357Labels permutation176 permutation2
    _ = mixedMoment B node4805 node4805Labels := by rfl

def raw14358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14358Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14358step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14358 raw14358Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw14358 raw14358Labels = mixedMoment B raw14358step0 raw14358step0Labels := by
      have hz : ∀ j, raw14358 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14358step0 = (fun i j => raw14358 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14358step0 raw14358; decide +kernel
      have hl : raw14358step0Labels = raw14358Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14358 raw14358Labels permutation346 hz
    _ = mixedMoment B node4889 node4889Labels := by rfl

def raw14359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw14359Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14359step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw14359step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14359step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14359step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14359 raw14359Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw14359 raw14359Labels = mixedMoment B raw14359step0 raw14359step0Labels := by
      have hz : ∀ j, raw14359 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14359step0 = (fun i j => raw14359 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14359step0 raw14359; decide +kernel
      have hl : raw14359step0Labels = raw14359Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14359 raw14359Labels permutation346 hz
    mixedMoment B raw14359step0 raw14359step0Labels = mixedMoment B raw14359step1 raw14359step1Labels := by
      have ha : raw14359step1 = (fun i j => raw14359step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14359step1 raw14359step0; decide +kernel
      have hl : raw14359step1Labels = raw14359step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14359step0 raw14359step0Labels permutation34 permutation2
    _ = mixedMoment B node4889 node4889Labels := by rfl

def raw14360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14360Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14360step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14360step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw14360step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical14360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14360 raw14360Labels = mixedMoment B node4068 node4068Labels := by
  calc
    mixedMoment B raw14360 raw14360Labels = mixedMoment B raw14360step0 raw14360step0Labels := by
      have hz : ∀ j, raw14360 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14360step0 = (fun i j => raw14360 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14360step0 raw14360; decide +kernel
      have hl : raw14360step0Labels = raw14360Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14360 raw14360Labels permutation346 hz
    mixedMoment B raw14360step0 raw14360step0Labels = mixedMoment B raw14360step1 raw14360step1Labels := by
      have hz : ∀ i, raw14360step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw14360step1 = (fun i j => raw14360step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw14360step1 raw14360step0; decide +kernel
      have hl : raw14360step1Labels = (fun j => raw14360step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw14360step0 raw14360step0Labels permutation6 hz
    _ = mixedMoment B node4068 node4068Labels := by rfl

def raw14361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14361Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14361step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw14361step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14361step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw14361step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical14361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14361 raw14361Labels = mixedMoment B node4079 node4079Labels := by
  calc
    mixedMoment B raw14361 raw14361Labels = mixedMoment B raw14361step0 raw14361step0Labels := by
      have hz : ∀ i, raw14361 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw14361step0 = (fun i j => raw14361 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw14361step0 raw14361; decide +kernel
      have hl : raw14361step0Labels = (fun j => raw14361Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw14361 raw14361Labels permutation6 hz
    mixedMoment B raw14361step0 raw14361step0Labels = mixedMoment B raw14361step1 raw14361step1Labels := by
      have ha : raw14361step1 = (fun i j => raw14361step0 (permutation176 i) (permutation0 j)) := by apply Matrix.ext; unfold raw14361step1 raw14361step0; decide +kernel
      have hl : raw14361step1Labels = raw14361step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14361step0 raw14361step0Labels permutation176 permutation0
    _ = mixedMoment B node4079 node4079Labels := by rfl

def raw14362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw14362Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14362step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14362step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14362step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14362step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14362step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw14362step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical14362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14362 raw14362Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw14362 raw14362Labels = mixedMoment B raw14362step0 raw14362step0Labels := by
      have hz : ∀ j, raw14362 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw14362step0 = (fun i j => raw14362 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw14362step0 raw14362; decide +kernel
      have hl : raw14362step0Labels = raw14362Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14362 raw14362Labels permutation520 hz
    mixedMoment B raw14362step0 raw14362step0Labels = mixedMoment B raw14362step1 raw14362step1Labels := by
      have hz : ∀ j, raw14362step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14362step1 = (fun i j => raw14362step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14362step1 raw14362step0; decide +kernel
      have hl : raw14362step1Labels = raw14362step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14362step0 raw14362step0Labels permutation80 hz
    mixedMoment B raw14362step1 raw14362step1Labels = mixedMoment B raw14362step2 raw14362step2Labels := by
      have hz : ∀ i, raw14362step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw14362step2 = (fun i j => raw14362step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw14362step2 raw14362step1; decide +kernel
      have hl : raw14362step2Labels = (fun j => raw14362step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw14362step1 raw14362step1Labels permutation6 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

def raw14363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw14363Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14363step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14363step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14363step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14363step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw14363step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical14363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14363 raw14363Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw14363 raw14363Labels = mixedMoment B raw14363step0 raw14363step0Labels := by
      have hz : ∀ j, raw14363 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14363step0 = (fun i j => raw14363 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14363step0 raw14363; decide +kernel
      have hl : raw14363step0Labels = raw14363Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14363 raw14363Labels permutation590 hz
    mixedMoment B raw14363step0 raw14363step0Labels = mixedMoment B raw14363step1 raw14363step1Labels := by
      have hz : ∀ j, raw14363step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14363step1 = (fun i j => raw14363step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14363step1 raw14363step0; decide +kernel
      have hl : raw14363step1Labels = raw14363step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14363step0 raw14363step0Labels permutation80 hz
    mixedMoment B raw14363step1 raw14363step1Labels = mixedMoment B raw14363step2 raw14363step2Labels := by
      have hz : ∀ i, raw14363step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw14363step2 = (fun i j => raw14363step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw14363step2 raw14363step1; decide +kernel
      have hl : raw14363step2Labels = (fun j => raw14363step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw14363step1 raw14363step1Labels permutation6 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

def raw14364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14364Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14364step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14364step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw14364step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical14364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14364 raw14364Labels = mixedMoment B node4068 node4068Labels := by
  calc
    mixedMoment B raw14364 raw14364Labels = mixedMoment B raw14364step0 raw14364step0Labels := by
      have hz : ∀ j, raw14364 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14364step0 = (fun i j => raw14364 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14364step0 raw14364; decide +kernel
      have hl : raw14364step0Labels = raw14364Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14364 raw14364Labels permutation265 hz
    mixedMoment B raw14364step0 raw14364step0Labels = mixedMoment B raw14364step1 raw14364step1Labels := by
      have hz : ∀ i, raw14364step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw14364step1 = (fun i j => raw14364step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw14364step1 raw14364step0; decide +kernel
      have hl : raw14364step1Labels = (fun j => raw14364step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw14364step0 raw14364step0Labels permutation6 hz
    _ = mixedMoment B node4068 node4068Labels := by rfl

def raw14365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14365Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14365step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw14365step0Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical14365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14365 raw14365Labels = mixedMoment B node4079 node4079Labels := by
  calc
    mixedMoment B raw14365 raw14365Labels = mixedMoment B raw14365step0 raw14365step0Labels := by
      have hz : ∀ i, raw14365 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw14365step0 = (fun i j => raw14365 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw14365step0 raw14365; decide +kernel
      have hl : raw14365step0Labels = (fun j => raw14365Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw14365 raw14365Labels permutation6 hz
    _ = mixedMoment B node4079 node4079Labels := by rfl

def raw14366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw14366Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14366step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14366step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14366step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14366step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw14366step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical14366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14366 raw14366Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw14366 raw14366Labels = mixedMoment B raw14366step0 raw14366step0Labels := by
      have hz : ∀ j, raw14366 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw14366step0 = (fun i j => raw14366 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw14366step0 raw14366; decide +kernel
      have hl : raw14366step0Labels = raw14366Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14366 raw14366Labels permutation520 hz
    mixedMoment B raw14366step0 raw14366step0Labels = mixedMoment B raw14366step1 raw14366step1Labels := by
      have hz : ∀ j, raw14366step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14366step1 = (fun i j => raw14366step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14366step1 raw14366step0; decide +kernel
      have hl : raw14366step1Labels = raw14366step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14366step0 raw14366step0Labels permutation56 hz
    mixedMoment B raw14366step1 raw14366step1Labels = mixedMoment B raw14366step2 raw14366step2Labels := by
      have hz : ∀ i, raw14366step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw14366step2 = (fun i j => raw14366step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw14366step2 raw14366step1; decide +kernel
      have hl : raw14366step2Labels = (fun j => raw14366step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw14366step1 raw14366step1Labels permutation6 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

def raw14367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw14367Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14367step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14367step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14367step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14367step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw14367step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical14367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14367 raw14367Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw14367 raw14367Labels = mixedMoment B raw14367step0 raw14367step0Labels := by
      have hz : ∀ j, raw14367 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14367step0 = (fun i j => raw14367 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14367step0 raw14367; decide +kernel
      have hl : raw14367step0Labels = raw14367Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14367 raw14367Labels permutation590 hz
    mixedMoment B raw14367step0 raw14367step0Labels = mixedMoment B raw14367step1 raw14367step1Labels := by
      have hz : ∀ j, raw14367step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14367step1 = (fun i j => raw14367step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14367step1 raw14367step0; decide +kernel
      have hl : raw14367step1Labels = raw14367step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14367step0 raw14367step0Labels permutation56 hz
    mixedMoment B raw14367step1 raw14367step1Labels = mixedMoment B raw14367step2 raw14367step2Labels := by
      have hz : ∀ i, raw14367step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw14367step2 = (fun i j => raw14367step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw14367step2 raw14367step1; decide +kernel
      have hl : raw14367step2Labels = (fun j => raw14367step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw14367step1 raw14367step1Labels permutation6 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

def raw14368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14368Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14368step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14368step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14368step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14368step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![2, -2], ![1, -1], ![1, -1]]
def raw14368step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14368step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw14368step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical14368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14368 raw14368Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw14368 raw14368Labels = mixedMoment B raw14368step0 raw14368step0Labels := by
      have hz : ∀ j, raw14368 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14368step0 = (fun i j => raw14368 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14368step0 raw14368; decide +kernel
      have hl : raw14368step0Labels = raw14368Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14368 raw14368Labels permutation346 hz
    mixedMoment B raw14368step0 raw14368step0Labels = mixedMoment B raw14368step1 raw14368step1Labels := by
      have hz : ∀ j, raw14368step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14368step1 = (fun i j => raw14368step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14368step1 raw14368step0; decide +kernel
      have hl : raw14368step1Labels = raw14368step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14368step0 raw14368step0Labels permutation56 hz
    mixedMoment B raw14368step1 raw14368step1Labels = mixedMoment B raw14368step2 raw14368step2Labels := by
      have hz : ∀ i, raw14368step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw14368step2 = (fun i j => raw14368step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw14368step2 raw14368step1; decide +kernel
      have hl : raw14368step2Labels = (fun j => raw14368step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw14368step1 raw14368step1Labels permutation6 hz
    mixedMoment B raw14368step2 raw14368step2Labels = mixedMoment B raw14368step3 raw14368step3Labels := by
      have ha : raw14368step3 = (fun i j => raw14368step2 (permutation11 i) (permutation0 j)) := by apply Matrix.ext; unfold raw14368step3 raw14368step2; decide +kernel
      have hl : raw14368step3Labels = raw14368step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14368step2 raw14368step2Labels permutation11 permutation0
    _ = mixedMoment B node4069 node4069Labels := by rfl

def raw14369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14369Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14369step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14369step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14369step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![1, -1], ![1, -1]]
def raw14369step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14369step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw14369step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical14369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14369 raw14369Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw14369 raw14369Labels = mixedMoment B raw14369step0 raw14369step0Labels := by
      have hz : ∀ j, raw14369 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14369step0 = (fun i j => raw14369 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14369step0 raw14369; decide +kernel
      have hl : raw14369step0Labels = raw14369Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14369 raw14369Labels permutation346 hz
    mixedMoment B raw14369step0 raw14369step0Labels = mixedMoment B raw14369step1 raw14369step1Labels := by
      have hz : ∀ i, raw14369step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw14369step1 = (fun i j => raw14369step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw14369step1 raw14369step0; decide +kernel
      have hl : raw14369step1Labels = (fun j => raw14369step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw14369step0 raw14369step0Labels permutation6 hz
    mixedMoment B raw14369step1 raw14369step1Labels = mixedMoment B raw14369step2 raw14369step2Labels := by
      have ha : raw14369step2 = (fun i j => raw14369step1 (permutation35 i) (permutation0 j)) := by apply Matrix.ext; unfold raw14369step2 raw14369step1; decide +kernel
      have hl : raw14369step2Labels = raw14369step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14369step1 raw14369step1Labels permutation35 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw14370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14370Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14370step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw14370step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14370step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![1, -1], ![1, -1]]
def raw14370step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14370step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw14370step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical14370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14370 raw14370Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw14370 raw14370Labels = mixedMoment B raw14370step0 raw14370step0Labels := by
      have hz : ∀ j, raw14370 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14370step0 = (fun i j => raw14370 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14370step0 raw14370; decide +kernel
      have hl : raw14370step0Labels = raw14370Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14370 raw14370Labels permutation265 hz
    mixedMoment B raw14370step0 raw14370step0Labels = mixedMoment B raw14370step1 raw14370step1Labels := by
      have hz : ∀ i, raw14370step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw14370step1 = (fun i j => raw14370step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw14370step1 raw14370step0; decide +kernel
      have hl : raw14370step1Labels = (fun j => raw14370step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw14370step0 raw14370step0Labels permutation6 hz
    mixedMoment B raw14370step1 raw14370step1Labels = mixedMoment B raw14370step2 raw14370step2Labels := by
      have ha : raw14370step2 = (fun i j => raw14370step1 (permutation35 i) (permutation0 j)) := by apply Matrix.ext; unfold raw14370step2 raw14370step1; decide +kernel
      have hl : raw14370step2Labels = raw14370step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14370step1 raw14370step1Labels permutation35 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw14371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0]]
def raw14371Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw14371step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14371step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw14371step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14371step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![2, -2, 0], ![1, -1, 0]]
def raw14371step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14371step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]
def raw14371step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14371step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw14371step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical14371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14371 raw14371Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw14371 raw14371Labels = mixedMoment B raw14371step0 raw14371step0Labels := by
      have hz : ∀ j, raw14371 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw14371step0 = (fun i j => raw14371 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw14371step0 raw14371; decide +kernel
      have hl : raw14371step0Labels = raw14371Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14371 raw14371Labels permutation520 hz
    mixedMoment B raw14371step0 raw14371step0Labels = mixedMoment B raw14371step1 raw14371step1Labels := by
      have hz : ∀ j, raw14371step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14371step1 = (fun i j => raw14371step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14371step1 raw14371step0; decide +kernel
      have hl : raw14371step1Labels = raw14371step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14371step0 raw14371step0Labels permutation80 hz
    mixedMoment B raw14371step1 raw14371step1Labels = mixedMoment B raw14371step2 raw14371step2Labels := by
      have hz : ∀ j, raw14371step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw14371step2 = (fun i j => raw14371step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw14371step2 raw14371step1; decide +kernel
      have hl : raw14371step2Labels = raw14371step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14371step1 raw14371step1Labels permutation14 hz
    mixedMoment B raw14371step2 raw14371step2Labels = mixedMoment B raw14371step3 raw14371step3Labels := by
      have hz : ∀ i, raw14371step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw14371step3 = (fun i j => raw14371step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw14371step3 raw14371step2; decide +kernel
      have hl : raw14371step3Labels = (fun j => raw14371step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw14371step2 raw14371step2Labels permutation6 hz
    mixedMoment B raw14371step3 raw14371step3Labels = mixedMoment B raw14371step4 raw14371step4Labels := by
      have ha : raw14371step4 = (fun i j => raw14371step3 (permutation3 i) (permutation0 j)) := by apply Matrix.ext; unfold raw14371step4 raw14371step3; decide +kernel
      have hl : raw14371step4Labels = raw14371step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14371step3 raw14371step3Labels permutation3 permutation0
    _ = mixedMoment B node4084 node4084Labels := by rfl

def raw14372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0]]
def raw14372Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw14372step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14372step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw14372step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14372step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![2, -2, 0], ![1, -1, 0]]
def raw14372step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14372step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]
def raw14372step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14372step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw14372step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical14372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14372 raw14372Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw14372 raw14372Labels = mixedMoment B raw14372step0 raw14372step0Labels := by
      have hz : ∀ j, raw14372 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14372step0 = (fun i j => raw14372 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14372step0 raw14372; decide +kernel
      have hl : raw14372step0Labels = raw14372Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14372 raw14372Labels permutation590 hz
    mixedMoment B raw14372step0 raw14372step0Labels = mixedMoment B raw14372step1 raw14372step1Labels := by
      have hz : ∀ j, raw14372step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14372step1 = (fun i j => raw14372step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14372step1 raw14372step0; decide +kernel
      have hl : raw14372step1Labels = raw14372step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14372step0 raw14372step0Labels permutation80 hz
    mixedMoment B raw14372step1 raw14372step1Labels = mixedMoment B raw14372step2 raw14372step2Labels := by
      have hz : ∀ j, raw14372step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw14372step2 = (fun i j => raw14372step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw14372step2 raw14372step1; decide +kernel
      have hl : raw14372step2Labels = raw14372step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14372step1 raw14372step1Labels permutation14 hz
    mixedMoment B raw14372step2 raw14372step2Labels = mixedMoment B raw14372step3 raw14372step3Labels := by
      have hz : ∀ i, raw14372step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw14372step3 = (fun i j => raw14372step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw14372step3 raw14372step2; decide +kernel
      have hl : raw14372step3Labels = (fun j => raw14372step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw14372step2 raw14372step2Labels permutation6 hz
    mixedMoment B raw14372step3 raw14372step3Labels = mixedMoment B raw14372step4 raw14372step4Labels := by
      have ha : raw14372step4 = (fun i j => raw14372step3 (permutation3 i) (permutation0 j)) := by apply Matrix.ext; unfold raw14372step4 raw14372step3; decide +kernel
      have hl : raw14372step4Labels = raw14372step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14372step3 raw14372step3Labels permutation3 permutation0
    _ = mixedMoment B node4084 node4084Labels := by rfl

def raw14373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw14373Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 4, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw14373step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14373step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 4, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw14373step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14373step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![2, -2], ![1, -1]]
def raw14373step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14373step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![1, -1], ![1, -1], ![2, -2]]
def raw14373step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical14373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14373 raw14373Labels = mixedMoment B node4069 node4069Labels := by
  calc
    mixedMoment B raw14373 raw14373Labels = mixedMoment B raw14373step0 raw14373step0Labels := by
      have hz : ∀ j, raw14373 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14373step0 = (fun i j => raw14373 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14373step0 raw14373; decide +kernel
      have hl : raw14373step0Labels = raw14373Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14373 raw14373Labels permutation346 hz
    mixedMoment B raw14373step0 raw14373step0Labels = mixedMoment B raw14373step1 raw14373step1Labels := by
      have hz : ∀ j, raw14373step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw14373step1 = (fun i j => raw14373step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw14373step1 raw14373step0; decide +kernel
      have hl : raw14373step1Labels = raw14373step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14373step0 raw14373step0Labels permutation56 hz
    mixedMoment B raw14373step1 raw14373step1Labels = mixedMoment B raw14373step2 raw14373step2Labels := by
      have hz : ∀ i, raw14373step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw14373step2 = (fun i j => raw14373step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw14373step2 raw14373step1; decide +kernel
      have hl : raw14373step2Labels = (fun j => raw14373step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw14373step1 raw14373step1Labels permutation6 hz
    mixedMoment B raw14373step2 raw14373step2Labels = mixedMoment B raw14373step3 raw14373step3Labels := by
      have ha : raw14373step3 = (fun i j => raw14373step2 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw14373step3 raw14373step2; decide +kernel
      have hl : raw14373step3Labels = raw14373step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14373step2 raw14373step2Labels permutation9 permutation0
    _ = mixedMoment B node4069 node4069Labels := by rfl

def raw14374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw14374Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw14374step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14374step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![2, -2], ![1, -1]]
def raw14374step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14374step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw14374step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical14374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14374 raw14374Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw14374 raw14374Labels = mixedMoment B raw14374step0 raw14374step0Labels := by
      have hz : ∀ j, raw14374 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw14374step0 = (fun i j => raw14374 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw14374step0 raw14374; decide +kernel
      have hl : raw14374step0Labels = raw14374Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14374 raw14374Labels permutation346 hz
    mixedMoment B raw14374step0 raw14374step0Labels = mixedMoment B raw14374step1 raw14374step1Labels := by
      have hz : ∀ i, raw14374step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw14374step1 = (fun i j => raw14374step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw14374step1 raw14374step0; decide +kernel
      have hl : raw14374step1Labels = (fun j => raw14374step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw14374step0 raw14374step0Labels permutation6 hz
    mixedMoment B raw14374step1 raw14374step1Labels = mixedMoment B raw14374step2 raw14374step2Labels := by
      have ha : raw14374step2 = (fun i j => raw14374step1 (permutation33 i) (permutation0 j)) := by apply Matrix.ext; unfold raw14374step2 raw14374step1; decide +kernel
      have hl : raw14374step2Labels = raw14374step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14374step1 raw14374step1Labels permutation33 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw14375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw14375Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw14375step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14375step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![2, -2], ![1, -1]]
def raw14375step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14375step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw14375step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical14375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14375 raw14375Labels = mixedMoment B node4080 node4080Labels := by
  calc
    mixedMoment B raw14375 raw14375Labels = mixedMoment B raw14375step0 raw14375step0Labels := by
      have hz : ∀ j, raw14375 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw14375step0 = (fun i j => raw14375 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw14375step0 raw14375; decide +kernel
      have hl : raw14375step0Labels = raw14375Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14375 raw14375Labels permutation265 hz
    mixedMoment B raw14375step0 raw14375step0Labels = mixedMoment B raw14375step1 raw14375step1Labels := by
      have hz : ∀ i, raw14375step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw14375step1 = (fun i j => raw14375step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw14375step1 raw14375step0; decide +kernel
      have hl : raw14375step1Labels = (fun j => raw14375step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw14375step0 raw14375step0Labels permutation6 hz
    mixedMoment B raw14375step1 raw14375step1Labels = mixedMoment B raw14375step2 raw14375step2Labels := by
      have ha : raw14375step2 = (fun i j => raw14375step1 (permutation33 i) (permutation0 j)) := by apply Matrix.ext; unfold raw14375step2 raw14375step1; decide +kernel
      have hl : raw14375step2Labels = raw14375step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14375step1 raw14375step1Labels permutation33 permutation0
    _ = mixedMoment B node4080 node4080Labels := by rfl

def raw14376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0]]
def raw14376Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw14376step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14376step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw14376step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14376step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![2, -2, 0]]
def raw14376step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14376step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw14376step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical14376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14376 raw14376Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw14376 raw14376Labels = mixedMoment B raw14376step0 raw14376step0Labels := by
      have hz : ∀ j, raw14376 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14376step0 = (fun i j => raw14376 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14376step0 raw14376; decide +kernel
      have hl : raw14376step0Labels = raw14376Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14376 raw14376Labels permutation590 hz
    mixedMoment B raw14376step0 raw14376step0Labels = mixedMoment B raw14376step1 raw14376step1Labels := by
      have hz : ∀ j, raw14376step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw14376step1 = (fun i j => raw14376step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw14376step1 raw14376step0; decide +kernel
      have hl : raw14376step1Labels = raw14376step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14376step0 raw14376step0Labels permutation80 hz
    mixedMoment B raw14376step1 raw14376step1Labels = mixedMoment B raw14376step2 raw14376step2Labels := by
      have hz : ∀ j, raw14376step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw14376step2 = (fun i j => raw14376step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw14376step2 raw14376step1; decide +kernel
      have hl : raw14376step2Labels = raw14376step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14376step1 raw14376step1Labels permutation14 hz
    mixedMoment B raw14376step2 raw14376step2Labels = mixedMoment B raw14376step3 raw14376step3Labels := by
      have hz : ∀ i, raw14376step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw14376step3 = (fun i j => raw14376step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw14376step3 raw14376step2; decide +kernel
      have hl : raw14376step3Labels = (fun j => raw14376step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw14376step2 raw14376step2Labels permutation6 hz
    _ = mixedMoment B node4084 node4084Labels := by rfl

def raw14377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14377Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14377step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw14377step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14377step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14377step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14377step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14377step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14377 raw14377Labels = mixedMoment B node5402 node5402Labels := by
  calc
    mixedMoment B raw14377 raw14377Labels = mixedMoment B raw14377step0 raw14377step0Labels := by
      have ha : raw14377step0 = (fun i j => raw14377 (permutation472 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14377step0 raw14377; decide +kernel
      have hl : raw14377step0Labels = raw14377Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14377 raw14377Labels permutation472 permutation4
    mixedMoment B raw14377step0 raw14377step0Labels = mixedMoment B raw14377step1 raw14377step1Labels := by
      have ha : raw14377step1 = -raw14377step0 := by apply Matrix.ext; change ∀ i j, raw14377step1 i j = -(raw14377step0 i j); unfold raw14377step1 raw14377step0; decide +kernel
      have hl : raw14377step1Labels = raw14377step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14377step1 raw14377step1Labels = mixedMoment B raw14377step2 raw14377step2Labels := by
      have ha : raw14377step2 = raw14377step1 := by apply Matrix.ext; unfold raw14377step2 raw14377step1; decide +kernel
      have hl : raw14377step1Labels = labelEmbedding7 ∘ raw14377step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14377step1 raw14377step1Labels raw14377step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5402 node5402Labels := by rfl

def raw14378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14378Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14378step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw14378step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14378step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14378step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14378step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14378step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14378 raw14378Labels = mixedMoment B node5353 node5353Labels := by
  calc
    mixedMoment B raw14378 raw14378Labels = mixedMoment B raw14378step0 raw14378step0Labels := by
      have ha : raw14378step0 = (fun i j => raw14378 (permutation472 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14378step0 raw14378; decide +kernel
      have hl : raw14378step0Labels = raw14378Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14378 raw14378Labels permutation472 permutation4
    mixedMoment B raw14378step0 raw14378step0Labels = mixedMoment B raw14378step1 raw14378step1Labels := by
      have ha : raw14378step1 = -raw14378step0 := by apply Matrix.ext; change ∀ i j, raw14378step1 i j = -(raw14378step0 i j); unfold raw14378step1 raw14378step0; decide +kernel
      have hl : raw14378step1Labels = raw14378step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14378step1 raw14378step1Labels = mixedMoment B raw14378step2 raw14378step2Labels := by
      have ha : raw14378step2 = raw14378step1 := by apply Matrix.ext; unfold raw14378step2 raw14378step1; decide +kernel
      have hl : raw14378step1Labels = labelEmbedding7 ∘ raw14378step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14378step1 raw14378step1Labels raw14378step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5353 node5353Labels := by rfl

def raw14379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14379Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14379step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw14379step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14379step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14379step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14379step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14379step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14379 raw14379Labels = mixedMoment B node5074 node5074Labels := by
  calc
    mixedMoment B raw14379 raw14379Labels = mixedMoment B raw14379step0 raw14379step0Labels := by
      have ha : raw14379step0 = (fun i j => raw14379 (permutation472 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14379step0 raw14379; decide +kernel
      have hl : raw14379step0Labels = raw14379Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14379 raw14379Labels permutation472 permutation4
    mixedMoment B raw14379step0 raw14379step0Labels = mixedMoment B raw14379step1 raw14379step1Labels := by
      have ha : raw14379step1 = -raw14379step0 := by apply Matrix.ext; change ∀ i j, raw14379step1 i j = -(raw14379step0 i j); unfold raw14379step1 raw14379step0; decide +kernel
      have hl : raw14379step1Labels = raw14379step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14379step1 raw14379step1Labels = mixedMoment B raw14379step2 raw14379step2Labels := by
      have ha : raw14379step2 = raw14379step1 := by apply Matrix.ext; unfold raw14379step2 raw14379step1; decide +kernel
      have hl : raw14379step1Labels = labelEmbedding7 ∘ raw14379step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14379step1 raw14379step1Labels raw14379step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5074 node5074Labels := by rfl

def raw14380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]
def raw14380Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14380step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14380step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14380step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw14380step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14380step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14380step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14380step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14380step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14380 raw14380Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw14380 raw14380Labels = mixedMoment B raw14380step0 raw14380step0Labels := by
      have hz : ∀ j, raw14380 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw14380step0 = (fun i j => raw14380 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw14380step0 raw14380; decide +kernel
      have hl : raw14380step0Labels = raw14380Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14380 raw14380Labels permutation520 hz
    mixedMoment B raw14380step0 raw14380step0Labels = mixedMoment B raw14380step1 raw14380step1Labels := by
      have ha : raw14380step1 = (fun i j => raw14380step0 (permutation118 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14380step1 raw14380step0; decide +kernel
      have hl : raw14380step1Labels = raw14380step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14380step0 raw14380step0Labels permutation118 permutation4
    mixedMoment B raw14380step1 raw14380step1Labels = mixedMoment B raw14380step2 raw14380step2Labels := by
      have ha : raw14380step2 = -raw14380step1 := by apply Matrix.ext; change ∀ i j, raw14380step2 i j = -(raw14380step1 i j); unfold raw14380step2 raw14380step1; decide +kernel
      have hl : raw14380step2Labels = raw14380step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14380step2 raw14380step2Labels = mixedMoment B raw14380step3 raw14380step3Labels := by
      have ha : raw14380step3 = raw14380step2 := by apply Matrix.ext; unfold raw14380step3 raw14380step2; decide +kernel
      have hl : raw14380step2Labels = labelEmbedding7 ∘ raw14380step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14380step2 raw14380step2Labels raw14380step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw14381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw14381Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14381step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14381step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14381step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14381step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14381 raw14381Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw14381 raw14381Labels = mixedMoment B raw14381step0 raw14381step0Labels := by
      have ha : raw14381step0 = (fun i j => raw14381 (permutation480 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14381step0 raw14381; decide +kernel
      have hl : raw14381step0Labels = raw14381Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14381 raw14381Labels permutation480 permutation6
    mixedMoment B raw14381step0 raw14381step0Labels = mixedMoment B raw14381step1 raw14381step1Labels := by
      have ha : raw14381step1 = raw14381step0 := by apply Matrix.ext; unfold raw14381step1 raw14381step0; decide +kernel
      have hl : raw14381step0Labels = labelEmbedding9 ∘ raw14381step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14381step0 raw14381step0Labels raw14381step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

def raw14382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14382Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14382 raw14382Labels = mixedMoment B node5254 node5254Labels := by
  calc
    _ = mixedMoment B node5254 node5254Labels := by rfl

def raw14383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14383Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14383step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw14383step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14383step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14383step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14383step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14383step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14383 raw14383Labels = mixedMoment B node5360 node5360Labels := by
  calc
    mixedMoment B raw14383 raw14383Labels = mixedMoment B raw14383step0 raw14383step0Labels := by
      have ha : raw14383step0 = (fun i j => raw14383 (permutation467 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14383step0 raw14383; decide +kernel
      have hl : raw14383step0Labels = raw14383Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14383 raw14383Labels permutation467 permutation4
    mixedMoment B raw14383step0 raw14383step0Labels = mixedMoment B raw14383step1 raw14383step1Labels := by
      have ha : raw14383step1 = -raw14383step0 := by apply Matrix.ext; change ∀ i j, raw14383step1 i j = -(raw14383step0 i j); unfold raw14383step1 raw14383step0; decide +kernel
      have hl : raw14383step1Labels = raw14383step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14383step1 raw14383step1Labels = mixedMoment B raw14383step2 raw14383step2Labels := by
      have ha : raw14383step2 = raw14383step1 := by apply Matrix.ext; unfold raw14383step2 raw14383step1; decide +kernel
      have hl : raw14383step1Labels = labelEmbedding7 ∘ raw14383step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14383step1 raw14383step1Labels raw14383step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5360 node5360Labels := by rfl

def raw14384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14384Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14384step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw14384step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14384step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14384step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14384step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14384step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14384 raw14384Labels = mixedMoment B node5086 node5086Labels := by
  calc
    mixedMoment B raw14384 raw14384Labels = mixedMoment B raw14384step0 raw14384step0Labels := by
      have ha : raw14384step0 = (fun i j => raw14384 (permutation467 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14384step0 raw14384; decide +kernel
      have hl : raw14384step0Labels = raw14384Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14384 raw14384Labels permutation467 permutation4
    mixedMoment B raw14384step0 raw14384step0Labels = mixedMoment B raw14384step1 raw14384step1Labels := by
      have ha : raw14384step1 = -raw14384step0 := by apply Matrix.ext; change ∀ i j, raw14384step1 i j = -(raw14384step0 i j); unfold raw14384step1 raw14384step0; decide +kernel
      have hl : raw14384step1Labels = raw14384step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14384step1 raw14384step1Labels = mixedMoment B raw14384step2 raw14384step2Labels := by
      have ha : raw14384step2 = raw14384step1 := by apply Matrix.ext; unfold raw14384step2 raw14384step1; decide +kernel
      have hl : raw14384step1Labels = labelEmbedding7 ∘ raw14384step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14384step1 raw14384step1Labels raw14384step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5086 node5086Labels := by rfl

def raw14385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]
def raw14385Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14385step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14385step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw14385step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14385step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14385step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14385step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14385step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14385 raw14385Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw14385 raw14385Labels = mixedMoment B raw14385step0 raw14385step0Labels := by
      have hz : ∀ j, raw14385 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw14385step0 = (fun i j => raw14385 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw14385step0 raw14385; decide +kernel
      have hl : raw14385step0Labels = raw14385Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14385 raw14385Labels permutation520 hz
    mixedMoment B raw14385step0 raw14385step0Labels = mixedMoment B raw14385step1 raw14385step1Labels := by
      have ha : raw14385step1 = (fun i j => raw14385step0 (permutation116 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14385step1 raw14385step0; decide +kernel
      have hl : raw14385step1Labels = raw14385step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14385step0 raw14385step0Labels permutation116 permutation4
    mixedMoment B raw14385step1 raw14385step1Labels = mixedMoment B raw14385step2 raw14385step2Labels := by
      have ha : raw14385step2 = -raw14385step1 := by apply Matrix.ext; change ∀ i j, raw14385step2 i j = -(raw14385step1 i j); unfold raw14385step2 raw14385step1; decide +kernel
      have hl : raw14385step2Labels = raw14385step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14385step2 raw14385step2Labels = mixedMoment B raw14385step3 raw14385step3Labels := by
      have ha : raw14385step3 = raw14385step2 := by apply Matrix.ext; unfold raw14385step3 raw14385step2; decide +kernel
      have hl : raw14385step2Labels = labelEmbedding7 ∘ raw14385step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14385step2 raw14385step2Labels raw14385step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

def raw14386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw14386Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14386step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14386step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw14386step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14386step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14386 raw14386Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw14386 raw14386Labels = mixedMoment B raw14386step0 raw14386step0Labels := by
      have ha : raw14386step0 = (fun i j => raw14386 (permutation480 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14386step0 raw14386; decide +kernel
      have hl : raw14386step0Labels = raw14386Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14386 raw14386Labels permutation480 permutation6
    mixedMoment B raw14386step0 raw14386step0Labels = mixedMoment B raw14386step1 raw14386step1Labels := by
      have ha : raw14386step1 = raw14386step0 := by apply Matrix.ext; unfold raw14386step1 raw14386step0; decide +kernel
      have hl : raw14386step0Labels = labelEmbedding9 ∘ raw14386step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14386step0 raw14386step0Labels raw14386step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

def raw14387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14387Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14387step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14387step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14387 raw14387Labels = mixedMoment B node5086 node5086Labels := by
  calc
    mixedMoment B raw14387 raw14387Labels = mixedMoment B raw14387step0 raw14387step0Labels := by
      have ha : raw14387step0 = (fun i j => raw14387 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14387step0 raw14387; decide +kernel
      have hl : raw14387step0Labels = raw14387Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14387 raw14387Labels permutation160 permutation2
    _ = mixedMoment B node5086 node5086Labels := by rfl

def raw14388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14388Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14388step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14388step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14388 raw14388Labels = mixedMoment B node5360 node5360Labels := by
  calc
    mixedMoment B raw14388 raw14388Labels = mixedMoment B raw14388step0 raw14388step0Labels := by
      have ha : raw14388step0 = (fun i j => raw14388 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14388step0 raw14388; decide +kernel
      have hl : raw14388step0Labels = raw14388Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14388 raw14388Labels permutation160 permutation2
    _ = mixedMoment B node5360 node5360Labels := by rfl

def raw14389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 0, -1], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14389Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14389step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw14389step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14389step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14389step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14389step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14389step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14389 raw14389Labels = mixedMoment B node5254 node5254Labels := by
  calc
    mixedMoment B raw14389 raw14389Labels = mixedMoment B raw14389step0 raw14389step0Labels := by
      have ha : raw14389step0 = (fun i j => raw14389 (permutation470 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14389step0 raw14389; decide +kernel
      have hl : raw14389step0Labels = raw14389Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14389 raw14389Labels permutation470 permutation4
    mixedMoment B raw14389step0 raw14389step0Labels = mixedMoment B raw14389step1 raw14389step1Labels := by
      have ha : raw14389step1 = -raw14389step0 := by apply Matrix.ext; change ∀ i j, raw14389step1 i j = -(raw14389step0 i j); unfold raw14389step1 raw14389step0; decide +kernel
      have hl : raw14389step1Labels = raw14389step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14389step1 raw14389step1Labels = mixedMoment B raw14389step2 raw14389step2Labels := by
      have ha : raw14389step2 = raw14389step1 := by apply Matrix.ext; unfold raw14389step2 raw14389step1; decide +kernel
      have hl : raw14389step1Labels = labelEmbedding7 ∘ raw14389step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14389step1 raw14389step1Labels raw14389step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5254 node5254Labels := by rfl

def raw14390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]
def raw14390Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14390step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14390step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14390step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14390step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14390 raw14390Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw14390 raw14390Labels = mixedMoment B raw14390step0 raw14390step0Labels := by
      have hz : ∀ j, raw14390 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw14390step0 = (fun i j => raw14390 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw14390step0 raw14390; decide +kernel
      have hl : raw14390step0Labels = raw14390Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14390 raw14390Labels permutation520 hz
    mixedMoment B raw14390step0 raw14390step0Labels = mixedMoment B raw14390step1 raw14390step1Labels := by
      have ha : raw14390step1 = (fun i j => raw14390step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14390step1 raw14390step0; decide +kernel
      have hl : raw14390step1Labels = raw14390step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14390step0 raw14390step0Labels permutation34 permutation2
    _ = mixedMoment B node5412 node5412Labels := by rfl

def raw14391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw14391Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14391step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw14391step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14391step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14391step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14391step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14391step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14391 raw14391Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw14391 raw14391Labels = mixedMoment B raw14391step0 raw14391step0Labels := by
      have ha : raw14391step0 = (fun i j => raw14391 (permutation168 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14391step0 raw14391; decide +kernel
      have hl : raw14391step0Labels = raw14391Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14391 raw14391Labels permutation168 permutation7
    mixedMoment B raw14391step0 raw14391step0Labels = mixedMoment B raw14391step1 raw14391step1Labels := by
      have ha : raw14391step1 = -raw14391step0 := by apply Matrix.ext; change ∀ i j, raw14391step1 i j = -(raw14391step0 i j); unfold raw14391step1 raw14391step0; decide +kernel
      have hl : raw14391step1Labels = raw14391step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14391step1 raw14391step1Labels = mixedMoment B raw14391step2 raw14391step2Labels := by
      have ha : raw14391step2 = raw14391step1 := by apply Matrix.ext; unfold raw14391step2 raw14391step1; decide +kernel
      have hl : raw14391step1Labels = labelEmbedding10 ∘ raw14391step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14391step1 raw14391step1Labels raw14391step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

def raw14392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14392Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14392step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14392step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14392 raw14392Labels = mixedMoment B node5074 node5074Labels := by
  calc
    mixedMoment B raw14392 raw14392Labels = mixedMoment B raw14392step0 raw14392step0Labels := by
      have ha : raw14392step0 = (fun i j => raw14392 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14392step0 raw14392; decide +kernel
      have hl : raw14392step0Labels = raw14392Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14392 raw14392Labels permutation154 permutation2
    _ = mixedMoment B node5074 node5074Labels := by rfl

def raw14393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14393Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14393step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14393step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14393 raw14393Labels = mixedMoment B node5353 node5353Labels := by
  calc
    mixedMoment B raw14393 raw14393Labels = mixedMoment B raw14393step0 raw14393step0Labels := by
      have ha : raw14393step0 = (fun i j => raw14393 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14393step0 raw14393; decide +kernel
      have hl : raw14393step0Labels = raw14393Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14393 raw14393Labels permutation154 permutation2
    _ = mixedMoment B node5353 node5353Labels := by rfl

def raw14394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14394Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14394step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14394step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14394 raw14394Labels = mixedMoment B node5402 node5402Labels := by
  calc
    mixedMoment B raw14394 raw14394Labels = mixedMoment B raw14394step0 raw14394step0Labels := by
      have ha : raw14394step0 = (fun i j => raw14394 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14394step0 raw14394; decide +kernel
      have hl : raw14394step0Labels = raw14394Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14394 raw14394Labels permutation154 permutation2
    _ = mixedMoment B node5402 node5402Labels := by rfl

def raw14395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![0, 0, 0], ![2, -2, 0]]
def raw14395Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14395step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14395 raw14395Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw14395 raw14395Labels = mixedMoment B raw14395step0 raw14395step0Labels := by
      have hz : ∀ j, raw14395 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw14395step0 = (fun i j => raw14395 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw14395step0 raw14395; decide +kernel
      have hl : raw14395step0Labels = raw14395Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14395 raw14395Labels permutation520 hz
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw14396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw14396Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14396step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw14396step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14396step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14396step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw14396step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14396step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14396 raw14396Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw14396 raw14396Labels = mixedMoment B raw14396step0 raw14396step0Labels := by
      have ha : raw14396step0 = (fun i j => raw14396 (permutation168 i) (permutation7 j)) := by apply Matrix.ext; unfold raw14396step0 raw14396; decide +kernel
      have hl : raw14396step0Labels = raw14396Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14396 raw14396Labels permutation168 permutation7
    mixedMoment B raw14396step0 raw14396step0Labels = mixedMoment B raw14396step1 raw14396step1Labels := by
      have ha : raw14396step1 = -raw14396step0 := by apply Matrix.ext; change ∀ i j, raw14396step1 i j = -(raw14396step0 i j); unfold raw14396step1 raw14396step0; decide +kernel
      have hl : raw14396step1Labels = raw14396step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14396step1 raw14396step1Labels = mixedMoment B raw14396step2 raw14396step2Labels := by
      have ha : raw14396step2 = raw14396step1 := by apply Matrix.ext; unfold raw14396step2 raw14396step1; decide +kernel
      have hl : raw14396step1Labels = labelEmbedding10 ∘ raw14396step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14396step1 raw14396step1Labels raw14396step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

def raw14397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw14397Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14397 raw14397Labels = mixedMoment B node5068 node5068Labels := by
  calc
    _ = mixedMoment B node5068 node5068Labels := by rfl

def raw14398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw14398Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14398step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw14398step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14398step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw14398step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14398step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw14398step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14398 raw14398Labels = mixedMoment B node5322 node5322Labels := by
  calc
    mixedMoment B raw14398 raw14398Labels = mixedMoment B raw14398step0 raw14398step0Labels := by
      have ha : raw14398step0 = (fun i j => raw14398 (permutation583 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14398step0 raw14398; decide +kernel
      have hl : raw14398step0Labels = raw14398Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14398 raw14398Labels permutation583 permutation3
    mixedMoment B raw14398step0 raw14398step0Labels = mixedMoment B raw14398step1 raw14398step1Labels := by
      have ha : raw14398step1 = -raw14398step0 := by apply Matrix.ext; change ∀ i j, raw14398step1 i j = -(raw14398step0 i j); unfold raw14398step1 raw14398step0; decide +kernel
      have hl : raw14398step1Labels = raw14398step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14398step1 raw14398step1Labels = mixedMoment B raw14398step2 raw14398step2Labels := by
      have ha : raw14398step2 = raw14398step1 := by apply Matrix.ext; unfold raw14398step2 raw14398step1; decide +kernel
      have hl : raw14398step1Labels = labelEmbedding6 ∘ raw14398step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14398step1 raw14398step1Labels raw14398step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5322 node5322Labels := by rfl

def raw14399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw14399Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14399step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw14399step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14399step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw14399step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14399 raw14399Labels = mixedMoment B node5322 node5322Labels := by
  calc
    mixedMoment B raw14399 raw14399Labels = mixedMoment B raw14399step0 raw14399step0Labels := by
      have ha : raw14399step0 = (fun i j => raw14399 (permutation575 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14399step0 raw14399; decide +kernel
      have hl : raw14399step0Labels = raw14399Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14399 raw14399Labels permutation575 permutation5
    mixedMoment B raw14399step0 raw14399step0Labels = mixedMoment B raw14399step1 raw14399step1Labels := by
      have ha : raw14399step1 = raw14399step0 := by apply Matrix.ext; unfold raw14399step1 raw14399step0; decide +kernel
      have hl : raw14399step0Labels = labelEmbedding8 ∘ raw14399step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14399step0 raw14399step0Labels raw14399step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5322 node5322Labels := by rfl

def raw14400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 3, -2], ![2, -2, 0], ![2, -2, 0]]
def raw14400Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14400step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0], ![-2, 2, 0]]
def raw14400step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14400step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw14400step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14400step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw14400step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14400 raw14400Labels = mixedMoment B node5068 node5068Labels := by
  calc
    mixedMoment B raw14400 raw14400Labels = mixedMoment B raw14400step0 raw14400step0Labels := by
      have ha : raw14400step0 = (fun i j => raw14400 (permutation470 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14400step0 raw14400; decide +kernel
      have hl : raw14400step0Labels = raw14400Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14400 raw14400Labels permutation470 permutation4
    mixedMoment B raw14400step0 raw14400step0Labels = mixedMoment B raw14400step1 raw14400step1Labels := by
      have ha : raw14400step1 = -raw14400step0 := by apply Matrix.ext; change ∀ i j, raw14400step1 i j = -(raw14400step0 i j); unfold raw14400step1 raw14400step0; decide +kernel
      have hl : raw14400step1Labels = raw14400step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14400step1 raw14400step1Labels = mixedMoment B raw14400step2 raw14400step2Labels := by
      have ha : raw14400step2 = raw14400step1 := by apply Matrix.ext; unfold raw14400step2 raw14400step1; decide +kernel
      have hl : raw14400step1Labels = labelEmbedding7 ∘ raw14400step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14400step1 raw14400step1Labels raw14400step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5068 node5068Labels := by rfl

def raw14401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0]]
def raw14401Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14401step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14401step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14401 raw14401Labels = mixedMoment B node5407 node5407Labels := by
  calc
    mixedMoment B raw14401 raw14401Labels = mixedMoment B raw14401step0 raw14401step0Labels := by
      have ha : raw14401step0 = (fun i j => raw14401 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14401step0 raw14401; decide +kernel
      have hl : raw14401step0Labels = raw14401Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14401 raw14401Labels permutation153 permutation2
    _ = mixedMoment B node5407 node5407Labels := by rfl

def raw14402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw14402Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14402step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw14402step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14402step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw14402step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14402step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw14402step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14402 raw14402Labels = mixedMoment B node4733 node4733Labels := by
  calc
    mixedMoment B raw14402 raw14402Labels = mixedMoment B raw14402step0 raw14402step0Labels := by
      have ha : raw14402step0 = (fun i j => raw14402 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14402step0 raw14402; decide +kernel
      have hl : raw14402step0Labels = raw14402Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14402 raw14402Labels permutation682 permutation3
    mixedMoment B raw14402step0 raw14402step0Labels = mixedMoment B raw14402step1 raw14402step1Labels := by
      have ha : raw14402step1 = -raw14402step0 := by apply Matrix.ext; change ∀ i j, raw14402step1 i j = -(raw14402step0 i j); unfold raw14402step1 raw14402step0; decide +kernel
      have hl : raw14402step1Labels = raw14402step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14402step1 raw14402step1Labels = mixedMoment B raw14402step2 raw14402step2Labels := by
      have ha : raw14402step2 = raw14402step1 := by apply Matrix.ext; unfold raw14402step2 raw14402step1; decide +kernel
      have hl : raw14402step1Labels = labelEmbedding6 ∘ raw14402step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14402step1 raw14402step1Labels raw14402step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4733 node4733Labels := by rfl

def raw14403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw14403Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14403step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw14403step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14403step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw14403step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14403step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw14403step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14403 raw14403Labels = mixedMoment B node4735 node4735Labels := by
  calc
    mixedMoment B raw14403 raw14403Labels = mixedMoment B raw14403step0 raw14403step0Labels := by
      have ha : raw14403step0 = (fun i j => raw14403 (permutation681 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14403step0 raw14403; decide +kernel
      have hl : raw14403step0Labels = raw14403Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14403 raw14403Labels permutation681 permutation3
    mixedMoment B raw14403step0 raw14403step0Labels = mixedMoment B raw14403step1 raw14403step1Labels := by
      have ha : raw14403step1 = -raw14403step0 := by apply Matrix.ext; change ∀ i j, raw14403step1 i j = -(raw14403step0 i j); unfold raw14403step1 raw14403step0; decide +kernel
      have hl : raw14403step1Labels = raw14403step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14403step1 raw14403step1Labels = mixedMoment B raw14403step2 raw14403step2Labels := by
      have ha : raw14403step2 = raw14403step1 := by apply Matrix.ext; unfold raw14403step2 raw14403step1; decide +kernel
      have hl : raw14403step1Labels = labelEmbedding6 ∘ raw14403step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14403step1 raw14403step1Labels raw14403step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4735 node4735Labels := by rfl

def raw14404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw14404Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14404step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw14404step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14404step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw14404step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14404 raw14404Labels = mixedMoment B node4735 node4735Labels := by
  calc
    mixedMoment B raw14404 raw14404Labels = mixedMoment B raw14404step0 raw14404step0Labels := by
      have ha : raw14404step0 = (fun i j => raw14404 (permutation672 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14404step0 raw14404; decide +kernel
      have hl : raw14404step0Labels = raw14404Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14404 raw14404Labels permutation672 permutation5
    mixedMoment B raw14404step0 raw14404step0Labels = mixedMoment B raw14404step1 raw14404step1Labels := by
      have ha : raw14404step1 = raw14404step0 := by apply Matrix.ext; unfold raw14404step1 raw14404step0; decide +kernel
      have hl : raw14404step0Labels = labelEmbedding8 ∘ raw14404step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14404step0 raw14404step0Labels raw14404step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4735 node4735Labels := by rfl

def raw14405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 3, -2], ![1, -1, 0], ![3, -3, 0]]
def raw14405Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14405step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw14405step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14405step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw14405step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14405 raw14405Labels = mixedMoment B node4733 node4733Labels := by
  calc
    mixedMoment B raw14405 raw14405Labels = mixedMoment B raw14405step0 raw14405step0Labels := by
      have ha : raw14405step0 = (fun i j => raw14405 (permutation671 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14405step0 raw14405; decide +kernel
      have hl : raw14405step0Labels = raw14405Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14405 raw14405Labels permutation671 permutation5
    mixedMoment B raw14405step0 raw14405step0Labels = mixedMoment B raw14405step1 raw14405step1Labels := by
      have ha : raw14405step1 = raw14405step0 := by apply Matrix.ext; unfold raw14405step1 raw14405step0; decide +kernel
      have hl : raw14405step0Labels = labelEmbedding8 ∘ raw14405step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14405step0 raw14405step0Labels raw14405step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4733 node4733Labels := by rfl

def raw14406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![0, 0, 0], ![3, -3, 0]]
def raw14406Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw14406step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14406step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw14406step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14406step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14406step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14406step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14406step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14406 raw14406Labels = mixedMoment B node4891 node4891Labels := by
  calc
    mixedMoment B raw14406 raw14406Labels = mixedMoment B raw14406step0 raw14406step0Labels := by
      have hz : ∀ j, raw14406 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw14406step0 = (fun i j => raw14406 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw14406step0 raw14406; decide +kernel
      have hl : raw14406step0Labels = raw14406Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14406 raw14406Labels permutation520 hz
    mixedMoment B raw14406step0 raw14406step0Labels = mixedMoment B raw14406step1 raw14406step1Labels := by
      have ha : raw14406step1 = (fun i j => raw14406step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14406step1 raw14406step0; decide +kernel
      have hl : raw14406step1Labels = raw14406step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14406step0 raw14406step0Labels permutation145 permutation3
    mixedMoment B raw14406step1 raw14406step1Labels = mixedMoment B raw14406step2 raw14406step2Labels := by
      have ha : raw14406step2 = -raw14406step1 := by apply Matrix.ext; change ∀ i j, raw14406step2 i j = -(raw14406step1 i j); unfold raw14406step2 raw14406step1; decide +kernel
      have hl : raw14406step2Labels = raw14406step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14406step2 raw14406step2Labels = mixedMoment B raw14406step3 raw14406step3Labels := by
      have ha : raw14406step3 = raw14406step2 := by apply Matrix.ext; unfold raw14406step3 raw14406step2; decide +kernel
      have hl : raw14406step2Labels = labelEmbedding6 ∘ raw14406step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14406step2 raw14406step2Labels raw14406step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4891 node4891Labels := by rfl

def raw14407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14407Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14407step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw14407step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14407step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw14407step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14407 raw14407Labels = mixedMoment B node3802 node3802Labels := by
  calc
    mixedMoment B raw14407 raw14407Labels = mixedMoment B raw14407step0 raw14407step0Labels := by
      have ha : raw14407step0 = (fun i j => raw14407 (permutation681 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14407step0 raw14407; decide +kernel
      have hl : raw14407step0Labels = raw14407Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14407 raw14407Labels permutation681 permutation3
    mixedMoment B raw14407step0 raw14407step0Labels = mixedMoment B raw14407step1 raw14407step1Labels := by
      have ha : raw14407step1 = -raw14407step0 := by apply Matrix.ext; change ∀ i j, raw14407step1 i j = -(raw14407step0 i j); unfold raw14407step1 raw14407step0; decide +kernel
      have hl : raw14407step1Labels = raw14407step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3802 node3802Labels := by rfl

def raw14408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14408Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14408step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14408step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14408 raw14408Labels = mixedMoment B node3761 node3761Labels := by
  calc
    mixedMoment B raw14408 raw14408Labels = mixedMoment B raw14408step0 raw14408step0Labels := by
      have ha : raw14408step0 = (fun i j => raw14408 (permutation480 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14408step0 raw14408; decide +kernel
      have hl : raw14408step0Labels = raw14408Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14408 raw14408Labels permutation480 permutation6
    _ = mixedMoment B node3761 node3761Labels := by rfl

def raw14409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14409Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14409step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14409step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14409 raw14409Labels = mixedMoment B node3463 node3463Labels := by
  calc
    mixedMoment B raw14409 raw14409Labels = mixedMoment B raw14409step0 raw14409step0Labels := by
      have ha : raw14409step0 = (fun i j => raw14409 (permutation480 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14409step0 raw14409; decide +kernel
      have hl : raw14409step0Labels = raw14409Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14409 raw14409Labels permutation480 permutation6
    _ = mixedMoment B node3463 node3463Labels := by rfl

def raw14410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]
def raw14410Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14410step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14410step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14410step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw14410step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14410 raw14410Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw14410 raw14410Labels = mixedMoment B raw14410step0 raw14410step0Labels := by
      have hz : ∀ j, raw14410 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw14410step0 = (fun i j => raw14410 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw14410step0 raw14410; decide +kernel
      have hl : raw14410step0Labels = raw14410Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14410 raw14410Labels permutation520 hz
    mixedMoment B raw14410step0 raw14410step0Labels = mixedMoment B raw14410step1 raw14410step1Labels := by
      have ha : raw14410step1 = (fun i j => raw14410step0 (permutation121 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14410step1 raw14410step0; decide +kernel
      have hl : raw14410step1Labels = raw14410step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14410step0 raw14410step0Labels permutation121 permutation6
    _ = mixedMoment B node3813 node3813Labels := by rfl

def raw14411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw14411Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14411step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw14411step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14411 raw14411Labels = mixedMoment B node3800 node3800Labels := by
  calc
    mixedMoment B raw14411 raw14411Labels = mixedMoment B raw14411step0 raw14411step0Labels := by
      have ha : raw14411step0 = (fun i j => raw14411 (permutation480 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14411step0 raw14411; decide +kernel
      have hl : raw14411step0Labels = raw14411Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14411 raw14411Labels permutation480 permutation6
    _ = mixedMoment B node3800 node3800Labels := by rfl

def raw14412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14412Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14412step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw14412step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14412 raw14412Labels = mixedMoment B node3016 node3016Labels := by
  calc
    mixedMoment B raw14412 raw14412Labels = mixedMoment B raw14412step0 raw14412step0Labels := by
      have ha : raw14412step0 = (fun i j => raw14412 (permutation206 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14412step0 raw14412; decide +kernel
      have hl : raw14412step0Labels = raw14412Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14412 raw14412Labels permutation206 permutation3
    _ = mixedMoment B node3016 node3016Labels := by rfl

def raw14413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14413Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14413step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14413step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14413 raw14413Labels = mixedMoment B node3762 node3762Labels := by
  calc
    mixedMoment B raw14413 raw14413Labels = mixedMoment B raw14413step0 raw14413step0Labels := by
      have ha : raw14413step0 = (fun i j => raw14413 (permutation480 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14413step0 raw14413; decide +kernel
      have hl : raw14413step0Labels = raw14413Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14413 raw14413Labels permutation480 permutation6
    _ = mixedMoment B node3762 node3762Labels := by rfl

def raw14414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14414Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14414step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14414step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14414 raw14414Labels = mixedMoment B node3464 node3464Labels := by
  calc
    mixedMoment B raw14414 raw14414Labels = mixedMoment B raw14414step0 raw14414step0Labels := by
      have ha : raw14414step0 = (fun i j => raw14414 (permutation480 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14414step0 raw14414; decide +kernel
      have hl : raw14414step0Labels = raw14414Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14414 raw14414Labels permutation480 permutation6
    _ = mixedMoment B node3464 node3464Labels := by rfl

def raw14415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]
def raw14415Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14415step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14415step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14415step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14415step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14415 raw14415Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw14415 raw14415Labels = mixedMoment B raw14415step0 raw14415step0Labels := by
      have hz : ∀ j, raw14415 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw14415step0 = (fun i j => raw14415 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw14415step0 raw14415; decide +kernel
      have hl : raw14415step0Labels = raw14415Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14415 raw14415Labels permutation520 hz
    mixedMoment B raw14415step0 raw14415step0Labels = mixedMoment B raw14415step1 raw14415step1Labels := by
      have ha : raw14415step1 = (fun i j => raw14415step0 (permutation121 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14415step1 raw14415step0; decide +kernel
      have hl : raw14415step1Labels = raw14415step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14415step0 raw14415step0Labels permutation121 permutation6
    _ = mixedMoment B node3814 node3814Labels := by rfl

def raw14416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw14416Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14416step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw14416step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14416 raw14416Labels = mixedMoment B node3801 node3801Labels := by
  calc
    mixedMoment B raw14416 raw14416Labels = mixedMoment B raw14416step0 raw14416step0Labels := by
      have ha : raw14416step0 = (fun i j => raw14416 (permutation480 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14416step0 raw14416; decide +kernel
      have hl : raw14416step0Labels = raw14416Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14416 raw14416Labels permutation480 permutation6
    _ = mixedMoment B node3801 node3801Labels := by rfl

def raw14417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14417Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14417step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw14417step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14417 raw14417Labels = mixedMoment B node2974 node2974Labels := by
  calc
    mixedMoment B raw14417 raw14417Labels = mixedMoment B raw14417step0 raw14417step0Labels := by
      have ha : raw14417step0 = (fun i j => raw14417 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14417step0 raw14417; decide +kernel
      have hl : raw14417step0Labels = raw14417Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14417 raw14417Labels permutation158 permutation3
    _ = mixedMoment B node2974 node2974Labels := by rfl

def raw14418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14418Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14418step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw14418step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14418step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw14418step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14418 raw14418Labels = mixedMoment B node3780 node3780Labels := by
  calc
    mixedMoment B raw14418 raw14418Labels = mixedMoment B raw14418step0 raw14418step0Labels := by
      have ha : raw14418step0 = (fun i j => raw14418 (permutation681 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14418step0 raw14418; decide +kernel
      have hl : raw14418step0Labels = raw14418Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14418 raw14418Labels permutation681 permutation3
    mixedMoment B raw14418step0 raw14418step0Labels = mixedMoment B raw14418step1 raw14418step1Labels := by
      have ha : raw14418step1 = -raw14418step0 := by apply Matrix.ext; change ∀ i j, raw14418step1 i j = -(raw14418step0 i j); unfold raw14418step1 raw14418step0; decide +kernel
      have hl : raw14418step1Labels = raw14418step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3780 node3780Labels := by rfl

def raw14419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 0, -1], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14419Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14419step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14419step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14419 raw14419Labels = mixedMoment B node3528 node3528Labels := by
  calc
    mixedMoment B raw14419 raw14419Labels = mixedMoment B raw14419step0 raw14419step0Labels := by
      have ha : raw14419step0 = (fun i j => raw14419 (permutation480 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14419step0 raw14419; decide +kernel
      have hl : raw14419step0Labels = raw14419Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14419 raw14419Labels permutation480 permutation6
    _ = mixedMoment B node3528 node3528Labels := by rfl

def raw14420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]
def raw14420Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14420step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14420step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw14420step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14420step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14420step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14420 raw14420Labels = mixedMoment B node3856 node3856Labels := by
  calc
    mixedMoment B raw14420 raw14420Labels = mixedMoment B raw14420step0 raw14420step0Labels := by
      have hz : ∀ j, raw14420 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw14420step0 = (fun i j => raw14420 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw14420step0 raw14420; decide +kernel
      have hl : raw14420step0Labels = raw14420Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14420 raw14420Labels permutation520 hz
    mixedMoment B raw14420step0 raw14420step0Labels = mixedMoment B raw14420step1 raw14420step1Labels := by
      have ha : raw14420step1 = (fun i j => raw14420step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14420step1 raw14420step0; decide +kernel
      have hl : raw14420step1Labels = raw14420step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14420step0 raw14420step0Labels permutation145 permutation3
    mixedMoment B raw14420step1 raw14420step1Labels = mixedMoment B raw14420step2 raw14420step2Labels := by
      have ha : raw14420step2 = -raw14420step1 := by apply Matrix.ext; change ∀ i j, raw14420step2 i j = -(raw14420step1 i j); unfold raw14420step2 raw14420step1; decide +kernel
      have hl : raw14420step2Labels = raw14420step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3856 node3856Labels := by rfl

def raw14421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw14421Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14421step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw14421step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14421 raw14421Labels = mixedMoment B node3847 node3847Labels := by
  calc
    mixedMoment B raw14421 raw14421Labels = mixedMoment B raw14421step0 raw14421step0Labels := by
      have ha : raw14421step0 = (fun i j => raw14421 (permutation480 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14421step0 raw14421; decide +kernel
      have hl : raw14421step0Labels = raw14421Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14421 raw14421Labels permutation480 permutation6
    _ = mixedMoment B node3847 node3847Labels := by rfl

def raw14422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14422Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14422step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw14422step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14422 raw14422Labels = mixedMoment B node2984 node2984Labels := by
  calc
    mixedMoment B raw14422 raw14422Labels = mixedMoment B raw14422step0 raw14422step0Labels := by
      have ha : raw14422step0 = (fun i j => raw14422 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14422step0 raw14422; decide +kernel
      have hl : raw14422step0Labels = raw14422Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14422 raw14422Labels permutation152 permutation3
    _ = mixedMoment B node2984 node2984Labels := by rfl

def raw14423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14423Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14423step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw14423step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14423step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw14423step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14423 raw14423Labels = mixedMoment B node3783 node3783Labels := by
  calc
    mixedMoment B raw14423 raw14423Labels = mixedMoment B raw14423step0 raw14423step0Labels := by
      have ha : raw14423step0 = (fun i j => raw14423 (permutation687 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14423step0 raw14423; decide +kernel
      have hl : raw14423step0Labels = raw14423Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14423 raw14423Labels permutation687 permutation3
    mixedMoment B raw14423step0 raw14423step0Labels = mixedMoment B raw14423step1 raw14423step1Labels := by
      have ha : raw14423step1 = -raw14423step0 := by apply Matrix.ext; change ∀ i j, raw14423step1 i j = -(raw14423step0 i j); unfold raw14423step1 raw14423step0; decide +kernel
      have hl : raw14423step1Labels = raw14423step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3783 node3783Labels := by rfl

def raw14424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14424Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14424step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw14424step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14424step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14424step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14424 raw14424Labels = mixedMoment B node3788 node3788Labels := by
  calc
    mixedMoment B raw14424 raw14424Labels = mixedMoment B raw14424step0 raw14424step0Labels := by
      have ha : raw14424step0 = (fun i j => raw14424 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14424step0 raw14424; decide +kernel
      have hl : raw14424step0Labels = raw14424Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14424 raw14424Labels permutation686 permutation3
    mixedMoment B raw14424step0 raw14424step0Labels = mixedMoment B raw14424step1 raw14424step1Labels := by
      have ha : raw14424step1 = -raw14424step0 := by apply Matrix.ext; change ∀ i j, raw14424step1 i j = -(raw14424step0 i j); unfold raw14424step1 raw14424step0; decide +kernel
      have hl : raw14424step1Labels = raw14424step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3788 node3788Labels := by rfl

def raw14425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![0, 0, 0], ![2, -2, 0]]
def raw14425Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14425step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14425step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw14425step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14425step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw14425step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14425 raw14425Labels = mixedMoment B node3883 node3883Labels := by
  calc
    mixedMoment B raw14425 raw14425Labels = mixedMoment B raw14425step0 raw14425step0Labels := by
      have hz : ∀ j, raw14425 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw14425step0 = (fun i j => raw14425 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw14425step0 raw14425; decide +kernel
      have hl : raw14425step0Labels = raw14425Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14425 raw14425Labels permutation520 hz
    mixedMoment B raw14425step0 raw14425step0Labels = mixedMoment B raw14425step1 raw14425step1Labels := by
      have ha : raw14425step1 = (fun i j => raw14425step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14425step1 raw14425step0; decide +kernel
      have hl : raw14425step1Labels = raw14425step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14425step0 raw14425step0Labels permutation151 permutation3
    mixedMoment B raw14425step1 raw14425step1Labels = mixedMoment B raw14425step2 raw14425step2Labels := by
      have ha : raw14425step2 = -raw14425step1 := by apply Matrix.ext; change ∀ i j, raw14425step2 i j = -(raw14425step1 i j); unfold raw14425step2 raw14425step1; decide +kernel
      have hl : raw14425step2Labels = raw14425step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3883 node3883Labels := by rfl

def raw14426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw14426Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14426step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw14426step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14426 raw14426Labels = mixedMoment B node3977 node3977Labels := by
  calc
    mixedMoment B raw14426 raw14426Labels = mixedMoment B raw14426step0 raw14426step0Labels := by
      have ha : raw14426step0 = (fun i j => raw14426 (permutation480 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14426step0 raw14426; decide +kernel
      have hl : raw14426step0Labels = raw14426Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14426 raw14426Labels permutation480 permutation6
    _ = mixedMoment B node3977 node3977Labels := by rfl

def raw14427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw14427Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14427step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw14427step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14427 raw14427Labels = mixedMoment B node2970 node2970Labels := by
  calc
    mixedMoment B raw14427 raw14427Labels = mixedMoment B raw14427step0 raw14427step0Labels := by
      have ha : raw14427step0 = (fun i j => raw14427 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14427step0 raw14427; decide +kernel
      have hl : raw14427step0Labels = raw14427Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14427 raw14427Labels permutation158 permutation3
    _ = mixedMoment B node2970 node2970Labels := by rfl

def raw14428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw14428Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14428step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw14428step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14428step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw14428step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14428 raw14428Labels = mixedMoment B node3648 node3648Labels := by
  calc
    mixedMoment B raw14428 raw14428Labels = mixedMoment B raw14428step0 raw14428step0Labels := by
      have ha : raw14428step0 = (fun i j => raw14428 (permutation583 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14428step0 raw14428; decide +kernel
      have hl : raw14428step0Labels = raw14428Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14428 raw14428Labels permutation583 permutation3
    mixedMoment B raw14428step0 raw14428step0Labels = mixedMoment B raw14428step1 raw14428step1Labels := by
      have ha : raw14428step1 = -raw14428step0 := by apply Matrix.ext; change ∀ i j, raw14428step1 i j = -(raw14428step0 i j); unfold raw14428step1 raw14428step0; decide +kernel
      have hl : raw14428step1Labels = raw14428step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3648 node3648Labels := by rfl

def raw14429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw14429Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14429step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, 0, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw14429step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14429step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14429step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14429 raw14429Labels = mixedMoment B node3658 node3658Labels := by
  calc
    mixedMoment B raw14429 raw14429Labels = mixedMoment B raw14429step0 raw14429step0Labels := by
      have ha : raw14429step0 = (fun i j => raw14429 (permutation587 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14429step0 raw14429; decide +kernel
      have hl : raw14429step0Labels = raw14429Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14429 raw14429Labels permutation587 permutation3
    mixedMoment B raw14429step0 raw14429step0Labels = mixedMoment B raw14429step1 raw14429step1Labels := by
      have ha : raw14429step1 = -raw14429step0 := by apply Matrix.ext; change ∀ i j, raw14429step1 i j = -(raw14429step0 i j); unfold raw14429step1 raw14429step0; decide +kernel
      have hl : raw14429step1Labels = raw14429step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3658 node3658Labels := by rfl

def raw14430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 3, -2], ![2, -2, 0], ![2, -2, 0]]
def raw14430Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14430step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14430step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14430 raw14430Labels = mixedMoment B node3473 node3473Labels := by
  calc
    mixedMoment B raw14430 raw14430Labels = mixedMoment B raw14430step0 raw14430step0Labels := by
      have ha : raw14430step0 = (fun i j => raw14430 (permutation480 i) (permutation6 j)) := by apply Matrix.ext; unfold raw14430step0 raw14430; decide +kernel
      have hl : raw14430step0Labels = raw14430Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14430 raw14430Labels permutation480 permutation6
    _ = mixedMoment B node3473 node3473Labels := by rfl

def raw14431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0]]
def raw14431Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14431step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw14431step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14431step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14431step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14431 raw14431Labels = mixedMoment B node3803 node3803Labels := by
  calc
    mixedMoment B raw14431 raw14431Labels = mixedMoment B raw14431step0 raw14431step0Labels := by
      have ha : raw14431step0 = (fun i j => raw14431 (permutation584 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14431step0 raw14431; decide +kernel
      have hl : raw14431step0Labels = raw14431Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14431 raw14431Labels permutation584 permutation3
    mixedMoment B raw14431step0 raw14431step0Labels = mixedMoment B raw14431step1 raw14431step1Labels := by
      have ha : raw14431step1 = -raw14431step0 := by apply Matrix.ext; change ∀ i j, raw14431step1 i j = -(raw14431step0 i j); unfold raw14431step1 raw14431step0; decide +kernel
      have hl : raw14431step1Labels = raw14431step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3803 node3803Labels := by rfl

def raw14432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw14432Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14432step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-3, 2, 1]]
def raw14432step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14432step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -2, -1]]
def raw14432step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14432 raw14432Labels = mixedMoment B node1902 node1902Labels := by
  calc
    mixedMoment B raw14432 raw14432Labels = mixedMoment B raw14432step0 raw14432step0Labels := by
      have ha : raw14432step0 = (fun i j => raw14432 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14432step0 raw14432; decide +kernel
      have hl : raw14432step0Labels = raw14432Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14432 raw14432Labels permutation682 permutation3
    mixedMoment B raw14432step0 raw14432step0Labels = mixedMoment B raw14432step1 raw14432step1Labels := by
      have ha : raw14432step1 = -raw14432step0 := by apply Matrix.ext; change ∀ i j, raw14432step1 i j = -(raw14432step0 i j); unfold raw14432step1 raw14432step0; decide +kernel
      have hl : raw14432step1Labels = raw14432step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1902 node1902Labels := by rfl

def raw14433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw14433Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14433step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw14433step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14433step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw14433step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14433 raw14433Labels = mixedMoment B node1904 node1904Labels := by
  calc
    mixedMoment B raw14433 raw14433Labels = mixedMoment B raw14433step0 raw14433step0Labels := by
      have ha : raw14433step0 = (fun i j => raw14433 (permutation681 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14433step0 raw14433; decide +kernel
      have hl : raw14433step0Labels = raw14433Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14433 raw14433Labels permutation681 permutation3
    mixedMoment B raw14433step0 raw14433step0Labels = mixedMoment B raw14433step1 raw14433step1Labels := by
      have ha : raw14433step1 = -raw14433step0 := by apply Matrix.ext; change ∀ i j, raw14433step1 i j = -(raw14433step0 i j); unfold raw14433step1 raw14433step0; decide +kernel
      have hl : raw14433step1Labels = raw14433step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1904 node1904Labels := by rfl

def raw14434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw14434Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14434step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw14434step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14434step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14434step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14434 raw14434Labels = mixedMoment B node1923 node1923Labels := by
  calc
    mixedMoment B raw14434 raw14434Labels = mixedMoment B raw14434step0 raw14434step0Labels := by
      have ha : raw14434step0 = (fun i j => raw14434 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14434step0 raw14434; decide +kernel
      have hl : raw14434step0Labels = raw14434Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14434 raw14434Labels permutation686 permutation3
    mixedMoment B raw14434step0 raw14434step0Labels = mixedMoment B raw14434step1 raw14434step1Labels := by
      have ha : raw14434step1 = -raw14434step0 := by apply Matrix.ext; change ∀ i j, raw14434step1 i j = -(raw14434step0 i j); unfold raw14434step1 raw14434step0; decide +kernel
      have hl : raw14434step1Labels = raw14434step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1923 node1923Labels := by rfl

def raw14435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 3, -2], ![1, -1, 0], ![3, -3, 0]]
def raw14435Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14435step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -2, 3], ![-2, 2, 0]]
def raw14435step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14435step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw14435step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14435 raw14435Labels = mixedMoment B node1910 node1910Labels := by
  calc
    mixedMoment B raw14435 raw14435Labels = mixedMoment B raw14435step0 raw14435step0Labels := by
      have ha : raw14435step0 = (fun i j => raw14435 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14435step0 raw14435; decide +kernel
      have hl : raw14435step0Labels = raw14435Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14435 raw14435Labels permutation680 permutation3
    mixedMoment B raw14435step0 raw14435step0Labels = mixedMoment B raw14435step1 raw14435step1Labels := by
      have ha : raw14435step1 = -raw14435step0 := by apply Matrix.ext; change ∀ i j, raw14435step1 i j = -(raw14435step0 i j); unfold raw14435step1 raw14435step0; decide +kernel
      have hl : raw14435step1Labels = raw14435step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1910 node1910Labels := by rfl

def raw14436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![0, 0, 0], ![3, -3, 0]]
def raw14436Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14436step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![3, -3, 0]]
def raw14436step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw14436step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -2, 2], ![-1, 1, 0], ![-2, 2, 0]]
def raw14436step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14436step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14436step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14436 raw14436Labels = mixedMoment B node2253 node2253Labels := by
  calc
    mixedMoment B raw14436 raw14436Labels = mixedMoment B raw14436step0 raw14436step0Labels := by
      have hz : ∀ j, raw14436 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw14436step0 = (fun i j => raw14436 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw14436step0 raw14436; decide +kernel
      have hl : raw14436step0Labels = raw14436Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14436 raw14436Labels permutation520 hz
    mixedMoment B raw14436step0 raw14436step0Labels = mixedMoment B raw14436step1 raw14436step1Labels := by
      have ha : raw14436step1 = (fun i j => raw14436step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14436step1 raw14436step0; decide +kernel
      have hl : raw14436step1Labels = raw14436step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14436step0 raw14436step0Labels permutation145 permutation3
    mixedMoment B raw14436step1 raw14436step1Labels = mixedMoment B raw14436step2 raw14436step2Labels := by
      have ha : raw14436step2 = -raw14436step1 := by apply Matrix.ext; change ∀ i j, raw14436step2 i j = -(raw14436step1 i j); unfold raw14436step2 raw14436step1; decide +kernel
      have hl : raw14436step2Labels = raw14436step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2253 node2253Labels := by rfl

def raw14437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14437Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14437 raw14437Labels = mixedMoment B node3803 node3803Labels := by
  calc
    _ = mixedMoment B node3803 node3803Labels := by rfl

def raw14438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14438Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14438step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw14438step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14438step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14438step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14438 raw14438Labels = mixedMoment B node3788 node3788Labels := by
  calc
    mixedMoment B raw14438 raw14438Labels = mixedMoment B raw14438step0 raw14438step0Labels := by
      have ha : raw14438step0 = (fun i j => raw14438 (permutation472 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14438step0 raw14438; decide +kernel
      have hl : raw14438step0Labels = raw14438Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14438 raw14438Labels permutation472 permutation4
    mixedMoment B raw14438step0 raw14438step0Labels = mixedMoment B raw14438step1 raw14438step1Labels := by
      have ha : raw14438step1 = -raw14438step0 := by apply Matrix.ext; change ∀ i j, raw14438step1 i j = -(raw14438step0 i j); unfold raw14438step1 raw14438step0; decide +kernel
      have hl : raw14438step1Labels = raw14438step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3788 node3788Labels := by rfl

def raw14439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14439Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14439step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw14439step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14439step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14439step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14439 raw14439Labels = mixedMoment B node3691 node3691Labels := by
  calc
    mixedMoment B raw14439 raw14439Labels = mixedMoment B raw14439step0 raw14439step0Labels := by
      have ha : raw14439step0 = (fun i j => raw14439 (permutation472 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14439step0 raw14439; decide +kernel
      have hl : raw14439step0Labels = raw14439Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14439 raw14439Labels permutation472 permutation4
    mixedMoment B raw14439step0 raw14439step0Labels = mixedMoment B raw14439step1 raw14439step1Labels := by
      have ha : raw14439step1 = -raw14439step0 := by apply Matrix.ext; change ∀ i j, raw14439step1 i j = -(raw14439step0 i j); unfold raw14439step1 raw14439step0; decide +kernel
      have hl : raw14439step1Labels = raw14439step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3691 node3691Labels := by rfl

def raw14440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14440Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14440step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw14440step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14440step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14440step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14440 raw14440Labels = mixedMoment B node2481 node2481Labels := by
  calc
    mixedMoment B raw14440 raw14440Labels = mixedMoment B raw14440step0 raw14440step0Labels := by
      have ha : raw14440step0 = (fun i j => raw14440 (permutation472 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14440step0 raw14440; decide +kernel
      have hl : raw14440step0Labels = raw14440Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14440 raw14440Labels permutation472 permutation4
    mixedMoment B raw14440step0 raw14440step0Labels = mixedMoment B raw14440step1 raw14440step1Labels := by
      have ha : raw14440step1 = -raw14440step0 := by apply Matrix.ext; change ∀ i j, raw14440step1 i j = -(raw14440step0 i j); unfold raw14440step1 raw14440step0; decide +kernel
      have hl : raw14440step1Labels = raw14440step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2481 node2481Labels := by rfl

def raw14441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]
def raw14441Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14441step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14441step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw14441step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14441step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14441step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14441 raw14441Labels = mixedMoment B node3809 node3809Labels := by
  calc
    mixedMoment B raw14441 raw14441Labels = mixedMoment B raw14441step0 raw14441step0Labels := by
      have hz : ∀ j, raw14441 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw14441step0 = (fun i j => raw14441 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw14441step0 raw14441; decide +kernel
      have hl : raw14441step0Labels = raw14441Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14441 raw14441Labels permutation520 hz
    mixedMoment B raw14441step0 raw14441step0Labels = mixedMoment B raw14441step1 raw14441step1Labels := by
      have ha : raw14441step1 = (fun i j => raw14441step0 (permutation118 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14441step1 raw14441step0; decide +kernel
      have hl : raw14441step1Labels = raw14441step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14441step0 raw14441step0Labels permutation118 permutation4
    mixedMoment B raw14441step1 raw14441step1Labels = mixedMoment B raw14441step2 raw14441step2Labels := by
      have ha : raw14441step2 = -raw14441step1 := by apply Matrix.ext; change ∀ i j, raw14441step2 i j = -(raw14441step1 i j); unfold raw14441step2 raw14441step1; decide +kernel
      have hl : raw14441step2Labels = raw14441step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3809 node3809Labels := by rfl

def raw14442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw14442Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14442step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw14442step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14442step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw14442step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14442 raw14442Labels = mixedMoment B node3805 node3805Labels := by
  calc
    mixedMoment B raw14442 raw14442Labels = mixedMoment B raw14442step0 raw14442step0Labels := by
      have ha : raw14442step0 = (fun i j => raw14442 (permutation473 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14442step0 raw14442; decide +kernel
      have hl : raw14442step0Labels = raw14442Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14442 raw14442Labels permutation473 permutation4
    mixedMoment B raw14442step0 raw14442step0Labels = mixedMoment B raw14442step1 raw14442step1Labels := by
      have ha : raw14442step1 = -raw14442step0 := by apply Matrix.ext; change ∀ i j, raw14442step1 i j = -(raw14442step0 i j); unfold raw14442step1 raw14442step0; decide +kernel
      have hl : raw14442step1Labels = raw14442step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3805 node3805Labels := by rfl

def raw14443 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2], ![0, 0], ![0, 0]]
def raw14443Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14443step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2], ![0, 0]]
def raw14443step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw14443step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw14443step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical14443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14443 raw14443Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw14443 raw14443Labels = mixedMoment B raw14443step0 raw14443step0Labels := by
      have hz : ∀ j, raw14443 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw14443step0 = (fun i j => raw14443 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw14443step0 raw14443; decide +kernel
      have hl : raw14443step0Labels = raw14443Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14443 raw14443Labels permutation590 hz
    mixedMoment B raw14443step0 raw14443step0Labels = mixedMoment B raw14443step1 raw14443step1Labels := by
      have hz : ∀ j, raw14443step0 (permutation128 0) j = 0 := by decide +kernel
      have ha : raw14443step1 = (fun i j => raw14443step0 (permutation128 i.succ) j) := by apply Matrix.ext; unfold raw14443step1 raw14443step0; decide +kernel
      have hl : raw14443step1Labels = raw14443step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14443step0 raw14443step0Labels permutation128 hz
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw14444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14444Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14444 raw14444Labels = mixedMoment B node2714 node2714Labels := by
  calc
    _ = mixedMoment B node2714 node2714Labels := by rfl

def raw14445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14445Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14445step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14445step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14445 raw14445Labels = mixedMoment B node2494 node2494Labels := by
  calc
    mixedMoment B raw14445 raw14445Labels = mixedMoment B raw14445step0 raw14445step0Labels := by
      have ha : raw14445step0 = (fun i j => raw14445 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14445step0 raw14445; decide +kernel
      have hl : raw14445step0Labels = raw14445Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14445 raw14445Labels permutation160 permutation2
    _ = mixedMoment B node2494 node2494Labels := by rfl

def raw14446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14446Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14446step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14446step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14446 raw14446Labels = mixedMoment B node2481 node2481Labels := by
  calc
    mixedMoment B raw14446 raw14446Labels = mixedMoment B raw14446step0 raw14446step0Labels := by
      have ha : raw14446step0 = (fun i j => raw14446 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14446step0 raw14446; decide +kernel
      have hl : raw14446step0Labels = raw14446Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14446 raw14446Labels permutation154 permutation2
    _ = mixedMoment B node2481 node2481Labels := by rfl

def raw14447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw14447Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14447 raw14447Labels = mixedMoment B node2475 node2475Labels := by
  calc
    _ = mixedMoment B node2475 node2475Labels := by rfl

def raw14448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw14448Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14448 raw14448Labels = mixedMoment B node2474 node2474Labels := by
  calc
    _ = mixedMoment B node2474 node2474Labels := by rfl

def raw14449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14449Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14449step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw14449step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14449step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14449step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14449 raw14449Labels = mixedMoment B node3698 node3698Labels := by
  calc
    mixedMoment B raw14449 raw14449Labels = mixedMoment B raw14449step0 raw14449step0Labels := by
      have ha : raw14449step0 = (fun i j => raw14449 (permutation467 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14449step0 raw14449; decide +kernel
      have hl : raw14449step0Labels = raw14449Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14449 raw14449Labels permutation467 permutation4
    mixedMoment B raw14449step0 raw14449step0Labels = mixedMoment B raw14449step1 raw14449step1Labels := by
      have ha : raw14449step1 = -raw14449step0 := by apply Matrix.ext; change ∀ i j, raw14449step1 i j = -(raw14449step0 i j); unfold raw14449step1 raw14449step0; decide +kernel
      have hl : raw14449step1Labels = raw14449step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3698 node3698Labels := by rfl

def raw14450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14450Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14450step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-2, 2, 0]]
def raw14450step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14450step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14450step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14450 raw14450Labels = mixedMoment B node2494 node2494Labels := by
  calc
    mixedMoment B raw14450 raw14450Labels = mixedMoment B raw14450step0 raw14450step0Labels := by
      have ha : raw14450step0 = (fun i j => raw14450 (permutation467 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14450step0 raw14450; decide +kernel
      have hl : raw14450step0Labels = raw14450Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14450 raw14450Labels permutation467 permutation4
    mixedMoment B raw14450step0 raw14450step0Labels = mixedMoment B raw14450step1 raw14450step1Labels := by
      have ha : raw14450step1 = -raw14450step0 := by apply Matrix.ext; change ∀ i j, raw14450step1 i j = -(raw14450step0 i j); unfold raw14450step1 raw14450step0; decide +kernel
      have hl : raw14450step1Labels = raw14450step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2494 node2494Labels := by rfl

def raw14451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0]]
def raw14451Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14451step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14451step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14451step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw14451step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14451step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw14451step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14451 raw14451Labels = mixedMoment B node3814 node3814Labels := by
  calc
    mixedMoment B raw14451 raw14451Labels = mixedMoment B raw14451step0 raw14451step0Labels := by
      have hz : ∀ j, raw14451 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw14451step0 = (fun i j => raw14451 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw14451step0 raw14451; decide +kernel
      have hl : raw14451step0Labels = raw14451Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw14451 raw14451Labels permutation520 hz
    mixedMoment B raw14451step0 raw14451step0Labels = mixedMoment B raw14451step1 raw14451step1Labels := by
      have ha : raw14451step1 = (fun i j => raw14451step0 (permutation116 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14451step1 raw14451step0; decide +kernel
      have hl : raw14451step1Labels = raw14451step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14451step0 raw14451step0Labels permutation116 permutation4
    mixedMoment B raw14451step1 raw14451step1Labels = mixedMoment B raw14451step2 raw14451step2Labels := by
      have ha : raw14451step2 = -raw14451step1 := by apply Matrix.ext; change ∀ i j, raw14451step2 i j = -(raw14451step1 i j); unfold raw14451step2 raw14451step1; decide +kernel
      have hl : raw14451step2Labels = raw14451step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3814 node3814Labels := by rfl

def raw14452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw14452Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14452step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw14452step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14452step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw14452step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14452 raw14452Labels = mixedMoment B node3812 node3812Labels := by
  calc
    mixedMoment B raw14452 raw14452Labels = mixedMoment B raw14452step0 raw14452step0Labels := by
      have ha : raw14452step0 = (fun i j => raw14452 (permutation468 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14452step0 raw14452; decide +kernel
      have hl : raw14452step0Labels = raw14452Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14452 raw14452Labels permutation468 permutation4
    mixedMoment B raw14452step0 raw14452step0Labels = mixedMoment B raw14452step1 raw14452step1Labels := by
      have ha : raw14452step1 = -raw14452step0 := by apply Matrix.ext; change ∀ i j, raw14452step1 i j = -(raw14452step0 i j); unfold raw14452step1 raw14452step0; decide +kernel
      have hl : raw14452step1Labels = raw14452step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3812 node3812Labels := by rfl

def raw14453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14453Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14453step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw14453step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14453 raw14453Labels = mixedMoment B node3698 node3698Labels := by
  calc
    mixedMoment B raw14453 raw14453Labels = mixedMoment B raw14453step0 raw14453step0Labels := by
      have ha : raw14453step0 = (fun i j => raw14453 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14453step0 raw14453; decide +kernel
      have hl : raw14453step0Labels = raw14453Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14453 raw14453Labels permutation160 permutation2
    _ = mixedMoment B node3698 node3698Labels := by rfl

def raw14454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 1, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14454Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14454step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw14454step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14454 raw14454Labels = mixedMoment B node3691 node3691Labels := by
  calc
    mixedMoment B raw14454 raw14454Labels = mixedMoment B raw14454step0 raw14454step0Labels := by
      have ha : raw14454step0 = (fun i j => raw14454 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14454step0 raw14454; decide +kernel
      have hl : raw14454step0Labels = raw14454Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14454 raw14454Labels permutation154 permutation2
    _ = mixedMoment B node3691 node3691Labels := by rfl

def raw14455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw14455Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14455 raw14455Labels = mixedMoment B node3686 node3686Labels := by
  calc
    _ = mixedMoment B node3686 node3686Labels := by rfl

def raw14456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![3, -3, 0]]
def raw14456Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14456step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -3, 0], ![1, -1, 0], ![0, 2, -2], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw14456step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14456step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, -2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw14456step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14456 raw14456Labels = mixedMoment B node3217 node3217Labels := by
  calc
    mixedMoment B raw14456 raw14456Labels = mixedMoment B raw14456step0 raw14456step0Labels := by
      have ha : raw14456step0 = (fun i j => raw14456 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14456step0 raw14456; decide +kernel
      have hl : raw14456step0Labels = raw14456Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14456 raw14456Labels permutation688 permutation2
    mixedMoment B raw14456step0 raw14456step0Labels = mixedMoment B raw14456step1 raw14456step1Labels := by
      have ha : raw14456step1 = -raw14456step0 := by apply Matrix.ext; change ∀ i j, raw14456step1 i j = -(raw14456step0 i j); unfold raw14456step1 raw14456step0; decide +kernel
      have hl : raw14456step1Labels = raw14456step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3217 node3217Labels := by rfl

def raw14457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw14457Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14457step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0], ![-2, 2, 0]]
def raw14457step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14457step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw14457step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14457 raw14457Labels = mixedMoment B node3686 node3686Labels := by
  calc
    mixedMoment B raw14457 raw14457Labels = mixedMoment B raw14457step0 raw14457step0Labels := by
      have ha : raw14457step0 = (fun i j => raw14457 (permutation470 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14457step0 raw14457; decide +kernel
      have hl : raw14457step0Labels = raw14457Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14457 raw14457Labels permutation470 permutation4
    mixedMoment B raw14457step0 raw14457step0Labels = mixedMoment B raw14457step1 raw14457step1Labels := by
      have ha : raw14457step1 = -raw14457step0 := by apply Matrix.ext; change ∀ i j, raw14457step1 i j = -(raw14457step0 i j); unfold raw14457step1 raw14457step0; decide +kernel
      have hl : raw14457step1Labels = raw14457step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3686 node3686Labels := by rfl

def raw14458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![-1, 3, -2], ![2, -2, 0], ![2, -2, 0]]
def raw14458Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14458step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-2, 2, 0], ![-2, 2, 0]]
def raw14458step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14458step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![2, -2, 0]]
def raw14458step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14458 raw14458Labels = mixedMoment B node2475 node2475Labels := by
  calc
    mixedMoment B raw14458 raw14458Labels = mixedMoment B raw14458step0 raw14458step0Labels := by
      have ha : raw14458step0 = (fun i j => raw14458 (permutation470 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14458step0 raw14458; decide +kernel
      have hl : raw14458step0Labels = raw14458Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14458 raw14458Labels permutation470 permutation4
    mixedMoment B raw14458step0 raw14458step0Labels = mixedMoment B raw14458step1 raw14458step1Labels := by
      have ha : raw14458step1 = -raw14458step0 := by apply Matrix.ext; change ∀ i j, raw14458step1 i j = -(raw14458step0 i j); unfold raw14458step1 raw14458step0; decide +kernel
      have hl : raw14458step1Labels = raw14458step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2475 node2475Labels := by rfl

def raw14459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0]]
def raw14459Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw14459step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw14459step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical14459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14459 raw14459Labels = mixedMoment B node3803 node3803Labels := by
  calc
    mixedMoment B raw14459 raw14459Labels = mixedMoment B raw14459step0 raw14459step0Labels := by
      have ha : raw14459step0 = (fun i j => raw14459 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw14459step0 raw14459; decide +kernel
      have hl : raw14459step0Labels = raw14459Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14459 raw14459Labels permutation153 permutation2
    _ = mixedMoment B node3803 node3803Labels := by rfl

def raw14460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14460Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14460step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw14460step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14460step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw14460step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14460 raw14460Labels = mixedMoment B node5420 node5420Labels := by
  calc
    mixedMoment B raw14460 raw14460Labels = mixedMoment B raw14460step0 raw14460step0Labels := by
      have ha : raw14460step0 = (fun i j => raw14460 (permutation628 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14460step0 raw14460; decide +kernel
      have hl : raw14460step0Labels = raw14460Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14460 raw14460Labels permutation628 permutation5
    mixedMoment B raw14460step0 raw14460step0Labels = mixedMoment B raw14460step1 raw14460step1Labels := by
      have ha : raw14460step1 = raw14460step0 := by apply Matrix.ext; unfold raw14460step1 raw14460step0; decide +kernel
      have hl : raw14460step0Labels = labelEmbedding8 ∘ raw14460step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14460step0 raw14460step0Labels raw14460step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5420 node5420Labels := by rfl

def raw14461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14461Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14461step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw14461step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14461step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14461step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw14461step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw14461step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14461 raw14461Labels = mixedMoment B node5445 node5445Labels := by
  calc
    mixedMoment B raw14461 raw14461Labels = mixedMoment B raw14461step0 raw14461step0Labels := by
      have ha : raw14461step0 = (fun i j => raw14461 (permutation684 i) (permutation3 j)) := by apply Matrix.ext; unfold raw14461step0 raw14461; decide +kernel
      have hl : raw14461step0Labels = raw14461Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14461 raw14461Labels permutation684 permutation3
    mixedMoment B raw14461step0 raw14461step0Labels = mixedMoment B raw14461step1 raw14461step1Labels := by
      have ha : raw14461step1 = -raw14461step0 := by apply Matrix.ext; change ∀ i j, raw14461step1 i j = -(raw14461step0 i j); unfold raw14461step1 raw14461step0; decide +kernel
      have hl : raw14461step1Labels = raw14461step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14461step1 raw14461step1Labels = mixedMoment B raw14461step2 raw14461step2Labels := by
      have ha : raw14461step2 = raw14461step1 := by apply Matrix.ext; unfold raw14461step2 raw14461step1; decide +kernel
      have hl : raw14461step1Labels = labelEmbedding6 ∘ raw14461step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14461step1 raw14461step1Labels raw14461step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5445 node5445Labels := by rfl

def raw14462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14462Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14462step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw14462step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw14462step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw14462step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14462 raw14462Labels = mixedMoment B node5421 node5421Labels := by
  calc
    mixedMoment B raw14462 raw14462Labels = mixedMoment B raw14462step0 raw14462step0Labels := by
      have ha : raw14462step0 = (fun i j => raw14462 (permutation627 i) (permutation5 j)) := by apply Matrix.ext; unfold raw14462step0 raw14462; decide +kernel
      have hl : raw14462step0Labels = raw14462Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14462 raw14462Labels permutation627 permutation5
    mixedMoment B raw14462step0 raw14462step0Labels = mixedMoment B raw14462step1 raw14462step1Labels := by
      have ha : raw14462step1 = raw14462step0 := by apply Matrix.ext; unfold raw14462step1 raw14462step0; decide +kernel
      have hl : raw14462step0Labels = labelEmbedding8 ∘ raw14462step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14462step0 raw14462step0Labels raw14462step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5421 node5421Labels := by rfl

def raw14463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -2, 0]]
def raw14463Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw14463step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw14463step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14463step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14463step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw14463step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw14463step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical14463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw14463 raw14463Labels = mixedMoment B node5397 node5397Labels := by
  calc
    mixedMoment B raw14463 raw14463Labels = mixedMoment B raw14463step0 raw14463step0Labels := by
      have ha : raw14463step0 = (fun i j => raw14463 (permutation556 i) (permutation4 j)) := by apply Matrix.ext; unfold raw14463step0 raw14463; decide +kernel
      have hl : raw14463step0Labels = raw14463Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw14463 raw14463Labels permutation556 permutation4
    mixedMoment B raw14463step0 raw14463step0Labels = mixedMoment B raw14463step1 raw14463step1Labels := by
      have ha : raw14463step1 = -raw14463step0 := by apply Matrix.ext; change ∀ i j, raw14463step1 i j = -(raw14463step0 i j); unfold raw14463step1 raw14463step0; decide +kernel
      have hl : raw14463step1Labels = raw14463step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw14463step1 raw14463step1Labels = mixedMoment B raw14463step2 raw14463step2Labels := by
      have ha : raw14463step2 = raw14463step1 := by apply Matrix.ext; unfold raw14463step2 raw14463step1; decide +kernel
      have hl : raw14463step1Labels = labelEmbedding7 ∘ raw14463step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw14463step1 raw14463step1Labels raw14463step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5397 node5397Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
