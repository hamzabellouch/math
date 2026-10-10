import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw3328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3328Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3328step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3328step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3328step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw3328step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical3328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3328 raw3328Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw3328 raw3328Labels = mixedMoment B raw3328step0 raw3328step0Labels := by
      have hz : ∀ j, raw3328 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3328step0 = (fun i j => raw3328 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3328step0 raw3328; decide +kernel
      have hl : raw3328step0Labels = raw3328Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3328 raw3328Labels permutation434 hz
    mixedMoment B raw3328step0 raw3328step0Labels = mixedMoment B raw3328step1 raw3328step1Labels := by
      have hz : ∀ i, raw3328step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3328step1 = (fun i j => raw3328step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3328step1 raw3328step0; decide +kernel
      have hl : raw3328step1Labels = (fun j => raw3328step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3328step0 raw3328step0Labels permutation6 hz
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw3329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3329Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3329step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3329step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![1, -1], ![1, -1]]
def raw3329step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3329step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw3329step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical3329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3329 raw3329Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw3329 raw3329Labels = mixedMoment B raw3329step0 raw3329step0Labels := by
      have hz : ∀ j, raw3329 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3329step0 = (fun i j => raw3329 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3329step0 raw3329; decide +kernel
      have hl : raw3329step0Labels = raw3329Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3329 raw3329Labels permutation265 hz
    mixedMoment B raw3329step0 raw3329step0Labels = mixedMoment B raw3329step1 raw3329step1Labels := by
      have hz : ∀ i, raw3329step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3329step1 = (fun i j => raw3329step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3329step1 raw3329step0; decide +kernel
      have hl : raw3329step1Labels = (fun j => raw3329step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3329step0 raw3329step0Labels permutation6 hz
    mixedMoment B raw3329step1 raw3329step1Labels = mixedMoment B raw3329step2 raw3329step2Labels := by
      have ha : raw3329step2 = (fun i j => raw3329step1 (permutation38 i) (permutation0 j)) := by apply Matrix.ext; unfold raw3329step2 raw3329step1; decide +kernel
      have hl : raw3329step2Labels = raw3329step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3329step1 raw3329step1Labels permutation38 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw3330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0]]
def raw3330Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw3330step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3330step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3330step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3330step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3330step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3330step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw3330step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical3330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3330 raw3330Labels = mixedMoment B node4093 node4093Labels := by
  calc
    mixedMoment B raw3330 raw3330Labels = mixedMoment B raw3330step0 raw3330step0Labels := by
      have hz : ∀ j, raw3330 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw3330step0 = (fun i j => raw3330 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw3330step0 raw3330; decide +kernel
      have hl : raw3330step0Labels = raw3330Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3330 raw3330Labels permutation590 hz
    mixedMoment B raw3330step0 raw3330step0Labels = mixedMoment B raw3330step1 raw3330step1Labels := by
      have hz : ∀ j, raw3330step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw3330step1 = (fun i j => raw3330step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw3330step1 raw3330step0; decide +kernel
      have hl : raw3330step1Labels = raw3330step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3330step0 raw3330step0Labels permutation104 hz
    mixedMoment B raw3330step1 raw3330step1Labels = mixedMoment B raw3330step2 raw3330step2Labels := by
      have hz : ∀ j, raw3330step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3330step2 = (fun i j => raw3330step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3330step2 raw3330step1; decide +kernel
      have hl : raw3330step2Labels = raw3330step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3330step1 raw3330step1Labels permutation14 hz
    mixedMoment B raw3330step2 raw3330step2Labels = mixedMoment B raw3330step3 raw3330step3Labels := by
      have hz : ∀ i, raw3330step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3330step3 = (fun i j => raw3330step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3330step3 raw3330step2; decide +kernel
      have hl : raw3330step3Labels = (fun j => raw3330step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3330step2 raw3330step2Labels permutation6 hz
    _ = mixedMoment B node4093 node4093Labels := by rfl

def raw3331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3331Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3331step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3331step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3331step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3331step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw3331step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical3331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3331 raw3331Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw3331 raw3331Labels = mixedMoment B raw3331step0 raw3331step0Labels := by
      have hz : ∀ j, raw3331 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3331step0 = (fun i j => raw3331 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3331step0 raw3331; decide +kernel
      have hl : raw3331step0Labels = raw3331Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3331 raw3331Labels permutation346 hz
    mixedMoment B raw3331step0 raw3331step0Labels = mixedMoment B raw3331step1 raw3331step1Labels := by
      have hz : ∀ j, raw3331step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3331step1 = (fun i j => raw3331step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3331step1 raw3331step0; decide +kernel
      have hl : raw3331step1Labels = raw3331step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3331step0 raw3331step0Labels permutation56 hz
    mixedMoment B raw3331step1 raw3331step1Labels = mixedMoment B raw3331step2 raw3331step2Labels := by
      have hz : ∀ i, raw3331step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3331step2 = (fun i j => raw3331step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3331step2 raw3331step1; decide +kernel
      have hl : raw3331step2Labels = (fun j => raw3331step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3331step1 raw3331step1Labels permutation6 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

def raw3332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3332Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3332step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3332step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3332step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw3332step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical3332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3332 raw3332Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw3332 raw3332Labels = mixedMoment B raw3332step0 raw3332step0Labels := by
      have hz : ∀ j, raw3332 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3332step0 = (fun i j => raw3332 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3332step0 raw3332; decide +kernel
      have hl : raw3332step0Labels = raw3332Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3332 raw3332Labels permutation346 hz
    mixedMoment B raw3332step0 raw3332step0Labels = mixedMoment B raw3332step1 raw3332step1Labels := by
      have hz : ∀ i, raw3332step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3332step1 = (fun i j => raw3332step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3332step1 raw3332step0; decide +kernel
      have hl : raw3332step1Labels = (fun j => raw3332step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3332step0 raw3332step0Labels permutation6 hz
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw3333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3333Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3333step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3333step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3333step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw3333step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical3333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3333 raw3333Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw3333 raw3333Labels = mixedMoment B raw3333step0 raw3333step0Labels := by
      have hz : ∀ j, raw3333 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3333step0 = (fun i j => raw3333 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3333step0 raw3333; decide +kernel
      have hl : raw3333step0Labels = raw3333Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3333 raw3333Labels permutation265 hz
    mixedMoment B raw3333step0 raw3333step0Labels = mixedMoment B raw3333step1 raw3333step1Labels := by
      have hz : ∀ i, raw3333step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3333step1 = (fun i j => raw3333step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3333step1 raw3333step0; decide +kernel
      have hl : raw3333step1Labels = (fun j => raw3333step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3333step0 raw3333step0Labels permutation6 hz
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw3334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw3334Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3334step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3334step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3334step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3334step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3334step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3334step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3334step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw3334step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical3334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3334 raw3334Labels = mixedMoment B node4093 node4093Labels := by
  calc
    mixedMoment B raw3334 raw3334Labels = mixedMoment B raw3334step0 raw3334step0Labels := by
      have hz : ∀ j, raw3334 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw3334step0 = (fun i j => raw3334 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw3334step0 raw3334; decide +kernel
      have hl : raw3334step0Labels = raw3334Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3334 raw3334Labels permutation590 hz
    mixedMoment B raw3334step0 raw3334step0Labels = mixedMoment B raw3334step1 raw3334step1Labels := by
      have hz : ∀ j, raw3334step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3334step1 = (fun i j => raw3334step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3334step1 raw3334step0; decide +kernel
      have hl : raw3334step1Labels = raw3334step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3334step0 raw3334step0Labels permutation80 hz
    mixedMoment B raw3334step1 raw3334step1Labels = mixedMoment B raw3334step2 raw3334step2Labels := by
      have hz : ∀ j, raw3334step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3334step2 = (fun i j => raw3334step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3334step2 raw3334step1; decide +kernel
      have hl : raw3334step2Labels = raw3334step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3334step1 raw3334step1Labels permutation14 hz
    mixedMoment B raw3334step2 raw3334step2Labels = mixedMoment B raw3334step3 raw3334step3Labels := by
      have hz : ∀ i, raw3334step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3334step3 = (fun i j => raw3334step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3334step3 raw3334step2; decide +kernel
      have hl : raw3334step3Labels = (fun j => raw3334step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3334step2 raw3334step2Labels permutation6 hz
    _ = mixedMoment B node4093 node4093Labels := by rfl

def raw3335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw3335Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw3335step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3335step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw3335step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3335step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![2, -2, 0], ![1, -1, 0]]
def raw3335step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3335step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![2, -2], ![1, -1]]
def raw3335step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3335step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![2, -2]]
def raw3335step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical3335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3335 raw3335Labels = mixedMoment B node4084 node4084Labels := by
  calc
    mixedMoment B raw3335 raw3335Labels = mixedMoment B raw3335step0 raw3335step0Labels := by
      have hz : ∀ j, raw3335 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3335step0 = (fun i j => raw3335 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3335step0 raw3335; decide +kernel
      have hl : raw3335step0Labels = raw3335Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3335 raw3335Labels permutation434 hz
    mixedMoment B raw3335step0 raw3335step0Labels = mixedMoment B raw3335step1 raw3335step1Labels := by
      have hz : ∀ j, raw3335step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3335step1 = (fun i j => raw3335step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3335step1 raw3335step0; decide +kernel
      have hl : raw3335step1Labels = raw3335step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3335step0 raw3335step0Labels permutation80 hz
    mixedMoment B raw3335step1 raw3335step1Labels = mixedMoment B raw3335step2 raw3335step2Labels := by
      have hz : ∀ j, raw3335step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3335step2 = (fun i j => raw3335step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3335step2 raw3335step1; decide +kernel
      have hl : raw3335step2Labels = raw3335step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3335step1 raw3335step1Labels permutation14 hz
    mixedMoment B raw3335step2 raw3335step2Labels = mixedMoment B raw3335step3 raw3335step3Labels := by
      have hz : ∀ i, raw3335step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3335step3 = (fun i j => raw3335step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3335step3 raw3335step2; decide +kernel
      have hl : raw3335step3Labels = (fun j => raw3335step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3335step2 raw3335step2Labels permutation6 hz
    mixedMoment B raw3335step3 raw3335step3Labels = mixedMoment B raw3335step4 raw3335step4Labels := by
      have ha : raw3335step4 = (fun i j => raw3335step3 (permutation3 i) (permutation0 j)) := by apply Matrix.ext; unfold raw3335step4 raw3335step3; decide +kernel
      have hl : raw3335step4Labels = raw3335step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3335step3 raw3335step3Labels permutation3 permutation0
    _ = mixedMoment B node4084 node4084Labels := by rfl

def raw3336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw3336Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3336step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw3336step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3336step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw3336step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3336step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]
def raw3336step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3336step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw3336step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical3336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3336 raw3336Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw3336 raw3336Labels = mixedMoment B raw3336step0 raw3336step0Labels := by
      have hz : ∀ j, raw3336 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3336step0 = (fun i j => raw3336 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3336step0 raw3336; decide +kernel
      have hl : raw3336step0Labels = raw3336Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3336 raw3336Labels permutation434 hz
    mixedMoment B raw3336step0 raw3336step0Labels = mixedMoment B raw3336step1 raw3336step1Labels := by
      have hz : ∀ j, raw3336step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3336step1 = (fun i j => raw3336step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3336step1 raw3336step0; decide +kernel
      have hl : raw3336step1Labels = raw3336step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3336step0 raw3336step0Labels permutation80 hz
    mixedMoment B raw3336step1 raw3336step1Labels = mixedMoment B raw3336step2 raw3336step2Labels := by
      have hz : ∀ i, raw3336step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3336step2 = (fun i j => raw3336step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3336step2 raw3336step1; decide +kernel
      have hl : raw3336step2Labels = (fun j => raw3336step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3336step1 raw3336step1Labels permutation6 hz
    mixedMoment B raw3336step2 raw3336step2Labels = mixedMoment B raw3336step3 raw3336step3Labels := by
      have ha : raw3336step3 = (fun i j => raw3336step2 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw3336step3 raw3336step2; decide +kernel
      have hl : raw3336step3Labels = raw3336step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3336step2 raw3336step2Labels permutation9 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw3337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw3337Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw3337step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3337step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw3337step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3337step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]
def raw3337step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3337step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw3337step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical3337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3337 raw3337Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw3337 raw3337Labels = mixedMoment B raw3337step0 raw3337step0Labels := by
      have hz : ∀ j, raw3337 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3337step0 = (fun i j => raw3337 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3337step0 raw3337; decide +kernel
      have hl : raw3337step0Labels = raw3337Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3337 raw3337Labels permutation434 hz
    mixedMoment B raw3337step0 raw3337step0Labels = mixedMoment B raw3337step1 raw3337step1Labels := by
      have hz : ∀ j, raw3337step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3337step1 = (fun i j => raw3337step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3337step1 raw3337step0; decide +kernel
      have hl : raw3337step1Labels = raw3337step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3337step0 raw3337step0Labels permutation56 hz
    mixedMoment B raw3337step1 raw3337step1Labels = mixedMoment B raw3337step2 raw3337step2Labels := by
      have hz : ∀ i, raw3337step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3337step2 = (fun i j => raw3337step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3337step2 raw3337step1; decide +kernel
      have hl : raw3337step2Labels = (fun j => raw3337step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3337step1 raw3337step1Labels permutation6 hz
    mixedMoment B raw3337step2 raw3337step2Labels = mixedMoment B raw3337step3 raw3337step3Labels := by
      have ha : raw3337step3 = (fun i j => raw3337step2 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw3337step3 raw3337step2; decide +kernel
      have hl : raw3337step3Labels = raw3337step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3337step2 raw3337step2Labels permutation9 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw3338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw3338Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3338step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw3338step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3338step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw3338step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3338step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![2, -2], ![1, -1]]
def raw3338step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3338step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw3338step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical3338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3338 raw3338Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw3338 raw3338Labels = mixedMoment B raw3338step0 raw3338step0Labels := by
      have hz : ∀ j, raw3338 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3338step0 = (fun i j => raw3338 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3338step0 raw3338; decide +kernel
      have hl : raw3338step0Labels = raw3338Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3338 raw3338Labels permutation346 hz
    mixedMoment B raw3338step0 raw3338step0Labels = mixedMoment B raw3338step1 raw3338step1Labels := by
      have hz : ∀ j, raw3338step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3338step1 = (fun i j => raw3338step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3338step1 raw3338step0; decide +kernel
      have hl : raw3338step1Labels = raw3338step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3338step0 raw3338step0Labels permutation56 hz
    mixedMoment B raw3338step1 raw3338step1Labels = mixedMoment B raw3338step2 raw3338step2Labels := by
      have hz : ∀ i, raw3338step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3338step2 = (fun i j => raw3338step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3338step2 raw3338step1; decide +kernel
      have hl : raw3338step2Labels = (fun j => raw3338step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3338step1 raw3338step1Labels permutation6 hz
    mixedMoment B raw3338step2 raw3338step2Labels = mixedMoment B raw3338step3 raw3338step3Labels := by
      have ha : raw3338step3 = (fun i j => raw3338step2 (permutation9 i) (permutation0 j)) := by apply Matrix.ext; unfold raw3338step3 raw3338step2; decide +kernel
      have hl : raw3338step3Labels = raw3338step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3338step2 raw3338step2Labels permutation9 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw3339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0]]
def raw3339Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw3339step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3339step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw3339step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3339step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![2, -2, 0]]
def raw3339step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3339step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-2, 2, 0], ![2, -2, 0]]
def raw3339step3Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3339step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]
def raw3339step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical3339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3339 raw3339Labels = mixedMoment B node4094 node4094Labels := by
  calc
    mixedMoment B raw3339 raw3339Labels = mixedMoment B raw3339step0 raw3339step0Labels := by
      have hz : ∀ j, raw3339 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw3339step0 = (fun i j => raw3339 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw3339step0 raw3339; decide +kernel
      have hl : raw3339step0Labels = raw3339Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3339 raw3339Labels permutation590 hz
    mixedMoment B raw3339step0 raw3339step0Labels = mixedMoment B raw3339step1 raw3339step1Labels := by
      have hz : ∀ j, raw3339step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw3339step1 = (fun i j => raw3339step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw3339step1 raw3339step0; decide +kernel
      have hl : raw3339step1Labels = raw3339step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3339step0 raw3339step0Labels permutation104 hz
    mixedMoment B raw3339step1 raw3339step1Labels = mixedMoment B raw3339step2 raw3339step2Labels := by
      have hz : ∀ j, raw3339step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw3339step2 = (fun i j => raw3339step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw3339step2 raw3339step1; decide +kernel
      have hl : raw3339step2Labels = raw3339step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3339step1 raw3339step1Labels permutation20 hz
    mixedMoment B raw3339step2 raw3339step2Labels = mixedMoment B raw3339step3 raw3339step3Labels := by
      have hz : ∀ j, raw3339step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw3339step3 = (fun i j => raw3339step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw3339step3 raw3339step2; decide +kernel
      have hl : raw3339step3Labels = raw3339step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3339step2 raw3339step2Labels permutation4 hz
    mixedMoment B raw3339step3 raw3339step3Labels = mixedMoment B raw3339step4 raw3339step4Labels := by
      have hz : ∀ i, raw3339step3 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3339step4 = (fun i j => raw3339step3 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3339step4 raw3339step3; decide +kernel
      have hl : raw3339step4Labels = (fun j => raw3339step3Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3339step3 raw3339step3Labels permutation6 hz
    _ = mixedMoment B node4094 node4094Labels := by rfl

def raw3340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw3340Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw3340step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3340step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw3340step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3340step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![0, 0, 0], ![2, -2, 0]]
def raw3340step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3340step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-2, 2, 0], ![2, -2, 0]]
def raw3340step3Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3340step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-2, 2], ![2, -2]]
def raw3340step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical3340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3340 raw3340Labels = mixedMoment B node4094 node4094Labels := by
  calc
    mixedMoment B raw3340 raw3340Labels = mixedMoment B raw3340step0 raw3340step0Labels := by
      have hz : ∀ j, raw3340 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3340step0 = (fun i j => raw3340 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3340step0 raw3340; decide +kernel
      have hl : raw3340step0Labels = raw3340Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3340 raw3340Labels permutation520 hz
    mixedMoment B raw3340step0 raw3340step0Labels = mixedMoment B raw3340step1 raw3340step1Labels := by
      have hz : ∀ j, raw3340step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw3340step1 = (fun i j => raw3340step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw3340step1 raw3340step0; decide +kernel
      have hl : raw3340step1Labels = raw3340step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3340step0 raw3340step0Labels permutation104 hz
    mixedMoment B raw3340step1 raw3340step1Labels = mixedMoment B raw3340step2 raw3340step2Labels := by
      have hz : ∀ j, raw3340step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw3340step2 = (fun i j => raw3340step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw3340step2 raw3340step1; decide +kernel
      have hl : raw3340step2Labels = raw3340step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3340step1 raw3340step1Labels permutation20 hz
    mixedMoment B raw3340step2 raw3340step2Labels = mixedMoment B raw3340step3 raw3340step3Labels := by
      have hz : ∀ j, raw3340step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw3340step3 = (fun i j => raw3340step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw3340step3 raw3340step2; decide +kernel
      have hl : raw3340step3Labels = raw3340step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3340step2 raw3340step2Labels permutation4 hz
    mixedMoment B raw3340step3 raw3340step3Labels = mixedMoment B raw3340step4 raw3340step4Labels := by
      have hz : ∀ i, raw3340step3 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3340step4 = (fun i j => raw3340step3 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3340step4 raw3340step3; decide +kernel
      have hl : raw3340step4Labels = (fun j => raw3340step3Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3340step3 raw3340step3Labels permutation6 hz
    _ = mixedMoment B node4094 node4094Labels := by rfl

def raw3341 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3341Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3341step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3341step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3341step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3341step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3341 raw3341Labels = mixedMoment B node5489 node5489Labels := by
  calc
    mixedMoment B raw3341 raw3341Labels = mixedMoment B raw3341step0 raw3341step0Labels := by
      have ha : raw3341step0 = (fun i j => raw3341 (permutation295 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3341step0 raw3341; decide +kernel
      have hl : raw3341step0Labels = raw3341Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3341 raw3341Labels permutation295 permutation3
    mixedMoment B raw3341step0 raw3341step0Labels = mixedMoment B raw3341step1 raw3341step1Labels := by
      have ha : raw3341step1 = raw3341step0 := by apply Matrix.ext; unfold raw3341step1 raw3341step0; decide +kernel
      have hl : raw3341step0Labels = labelEmbedding6 ∘ raw3341step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3341step0 raw3341step0Labels raw3341step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5489 node5489Labels := by rfl

def raw3342 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3342Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3342step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3342step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3342step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3342step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3342step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3342step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3342 raw3342Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw3342 raw3342Labels = mixedMoment B raw3342step0 raw3342step0Labels := by
      have ha : raw3342step0 = (fun i j => raw3342 (permutation387 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3342step0 raw3342; decide +kernel
      have hl : raw3342step0Labels = raw3342Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3342 raw3342Labels permutation387 permutation4
    mixedMoment B raw3342step0 raw3342step0Labels = mixedMoment B raw3342step1 raw3342step1Labels := by
      have ha : raw3342step1 = -raw3342step0 := by apply Matrix.ext; change ∀ i j, raw3342step1 i j = -(raw3342step0 i j); unfold raw3342step1 raw3342step0; decide +kernel
      have hl : raw3342step1Labels = raw3342step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3342step1 raw3342step1Labels = mixedMoment B raw3342step2 raw3342step2Labels := by
      have ha : raw3342step2 = raw3342step1 := by apply Matrix.ext; unfold raw3342step2 raw3342step1; decide +kernel
      have hl : raw3342step1Labels = labelEmbedding7 ∘ raw3342step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3342step1 raw3342step1Labels raw3342step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw3343 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3343Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3343step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3343step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3343step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3343step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3343step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3343step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3343 raw3343Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw3343 raw3343Labels = mixedMoment B raw3343step0 raw3343step0Labels := by
      have ha : raw3343step0 = (fun i j => raw3343 (permutation473 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3343step0 raw3343; decide +kernel
      have hl : raw3343step0Labels = raw3343Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3343 raw3343Labels permutation473 permutation4
    mixedMoment B raw3343step0 raw3343step0Labels = mixedMoment B raw3343step1 raw3343step1Labels := by
      have ha : raw3343step1 = -raw3343step0 := by apply Matrix.ext; change ∀ i j, raw3343step1 i j = -(raw3343step0 i j); unfold raw3343step1 raw3343step0; decide +kernel
      have hl : raw3343step1Labels = raw3343step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3343step1 raw3343step1Labels = mixedMoment B raw3343step2 raw3343step2Labels := by
      have ha : raw3343step2 = raw3343step1 := by apply Matrix.ext; unfold raw3343step2 raw3343step1; decide +kernel
      have hl : raw3343step1Labels = labelEmbedding7 ∘ raw3343step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3343step1 raw3343step1Labels raw3343step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw3344 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0]]
def raw3344Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw3344step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3344step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3344step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3344step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3344step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3344step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3344step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3344 raw3344Labels = mixedMoment B node5499 node5499Labels := by
  calc
    mixedMoment B raw3344 raw3344Labels = mixedMoment B raw3344step0 raw3344step0Labels := by
      have hz : ∀ j, raw3344 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3344step0 = (fun i j => raw3344 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3344step0 raw3344; decide +kernel
      have hl : raw3344step0Labels = raw3344Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3344 raw3344Labels permutation520 hz
    mixedMoment B raw3344step0 raw3344step0Labels = mixedMoment B raw3344step1 raw3344step1Labels := by
      have ha : raw3344step1 = (fun i j => raw3344step0 (permutation95 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3344step1 raw3344step0; decide +kernel
      have hl : raw3344step1Labels = raw3344step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3344step0 raw3344step0Labels permutation95 permutation4
    mixedMoment B raw3344step1 raw3344step1Labels = mixedMoment B raw3344step2 raw3344step2Labels := by
      have ha : raw3344step2 = -raw3344step1 := by apply Matrix.ext; change ∀ i j, raw3344step2 i j = -(raw3344step1 i j); unfold raw3344step2 raw3344step1; decide +kernel
      have hl : raw3344step2Labels = raw3344step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3344step2 raw3344step2Labels = mixedMoment B raw3344step3 raw3344step3Labels := by
      have ha : raw3344step3 = raw3344step2 := by apply Matrix.ext; unfold raw3344step3 raw3344step2; decide +kernel
      have hl : raw3344step2Labels = labelEmbedding7 ∘ raw3344step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3344step2 raw3344step2Labels raw3344step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5499 node5499Labels := by rfl

def raw3345 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0]]
def raw3345Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw3345step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3345step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3345step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3345step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3345step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3345step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3345step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3345 raw3345Labels = mixedMoment B node5499 node5499Labels := by
  calc
    mixedMoment B raw3345 raw3345Labels = mixedMoment B raw3345step0 raw3345step0Labels := by
      have hz : ∀ j, raw3345 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw3345step0 = (fun i j => raw3345 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw3345step0 raw3345; decide +kernel
      have hl : raw3345step0Labels = raw3345Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3345 raw3345Labels permutation590 hz
    mixedMoment B raw3345step0 raw3345step0Labels = mixedMoment B raw3345step1 raw3345step1Labels := by
      have ha : raw3345step1 = (fun i j => raw3345step0 (permutation95 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3345step1 raw3345step0; decide +kernel
      have hl : raw3345step1Labels = raw3345step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3345step0 raw3345step0Labels permutation95 permutation4
    mixedMoment B raw3345step1 raw3345step1Labels = mixedMoment B raw3345step2 raw3345step2Labels := by
      have ha : raw3345step2 = -raw3345step1 := by apply Matrix.ext; change ∀ i j, raw3345step2 i j = -(raw3345step1 i j); unfold raw3345step2 raw3345step1; decide +kernel
      have hl : raw3345step2Labels = raw3345step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3345step2 raw3345step2Labels = mixedMoment B raw3345step3 raw3345step3Labels := by
      have ha : raw3345step3 = raw3345step2 := by apply Matrix.ext; unfold raw3345step3 raw3345step2; decide +kernel
      have hl : raw3345step2Labels = labelEmbedding7 ∘ raw3345step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3345step2 raw3345step2Labels raw3345step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5499 node5499Labels := by rfl

def raw3346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3346Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3346step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3346step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3346step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3346step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3346 raw3346Labels = mixedMoment B node5489 node5489Labels := by
  calc
    mixedMoment B raw3346 raw3346Labels = mixedMoment B raw3346step0 raw3346step0Labels := by
      have ha : raw3346step0 = (fun i j => raw3346 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3346step0 raw3346; decide +kernel
      have hl : raw3346step0Labels = raw3346Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3346 raw3346Labels permutation182 permutation3
    mixedMoment B raw3346step0 raw3346step0Labels = mixedMoment B raw3346step1 raw3346step1Labels := by
      have ha : raw3346step1 = raw3346step0 := by apply Matrix.ext; unfold raw3346step1 raw3346step0; decide +kernel
      have hl : raw3346step0Labels = labelEmbedding6 ∘ raw3346step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3346step0 raw3346step0Labels raw3346step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5489 node5489Labels := by rfl

def raw3347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3347Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3347step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3347step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3347step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3347step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3347step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3347step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3347 raw3347Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw3347 raw3347Labels = mixedMoment B raw3347step0 raw3347step0Labels := by
      have ha : raw3347step0 = (fun i j => raw3347 (permutation383 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3347step0 raw3347; decide +kernel
      have hl : raw3347step0Labels = raw3347Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3347 raw3347Labels permutation383 permutation4
    mixedMoment B raw3347step0 raw3347step0Labels = mixedMoment B raw3347step1 raw3347step1Labels := by
      have ha : raw3347step1 = -raw3347step0 := by apply Matrix.ext; change ∀ i j, raw3347step1 i j = -(raw3347step0 i j); unfold raw3347step1 raw3347step0; decide +kernel
      have hl : raw3347step1Labels = raw3347step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3347step1 raw3347step1Labels = mixedMoment B raw3347step2 raw3347step2Labels := by
      have ha : raw3347step2 = raw3347step1 := by apply Matrix.ext; unfold raw3347step2 raw3347step1; decide +kernel
      have hl : raw3347step1Labels = labelEmbedding7 ∘ raw3347step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3347step1 raw3347step1Labels raw3347step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw3348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3348Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3348step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3348step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3348step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3348step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3348step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3348step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3348 raw3348Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw3348 raw3348Labels = mixedMoment B raw3348step0 raw3348step0Labels := by
      have ha : raw3348step0 = (fun i j => raw3348 (permutation468 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3348step0 raw3348; decide +kernel
      have hl : raw3348step0Labels = raw3348Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3348 raw3348Labels permutation468 permutation4
    mixedMoment B raw3348step0 raw3348step0Labels = mixedMoment B raw3348step1 raw3348step1Labels := by
      have ha : raw3348step1 = -raw3348step0 := by apply Matrix.ext; change ∀ i j, raw3348step1 i j = -(raw3348step0 i j); unfold raw3348step1 raw3348step0; decide +kernel
      have hl : raw3348step1Labels = raw3348step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3348step1 raw3348step1Labels = mixedMoment B raw3348step2 raw3348step2Labels := by
      have ha : raw3348step2 = raw3348step1 := by apply Matrix.ext; unfold raw3348step2 raw3348step1; decide +kernel
      have hl : raw3348step1Labels = labelEmbedding7 ∘ raw3348step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3348step1 raw3348step1Labels raw3348step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw3349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0]]
def raw3349Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw3349step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3349step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3349step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3349step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3349step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3349step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3349step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3349 raw3349Labels = mixedMoment B node5499 node5499Labels := by
  calc
    mixedMoment B raw3349 raw3349Labels = mixedMoment B raw3349step0 raw3349step0Labels := by
      have hz : ∀ j, raw3349 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3349step0 = (fun i j => raw3349 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3349step0 raw3349; decide +kernel
      have hl : raw3349step0Labels = raw3349Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3349 raw3349Labels permutation520 hz
    mixedMoment B raw3349step0 raw3349step0Labels = mixedMoment B raw3349step1 raw3349step1Labels := by
      have ha : raw3349step1 = (fun i j => raw3349step0 (permutation93 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3349step1 raw3349step0; decide +kernel
      have hl : raw3349step1Labels = raw3349step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3349step0 raw3349step0Labels permutation93 permutation4
    mixedMoment B raw3349step1 raw3349step1Labels = mixedMoment B raw3349step2 raw3349step2Labels := by
      have ha : raw3349step2 = -raw3349step1 := by apply Matrix.ext; change ∀ i j, raw3349step2 i j = -(raw3349step1 i j); unfold raw3349step2 raw3349step1; decide +kernel
      have hl : raw3349step2Labels = raw3349step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3349step2 raw3349step2Labels = mixedMoment B raw3349step3 raw3349step3Labels := by
      have ha : raw3349step3 = raw3349step2 := by apply Matrix.ext; unfold raw3349step3 raw3349step2; decide +kernel
      have hl : raw3349step2Labels = labelEmbedding7 ∘ raw3349step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3349step2 raw3349step2Labels raw3349step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5499 node5499Labels := by rfl

def raw3350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0]]
def raw3350Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw3350step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3350step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3350step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3350step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3350step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3350step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3350step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3350 raw3350Labels = mixedMoment B node5499 node5499Labels := by
  calc
    mixedMoment B raw3350 raw3350Labels = mixedMoment B raw3350step0 raw3350step0Labels := by
      have hz : ∀ j, raw3350 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw3350step0 = (fun i j => raw3350 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw3350step0 raw3350; decide +kernel
      have hl : raw3350step0Labels = raw3350Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3350 raw3350Labels permutation590 hz
    mixedMoment B raw3350step0 raw3350step0Labels = mixedMoment B raw3350step1 raw3350step1Labels := by
      have ha : raw3350step1 = (fun i j => raw3350step0 (permutation93 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3350step1 raw3350step0; decide +kernel
      have hl : raw3350step1Labels = raw3350step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3350step0 raw3350step0Labels permutation93 permutation4
    mixedMoment B raw3350step1 raw3350step1Labels = mixedMoment B raw3350step2 raw3350step2Labels := by
      have ha : raw3350step2 = -raw3350step1 := by apply Matrix.ext; change ∀ i j, raw3350step2 i j = -(raw3350step1 i j); unfold raw3350step2 raw3350step1; decide +kernel
      have hl : raw3350step2Labels = raw3350step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3350step2 raw3350step2Labels = mixedMoment B raw3350step3 raw3350step3Labels := by
      have ha : raw3350step3 = raw3350step2 := by apply Matrix.ext; unfold raw3350step3 raw3350step2; decide +kernel
      have hl : raw3350step2Labels = labelEmbedding7 ∘ raw3350step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3350step2 raw3350step2Labels raw3350step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5499 node5499Labels := by rfl

def raw3351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3351Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3351step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3351step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3351 raw3351Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw3351 raw3351Labels = mixedMoment B raw3351step0 raw3351step0Labels := by
      have ha : raw3351step0 = (fun i j => raw3351 (permutation161 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3351step0 raw3351; decide +kernel
      have hl : raw3351step0Labels = raw3351Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3351 raw3351Labels permutation161 permutation2
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw3352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3352Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3352step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3352step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3352 raw3352Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw3352 raw3352Labels = mixedMoment B raw3352step0 raw3352step0Labels := by
      have ha : raw3352step0 = (fun i j => raw3352 (permutation274 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3352step0 raw3352; decide +kernel
      have hl : raw3352step0Labels = raw3352Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3352 raw3352Labels permutation274 permutation2
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw3353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3353Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3353step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw3353step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3353step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3353step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3353step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3353step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3353 raw3353Labels = mixedMoment B node5489 node5489Labels := by
  calc
    mixedMoment B raw3353 raw3353Labels = mixedMoment B raw3353step0 raw3353step0Labels := by
      have ha : raw3353step0 = (fun i j => raw3353 (permutation434 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3353step0 raw3353; decide +kernel
      have hl : raw3353step0Labels = raw3353Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3353 raw3353Labels permutation434 permutation5
    mixedMoment B raw3353step0 raw3353step0Labels = mixedMoment B raw3353step1 raw3353step1Labels := by
      have ha : raw3353step1 = -raw3353step0 := by apply Matrix.ext; change ∀ i j, raw3353step1 i j = -(raw3353step0 i j); unfold raw3353step1 raw3353step0; decide +kernel
      have hl : raw3353step1Labels = raw3353step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3353step1 raw3353step1Labels = mixedMoment B raw3353step2 raw3353step2Labels := by
      have ha : raw3353step2 = raw3353step1 := by apply Matrix.ext; unfold raw3353step2 raw3353step1; decide +kernel
      have hl : raw3353step1Labels = labelEmbedding8 ∘ raw3353step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3353step1 raw3353step1Labels raw3353step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5489 node5489Labels := by rfl

def raw3354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0]]
def raw3354Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3354step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw3354step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3354step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3354step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3354 raw3354Labels = mixedMoment B node5499 node5499Labels := by
  calc
    mixedMoment B raw3354 raw3354Labels = mixedMoment B raw3354step0 raw3354step0Labels := by
      have hz : ∀ j, raw3354 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3354step0 = (fun i j => raw3354 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3354step0 raw3354; decide +kernel
      have hl : raw3354step0Labels = raw3354Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3354 raw3354Labels permutation520 hz
    mixedMoment B raw3354step0 raw3354step0Labels = mixedMoment B raw3354step1 raw3354step1Labels := by
      have ha : raw3354step1 = (fun i j => raw3354step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3354step1 raw3354step0; decide +kernel
      have hl : raw3354step1Labels = raw3354step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3354step0 raw3354step0Labels permutation35 permutation2
    _ = mixedMoment B node5499 node5499Labels := by rfl

def raw3355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0]]
def raw3355Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw3355step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3355step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3355step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3355 raw3355Labels = mixedMoment B node5499 node5499Labels := by
  calc
    mixedMoment B raw3355 raw3355Labels = mixedMoment B raw3355step0 raw3355step0Labels := by
      have hz : ∀ j, raw3355 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw3355step0 = (fun i j => raw3355 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw3355step0 raw3355; decide +kernel
      have hl : raw3355step0Labels = raw3355Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3355 raw3355Labels permutation590 hz
    mixedMoment B raw3355step0 raw3355step0Labels = mixedMoment B raw3355step1 raw3355step1Labels := by
      have ha : raw3355step1 = (fun i j => raw3355step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3355step1 raw3355step0; decide +kernel
      have hl : raw3355step1Labels = raw3355step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3355step0 raw3355step0Labels permutation35 permutation2
    _ = mixedMoment B node5499 node5499Labels := by rfl

def raw3356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3356Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3356step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3356step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3356 raw3356Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw3356 raw3356Labels = mixedMoment B raw3356step0 raw3356step0Labels := by
      have ha : raw3356step0 = (fun i j => raw3356 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3356step0 raw3356; decide +kernel
      have hl : raw3356step0Labels = raw3356Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3356 raw3356Labels permutation155 permutation2
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw3357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3357Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3357step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3357step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3357 raw3357Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw3357 raw3357Labels = mixedMoment B raw3357step0 raw3357step0Labels := by
      have ha : raw3357step0 = (fun i j => raw3357 (permutation268 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3357step0 raw3357; decide +kernel
      have hl : raw3357step0Labels = raw3357Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3357 raw3357Labels permutation268 permutation2
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw3358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3358Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3358step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw3358step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3358step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3358step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3358step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3358step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3358 raw3358Labels = mixedMoment B node5489 node5489Labels := by
  calc
    mixedMoment B raw3358 raw3358Labels = mixedMoment B raw3358step0 raw3358step0Labels := by
      have ha : raw3358step0 = (fun i j => raw3358 (permutation346 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3358step0 raw3358; decide +kernel
      have hl : raw3358step0Labels = raw3358Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3358 raw3358Labels permutation346 permutation5
    mixedMoment B raw3358step0 raw3358step0Labels = mixedMoment B raw3358step1 raw3358step1Labels := by
      have ha : raw3358step1 = -raw3358step0 := by apply Matrix.ext; change ∀ i j, raw3358step1 i j = -(raw3358step0 i j); unfold raw3358step1 raw3358step0; decide +kernel
      have hl : raw3358step1Labels = raw3358step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3358step1 raw3358step1Labels = mixedMoment B raw3358step2 raw3358step2Labels := by
      have ha : raw3358step2 = raw3358step1 := by apply Matrix.ext; unfold raw3358step2 raw3358step1; decide +kernel
      have hl : raw3358step1Labels = labelEmbedding8 ∘ raw3358step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3358step1 raw3358step1Labels raw3358step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5489 node5489Labels := by rfl

def raw3359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0]]
def raw3359Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3359step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw3359step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3359step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3359step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3359 raw3359Labels = mixedMoment B node5499 node5499Labels := by
  calc
    mixedMoment B raw3359 raw3359Labels = mixedMoment B raw3359step0 raw3359step0Labels := by
      have hz : ∀ j, raw3359 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3359step0 = (fun i j => raw3359 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3359step0 raw3359; decide +kernel
      have hl : raw3359step0Labels = raw3359Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3359 raw3359Labels permutation520 hz
    mixedMoment B raw3359step0 raw3359step0Labels = mixedMoment B raw3359step1 raw3359step1Labels := by
      have ha : raw3359step1 = (fun i j => raw3359step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3359step1 raw3359step0; decide +kernel
      have hl : raw3359step1Labels = raw3359step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3359step0 raw3359step0Labels permutation33 permutation2
    _ = mixedMoment B node5499 node5499Labels := by rfl

def raw3360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0]]
def raw3360Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw3360step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3360step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3360step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3360 raw3360Labels = mixedMoment B node5499 node5499Labels := by
  calc
    mixedMoment B raw3360 raw3360Labels = mixedMoment B raw3360step0 raw3360step0Labels := by
      have hz : ∀ j, raw3360 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw3360step0 = (fun i j => raw3360 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw3360step0 raw3360; decide +kernel
      have hl : raw3360step0Labels = raw3360Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3360 raw3360Labels permutation590 hz
    mixedMoment B raw3360step0 raw3360step0Labels = mixedMoment B raw3360step1 raw3360step1Labels := by
      have ha : raw3360step1 = (fun i j => raw3360step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3360step1 raw3360step0; decide +kernel
      have hl : raw3360step1Labels = raw3360step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3360step0 raw3360step0Labels permutation33 permutation2
    _ = mixedMoment B node5499 node5499Labels := by rfl

def raw3361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw3361Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3361step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3361step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3361step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3361step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3361step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3361step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3361 raw3361Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw3361 raw3361Labels = mixedMoment B raw3361step0 raw3361step0Labels := by
      have ha : raw3361step0 = (fun i j => raw3361 (permutation584 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3361step0 raw3361; decide +kernel
      have hl : raw3361step0Labels = raw3361Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3361 raw3361Labels permutation584 permutation3
    mixedMoment B raw3361step0 raw3361step0Labels = mixedMoment B raw3361step1 raw3361step1Labels := by
      have ha : raw3361step1 = -raw3361step0 := by apply Matrix.ext; change ∀ i j, raw3361step1 i j = -(raw3361step0 i j); unfold raw3361step1 raw3361step0; decide +kernel
      have hl : raw3361step1Labels = raw3361step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3361step1 raw3361step1Labels = mixedMoment B raw3361step2 raw3361step2Labels := by
      have ha : raw3361step2 = raw3361step1 := by apply Matrix.ext; unfold raw3361step2 raw3361step1; decide +kernel
      have hl : raw3361step1Labels = labelEmbedding6 ∘ raw3361step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3361step1 raw3361step1Labels raw3361step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

def raw3362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw3362Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3362step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3362step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3362step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3362step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3362step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3362step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3362 raw3362Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw3362 raw3362Labels = mixedMoment B raw3362step0 raw3362step0Labels := by
      have ha : raw3362step0 = (fun i j => raw3362 (permutation583 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3362step0 raw3362; decide +kernel
      have hl : raw3362step0Labels = raw3362Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3362 raw3362Labels permutation583 permutation3
    mixedMoment B raw3362step0 raw3362step0Labels = mixedMoment B raw3362step1 raw3362step1Labels := by
      have ha : raw3362step1 = -raw3362step0 := by apply Matrix.ext; change ∀ i j, raw3362step1 i j = -(raw3362step0 i j); unfold raw3362step1 raw3362step0; decide +kernel
      have hl : raw3362step1Labels = raw3362step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3362step1 raw3362step1Labels = mixedMoment B raw3362step2 raw3362step2Labels := by
      have ha : raw3362step2 = raw3362step1 := by apply Matrix.ext; unfold raw3362step2 raw3362step1; decide +kernel
      have hl : raw3362step1Labels = labelEmbedding6 ∘ raw3362step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3362step1 raw3362step1Labels raw3362step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

def raw3363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw3363Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3363step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3363step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3363step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3363step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3363 raw3363Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw3363 raw3363Labels = mixedMoment B raw3363step0 raw3363step0Labels := by
      have ha : raw3363step0 = (fun i j => raw3363 (permutation570 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3363step0 raw3363; decide +kernel
      have hl : raw3363step0Labels = raw3363Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3363 raw3363Labels permutation570 permutation5
    mixedMoment B raw3363step0 raw3363step0Labels = mixedMoment B raw3363step1 raw3363step1Labels := by
      have ha : raw3363step1 = raw3363step0 := by apply Matrix.ext; unfold raw3363step1 raw3363step0; decide +kernel
      have hl : raw3363step0Labels = labelEmbedding8 ∘ raw3363step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3363step0 raw3363step0Labels raw3363step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

def raw3364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0]]
def raw3364Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3364step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3364step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3364step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3364step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3364 raw3364Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw3364 raw3364Labels = mixedMoment B raw3364step0 raw3364step0Labels := by
      have ha : raw3364step0 = (fun i j => raw3364 (permutation569 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3364step0 raw3364; decide +kernel
      have hl : raw3364step0Labels = raw3364Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3364 raw3364Labels permutation569 permutation5
    mixedMoment B raw3364step0 raw3364step0Labels = mixedMoment B raw3364step1 raw3364step1Labels := by
      have ha : raw3364step1 = raw3364step0 := by apply Matrix.ext; unfold raw3364step1 raw3364step0; decide +kernel
      have hl : raw3364step0Labels = labelEmbedding8 ∘ raw3364step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3364step0 raw3364step0Labels raw3364step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

def raw3365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0]]
def raw3365Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw3365step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3365step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0]]
def raw3365step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3365step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3365step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3365step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3365step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3365 raw3365Labels = mixedMoment B node5452 node5452Labels := by
  calc
    mixedMoment B raw3365 raw3365Labels = mixedMoment B raw3365step0 raw3365step0Labels := by
      have hz : ∀ j, raw3365 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw3365step0 = (fun i j => raw3365 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw3365step0 raw3365; decide +kernel
      have hl : raw3365step0Labels = raw3365Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3365 raw3365Labels permutation590 hz
    mixedMoment B raw3365step0 raw3365step0Labels = mixedMoment B raw3365step1 raw3365step1Labels := by
      have ha : raw3365step1 = (fun i j => raw3365step0 (permutation144 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3365step1 raw3365step0; decide +kernel
      have hl : raw3365step1Labels = raw3365step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3365step0 raw3365step0Labels permutation144 permutation3
    mixedMoment B raw3365step1 raw3365step1Labels = mixedMoment B raw3365step2 raw3365step2Labels := by
      have ha : raw3365step2 = -raw3365step1 := by apply Matrix.ext; change ∀ i j, raw3365step2 i j = -(raw3365step1 i j); unfold raw3365step2 raw3365step1; decide +kernel
      have hl : raw3365step2Labels = raw3365step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3365step2 raw3365step2Labels = mixedMoment B raw3365step3 raw3365step3Labels := by
      have ha : raw3365step3 = raw3365step2 := by apply Matrix.ext; unfold raw3365step3 raw3365step2; decide +kernel
      have hl : raw3365step2Labels = labelEmbedding6 ∘ raw3365step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3365step2 raw3365step2Labels raw3365step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5452 node5452Labels := by rfl

def raw3366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw3366Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3366step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3366step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3366step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3366step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3366step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3366step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3366 raw3366Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw3366 raw3366Labels = mixedMoment B raw3366step0 raw3366step0Labels := by
      have ha : raw3366step0 = (fun i j => raw3366 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3366step0 raw3366; decide +kernel
      have hl : raw3366step0Labels = raw3366Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3366 raw3366Labels permutation682 permutation3
    mixedMoment B raw3366step0 raw3366step0Labels = mixedMoment B raw3366step1 raw3366step1Labels := by
      have ha : raw3366step1 = -raw3366step0 := by apply Matrix.ext; change ∀ i j, raw3366step1 i j = -(raw3366step0 i j); unfold raw3366step1 raw3366step0; decide +kernel
      have hl : raw3366step1Labels = raw3366step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3366step1 raw3366step1Labels = mixedMoment B raw3366step2 raw3366step2Labels := by
      have ha : raw3366step2 = raw3366step1 := by apply Matrix.ext; unfold raw3366step2 raw3366step1; decide +kernel
      have hl : raw3366step1Labels = labelEmbedding6 ∘ raw3366step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3366step1 raw3366step1Labels raw3366step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

def raw3367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw3367Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3367step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3367step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3367step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3367step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3367step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3367step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3367 raw3367Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw3367 raw3367Labels = mixedMoment B raw3367step0 raw3367step0Labels := by
      have ha : raw3367step0 = (fun i j => raw3367 (permutation681 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3367step0 raw3367; decide +kernel
      have hl : raw3367step0Labels = raw3367Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3367 raw3367Labels permutation681 permutation3
    mixedMoment B raw3367step0 raw3367step0Labels = mixedMoment B raw3367step1 raw3367step1Labels := by
      have ha : raw3367step1 = -raw3367step0 := by apply Matrix.ext; change ∀ i j, raw3367step1 i j = -(raw3367step0 i j); unfold raw3367step1 raw3367step0; decide +kernel
      have hl : raw3367step1Labels = raw3367step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3367step1 raw3367step1Labels = mixedMoment B raw3367step2 raw3367step2Labels := by
      have ha : raw3367step2 = raw3367step1 := by apply Matrix.ext; unfold raw3367step2 raw3367step1; decide +kernel
      have hl : raw3367step1Labels = labelEmbedding6 ∘ raw3367step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3367step1 raw3367step1Labels raw3367step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

def raw3368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw3368Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3368step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3368step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3368step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3368step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3368 raw3368Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw3368 raw3368Labels = mixedMoment B raw3368step0 raw3368step0Labels := by
      have ha : raw3368step0 = (fun i j => raw3368 (permutation666 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3368step0 raw3368; decide +kernel
      have hl : raw3368step0Labels = raw3368Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3368 raw3368Labels permutation666 permutation5
    mixedMoment B raw3368step0 raw3368step0Labels = mixedMoment B raw3368step1 raw3368step1Labels := by
      have ha : raw3368step1 = raw3368step0 := by apply Matrix.ext; unfold raw3368step1 raw3368step0; decide +kernel
      have hl : raw3368step0Labels = labelEmbedding8 ∘ raw3368step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3368step0 raw3368step0Labels raw3368step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

def raw3369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw3369Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3369step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3369step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3369step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3369step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3369 raw3369Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw3369 raw3369Labels = mixedMoment B raw3369step0 raw3369step0Labels := by
      have ha : raw3369step0 = (fun i j => raw3369 (permutation665 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3369step0 raw3369; decide +kernel
      have hl : raw3369step0Labels = raw3369Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3369 raw3369Labels permutation665 permutation5
    mixedMoment B raw3369step0 raw3369step0Labels = mixedMoment B raw3369step1 raw3369step1Labels := by
      have ha : raw3369step1 = raw3369step0 := by apply Matrix.ext; unfold raw3369step1 raw3369step0; decide +kernel
      have hl : raw3369step0Labels = labelEmbedding8 ∘ raw3369step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3369step0 raw3369step0Labels raw3369step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

def raw3370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0]]
def raw3370Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3370step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw3370step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3370step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0]]
def raw3370step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3370step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3370step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3370step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3370step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3370 raw3370Labels = mixedMoment B node5452 node5452Labels := by
  calc
    mixedMoment B raw3370 raw3370Labels = mixedMoment B raw3370step0 raw3370step0Labels := by
      have hz : ∀ j, raw3370 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3370step0 = (fun i j => raw3370 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3370step0 raw3370; decide +kernel
      have hl : raw3370step0Labels = raw3370Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3370 raw3370Labels permutation520 hz
    mixedMoment B raw3370step0 raw3370step0Labels = mixedMoment B raw3370step1 raw3370step1Labels := by
      have ha : raw3370step1 = (fun i j => raw3370step0 (permutation144 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3370step1 raw3370step0; decide +kernel
      have hl : raw3370step1Labels = raw3370step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3370step0 raw3370step0Labels permutation144 permutation3
    mixedMoment B raw3370step1 raw3370step1Labels = mixedMoment B raw3370step2 raw3370step2Labels := by
      have ha : raw3370step2 = -raw3370step1 := by apply Matrix.ext; change ∀ i j, raw3370step2 i j = -(raw3370step1 i j); unfold raw3370step2 raw3370step1; decide +kernel
      have hl : raw3370step2Labels = raw3370step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3370step2 raw3370step2Labels = mixedMoment B raw3370step3 raw3370step3Labels := by
      have ha : raw3370step3 = raw3370step2 := by apply Matrix.ext; unfold raw3370step3 raw3370step2; decide +kernel
      have hl : raw3370step2Labels = labelEmbedding6 ∘ raw3370step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3370step2 raw3370step2Labels raw3370step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5452 node5452Labels := by rfl

def raw3371 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3371Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3371step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3371step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3371step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3371step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3371step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3371step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3371 raw3371Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw3371 raw3371Labels = mixedMoment B raw3371step0 raw3371step0Labels := by
      have ha : raw3371step0 = (fun i j => raw3371 (permutation318 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3371step0 raw3371; decide +kernel
      have hl : raw3371step0Labels = raw3371Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3371 raw3371Labels permutation318 permutation5
    mixedMoment B raw3371step0 raw3371step0Labels = mixedMoment B raw3371step1 raw3371step1Labels := by
      have ha : raw3371step1 = -raw3371step0 := by apply Matrix.ext; change ∀ i j, raw3371step1 i j = -(raw3371step0 i j); unfold raw3371step1 raw3371step0; decide +kernel
      have hl : raw3371step1Labels = raw3371step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3371step1 raw3371step1Labels = mixedMoment B raw3371step2 raw3371step2Labels := by
      have ha : raw3371step2 = raw3371step1 := by apply Matrix.ext; unfold raw3371step2 raw3371step1; decide +kernel
      have hl : raw3371step1Labels = labelEmbedding8 ∘ raw3371step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3371step1 raw3371step1Labels raw3371step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw3372 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3372Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3372step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3372step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3372 raw3372Labels = mixedMoment B node5500 node5500Labels := by
  calc
    mixedMoment B raw3372 raw3372Labels = mixedMoment B raw3372step0 raw3372step0Labels := by
      have ha : raw3372step0 = (fun i j => raw3372 (permutation367 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3372step0 raw3372; decide +kernel
      have hl : raw3372step0Labels = raw3372Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3372 raw3372Labels permutation367 permutation2
    _ = mixedMoment B node5500 node5500Labels := by rfl

def raw3373 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3373Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3373step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3373step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3373step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3373step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3373step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3373step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3373 raw3373Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw3373 raw3373Labels = mixedMoment B raw3373step0 raw3373step0Labels := by
      have ha : raw3373step0 = (fun i j => raw3373 (permutation464 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3373step0 raw3373; decide +kernel
      have hl : raw3373step0Labels = raw3373Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3373 raw3373Labels permutation464 permutation5
    mixedMoment B raw3373step0 raw3373step0Labels = mixedMoment B raw3373step1 raw3373step1Labels := by
      have ha : raw3373step1 = -raw3373step0 := by apply Matrix.ext; change ∀ i j, raw3373step1 i j = -(raw3373step0 i j); unfold raw3373step1 raw3373step0; decide +kernel
      have hl : raw3373step1Labels = raw3373step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3373step1 raw3373step1Labels = mixedMoment B raw3373step2 raw3373step2Labels := by
      have ha : raw3373step2 = raw3373step1 := by apply Matrix.ext; unfold raw3373step2 raw3373step1; decide +kernel
      have hl : raw3373step1Labels = labelEmbedding8 ∘ raw3373step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3373step1 raw3373step1Labels raw3373step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw3374 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1]]
def raw3374Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3374step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3374step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3374step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3374step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3374step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3374 raw3374Labels = mixedMoment B node5499 node5499Labels := by
  calc
    mixedMoment B raw3374 raw3374Labels = mixedMoment B raw3374step0 raw3374step0Labels := by
      have hz : ∀ j, raw3374 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3374step0 = (fun i j => raw3374 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3374step0 raw3374; decide +kernel
      have hl : raw3374step0Labels = raw3374Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3374 raw3374Labels permutation520 hz
    mixedMoment B raw3374step0 raw3374step0Labels = mixedMoment B raw3374step1 raw3374step1Labels := by
      have ha : raw3374step1 = (fun i j => raw3374step0 (permutation42 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3374step1 raw3374step0; decide +kernel
      have hl : raw3374step1Labels = raw3374step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3374step0 raw3374step0Labels permutation42 permutation4
    mixedMoment B raw3374step1 raw3374step1Labels = mixedMoment B raw3374step2 raw3374step2Labels := by
      have ha : raw3374step2 = raw3374step1 := by apply Matrix.ext; unfold raw3374step2 raw3374step1; decide +kernel
      have hl : raw3374step1Labels = labelEmbedding7 ∘ raw3374step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3374step1 raw3374step1Labels raw3374step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5499 node5499Labels := by rfl

def raw3375 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, -1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1]]
def raw3375Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3375step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3375step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3375step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3375step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3375 raw3375Labels = mixedMoment B node5497 node5497Labels := by
  calc
    mixedMoment B raw3375 raw3375Labels = mixedMoment B raw3375step0 raw3375step0Labels := by
      have ha : raw3375step0 = (fun i j => raw3375 (permutation188 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3375step0 raw3375; decide +kernel
      have hl : raw3375step0Labels = raw3375Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3375 raw3375Labels permutation188 permutation4
    mixedMoment B raw3375step0 raw3375step0Labels = mixedMoment B raw3375step1 raw3375step1Labels := by
      have ha : raw3375step1 = raw3375step0 := by apply Matrix.ext; unfold raw3375step1 raw3375step0; decide +kernel
      have hl : raw3375step0Labels = labelEmbedding7 ∘ raw3375step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3375step0 raw3375step0Labels raw3375step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5497 node5497Labels := by rfl

def raw3376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3376Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3376step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3376 raw3376Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw3376 raw3376Labels = mixedMoment B raw3376step0 raw3376step0Labels := by
      have hz : ∀ j, raw3376 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3376step0 = (fun i j => raw3376 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3376step0 raw3376; decide +kernel
      have hl : raw3376step0Labels = raw3376Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3376 raw3376Labels permutation265 hz
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw3377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3377Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3377step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3377step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3377 raw3377Labels = mixedMoment B node5499 node5499Labels := by
  calc
    mixedMoment B raw3377 raw3377Labels = mixedMoment B raw3377step0 raw3377step0Labels := by
      have hz : ∀ j, raw3377 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3377step0 = (fun i j => raw3377 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3377step0 raw3377; decide +kernel
      have hl : raw3377step0Labels = raw3377Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3377 raw3377Labels permutation265 hz
    _ = mixedMoment B node5499 node5499Labels := by rfl

def raw3378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3378Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3378step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3378step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3378step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3378step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3378step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3378step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3378step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3378step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3378 raw3378Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw3378 raw3378Labels = mixedMoment B raw3378step0 raw3378step0Labels := by
      have hz : ∀ j, raw3378 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3378step0 = (fun i j => raw3378 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3378step0 raw3378; decide +kernel
      have hl : raw3378step0Labels = raw3378Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3378 raw3378Labels permutation265 hz
    mixedMoment B raw3378step0 raw3378step0Labels = mixedMoment B raw3378step1 raw3378step1Labels := by
      have ha : raw3378step1 = (fun i j => raw3378step0 (permutation99 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3378step1 raw3378step0; decide +kernel
      have hl : raw3378step1Labels = raw3378step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3378step0 raw3378step0Labels permutation99 permutation4
    mixedMoment B raw3378step1 raw3378step1Labels = mixedMoment B raw3378step2 raw3378step2Labels := by
      have ha : raw3378step2 = -raw3378step1 := by apply Matrix.ext; change ∀ i j, raw3378step2 i j = -(raw3378step1 i j); unfold raw3378step2 raw3378step1; decide +kernel
      have hl : raw3378step2Labels = raw3378step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3378step2 raw3378step2Labels = mixedMoment B raw3378step3 raw3378step3Labels := by
      have ha : raw3378step3 = raw3378step2 := by apply Matrix.ext; unfold raw3378step3 raw3378step2; decide +kernel
      have hl : raw3378step2Labels = labelEmbedding7 ∘ raw3378step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3378step2 raw3378step2Labels raw3378step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw3379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1]]
def raw3379Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3379step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3379step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3379step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3379step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3379step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3379step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3379step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3379step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3379 raw3379Labels = mixedMoment B node5501 node5501Labels := by
  calc
    mixedMoment B raw3379 raw3379Labels = mixedMoment B raw3379step0 raw3379step0Labels := by
      have hz : ∀ j, raw3379 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3379step0 = (fun i j => raw3379 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3379step0 raw3379; decide +kernel
      have hl : raw3379step0Labels = raw3379Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3379 raw3379Labels permutation520 hz
    mixedMoment B raw3379step0 raw3379step0Labels = mixedMoment B raw3379step1 raw3379step1Labels := by
      have hz : ∀ j, raw3379step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3379step1 = (fun i j => raw3379step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3379step1 raw3379step0; decide +kernel
      have hl : raw3379step1Labels = raw3379step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3379step0 raw3379step0Labels permutation56 hz
    mixedMoment B raw3379step1 raw3379step1Labels = mixedMoment B raw3379step2 raw3379step2Labels := by
      have ha : raw3379step2 = (fun i j => raw3379step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3379step2 raw3379step1; decide +kernel
      have hl : raw3379step2Labels = raw3379step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3379step1 raw3379step1Labels permutation24 permutation6
    mixedMoment B raw3379step2 raw3379step2Labels = mixedMoment B raw3379step3 raw3379step3Labels := by
      have ha : raw3379step3 = raw3379step2 := by apply Matrix.ext; unfold raw3379step3 raw3379step2; decide +kernel
      have hl : raw3379step2Labels = labelEmbedding9 ∘ raw3379step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3379step2 raw3379step2Labels raw3379step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5501 node5501Labels := by rfl

def raw3380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1]]
def raw3380Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3380step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1]]
def raw3380step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3380step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3380step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3380step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3380step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3380step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3380step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3380 raw3380Labels = mixedMoment B node5499 node5499Labels := by
  calc
    mixedMoment B raw3380 raw3380Labels = mixedMoment B raw3380step0 raw3380step0Labels := by
      have hz : ∀ j, raw3380 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3380step0 = (fun i j => raw3380 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3380step0 raw3380; decide +kernel
      have hl : raw3380step0Labels = raw3380Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3380 raw3380Labels permutation265 hz
    mixedMoment B raw3380step0 raw3380step0Labels = mixedMoment B raw3380step1 raw3380step1Labels := by
      have ha : raw3380step1 = (fun i j => raw3380step0 (permutation99 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3380step1 raw3380step0; decide +kernel
      have hl : raw3380step1Labels = raw3380step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3380step0 raw3380step0Labels permutation99 permutation4
    mixedMoment B raw3380step1 raw3380step1Labels = mixedMoment B raw3380step2 raw3380step2Labels := by
      have ha : raw3380step2 = -raw3380step1 := by apply Matrix.ext; change ∀ i j, raw3380step2 i j = -(raw3380step1 i j); unfold raw3380step2 raw3380step1; decide +kernel
      have hl : raw3380step2Labels = raw3380step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3380step2 raw3380step2Labels = mixedMoment B raw3380step3 raw3380step3Labels := by
      have ha : raw3380step3 = raw3380step2 := by apply Matrix.ext; unfold raw3380step3 raw3380step2; decide +kernel
      have hl : raw3380step2Labels = labelEmbedding7 ∘ raw3380step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3380step2 raw3380step2Labels raw3380step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5499 node5499Labels := by rfl

def raw3381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3381Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3381step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw3381step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3381step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw3381step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3381 raw3381Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw3381 raw3381Labels = mixedMoment B raw3381step0 raw3381step0Labels := by
      have ha : raw3381step0 = (fun i j => raw3381 (permutation163 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3381step0 raw3381; decide +kernel
      have hl : raw3381step0Labels = raw3381Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3381 raw3381Labels permutation163 permutation3
    mixedMoment B raw3381step0 raw3381step0Labels = mixedMoment B raw3381step1 raw3381step1Labels := by
      have ha : raw3381step1 = raw3381step0 := by apply Matrix.ext; unfold raw3381step1 raw3381step0; decide +kernel
      have hl : raw3381step0Labels = labelEmbedding6 ∘ raw3381step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3381step0 raw3381step0Labels raw3381step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5478 node5478Labels := by rfl

def raw3382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3382Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3382step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw3382step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3382step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3382step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3382step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3382step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3382 raw3382Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw3382 raw3382Labels = mixedMoment B raw3382step0 raw3382step0Labels := by
      have ha : raw3382step0 = (fun i j => raw3382 (permutation310 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3382step0 raw3382; decide +kernel
      have hl : raw3382step0Labels = raw3382Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3382 raw3382Labels permutation310 permutation5
    mixedMoment B raw3382step0 raw3382step0Labels = mixedMoment B raw3382step1 raw3382step1Labels := by
      have ha : raw3382step1 = -raw3382step0 := by apply Matrix.ext; change ∀ i j, raw3382step1 i j = -(raw3382step0 i j); unfold raw3382step1 raw3382step0; decide +kernel
      have hl : raw3382step1Labels = raw3382step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3382step1 raw3382step1Labels = mixedMoment B raw3382step2 raw3382step2Labels := by
      have ha : raw3382step2 = raw3382step1 := by apply Matrix.ext; unfold raw3382step2 raw3382step1; decide +kernel
      have hl : raw3382step1Labels = labelEmbedding8 ∘ raw3382step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3382step1 raw3382step1Labels raw3382step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw3383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3383Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3383step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3383step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3383step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3383step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3383 raw3383Labels = mixedMoment B node5477 node5477Labels := by
  calc
    mixedMoment B raw3383 raw3383Labels = mixedMoment B raw3383step0 raw3383step0Labels := by
      have ha : raw3383step0 = (fun i j => raw3383 (permutation409 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3383step0 raw3383; decide +kernel
      have hl : raw3383step0Labels = raw3383Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3383 raw3383Labels permutation409 permutation5
    mixedMoment B raw3383step0 raw3383step0Labels = mixedMoment B raw3383step1 raw3383step1Labels := by
      have ha : raw3383step1 = raw3383step0 := by apply Matrix.ext; unfold raw3383step1 raw3383step0; decide +kernel
      have hl : raw3383step0Labels = labelEmbedding8 ∘ raw3383step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3383step0 raw3383step0Labels raw3383step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5477 node5477Labels := by rfl

def raw3384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1]]
def raw3384Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3384step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3384step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3384step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3384step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3384step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3384step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3384 raw3384Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw3384 raw3384Labels = mixedMoment B raw3384step0 raw3384step0Labels := by
      have hz : ∀ j, raw3384 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3384step0 = (fun i j => raw3384 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3384step0 raw3384; decide +kernel
      have hl : raw3384step0Labels = raw3384Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3384 raw3384Labels permutation520 hz
    mixedMoment B raw3384step0 raw3384step0Labels = mixedMoment B raw3384step1 raw3384step1Labels := by
      have ha : raw3384step1 = (fun i j => raw3384step0 (permutation84 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3384step1 raw3384step0; decide +kernel
      have hl : raw3384step1Labels = raw3384step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3384step0 raw3384step0Labels permutation84 permutation4
    mixedMoment B raw3384step1 raw3384step1Labels = mixedMoment B raw3384step2 raw3384step2Labels := by
      have ha : raw3384step2 = raw3384step1 := by apply Matrix.ext; unfold raw3384step2 raw3384step1; decide +kernel
      have hl : raw3384step1Labels = labelEmbedding7 ∘ raw3384step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3384step1 raw3384step1Labels raw3384step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw3385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1]]
def raw3385Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3385step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3385step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3385step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3385step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3385 raw3385Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw3385 raw3385Labels = mixedMoment B raw3385step0 raw3385step0Labels := by
      have ha : raw3385step0 = (fun i j => raw3385 (permutation400 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3385step0 raw3385; decide +kernel
      have hl : raw3385step0Labels = raw3385Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3385 raw3385Labels permutation400 permutation5
    mixedMoment B raw3385step0 raw3385step0Labels = mixedMoment B raw3385step1 raw3385step1Labels := by
      have ha : raw3385step1 = raw3385step0 := by apply Matrix.ext; unfold raw3385step1 raw3385step0; decide +kernel
      have hl : raw3385step0Labels = labelEmbedding8 ∘ raw3385step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3385step0 raw3385step0Labels raw3385step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw3386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3386Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3386step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3386step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3386step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3386step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3386 raw3386Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw3386 raw3386Labels = mixedMoment B raw3386step0 raw3386step0Labels := by
      have ha : raw3386step0 = (fun i j => raw3386 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3386step0 raw3386; decide +kernel
      have hl : raw3386step0Labels = raw3386Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3386 raw3386Labels permutation153 permutation3
    mixedMoment B raw3386step0 raw3386step0Labels = mixedMoment B raw3386step1 raw3386step1Labels := by
      have ha : raw3386step1 = raw3386step0 := by apply Matrix.ext; unfold raw3386step1 raw3386step0; decide +kernel
      have hl : raw3386step0Labels = labelEmbedding6 ∘ raw3386step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3386step0 raw3386step0Labels raw3386step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw3387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3387Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3387step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3387step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3387step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3387step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3387 raw3387Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw3387 raw3387Labels = mixedMoment B raw3387step0 raw3387step0Labels := by
      have ha : raw3387step0 = (fun i j => raw3387 (permutation266 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3387step0 raw3387; decide +kernel
      have hl : raw3387step0Labels = raw3387Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3387 raw3387Labels permutation266 permutation3
    mixedMoment B raw3387step0 raw3387step0Labels = mixedMoment B raw3387step1 raw3387step1Labels := by
      have ha : raw3387step1 = raw3387step0 := by apply Matrix.ext; unfold raw3387step1 raw3387step0; decide +kernel
      have hl : raw3387step0Labels = labelEmbedding6 ∘ raw3387step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3387step0 raw3387step0Labels raw3387step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw3388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3388Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3388step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3388step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3388 raw3388Labels = mixedMoment B node5497 node5497Labels := by
  calc
    mixedMoment B raw3388 raw3388Labels = mixedMoment B raw3388step0 raw3388step0Labels := by
      have ha : raw3388step0 = (fun i j => raw3388 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3388step0 raw3388; decide +kernel
      have hl : raw3388step0Labels = raw3388Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3388 raw3388Labels permutation178 permutation2
    _ = mixedMoment B node5497 node5497Labels := by rfl

def raw3389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1]]
def raw3389Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3389step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3389step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3389step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3389step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3389step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3389step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3389 raw3389Labels = mixedMoment B node5499 node5499Labels := by
  calc
    mixedMoment B raw3389 raw3389Labels = mixedMoment B raw3389step0 raw3389step0Labels := by
      have hz : ∀ j, raw3389 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3389step0 = (fun i j => raw3389 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3389step0 raw3389; decide +kernel
      have hl : raw3389step0Labels = raw3389Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3389 raw3389Labels permutation520 hz
    mixedMoment B raw3389step0 raw3389step0Labels = mixedMoment B raw3389step1 raw3389step1Labels := by
      have ha : raw3389step1 = (fun i j => raw3389step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3389step1 raw3389step0; decide +kernel
      have hl : raw3389step1Labels = raw3389step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3389step0 raw3389step0Labels permutation127 permutation2
    mixedMoment B raw3389step1 raw3389step1Labels = mixedMoment B raw3389step2 raw3389step2Labels := by
      have ha : raw3389step2 = -raw3389step1 := by apply Matrix.ext; change ∀ i j, raw3389step2 i j = -(raw3389step1 i j); unfold raw3389step2 raw3389step1; decide +kernel
      have hl : raw3389step2Labels = raw3389step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5499 node5499Labels := by rfl

def raw3390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![0, 1, -1]]
def raw3390Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3390step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3390step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3390 raw3390Labels = mixedMoment B node5500 node5500Labels := by
  calc
    mixedMoment B raw3390 raw3390Labels = mixedMoment B raw3390step0 raw3390step0Labels := by
      have ha : raw3390step0 = (fun i j => raw3390 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3390step0 raw3390; decide +kernel
      have hl : raw3390step0Labels = raw3390Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3390 raw3390Labels permutation157 permutation2
    _ = mixedMoment B node5500 node5500Labels := by rfl

def raw3391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw3391Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3391step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw3391step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3391step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3391step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3391step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3391step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3391 raw3391Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw3391 raw3391Labels = mixedMoment B raw3391step0 raw3391step0Labels := by
      have ha : raw3391step0 = (fun i j => raw3391 (permutation584 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3391step0 raw3391; decide +kernel
      have hl : raw3391step0Labels = raw3391Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3391 raw3391Labels permutation584 permutation3
    mixedMoment B raw3391step0 raw3391step0Labels = mixedMoment B raw3391step1 raw3391step1Labels := by
      have ha : raw3391step1 = -raw3391step0 := by apply Matrix.ext; change ∀ i j, raw3391step1 i j = -(raw3391step0 i j); unfold raw3391step1 raw3391step0; decide +kernel
      have hl : raw3391step1Labels = raw3391step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3391step1 raw3391step1Labels = mixedMoment B raw3391step2 raw3391step2Labels := by
      have ha : raw3391step2 = raw3391step1 := by apply Matrix.ext; unfold raw3391step2 raw3391step1; decide +kernel
      have hl : raw3391step1Labels = labelEmbedding6 ∘ raw3391step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3391step1 raw3391step1Labels raw3391step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw3392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw3392Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3392step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw3392step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3392step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw3392step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3392 raw3392Labels = mixedMoment B node5423 node5423Labels := by
  calc
    mixedMoment B raw3392 raw3392Labels = mixedMoment B raw3392step0 raw3392step0Labels := by
      have ha : raw3392step0 = (fun i j => raw3392 (permutation272 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3392step0 raw3392; decide +kernel
      have hl : raw3392step0Labels = raw3392Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3392 raw3392Labels permutation272 permutation3
    mixedMoment B raw3392step0 raw3392step0Labels = mixedMoment B raw3392step1 raw3392step1Labels := by
      have ha : raw3392step1 = raw3392step0 := by apply Matrix.ext; unfold raw3392step1 raw3392step0; decide +kernel
      have hl : raw3392step0Labels = labelEmbedding6 ∘ raw3392step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3392step0 raw3392step0Labels raw3392step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5423 node5423Labels := by rfl

def raw3393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw3393Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3393step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3393step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3393step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3393step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3393step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3393step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3393 raw3393Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw3393 raw3393Labels = mixedMoment B raw3393step0 raw3393step0Labels := by
      have ha : raw3393step0 = (fun i j => raw3393 (permutation585 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3393step0 raw3393; decide +kernel
      have hl : raw3393step0Labels = raw3393Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3393 raw3393Labels permutation585 permutation3
    mixedMoment B raw3393step0 raw3393step0Labels = mixedMoment B raw3393step1 raw3393step1Labels := by
      have ha : raw3393step1 = -raw3393step0 := by apply Matrix.ext; change ∀ i j, raw3393step1 i j = -(raw3393step0 i j); unfold raw3393step1 raw3393step0; decide +kernel
      have hl : raw3393step1Labels = raw3393step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3393step1 raw3393step1Labels = mixedMoment B raw3393step2 raw3393step2Labels := by
      have ha : raw3393step2 = raw3393step1 := by apply Matrix.ext; unfold raw3393step2 raw3393step1; decide +kernel
      have hl : raw3393step1Labels = labelEmbedding6 ∘ raw3393step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3393step1 raw3393step1Labels raw3393step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw3394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![2, -2, 0], ![1, 0, -1]]
def raw3394Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3394step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3394step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3394step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3394step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3394 raw3394Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw3394 raw3394Labels = mixedMoment B raw3394step0 raw3394step0Labels := by
      have ha : raw3394step0 = (fun i j => raw3394 (permutation547 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3394step0 raw3394; decide +kernel
      have hl : raw3394step0Labels = raw3394Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3394 raw3394Labels permutation547 permutation5
    mixedMoment B raw3394step0 raw3394step0Labels = mixedMoment B raw3394step1 raw3394step1Labels := by
      have ha : raw3394step1 = raw3394step0 := by apply Matrix.ext; unfold raw3394step1 raw3394step0; decide +kernel
      have hl : raw3394step0Labels = labelEmbedding8 ∘ raw3394step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3394step0 raw3394step0Labels raw3394step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw3395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![0, 1, -1]]
def raw3395Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3395step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3395step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3395step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3395step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3395 raw3395Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw3395 raw3395Labels = mixedMoment B raw3395step0 raw3395step0Labels := by
      have ha : raw3395step0 = (fun i j => raw3395 (permutation542 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3395step0 raw3395; decide +kernel
      have hl : raw3395step0Labels = raw3395Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3395 raw3395Labels permutation542 permutation5
    mixedMoment B raw3395step0 raw3395step0Labels = mixedMoment B raw3395step1 raw3395step1Labels := by
      have ha : raw3395step1 = raw3395step0 := by apply Matrix.ext; unfold raw3395step1 raw3395step0; decide +kernel
      have hl : raw3395step0Labels = labelEmbedding8 ∘ raw3395step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3395step0 raw3395step0Labels raw3395step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw3396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3396Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3396step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3396step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3396step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3396step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3396 raw3396Labels = mixedMoment B node5477 node5477Labels := by
  calc
    mixedMoment B raw3396 raw3396Labels = mixedMoment B raw3396step0 raw3396step0Labels := by
      have ha : raw3396step0 = (fun i j => raw3396 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3396step0 raw3396; decide +kernel
      have hl : raw3396step0Labels = raw3396Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3396 raw3396Labels permutation158 permutation3
    mixedMoment B raw3396step0 raw3396step0Labels = mixedMoment B raw3396step1 raw3396step1Labels := by
      have ha : raw3396step1 = raw3396step0 := by apply Matrix.ext; unfold raw3396step1 raw3396step0; decide +kernel
      have hl : raw3396step0Labels = labelEmbedding6 ∘ raw3396step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3396step0 raw3396step0Labels raw3396step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5477 node5477Labels := by rfl

def raw3397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3397Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3397step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3397step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3397step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw3397step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3397 raw3397Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw3397 raw3397Labels = mixedMoment B raw3397step0 raw3397step0Labels := by
      have ha : raw3397step0 = (fun i j => raw3397 (permutation271 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3397step0 raw3397; decide +kernel
      have hl : raw3397step0Labels = raw3397Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3397 raw3397Labels permutation271 permutation3
    mixedMoment B raw3397step0 raw3397step0Labels = mixedMoment B raw3397step1 raw3397step1Labels := by
      have ha : raw3397step1 = raw3397step0 := by apply Matrix.ext; unfold raw3397step1 raw3397step0; decide +kernel
      have hl : raw3397step0Labels = labelEmbedding6 ∘ raw3397step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3397step0 raw3397step0Labels raw3397step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw3398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3398Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3398step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3398step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3398step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3398step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3398step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3398step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3398 raw3398Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw3398 raw3398Labels = mixedMoment B raw3398step0 raw3398step0Labels := by
      have ha : raw3398step0 = (fun i j => raw3398 (permutation684 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3398step0 raw3398; decide +kernel
      have hl : raw3398step0Labels = raw3398Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3398 raw3398Labels permutation684 permutation3
    mixedMoment B raw3398step0 raw3398step0Labels = mixedMoment B raw3398step1 raw3398step1Labels := by
      have ha : raw3398step1 = -raw3398step0 := by apply Matrix.ext; change ∀ i j, raw3398step1 i j = -(raw3398step0 i j); unfold raw3398step1 raw3398step0; decide +kernel
      have hl : raw3398step1Labels = raw3398step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3398step1 raw3398step1Labels = mixedMoment B raw3398step2 raw3398step2Labels := by
      have ha : raw3398step2 = raw3398step1 := by apply Matrix.ext; unfold raw3398step2 raw3398step1; decide +kernel
      have hl : raw3398step1Labels = labelEmbedding6 ∘ raw3398step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3398step1 raw3398step1Labels raw3398step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw3399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3399Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3399step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw3399step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3399step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw3399step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3399step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw3399step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3399 raw3399Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw3399 raw3399Labels = mixedMoment B raw3399step0 raw3399step0Labels := by
      have ha : raw3399step0 = (fun i j => raw3399 (permutation677 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3399step0 raw3399; decide +kernel
      have hl : raw3399step0Labels = raw3399Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3399 raw3399Labels permutation677 permutation3
    mixedMoment B raw3399step0 raw3399step0Labels = mixedMoment B raw3399step1 raw3399step1Labels := by
      have ha : raw3399step1 = -raw3399step0 := by apply Matrix.ext; change ∀ i j, raw3399step1 i j = -(raw3399step0 i j); unfold raw3399step1 raw3399step0; decide +kernel
      have hl : raw3399step1Labels = raw3399step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3399step1 raw3399step1Labels = mixedMoment B raw3399step2 raw3399step2Labels := by
      have ha : raw3399step2 = raw3399step1 := by apply Matrix.ext; unfold raw3399step2 raw3399step1; decide +kernel
      have hl : raw3399step1Labels = labelEmbedding6 ∘ raw3399step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3399step1 raw3399step1Labels raw3399step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5478 node5478Labels := by rfl

def raw3400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw3400Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw3400step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3400step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3400step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3400step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3400step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3400 raw3400Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw3400 raw3400Labels = mixedMoment B raw3400step0 raw3400step0Labels := by
      have hz : ∀ j, raw3400 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3400step0 = (fun i j => raw3400 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3400step0 raw3400; decide +kernel
      have hl : raw3400step0Labels = raw3400Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3400 raw3400Labels permutation520 hz
    mixedMoment B raw3400step0 raw3400step0Labels = mixedMoment B raw3400step1 raw3400step1Labels := by
      have ha : raw3400step1 = (fun i j => raw3400step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3400step1 raw3400step0; decide +kernel
      have hl : raw3400step1Labels = raw3400step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3400step0 raw3400step0Labels permutation151 permutation2
    mixedMoment B raw3400step1 raw3400step1Labels = mixedMoment B raw3400step2 raw3400step2Labels := by
      have ha : raw3400step2 = -raw3400step1 := by apply Matrix.ext; change ∀ i j, raw3400step2 i j = -(raw3400step1 i j); unfold raw3400step2 raw3400step1; decide +kernel
      have hl : raw3400step2Labels = raw3400step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw3401 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3401Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3401step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3401step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3401step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3401 raw3401Labels = mixedMoment B node5493 node5493Labels := by
  calc
    mixedMoment B raw3401 raw3401Labels = mixedMoment B raw3401step0 raw3401step0Labels := by
      have hz : ∀ j, raw3401 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3401step0 = (fun i j => raw3401 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3401step0 raw3401; decide +kernel
      have hl : raw3401step0Labels = raw3401Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3401 raw3401Labels permutation346 hz
    mixedMoment B raw3401step0 raw3401step0Labels = mixedMoment B raw3401step1 raw3401step1Labels := by
      have hz : ∀ j, raw3401step0 (permutation32 0) j = 0 := by decide +kernel
      have ha : raw3401step1 = (fun i j => raw3401step0 (permutation32 i.succ) j) := by apply Matrix.ext; unfold raw3401step1 raw3401step0; decide +kernel
      have hl : raw3401step1Labels = raw3401step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3401step0 raw3401step0Labels permutation32 hz
    _ = mixedMoment B node5493 node5493Labels := by rfl

def raw3402 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3402Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3402step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3402step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3402step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3402step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3402step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3402step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3402 raw3402Labels = mixedMoment B node5499 node5499Labels := by
  calc
    mixedMoment B raw3402 raw3402Labels = mixedMoment B raw3402step0 raw3402step0Labels := by
      have hz : ∀ j, raw3402 (permutation152 0) j = 0 := by decide +kernel
      have ha : raw3402step0 = (fun i j => raw3402 (permutation152 i.succ) j) := by apply Matrix.ext; unfold raw3402step0 raw3402; decide +kernel
      have hl : raw3402step0Labels = raw3402Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3402 raw3402Labels permutation152 hz
    mixedMoment B raw3402step0 raw3402step0Labels = mixedMoment B raw3402step1 raw3402step1Labels := by
      have ha : raw3402step1 = (fun i j => raw3402step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3402step1 raw3402step0; decide +kernel
      have hl : raw3402step1Labels = raw3402step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3402step0 raw3402step0Labels permutation127 permutation2
    mixedMoment B raw3402step1 raw3402step1Labels = mixedMoment B raw3402step2 raw3402step2Labels := by
      have ha : raw3402step2 = -raw3402step1 := by apply Matrix.ext; change ∀ i j, raw3402step2 i j = -(raw3402step1 i j); unfold raw3402step2 raw3402step1; decide +kernel
      have hl : raw3402step2Labels = raw3402step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5499 node5499Labels := by rfl

def raw3403 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3403Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3403step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3403step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3403step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3403step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw3403step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw3403step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw3403step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical3403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3403 raw3403Labels = mixedMoment B node4096 node4096Labels := by
  calc
    mixedMoment B raw3403 raw3403Labels = mixedMoment B raw3403step0 raw3403step0Labels := by
      have hz : ∀ j, raw3403 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3403step0 = (fun i j => raw3403 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3403step0 raw3403; decide +kernel
      have hl : raw3403step0Labels = raw3403Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3403 raw3403Labels permutation346 hz
    mixedMoment B raw3403step0 raw3403step0Labels = mixedMoment B raw3403step1 raw3403step1Labels := by
      have hz : ∀ j, raw3403step0 (permutation32 0) j = 0 := by decide +kernel
      have ha : raw3403step1 = (fun i j => raw3403step0 (permutation32 i.succ) j) := by apply Matrix.ext; unfold raw3403step1 raw3403step0; decide +kernel
      have hl : raw3403step1Labels = raw3403step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3403step0 raw3403step0Labels permutation32 hz
    mixedMoment B raw3403step1 raw3403step1Labels = mixedMoment B raw3403step2 raw3403step2Labels := by
      have hz : ∀ i, raw3403step1 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw3403step2 = (fun i j => raw3403step1 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw3403step2 raw3403step1; decide +kernel
      have hl : raw3403step2Labels = (fun j => raw3403step1Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3403step1 raw3403step1Labels permutation4 hz
    mixedMoment B raw3403step2 raw3403step2Labels = mixedMoment B raw3403step3 raw3403step3Labels := by
      have ha : raw3403step3 = raw3403step2 := by apply Matrix.ext; unfold raw3403step3 raw3403step2; decide +kernel
      have hl : raw3403step2Labels = labelEmbedding2 ∘ raw3403step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3403step2 raw3403step2Labels raw3403step3Labels labelEmbedding2 hl
    _ = mixedMoment B node4096 node4096Labels := by rfl

def raw3404 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3404Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3404step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3404step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3404step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3404step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3404step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3404step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3404step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3404 raw3404Labels = mixedMoment B node5501 node5501Labels := by
  calc
    mixedMoment B raw3404 raw3404Labels = mixedMoment B raw3404step0 raw3404step0Labels := by
      have hz : ∀ j, raw3404 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3404step0 = (fun i j => raw3404 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3404step0 raw3404; decide +kernel
      have hl : raw3404step0Labels = raw3404Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3404 raw3404Labels permutation346 hz
    mixedMoment B raw3404step0 raw3404step0Labels = mixedMoment B raw3404step1 raw3404step1Labels := by
      have hz : ∀ j, raw3404step0 (permutation32 0) j = 0 := by decide +kernel
      have ha : raw3404step1 = (fun i j => raw3404step0 (permutation32 i.succ) j) := by apply Matrix.ext; unfold raw3404step1 raw3404step0; decide +kernel
      have hl : raw3404step1Labels = raw3404step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3404step0 raw3404step0Labels permutation32 hz
    mixedMoment B raw3404step1 raw3404step1Labels = mixedMoment B raw3404step2 raw3404step2Labels := by
      have ha : raw3404step2 = (fun i j => raw3404step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3404step2 raw3404step1; decide +kernel
      have hl : raw3404step2Labels = raw3404step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3404step1 raw3404step1Labels permutation24 permutation6
    mixedMoment B raw3404step2 raw3404step2Labels = mixedMoment B raw3404step3 raw3404step3Labels := by
      have ha : raw3404step3 = raw3404step2 := by apply Matrix.ext; unfold raw3404step3 raw3404step2; decide +kernel
      have hl : raw3404step2Labels = labelEmbedding9 ∘ raw3404step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3404step2 raw3404step2Labels raw3404step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5501 node5501Labels := by rfl

def raw3405 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3405Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3405step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3405step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3405step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3405step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3405step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3405step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3405step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3405step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3405 raw3405Labels = mixedMoment B node5501 node5501Labels := by
  calc
    mixedMoment B raw3405 raw3405Labels = mixedMoment B raw3405step0 raw3405step0Labels := by
      have hz : ∀ j, raw3405 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3405step0 = (fun i j => raw3405 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3405step0 raw3405; decide +kernel
      have hl : raw3405step0Labels = raw3405Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3405 raw3405Labels permutation346 hz
    mixedMoment B raw3405step0 raw3405step0Labels = mixedMoment B raw3405step1 raw3405step1Labels := by
      have hz : ∀ j, raw3405step0 (permutation32 0) j = 0 := by decide +kernel
      have ha : raw3405step1 = (fun i j => raw3405step0 (permutation32 i.succ) j) := by apply Matrix.ext; unfold raw3405step1 raw3405step0; decide +kernel
      have hl : raw3405step1Labels = raw3405step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3405step0 raw3405step0Labels permutation32 hz
    mixedMoment B raw3405step1 raw3405step1Labels = mixedMoment B raw3405step2 raw3405step2Labels := by
      have ha : raw3405step2 = (fun i j => raw3405step1 (permutation30 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3405step2 raw3405step1; decide +kernel
      have hl : raw3405step2Labels = raw3405step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3405step1 raw3405step1Labels permutation30 permutation6
    mixedMoment B raw3405step2 raw3405step2Labels = mixedMoment B raw3405step3 raw3405step3Labels := by
      have ha : raw3405step3 = raw3405step2 := by apply Matrix.ext; unfold raw3405step3 raw3405step2; decide +kernel
      have hl : raw3405step2Labels = labelEmbedding9 ∘ raw3405step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3405step2 raw3405step2Labels raw3405step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5501 node5501Labels := by rfl

def raw3406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3406Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3406step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3406step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3406step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3406step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3406step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3406 raw3406Labels = mixedMoment B node5452 node5452Labels := by
  calc
    mixedMoment B raw3406 raw3406Labels = mixedMoment B raw3406step0 raw3406step0Labels := by
      have hz : ∀ j, raw3406 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3406step0 = (fun i j => raw3406 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3406step0 raw3406; decide +kernel
      have hl : raw3406step0Labels = raw3406Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3406 raw3406Labels permutation346 hz
    mixedMoment B raw3406step0 raw3406step0Labels = mixedMoment B raw3406step1 raw3406step1Labels := by
      have ha : raw3406step1 = (fun i j => raw3406step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3406step1 raw3406step0; decide +kernel
      have hl : raw3406step1Labels = raw3406step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3406step0 raw3406step0Labels permutation32 permutation3
    mixedMoment B raw3406step1 raw3406step1Labels = mixedMoment B raw3406step2 raw3406step2Labels := by
      have ha : raw3406step2 = raw3406step1 := by apply Matrix.ext; unfold raw3406step2 raw3406step1; decide +kernel
      have hl : raw3406step1Labels = labelEmbedding6 ∘ raw3406step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3406step1 raw3406step1Labels raw3406step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5452 node5452Labels := by rfl

def raw3407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3407Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3407step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0]]
def raw3407step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3407step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3407step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3407 raw3407Labels = mixedMoment B node5498 node5498Labels := by
  calc
    mixedMoment B raw3407 raw3407Labels = mixedMoment B raw3407step0 raw3407step0Labels := by
      have ha : raw3407step0 = (fun i j => raw3407 (permutation578 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3407step0 raw3407; decide +kernel
      have hl : raw3407step0Labels = raw3407Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3407 raw3407Labels permutation578 permutation2
    mixedMoment B raw3407step0 raw3407step0Labels = mixedMoment B raw3407step1 raw3407step1Labels := by
      have ha : raw3407step1 = -raw3407step0 := by apply Matrix.ext; change ∀ i j, raw3407step1 i j = -(raw3407step0 i j); unfold raw3407step1 raw3407step0; decide +kernel
      have hl : raw3407step1Labels = raw3407step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5498 node5498Labels := by rfl

def raw3408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3408Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3408step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3408step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3408step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3408step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3408step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3408 raw3408Labels = mixedMoment B node5499 node5499Labels := by
  calc
    mixedMoment B raw3408 raw3408Labels = mixedMoment B raw3408step0 raw3408step0Labels := by
      have hz : ∀ j, raw3408 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3408step0 = (fun i j => raw3408 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3408step0 raw3408; decide +kernel
      have hl : raw3408step0Labels = raw3408Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3408 raw3408Labels permutation346 hz
    mixedMoment B raw3408step0 raw3408step0Labels = mixedMoment B raw3408step1 raw3408step1Labels := by
      have ha : raw3408step1 = (fun i j => raw3408step0 (permutation124 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3408step1 raw3408step0; decide +kernel
      have hl : raw3408step1Labels = raw3408step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3408step0 raw3408step0Labels permutation124 permutation2
    mixedMoment B raw3408step1 raw3408step1Labels = mixedMoment B raw3408step2 raw3408step2Labels := by
      have ha : raw3408step2 = -raw3408step1 := by apply Matrix.ext; change ∀ i j, raw3408step2 i j = -(raw3408step1 i j); unfold raw3408step2 raw3408step1; decide +kernel
      have hl : raw3408step2Labels = raw3408step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5499 node5499Labels := by rfl

def raw3409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3409Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3409step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3409step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3409step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3409step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3409step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3409 raw3409Labels = mixedMoment B node5499 node5499Labels := by
  calc
    mixedMoment B raw3409 raw3409Labels = mixedMoment B raw3409step0 raw3409step0Labels := by
      have hz : ∀ j, raw3409 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3409step0 = (fun i j => raw3409 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3409step0 raw3409; decide +kernel
      have hl : raw3409step0Labels = raw3409Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3409 raw3409Labels permutation346 hz
    mixedMoment B raw3409step0 raw3409step0Labels = mixedMoment B raw3409step1 raw3409step1Labels := by
      have ha : raw3409step1 = (fun i j => raw3409step0 (permutation66 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3409step1 raw3409step0; decide +kernel
      have hl : raw3409step1Labels = raw3409step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3409step0 raw3409step0Labels permutation66 permutation4
    mixedMoment B raw3409step1 raw3409step1Labels = mixedMoment B raw3409step2 raw3409step2Labels := by
      have ha : raw3409step2 = raw3409step1 := by apply Matrix.ext; unfold raw3409step2 raw3409step1; decide +kernel
      have hl : raw3409step1Labels = labelEmbedding7 ∘ raw3409step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3409step1 raw3409step1Labels raw3409step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5499 node5499Labels := by rfl

def raw3410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3410Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3410step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3410step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3410step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3410step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3410step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3410step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3410 raw3410Labels = mixedMoment B node5499 node5499Labels := by
  calc
    mixedMoment B raw3410 raw3410Labels = mixedMoment B raw3410step0 raw3410step0Labels := by
      have hz : ∀ j, raw3410 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3410step0 = (fun i j => raw3410 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3410step0 raw3410; decide +kernel
      have hl : raw3410step0Labels = raw3410Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3410 raw3410Labels permutation346 hz
    mixedMoment B raw3410step0 raw3410step0Labels = mixedMoment B raw3410step1 raw3410step1Labels := by
      have ha : raw3410step1 = (fun i j => raw3410step0 (permutation64 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3410step1 raw3410step0; decide +kernel
      have hl : raw3410step1Labels = raw3410step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3410step0 raw3410step0Labels permutation64 permutation4
    mixedMoment B raw3410step1 raw3410step1Labels = mixedMoment B raw3410step2 raw3410step2Labels := by
      have ha : raw3410step2 = raw3410step1 := by apply Matrix.ext; unfold raw3410step2 raw3410step1; decide +kernel
      have hl : raw3410step1Labels = labelEmbedding7 ∘ raw3410step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3410step1 raw3410step1Labels raw3410step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5499 node5499Labels := by rfl

def raw3411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3411Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3411step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3411step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3411step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3411step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3411 raw3411Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw3411 raw3411Labels = mixedMoment B raw3411step0 raw3411step0Labels := by
      have ha : raw3411step0 = (fun i j => raw3411 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3411step0 raw3411; decide +kernel
      have hl : raw3411step0Labels = raw3411Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3411 raw3411Labels permutation161 permutation3
    mixedMoment B raw3411step0 raw3411step0Labels = mixedMoment B raw3411step1 raw3411step1Labels := by
      have ha : raw3411step1 = raw3411step0 := by apply Matrix.ext; unfold raw3411step1 raw3411step0; decide +kernel
      have hl : raw3411step0Labels = labelEmbedding6 ∘ raw3411step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3411step0 raw3411step0Labels raw3411step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw3412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3412Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3412step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3412step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3412step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3412step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3412 raw3412Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw3412 raw3412Labels = mixedMoment B raw3412step0 raw3412step0Labels := by
      have ha : raw3412step0 = (fun i j => raw3412 (permutation274 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3412step0 raw3412; decide +kernel
      have hl : raw3412step0Labels = raw3412Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3412 raw3412Labels permutation274 permutation3
    mixedMoment B raw3412step0 raw3412step0Labels = mixedMoment B raw3412step1 raw3412step1Labels := by
      have ha : raw3412step1 = raw3412step0 := by apply Matrix.ext; unfold raw3412step1 raw3412step0; decide +kernel
      have hl : raw3412step0Labels = labelEmbedding6 ∘ raw3412step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3412step0 raw3412step0Labels raw3412step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw3413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3413Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3413step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3413step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3413 raw3413Labels = mixedMoment B node5497 node5497Labels := by
  calc
    mixedMoment B raw3413 raw3413Labels = mixedMoment B raw3413step0 raw3413step0Labels := by
      have ha : raw3413step0 = (fun i j => raw3413 (permutation305 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3413step0 raw3413; decide +kernel
      have hl : raw3413step0Labels = raw3413Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3413 raw3413Labels permutation305 permutation2
    _ = mixedMoment B node5497 node5497Labels := by rfl

def raw3414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3414Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3414step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3414step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3414 raw3414Labels = mixedMoment B node5500 node5500Labels := by
  calc
    mixedMoment B raw3414 raw3414Labels = mixedMoment B raw3414step0 raw3414step0Labels := by
      have ha : raw3414step0 = (fun i j => raw3414 (permutation273 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3414step0 raw3414; decide +kernel
      have hl : raw3414step0Labels = raw3414Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3414 raw3414Labels permutation273 permutation2
    _ = mixedMoment B node5500 node5500Labels := by rfl

def raw3415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3415Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3415step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3415step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3415 raw3415Labels = mixedMoment B node5500 node5500Labels := by
  calc
    mixedMoment B raw3415 raw3415Labels = mixedMoment B raw3415step0 raw3415step0Labels := by
      have ha : raw3415step0 = (fun i j => raw3415 (permutation275 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3415step0 raw3415; decide +kernel
      have hl : raw3415step0Labels = raw3415Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3415 raw3415Labels permutation275 permutation2
    _ = mixedMoment B node5500 node5500Labels := by rfl

def raw3416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3416Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3416step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3416step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3416step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3416step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3416step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3416 raw3416Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw3416 raw3416Labels = mixedMoment B raw3416step0 raw3416step0Labels := by
      have hz : ∀ j, raw3416 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3416step0 = (fun i j => raw3416 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3416step0 raw3416; decide +kernel
      have hl : raw3416step0Labels = raw3416Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3416 raw3416Labels permutation346 hz
    mixedMoment B raw3416step0 raw3416step0Labels = mixedMoment B raw3416step1 raw3416step1Labels := by
      have ha : raw3416step1 = (fun i j => raw3416step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3416step1 raw3416step0; decide +kernel
      have hl : raw3416step1Labels = raw3416step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3416step0 raw3416step0Labels permutation35 permutation3
    mixedMoment B raw3416step1 raw3416step1Labels = mixedMoment B raw3416step2 raw3416step2Labels := by
      have ha : raw3416step2 = raw3416step1 := by apply Matrix.ext; unfold raw3416step2 raw3416step1; decide +kernel
      have hl : raw3416step1Labels = labelEmbedding6 ∘ raw3416step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3416step1 raw3416step1Labels raw3416step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw3417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3417Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3417step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3417step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3417step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3417step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3417step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3417 raw3417Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw3417 raw3417Labels = mixedMoment B raw3417step0 raw3417step0Labels := by
      have hz : ∀ j, raw3417 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3417step0 = (fun i j => raw3417 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3417step0 raw3417; decide +kernel
      have hl : raw3417step0Labels = raw3417Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3417 raw3417Labels permutation346 hz
    mixedMoment B raw3417step0 raw3417step0Labels = mixedMoment B raw3417step1 raw3417step1Labels := by
      have ha : raw3417step1 = (fun i j => raw3417step0 (permutation59 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3417step1 raw3417step0; decide +kernel
      have hl : raw3417step1Labels = raw3417step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3417step0 raw3417step0Labels permutation59 permutation3
    mixedMoment B raw3417step1 raw3417step1Labels = mixedMoment B raw3417step2 raw3417step2Labels := by
      have ha : raw3417step2 = raw3417step1 := by apply Matrix.ext; unfold raw3417step2 raw3417step1; decide +kernel
      have hl : raw3417step1Labels = labelEmbedding6 ∘ raw3417step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3417step1 raw3417step1Labels raw3417step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5485 node5485Labels := by rfl

def raw3418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3418Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3418step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3418step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3418step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3418step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3418 raw3418Labels = mixedMoment B node5489 node5489Labels := by
  calc
    mixedMoment B raw3418 raw3418Labels = mixedMoment B raw3418step0 raw3418step0Labels := by
      have ha : raw3418step0 = (fun i j => raw3418 (permutation501 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3418step0 raw3418; decide +kernel
      have hl : raw3418step0Labels = raw3418Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3418 raw3418Labels permutation501 permutation5
    mixedMoment B raw3418step0 raw3418step0Labels = mixedMoment B raw3418step1 raw3418step1Labels := by
      have ha : raw3418step1 = raw3418step0 := by apply Matrix.ext; unfold raw3418step1 raw3418step0; decide +kernel
      have hl : raw3418step0Labels = labelEmbedding8 ∘ raw3418step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3418step0 raw3418step0Labels raw3418step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5489 node5489Labels := by rfl

def raw3419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3419Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3419step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3419step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3419step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3419step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3419step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3419 raw3419Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw3419 raw3419Labels = mixedMoment B raw3419step0 raw3419step0Labels := by
      have hz : ∀ j, raw3419 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3419step0 = (fun i j => raw3419 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3419step0 raw3419; decide +kernel
      have hl : raw3419step0Labels = raw3419Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3419 raw3419Labels permutation346 hz
    mixedMoment B raw3419step0 raw3419step0Labels = mixedMoment B raw3419step1 raw3419step1Labels := by
      have ha : raw3419step1 = (fun i j => raw3419step0 (permutation90 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3419step1 raw3419step0; decide +kernel
      have hl : raw3419step1Labels = raw3419step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3419step0 raw3419step0Labels permutation90 permutation4
    mixedMoment B raw3419step1 raw3419step1Labels = mixedMoment B raw3419step2 raw3419step2Labels := by
      have ha : raw3419step2 = raw3419step1 := by apply Matrix.ext; unfold raw3419step2 raw3419step1; decide +kernel
      have hl : raw3419step1Labels = labelEmbedding7 ∘ raw3419step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3419step1 raw3419step1Labels raw3419step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw3420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3420Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3420step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3420step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3420step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3420step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3420step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3420 raw3420Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw3420 raw3420Labels = mixedMoment B raw3420step0 raw3420step0Labels := by
      have hz : ∀ j, raw3420 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3420step0 = (fun i j => raw3420 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3420step0 raw3420; decide +kernel
      have hl : raw3420step0Labels = raw3420Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3420 raw3420Labels permutation346 hz
    mixedMoment B raw3420step0 raw3420step0Labels = mixedMoment B raw3420step1 raw3420step1Labels := by
      have ha : raw3420step1 = (fun i j => raw3420step0 (permutation88 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3420step1 raw3420step0; decide +kernel
      have hl : raw3420step1Labels = raw3420step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3420step0 raw3420step0Labels permutation88 permutation4
    mixedMoment B raw3420step1 raw3420step1Labels = mixedMoment B raw3420step2 raw3420step2Labels := by
      have ha : raw3420step2 = raw3420step1 := by apply Matrix.ext; unfold raw3420step2 raw3420step1; decide +kernel
      have hl : raw3420step1Labels = labelEmbedding7 ∘ raw3420step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3420step1 raw3420step1Labels raw3420step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw3421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3421Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3421step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3421step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3421step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3421step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3421step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3421step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3421 raw3421Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw3421 raw3421Labels = mixedMoment B raw3421step0 raw3421step0Labels := by
      have hz : ∀ j, raw3421 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3421step0 = (fun i j => raw3421 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3421step0 raw3421; decide +kernel
      have hl : raw3421step0Labels = raw3421Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3421 raw3421Labels permutation346 hz
    mixedMoment B raw3421step0 raw3421step0Labels = mixedMoment B raw3421step1 raw3421step1Labels := by
      have ha : raw3421step1 = (fun i j => raw3421step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3421step1 raw3421step0; decide +kernel
      have hl : raw3421step1Labels = raw3421step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3421step0 raw3421step0Labels permutation33 permutation3
    mixedMoment B raw3421step1 raw3421step1Labels = mixedMoment B raw3421step2 raw3421step2Labels := by
      have ha : raw3421step2 = raw3421step1 := by apply Matrix.ext; unfold raw3421step2 raw3421step1; decide +kernel
      have hl : raw3421step1Labels = labelEmbedding6 ∘ raw3421step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3421step1 raw3421step1Labels raw3421step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw3422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3422Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3422step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3422step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3422step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3422step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3422step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3422step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3422 raw3422Labels = mixedMoment B node5483 node5483Labels := by
  calc
    mixedMoment B raw3422 raw3422Labels = mixedMoment B raw3422step0 raw3422step0Labels := by
      have hz : ∀ j, raw3422 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3422step0 = (fun i j => raw3422 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3422step0 raw3422; decide +kernel
      have hl : raw3422step0Labels = raw3422Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3422 raw3422Labels permutation346 hz
    mixedMoment B raw3422step0 raw3422step0Labels = mixedMoment B raw3422step1 raw3422step1Labels := by
      have ha : raw3422step1 = (fun i j => raw3422step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3422step1 raw3422step0; decide +kernel
      have hl : raw3422step1Labels = raw3422step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3422step0 raw3422step0Labels permutation126 permutation2
    mixedMoment B raw3422step1 raw3422step1Labels = mixedMoment B raw3422step2 raw3422step2Labels := by
      have ha : raw3422step2 = -raw3422step1 := by apply Matrix.ext; change ∀ i j, raw3422step2 i j = -(raw3422step1 i j); unfold raw3422step2 raw3422step1; decide +kernel
      have hl : raw3422step2Labels = raw3422step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5483 node5483Labels := by rfl

def raw3423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3423Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3423step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3423step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3423step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3423step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3423 raw3423Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw3423 raw3423Labels = mixedMoment B raw3423step0 raw3423step0Labels := by
      have ha : raw3423step0 = (fun i j => raw3423 (permutation585 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3423step0 raw3423; decide +kernel
      have hl : raw3423step0Labels = raw3423Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3423 raw3423Labels permutation585 permutation2
    mixedMoment B raw3423step0 raw3423step0Labels = mixedMoment B raw3423step1 raw3423step1Labels := by
      have ha : raw3423step1 = -raw3423step0 := by apply Matrix.ext; change ∀ i j, raw3423step1 i j = -(raw3423step0 i j); unfold raw3423step1 raw3423step0; decide +kernel
      have hl : raw3423step1Labels = raw3423step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw3424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3424Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3424step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3424step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3424step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw3424step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3424step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3424step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3424 raw3424Labels = mixedMoment B node5486 node5486Labels := by
  calc
    mixedMoment B raw3424 raw3424Labels = mixedMoment B raw3424step0 raw3424step0Labels := by
      have hz : ∀ j, raw3424 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3424step0 = (fun i j => raw3424 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3424step0 raw3424; decide +kernel
      have hl : raw3424step0Labels = raw3424Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3424 raw3424Labels permutation346 hz
    mixedMoment B raw3424step0 raw3424step0Labels = mixedMoment B raw3424step1 raw3424step1Labels := by
      have ha : raw3424step1 = (fun i j => raw3424step0 (permutation122 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3424step1 raw3424step0; decide +kernel
      have hl : raw3424step1Labels = raw3424step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3424step0 raw3424step0Labels permutation122 permutation2
    mixedMoment B raw3424step1 raw3424step1Labels = mixedMoment B raw3424step2 raw3424step2Labels := by
      have ha : raw3424step2 = -raw3424step1 := by apply Matrix.ext; change ∀ i j, raw3424step2 i j = -(raw3424step1 i j); unfold raw3424step2 raw3424step1; decide +kernel
      have hl : raw3424step2Labels = raw3424step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5486 node5486Labels := by rfl

def raw3425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1]]
def raw3425Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1]]
def raw3425step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3425step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3425step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3425step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3425step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3425 raw3425Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw3425 raw3425Labels = mixedMoment B raw3425step0 raw3425step0Labels := by
      have hz : ∀ j, raw3425 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3425step0 = (fun i j => raw3425 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3425step0 raw3425; decide +kernel
      have hl : raw3425step0Labels = raw3425Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3425 raw3425Labels permutation346 hz
    mixedMoment B raw3425step0 raw3425step0Labels = mixedMoment B raw3425step1 raw3425step1Labels := by
      have ha : raw3425step1 = (fun i j => raw3425step0 (permutation126 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3425step1 raw3425step0; decide +kernel
      have hl : raw3425step1Labels = raw3425step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3425step0 raw3425step0Labels permutation126 permutation2
    mixedMoment B raw3425step1 raw3425step1Labels = mixedMoment B raw3425step2 raw3425step2Labels := by
      have ha : raw3425step2 = -raw3425step1 := by apply Matrix.ext; change ∀ i j, raw3425step2 i j = -(raw3425step1 i j); unfold raw3425step2 raw3425step1; decide +kernel
      have hl : raw3425step2Labels = raw3425step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw3426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3426Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3426step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3426step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3426step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3426step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3426step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3426step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3426 raw3426Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw3426 raw3426Labels = mixedMoment B raw3426step0 raw3426step0Labels := by
      have hz : ∀ j, raw3426 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3426step0 = (fun i j => raw3426 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3426step0 raw3426; decide +kernel
      have hl : raw3426step0Labels = raw3426Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3426 raw3426Labels permutation346 hz
    mixedMoment B raw3426step0 raw3426step0Labels = mixedMoment B raw3426step1 raw3426step1Labels := by
      have ha : raw3426step1 = (fun i j => raw3426step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3426step1 raw3426step0; decide +kernel
      have hl : raw3426step1Labels = raw3426step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3426step0 raw3426step0Labels permutation32 permutation3
    mixedMoment B raw3426step1 raw3426step1Labels = mixedMoment B raw3426step2 raw3426step2Labels := by
      have ha : raw3426step2 = raw3426step1 := by apply Matrix.ext; unfold raw3426step2 raw3426step1; decide +kernel
      have hl : raw3426step1Labels = labelEmbedding6 ∘ raw3426step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3426step1 raw3426step1Labels raw3426step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw3427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3427Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3427step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3427step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3427step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3427step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3427step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3427step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3427 raw3427Labels = mixedMoment B node5483 node5483Labels := by
  calc
    mixedMoment B raw3427 raw3427Labels = mixedMoment B raw3427step0 raw3427step0Labels := by
      have hz : ∀ j, raw3427 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3427step0 = (fun i j => raw3427 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3427step0 raw3427; decide +kernel
      have hl : raw3427step0Labels = raw3427Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3427 raw3427Labels permutation346 hz
    mixedMoment B raw3427step0 raw3427step0Labels = mixedMoment B raw3427step1 raw3427step1Labels := by
      have ha : raw3427step1 = (fun i j => raw3427step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3427step1 raw3427step0; decide +kernel
      have hl : raw3427step1Labels = raw3427step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3427step0 raw3427step0Labels permutation150 permutation2
    mixedMoment B raw3427step1 raw3427step1Labels = mixedMoment B raw3427step2 raw3427step2Labels := by
      have ha : raw3427step2 = -raw3427step1 := by apply Matrix.ext; change ∀ i j, raw3427step2 i j = -(raw3427step1 i j); unfold raw3427step2 raw3427step1; decide +kernel
      have hl : raw3427step2Labels = raw3427step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5483 node5483Labels := by rfl

def raw3428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3428Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3428step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3428step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3428step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3428step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3428 raw3428Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw3428 raw3428Labels = mixedMoment B raw3428step0 raw3428step0Labels := by
      have ha : raw3428step0 = (fun i j => raw3428 (permutation684 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3428step0 raw3428; decide +kernel
      have hl : raw3428step0Labels = raw3428Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3428 raw3428Labels permutation684 permutation2
    mixedMoment B raw3428step0 raw3428step0Labels = mixedMoment B raw3428step1 raw3428step1Labels := by
      have ha : raw3428step1 = -raw3428step0 := by apply Matrix.ext; change ∀ i j, raw3428step1 i j = -(raw3428step0 i j); unfold raw3428step1 raw3428step0; decide +kernel
      have hl : raw3428step1Labels = raw3428step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw3429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3429Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3429step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3429step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3429step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw3429step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3429step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3429step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3429 raw3429Labels = mixedMoment B node5486 node5486Labels := by
  calc
    mixedMoment B raw3429 raw3429Labels = mixedMoment B raw3429step0 raw3429step0Labels := by
      have hz : ∀ j, raw3429 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3429step0 = (fun i j => raw3429 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3429step0 raw3429; decide +kernel
      have hl : raw3429step0Labels = raw3429Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3429 raw3429Labels permutation346 hz
    mixedMoment B raw3429step0 raw3429step0Labels = mixedMoment B raw3429step1 raw3429step1Labels := by
      have ha : raw3429step1 = (fun i j => raw3429step0 (permutation146 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3429step1 raw3429step0; decide +kernel
      have hl : raw3429step1Labels = raw3429step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3429step0 raw3429step0Labels permutation146 permutation2
    mixedMoment B raw3429step1 raw3429step1Labels = mixedMoment B raw3429step2 raw3429step2Labels := by
      have ha : raw3429step2 = -raw3429step1 := by apply Matrix.ext; change ∀ i j, raw3429step2 i j = -(raw3429step1 i j); unfold raw3429step2 raw3429step1; decide +kernel
      have hl : raw3429step2Labels = raw3429step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5486 node5486Labels := by rfl

def raw3430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw3430Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw3430step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3430step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3430step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3430step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3430step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3430 raw3430Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw3430 raw3430Labels = mixedMoment B raw3430step0 raw3430step0Labels := by
      have hz : ∀ j, raw3430 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3430step0 = (fun i j => raw3430 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3430step0 raw3430; decide +kernel
      have hl : raw3430step0Labels = raw3430Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3430 raw3430Labels permutation346 hz
    mixedMoment B raw3430step0 raw3430step0Labels = mixedMoment B raw3430step1 raw3430step1Labels := by
      have ha : raw3430step1 = (fun i j => raw3430step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3430step1 raw3430step0; decide +kernel
      have hl : raw3430step1Labels = raw3430step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3430step0 raw3430step0Labels permutation150 permutation2
    mixedMoment B raw3430step1 raw3430step1Labels = mixedMoment B raw3430step2 raw3430step2Labels := by
      have ha : raw3430step2 = -raw3430step1 := by apply Matrix.ext; change ∀ i j, raw3430step2 i j = -(raw3430step1 i j); unfold raw3430step2 raw3430step1; decide +kernel
      have hl : raw3430step2Labels = raw3430step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw3431 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3431Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 0, 0], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3431step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3431step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 0, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3431step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3431step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3431step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3431step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw3431step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical3431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3431 raw3431Labels = mixedMoment B node4093 node4093Labels := by
  calc
    mixedMoment B raw3431 raw3431Labels = mixedMoment B raw3431step0 raw3431step0Labels := by
      have hz : ∀ j, raw3431 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3431step0 = (fun i j => raw3431 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3431step0 raw3431; decide +kernel
      have hl : raw3431step0Labels = raw3431Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3431 raw3431Labels permutation434 hz
    mixedMoment B raw3431step0 raw3431step0Labels = mixedMoment B raw3431step1 raw3431step1Labels := by
      have hz : ∀ j, raw3431step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3431step1 = (fun i j => raw3431step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3431step1 raw3431step0; decide +kernel
      have hl : raw3431step1Labels = raw3431step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3431step0 raw3431step0Labels permutation80 hz
    mixedMoment B raw3431step1 raw3431step1Labels = mixedMoment B raw3431step2 raw3431step2Labels := by
      have hz : ∀ j, raw3431step1 (permutation8 0) j = 0 := by decide +kernel
      have ha : raw3431step2 = (fun i j => raw3431step1 (permutation8 i.succ) j) := by apply Matrix.ext; unfold raw3431step2 raw3431step1; decide +kernel
      have hl : raw3431step2Labels = raw3431step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3431step1 raw3431step1Labels permutation8 hz
    mixedMoment B raw3431step2 raw3431step2Labels = mixedMoment B raw3431step3 raw3431step3Labels := by
      have hz : ∀ i, raw3431step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3431step3 = (fun i j => raw3431step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3431step3 raw3431step2; decide +kernel
      have hl : raw3431step3Labels = (fun j => raw3431step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3431step2 raw3431step2Labels permutation6 hz
    _ = mixedMoment B node4093 node4093Labels := by rfl

def raw3432 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3432Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3432step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3432step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3432step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3432step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3432step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw3432step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical3432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3432 raw3432Labels = mixedMoment B node4096 node4096Labels := by
  calc
    mixedMoment B raw3432 raw3432Labels = mixedMoment B raw3432step0 raw3432step0Labels := by
      have hz : ∀ j, raw3432 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3432step0 = (fun i j => raw3432 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3432step0 raw3432; decide +kernel
      have hl : raw3432step0Labels = raw3432Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3432 raw3432Labels permutation434 hz
    mixedMoment B raw3432step0 raw3432step0Labels = mixedMoment B raw3432step1 raw3432step1Labels := by
      have hz : ∀ j, raw3432step0 (permutation32 0) j = 0 := by decide +kernel
      have ha : raw3432step1 = (fun i j => raw3432step0 (permutation32 i.succ) j) := by apply Matrix.ext; unfold raw3432step1 raw3432step0; decide +kernel
      have hl : raw3432step1Labels = raw3432step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3432step0 raw3432step0Labels permutation32 hz
    mixedMoment B raw3432step1 raw3432step1Labels = mixedMoment B raw3432step2 raw3432step2Labels := by
      have hz : ∀ i, raw3432step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3432step2 = (fun i j => raw3432step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3432step2 raw3432step1; decide +kernel
      have hl : raw3432step2Labels = (fun j => raw3432step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3432step1 raw3432step1Labels permutation6 hz
    _ = mixedMoment B node4096 node4096Labels := by rfl

def raw3433 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3433Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3433step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3433step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3433step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3433step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3433step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw3433step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical3433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3433 raw3433Labels = mixedMoment B node4096 node4096Labels := by
  calc
    mixedMoment B raw3433 raw3433Labels = mixedMoment B raw3433step0 raw3433step0Labels := by
      have hz : ∀ j, raw3433 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3433step0 = (fun i j => raw3433 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3433step0 raw3433; decide +kernel
      have hl : raw3433step0Labels = raw3433Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3433 raw3433Labels permutation346 hz
    mixedMoment B raw3433step0 raw3433step0Labels = mixedMoment B raw3433step1 raw3433step1Labels := by
      have hz : ∀ j, raw3433step0 (permutation32 0) j = 0 := by decide +kernel
      have ha : raw3433step1 = (fun i j => raw3433step0 (permutation32 i.succ) j) := by apply Matrix.ext; unfold raw3433step1 raw3433step0; decide +kernel
      have hl : raw3433step1Labels = raw3433step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3433step0 raw3433step0Labels permutation32 hz
    mixedMoment B raw3433step1 raw3433step1Labels = mixedMoment B raw3433step2 raw3433step2Labels := by
      have hz : ∀ i, raw3433step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3433step2 = (fun i j => raw3433step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3433step2 raw3433step1; decide +kernel
      have hl : raw3433step2Labels = (fun j => raw3433step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3433step1 raw3433step1Labels permutation6 hz
    _ = mixedMoment B node4096 node4096Labels := by rfl

def raw3434 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0]]
def raw3434Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3434step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0]]
def raw3434step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3434step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw3434step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3434step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 1, 0], ![1, -1, 0]]
def raw3434step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3434step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-1, 1, 0], ![1, -1, 0]]
def raw3434step3Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3434step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]
def raw3434step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical3434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3434 raw3434Labels = mixedMoment B node4097 node4097Labels := by
  calc
    mixedMoment B raw3434 raw3434Labels = mixedMoment B raw3434step0 raw3434step0Labels := by
      have hz : ∀ j, raw3434 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3434step0 = (fun i j => raw3434 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3434step0 raw3434; decide +kernel
      have hl : raw3434step0Labels = raw3434Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3434 raw3434Labels permutation520 hz
    mixedMoment B raw3434step0 raw3434step0Labels = mixedMoment B raw3434step1 raw3434step1Labels := by
      have hz : ∀ j, raw3434step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw3434step1 = (fun i j => raw3434step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw3434step1 raw3434step0; decide +kernel
      have hl : raw3434step1Labels = raw3434step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3434step0 raw3434step0Labels permutation104 hz
    mixedMoment B raw3434step1 raw3434step1Labels = mixedMoment B raw3434step2 raw3434step2Labels := by
      have hz : ∀ j, raw3434step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw3434step2 = (fun i j => raw3434step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw3434step2 raw3434step1; decide +kernel
      have hl : raw3434step2Labels = raw3434step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3434step1 raw3434step1Labels permutation20 hz
    mixedMoment B raw3434step2 raw3434step2Labels = mixedMoment B raw3434step3 raw3434step3Labels := by
      have hz : ∀ j, raw3434step2 (permutation2 0) j = 0 := by decide +kernel
      have ha : raw3434step3 = (fun i j => raw3434step2 (permutation2 i.succ) j) := by apply Matrix.ext; unfold raw3434step3 raw3434step2; decide +kernel
      have hl : raw3434step3Labels = raw3434step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3434step2 raw3434step2Labels permutation2 hz
    mixedMoment B raw3434step3 raw3434step3Labels = mixedMoment B raw3434step4 raw3434step4Labels := by
      have hz : ∀ i, raw3434step3 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3434step4 = (fun i j => raw3434step3 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3434step4 raw3434step3; decide +kernel
      have hl : raw3434step4Labels = (fun j => raw3434step3Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3434step3 raw3434step3Labels permutation6 hz
    _ = mixedMoment B node4097 node4097Labels := by rfl

def raw3435 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0]]
def raw3435Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0]]
def raw3435step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3435step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw3435step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3435step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 0, 0], ![-1, 1, 0], ![1, -1, 0]]
def raw3435step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3435step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-1, 1, 0], ![1, -1, 0]]
def raw3435step3Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3435step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]
def raw3435step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical3435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3435 raw3435Labels = mixedMoment B node4097 node4097Labels := by
  calc
    mixedMoment B raw3435 raw3435Labels = mixedMoment B raw3435step0 raw3435step0Labels := by
      have hz : ∀ j, raw3435 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw3435step0 = (fun i j => raw3435 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw3435step0 raw3435; decide +kernel
      have hl : raw3435step0Labels = raw3435Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3435 raw3435Labels permutation590 hz
    mixedMoment B raw3435step0 raw3435step0Labels = mixedMoment B raw3435step1 raw3435step1Labels := by
      have hz : ∀ j, raw3435step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw3435step1 = (fun i j => raw3435step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw3435step1 raw3435step0; decide +kernel
      have hl : raw3435step1Labels = raw3435step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3435step0 raw3435step0Labels permutation104 hz
    mixedMoment B raw3435step1 raw3435step1Labels = mixedMoment B raw3435step2 raw3435step2Labels := by
      have hz : ∀ j, raw3435step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw3435step2 = (fun i j => raw3435step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw3435step2 raw3435step1; decide +kernel
      have hl : raw3435step2Labels = raw3435step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3435step1 raw3435step1Labels permutation20 hz
    mixedMoment B raw3435step2 raw3435step2Labels = mixedMoment B raw3435step3 raw3435step3Labels := by
      have hz : ∀ j, raw3435step2 (permutation2 0) j = 0 := by decide +kernel
      have ha : raw3435step3 = (fun i j => raw3435step2 (permutation2 i.succ) j) := by apply Matrix.ext; unfold raw3435step3 raw3435step2; decide +kernel
      have hl : raw3435step3Labels = raw3435step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3435step2 raw3435step2Labels permutation2 hz
    mixedMoment B raw3435step3 raw3435step3Labels = mixedMoment B raw3435step4 raw3435step4Labels := by
      have hz : ∀ i, raw3435step3 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3435step4 = (fun i j => raw3435step3 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3435step4 raw3435step3; decide +kernel
      have hl : raw3435step4Labels = (fun j => raw3435step3Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3435step3 raw3435step3Labels permutation6 hz
    _ = mixedMoment B node4097 node4097Labels := by rfl

def raw3436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3436Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3436step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3436step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3436step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]
def raw3436step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3436step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw3436step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical3436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3436 raw3436Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw3436 raw3436Labels = mixedMoment B raw3436step0 raw3436step0Labels := by
      have hz : ∀ j, raw3436 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3436step0 = (fun i j => raw3436 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3436step0 raw3436; decide +kernel
      have hl : raw3436step0Labels = raw3436Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3436 raw3436Labels permutation434 hz
    mixedMoment B raw3436step0 raw3436step0Labels = mixedMoment B raw3436step1 raw3436step1Labels := by
      have hz : ∀ i, raw3436step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3436step1 = (fun i j => raw3436step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3436step1 raw3436step0; decide +kernel
      have hl : raw3436step1Labels = (fun j => raw3436step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3436step0 raw3436step0Labels permutation6 hz
    mixedMoment B raw3436step1 raw3436step1Labels = mixedMoment B raw3436step2 raw3436step2Labels := by
      have ha : raw3436step2 = (fun i j => raw3436step1 (permutation56 i) (permutation0 j)) := by apply Matrix.ext; unfold raw3436step2 raw3436step1; decide +kernel
      have hl : raw3436step2Labels = raw3436step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3436step1 raw3436step1Labels permutation56 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw3437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3437Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3437step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![-1, 1], ![1, -1], ![1, -1]]
def raw3437step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3437step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw3437step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical3437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3437 raw3437Labels = mixedMoment B node4095 node4095Labels := by
  calc
    mixedMoment B raw3437 raw3437Labels = mixedMoment B raw3437step0 raw3437step0Labels := by
      have hz : ∀ i, raw3437 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3437step0 = (fun i j => raw3437 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3437step0 raw3437; decide +kernel
      have hl : raw3437step0Labels = (fun j => raw3437Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3437 raw3437Labels permutation6 hz
    mixedMoment B raw3437step0 raw3437step0Labels = mixedMoment B raw3437step1 raw3437step1Labels := by
      have ha : raw3437step1 = (fun i j => raw3437step0 (permutation158 i) (permutation0 j)) := by apply Matrix.ext; unfold raw3437step1 raw3437step0; decide +kernel
      have hl : raw3437step1Labels = raw3437step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3437step0 raw3437step0Labels permutation158 permutation0
    _ = mixedMoment B node4095 node4095Labels := by rfl

def raw3438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0]]
def raw3438Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3438step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw3438step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3438step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3438step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3438step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw3438step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical3438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3438 raw3438Labels = mixedMoment B node4096 node4096Labels := by
  calc
    mixedMoment B raw3438 raw3438Labels = mixedMoment B raw3438step0 raw3438step0Labels := by
      have hz : ∀ j, raw3438 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3438step0 = (fun i j => raw3438 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3438step0 raw3438; decide +kernel
      have hl : raw3438step0Labels = raw3438Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3438 raw3438Labels permutation520 hz
    mixedMoment B raw3438step0 raw3438step0Labels = mixedMoment B raw3438step1 raw3438step1Labels := by
      have hz : ∀ j, raw3438step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw3438step1 = (fun i j => raw3438step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw3438step1 raw3438step0; decide +kernel
      have hl : raw3438step1Labels = raw3438step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3438step0 raw3438step0Labels permutation104 hz
    mixedMoment B raw3438step1 raw3438step1Labels = mixedMoment B raw3438step2 raw3438step2Labels := by
      have hz : ∀ i, raw3438step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3438step2 = (fun i j => raw3438step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3438step2 raw3438step1; decide +kernel
      have hl : raw3438step2Labels = (fun j => raw3438step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3438step1 raw3438step1Labels permutation6 hz
    _ = mixedMoment B node4096 node4096Labels := by rfl

def raw3439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0]]
def raw3439Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3439step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw3439step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3439step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3439step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3439step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw3439step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical3439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3439 raw3439Labels = mixedMoment B node4096 node4096Labels := by
  calc
    mixedMoment B raw3439 raw3439Labels = mixedMoment B raw3439step0 raw3439step0Labels := by
      have hz : ∀ j, raw3439 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw3439step0 = (fun i j => raw3439 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw3439step0 raw3439; decide +kernel
      have hl : raw3439step0Labels = raw3439Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3439 raw3439Labels permutation590 hz
    mixedMoment B raw3439step0 raw3439step0Labels = mixedMoment B raw3439step1 raw3439step1Labels := by
      have hz : ∀ j, raw3439step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw3439step1 = (fun i j => raw3439step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw3439step1 raw3439step0; decide +kernel
      have hl : raw3439step1Labels = raw3439step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3439step0 raw3439step0Labels permutation104 hz
    mixedMoment B raw3439step1 raw3439step1Labels = mixedMoment B raw3439step2 raw3439step2Labels := by
      have hz : ∀ i, raw3439step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3439step2 = (fun i j => raw3439step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3439step2 raw3439step1; decide +kernel
      have hl : raw3439step2Labels = (fun j => raw3439step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3439step1 raw3439step1Labels permutation6 hz
    _ = mixedMoment B node4096 node4096Labels := by rfl

def raw3440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3440Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3440step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3440step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]
def raw3440step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3440step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw3440step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical3440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3440 raw3440Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw3440 raw3440Labels = mixedMoment B raw3440step0 raw3440step0Labels := by
      have hz : ∀ j, raw3440 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3440step0 = (fun i j => raw3440 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3440step0 raw3440; decide +kernel
      have hl : raw3440step0Labels = raw3440Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3440 raw3440Labels permutation346 hz
    mixedMoment B raw3440step0 raw3440step0Labels = mixedMoment B raw3440step1 raw3440step1Labels := by
      have hz : ∀ i, raw3440step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3440step1 = (fun i j => raw3440step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3440step1 raw3440step0; decide +kernel
      have hl : raw3440step1Labels = (fun j => raw3440step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3440step0 raw3440step0Labels permutation6 hz
    mixedMoment B raw3440step1 raw3440step1Labels = mixedMoment B raw3440step2 raw3440step2Labels := by
      have ha : raw3440step2 = (fun i j => raw3440step1 (permutation56 i) (permutation0 j)) := by apply Matrix.ext; unfold raw3440step2 raw3440step1; decide +kernel
      have hl : raw3440step2Labels = raw3440step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3440step1 raw3440step1Labels permutation56 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw3441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3441Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3441step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw3441step0Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical3441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3441 raw3441Labels = mixedMoment B node4095 node4095Labels := by
  calc
    mixedMoment B raw3441 raw3441Labels = mixedMoment B raw3441step0 raw3441step0Labels := by
      have hz : ∀ i, raw3441 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3441step0 = (fun i j => raw3441 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3441step0 raw3441; decide +kernel
      have hl : raw3441step0Labels = (fun j => raw3441Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3441 raw3441Labels permutation6 hz
    _ = mixedMoment B node4095 node4095Labels := by rfl

def raw3442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw3442Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3442step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3442step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3442step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3442step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw3442step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical3442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3442 raw3442Labels = mixedMoment B node4096 node4096Labels := by
  calc
    mixedMoment B raw3442 raw3442Labels = mixedMoment B raw3442step0 raw3442step0Labels := by
      have hz : ∀ j, raw3442 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw3442step0 = (fun i j => raw3442 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw3442step0 raw3442; decide +kernel
      have hl : raw3442step0Labels = raw3442Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3442 raw3442Labels permutation520 hz
    mixedMoment B raw3442step0 raw3442step0Labels = mixedMoment B raw3442step1 raw3442step1Labels := by
      have hz : ∀ j, raw3442step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3442step1 = (fun i j => raw3442step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3442step1 raw3442step0; decide +kernel
      have hl : raw3442step1Labels = raw3442step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3442step0 raw3442step0Labels permutation80 hz
    mixedMoment B raw3442step1 raw3442step1Labels = mixedMoment B raw3442step2 raw3442step2Labels := by
      have hz : ∀ i, raw3442step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3442step2 = (fun i j => raw3442step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3442step2 raw3442step1; decide +kernel
      have hl : raw3442step2Labels = (fun j => raw3442step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3442step1 raw3442step1Labels permutation6 hz
    _ = mixedMoment B node4096 node4096Labels := by rfl

def raw3443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw3443Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3443step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3443step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3443step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3443step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw3443step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical3443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3443 raw3443Labels = mixedMoment B node4096 node4096Labels := by
  calc
    mixedMoment B raw3443 raw3443Labels = mixedMoment B raw3443step0 raw3443step0Labels := by
      have hz : ∀ j, raw3443 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw3443step0 = (fun i j => raw3443 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw3443step0 raw3443; decide +kernel
      have hl : raw3443step0Labels = raw3443Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3443 raw3443Labels permutation590 hz
    mixedMoment B raw3443step0 raw3443step0Labels = mixedMoment B raw3443step1 raw3443step1Labels := by
      have hz : ∀ j, raw3443step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3443step1 = (fun i j => raw3443step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3443step1 raw3443step0; decide +kernel
      have hl : raw3443step1Labels = raw3443step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3443step0 raw3443step0Labels permutation80 hz
    mixedMoment B raw3443step1 raw3443step1Labels = mixedMoment B raw3443step2 raw3443step2Labels := by
      have hz : ∀ i, raw3443step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3443step2 = (fun i j => raw3443step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3443step2 raw3443step1; decide +kernel
      have hl : raw3443step2Labels = (fun j => raw3443step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3443step1 raw3443step1Labels permutation6 hz
    _ = mixedMoment B node4096 node4096Labels := by rfl

def raw3444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw3444Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3444step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw3444step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3444step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0]]
def raw3444step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3444step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![2, -2], ![1, -1]]
def raw3444step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3444step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw3444step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical3444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3444 raw3444Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw3444 raw3444Labels = mixedMoment B raw3444step0 raw3444step0Labels := by
      have hz : ∀ j, raw3444 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3444step0 = (fun i j => raw3444 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3444step0 raw3444; decide +kernel
      have hl : raw3444step0Labels = raw3444Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3444 raw3444Labels permutation434 hz
    mixedMoment B raw3444step0 raw3444step0Labels = mixedMoment B raw3444step1 raw3444step1Labels := by
      have hz : ∀ j, raw3444step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3444step1 = (fun i j => raw3444step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3444step1 raw3444step0; decide +kernel
      have hl : raw3444step1Labels = raw3444step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3444step0 raw3444step0Labels permutation80 hz
    mixedMoment B raw3444step1 raw3444step1Labels = mixedMoment B raw3444step2 raw3444step2Labels := by
      have hz : ∀ i, raw3444step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3444step2 = (fun i j => raw3444step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3444step2 raw3444step1; decide +kernel
      have hl : raw3444step2Labels = (fun j => raw3444step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3444step1 raw3444step1Labels permutation6 hz
    mixedMoment B raw3444step2 raw3444step2Labels = mixedMoment B raw3444step3 raw3444step3Labels := by
      have ha : raw3444step3 = (fun i j => raw3444step2 (permutation15 i) (permutation0 j)) := by apply Matrix.ext; unfold raw3444step3 raw3444step2; decide +kernel
      have hl : raw3444step3Labels = raw3444step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3444step2 raw3444step2Labels permutation15 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw3445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw3445Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw3445step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3445step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1]]
def raw3445step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3445step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw3445step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3445step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw3445step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical3445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3445 raw3445Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw3445 raw3445Labels = mixedMoment B raw3445step0 raw3445step0Labels := by
      have hz : ∀ j, raw3445 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3445step0 = (fun i j => raw3445 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3445step0 raw3445; decide +kernel
      have hl : raw3445step0Labels = raw3445Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3445 raw3445Labels permutation434 hz
    mixedMoment B raw3445step0 raw3445step0Labels = mixedMoment B raw3445step1 raw3445step1Labels := by
      have hz : ∀ i, raw3445step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3445step1 = (fun i j => raw3445step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3445step1 raw3445step0; decide +kernel
      have hl : raw3445step1Labels = (fun j => raw3445step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3445step0 raw3445step0Labels permutation6 hz
    mixedMoment B raw3445step1 raw3445step1Labels = mixedMoment B raw3445step2 raw3445step2Labels := by
      have ha : raw3445step2 = (fun i j => raw3445step1 (permutation122 i) (permutation0 j)) := by apply Matrix.ext; unfold raw3445step2 raw3445step1; decide +kernel
      have hl : raw3445step2Labels = raw3445step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3445step1 raw3445step1Labels permutation122 permutation0
    mixedMoment B raw3445step2 raw3445step2Labels = mixedMoment B raw3445step3 raw3445step3Labels := by
      have ha : raw3445step3 = -raw3445step2 := by apply Matrix.ext; change ∀ i j, raw3445step3 i j = -(raw3445step2 i j); unfold raw3445step3 raw3445step2; decide +kernel
      have hl : raw3445step3Labels = raw3445step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw3446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw3446Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw3446step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3446step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![2, -2], ![1, -1]]
def raw3446step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3446step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw3446step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3446step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw3446step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical3446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3446 raw3446Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw3446 raw3446Labels = mixedMoment B raw3446step0 raw3446step0Labels := by
      have hz : ∀ j, raw3446 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3446step0 = (fun i j => raw3446 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3446step0 raw3446; decide +kernel
      have hl : raw3446step0Labels = raw3446Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3446 raw3446Labels permutation346 hz
    mixedMoment B raw3446step0 raw3446step0Labels = mixedMoment B raw3446step1 raw3446step1Labels := by
      have hz : ∀ i, raw3446step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3446step1 = (fun i j => raw3446step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3446step1 raw3446step0; decide +kernel
      have hl : raw3446step1Labels = (fun j => raw3446step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3446step0 raw3446step0Labels permutation6 hz
    mixedMoment B raw3446step1 raw3446step1Labels = mixedMoment B raw3446step2 raw3446step2Labels := by
      have ha : raw3446step2 = (fun i j => raw3446step1 (permutation122 i) (permutation0 j)) := by apply Matrix.ext; unfold raw3446step2 raw3446step1; decide +kernel
      have hl : raw3446step2Labels = raw3446step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3446step1 raw3446step1Labels permutation122 permutation0
    mixedMoment B raw3446step2 raw3446step2Labels = mixedMoment B raw3446step3 raw3446step3Labels := by
      have ha : raw3446step3 = -raw3446step2 := by apply Matrix.ext; change ∀ i j, raw3446step3 i j = -(raw3446step2 i j); unfold raw3446step3 raw3446step2; decide +kernel
      have hl : raw3446step3Labels = raw3446step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw3447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0]]
def raw3447Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3447step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0]]
def raw3447step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3447step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw3447step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3447step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0]]
def raw3447step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3447step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![2, -2]]
def raw3447step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3447step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![2, -2], ![-1, 1], ![-1, 1]]
def raw3447step4Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3447step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw3447step5Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical3447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3447 raw3447Labels = mixedMoment B node4093 node4093Labels := by
  calc
    mixedMoment B raw3447 raw3447Labels = mixedMoment B raw3447step0 raw3447step0Labels := by
      have hz : ∀ j, raw3447 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw3447step0 = (fun i j => raw3447 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw3447step0 raw3447; decide +kernel
      have hl : raw3447step0Labels = raw3447Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3447 raw3447Labels permutation590 hz
    mixedMoment B raw3447step0 raw3447step0Labels = mixedMoment B raw3447step1 raw3447step1Labels := by
      have hz : ∀ j, raw3447step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw3447step1 = (fun i j => raw3447step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw3447step1 raw3447step0; decide +kernel
      have hl : raw3447step1Labels = raw3447step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3447step0 raw3447step0Labels permutation104 hz
    mixedMoment B raw3447step1 raw3447step1Labels = mixedMoment B raw3447step2 raw3447step2Labels := by
      have hz : ∀ j, raw3447step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw3447step2 = (fun i j => raw3447step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw3447step2 raw3447step1; decide +kernel
      have hl : raw3447step2Labels = raw3447step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3447step1 raw3447step1Labels permutation20 hz
    mixedMoment B raw3447step2 raw3447step2Labels = mixedMoment B raw3447step3 raw3447step3Labels := by
      have hz : ∀ i, raw3447step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3447step3 = (fun i j => raw3447step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3447step3 raw3447step2; decide +kernel
      have hl : raw3447step3Labels = (fun j => raw3447step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3447step2 raw3447step2Labels permutation6 hz
    mixedMoment B raw3447step3 raw3447step3Labels = mixedMoment B raw3447step4 raw3447step4Labels := by
      have ha : raw3447step4 = (fun i j => raw3447step3 (permutation6 i) (permutation0 j)) := by apply Matrix.ext; unfold raw3447step4 raw3447step3; decide +kernel
      have hl : raw3447step4Labels = raw3447step3Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3447step3 raw3447step3Labels permutation6 permutation0
    mixedMoment B raw3447step4 raw3447step4Labels = mixedMoment B raw3447step5 raw3447step5Labels := by
      have ha : raw3447step5 = -raw3447step4 := by apply Matrix.ext; change ∀ i j, raw3447step5 i j = -(raw3447step4 i j); unfold raw3447step5 raw3447step4; decide +kernel
      have hl : raw3447step5Labels = raw3447step4Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4093 node4093Labels := by rfl

def raw3448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3448Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3448step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3448step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3448step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3448step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3448step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![2, -2]]
def raw3448step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3448step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw3448step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical3448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3448 raw3448Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw3448 raw3448Labels = mixedMoment B raw3448step0 raw3448step0Labels := by
      have hz : ∀ j, raw3448 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3448step0 = (fun i j => raw3448 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3448step0 raw3448; decide +kernel
      have hl : raw3448step0Labels = raw3448Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3448 raw3448Labels permutation434 hz
    mixedMoment B raw3448step0 raw3448step0Labels = mixedMoment B raw3448step1 raw3448step1Labels := by
      have hz : ∀ j, raw3448step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3448step1 = (fun i j => raw3448step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3448step1 raw3448step0; decide +kernel
      have hl : raw3448step1Labels = raw3448step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3448step0 raw3448step0Labels permutation80 hz
    mixedMoment B raw3448step1 raw3448step1Labels = mixedMoment B raw3448step2 raw3448step2Labels := by
      have hz : ∀ i, raw3448step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3448step2 = (fun i j => raw3448step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3448step2 raw3448step1; decide +kernel
      have hl : raw3448step2Labels = (fun j => raw3448step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3448step1 raw3448step1Labels permutation6 hz
    mixedMoment B raw3448step2 raw3448step2Labels = mixedMoment B raw3448step3 raw3448step3Labels := by
      have ha : raw3448step3 = (fun i j => raw3448step2 (permutation14 i) (permutation0 j)) := by apply Matrix.ext; unfold raw3448step3 raw3448step2; decide +kernel
      have hl : raw3448step3Labels = raw3448step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3448step2 raw3448step2Labels permutation14 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw3449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3449Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3449step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3449step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3449step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]
def raw3449step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3449step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw3449step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3449step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw3449step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical3449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3449 raw3449Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw3449 raw3449Labels = mixedMoment B raw3449step0 raw3449step0Labels := by
      have hz : ∀ j, raw3449 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3449step0 = (fun i j => raw3449 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3449step0 raw3449; decide +kernel
      have hl : raw3449step0Labels = raw3449Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3449 raw3449Labels permutation434 hz
    mixedMoment B raw3449step0 raw3449step0Labels = mixedMoment B raw3449step1 raw3449step1Labels := by
      have hz : ∀ i, raw3449step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3449step1 = (fun i j => raw3449step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3449step1 raw3449step0; decide +kernel
      have hl : raw3449step1Labels = (fun j => raw3449step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3449step0 raw3449step0Labels permutation6 hz
    mixedMoment B raw3449step1 raw3449step1Labels = mixedMoment B raw3449step2 raw3449step2Labels := by
      have ha : raw3449step2 = (fun i j => raw3449step1 (permutation146 i) (permutation0 j)) := by apply Matrix.ext; unfold raw3449step2 raw3449step1; decide +kernel
      have hl : raw3449step2Labels = raw3449step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3449step1 raw3449step1Labels permutation146 permutation0
    mixedMoment B raw3449step2 raw3449step2Labels = mixedMoment B raw3449step3 raw3449step3Labels := by
      have ha : raw3449step3 = -raw3449step2 := by apply Matrix.ext; change ∀ i j, raw3449step3 i j = -(raw3449step2 i j); unfold raw3449step3 raw3449step2; decide +kernel
      have hl : raw3449step3Labels = raw3449step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw3450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3450Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw3450step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3450step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![-1, 1], ![1, -1], ![2, -2]]
def raw3450step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3450step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw3450step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3450step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw3450step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical3450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3450 raw3450Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw3450 raw3450Labels = mixedMoment B raw3450step0 raw3450step0Labels := by
      have hz : ∀ j, raw3450 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3450step0 = (fun i j => raw3450 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3450step0 raw3450; decide +kernel
      have hl : raw3450step0Labels = raw3450Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3450 raw3450Labels permutation346 hz
    mixedMoment B raw3450step0 raw3450step0Labels = mixedMoment B raw3450step1 raw3450step1Labels := by
      have hz : ∀ i, raw3450step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3450step1 = (fun i j => raw3450step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3450step1 raw3450step0; decide +kernel
      have hl : raw3450step1Labels = (fun j => raw3450step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3450step0 raw3450step0Labels permutation6 hz
    mixedMoment B raw3450step1 raw3450step1Labels = mixedMoment B raw3450step2 raw3450step2Labels := by
      have ha : raw3450step2 = (fun i j => raw3450step1 (permutation146 i) (permutation0 j)) := by apply Matrix.ext; unfold raw3450step2 raw3450step1; decide +kernel
      have hl : raw3450step2Labels = raw3450step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3450step1 raw3450step1Labels permutation146 permutation0
    mixedMoment B raw3450step2 raw3450step2Labels = mixedMoment B raw3450step3 raw3450step3Labels := by
      have ha : raw3450step3 = -raw3450step2 := by apply Matrix.ext; change ∀ i j, raw3450step3 i j = -(raw3450step2 i j); unfold raw3450step3 raw3450step2; decide +kernel
      have hl : raw3450step3Labels = raw3450step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw3451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3451Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3451step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3451step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3451step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3451step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3451step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -2, 3], ![-3, 3, 0]]
def raw3451step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3451step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3451step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3451step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3451step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3451 raw3451Labels = mixedMoment B node4844 node4844Labels := by
  calc
    mixedMoment B raw3451 raw3451Labels = mixedMoment B raw3451step0 raw3451step0Labels := by
      have hz : ∀ j, raw3451 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3451step0 = (fun i j => raw3451 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3451step0 raw3451; decide +kernel
      have hl : raw3451step0Labels = raw3451Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3451 raw3451Labels permutation434 hz
    mixedMoment B raw3451step0 raw3451step0Labels = mixedMoment B raw3451step1 raw3451step1Labels := by
      have hz : ∀ j, raw3451step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3451step1 = (fun i j => raw3451step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3451step1 raw3451step0; decide +kernel
      have hl : raw3451step1Labels = raw3451step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3451step0 raw3451step0Labels permutation80 hz
    mixedMoment B raw3451step1 raw3451step1Labels = mixedMoment B raw3451step2 raw3451step2Labels := by
      have ha : raw3451step2 = (fun i j => raw3451step1 (permutation22 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3451step2 raw3451step1; decide +kernel
      have hl : raw3451step2Labels = raw3451step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3451step1 raw3451step1Labels permutation22 permutation4
    mixedMoment B raw3451step2 raw3451step2Labels = mixedMoment B raw3451step3 raw3451step3Labels := by
      have ha : raw3451step3 = -raw3451step2 := by apply Matrix.ext; change ∀ i j, raw3451step3 i j = -(raw3451step2 i j); unfold raw3451step3 raw3451step2; decide +kernel
      have hl : raw3451step3Labels = raw3451step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3451step3 raw3451step3Labels = mixedMoment B raw3451step4 raw3451step4Labels := by
      have ha : raw3451step4 = raw3451step3 := by apply Matrix.ext; unfold raw3451step4 raw3451step3; decide +kernel
      have hl : raw3451step3Labels = labelEmbedding7 ∘ raw3451step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3451step3 raw3451step3Labels raw3451step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4844 node4844Labels := by rfl

def raw3452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3452Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3452step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3452step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3452step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3452step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3452step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -2, 3], ![-3, 3, 0]]
def raw3452step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3452step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3452step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3452step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3452step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3452 raw3452Labels = mixedMoment B node4844 node4844Labels := by
  calc
    mixedMoment B raw3452 raw3452Labels = mixedMoment B raw3452step0 raw3452step0Labels := by
      have hz : ∀ j, raw3452 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3452step0 = (fun i j => raw3452 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3452step0 raw3452; decide +kernel
      have hl : raw3452step0Labels = raw3452Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3452 raw3452Labels permutation434 hz
    mixedMoment B raw3452step0 raw3452step0Labels = mixedMoment B raw3452step1 raw3452step1Labels := by
      have hz : ∀ j, raw3452step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3452step1 = (fun i j => raw3452step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3452step1 raw3452step0; decide +kernel
      have hl : raw3452step1Labels = raw3452step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3452step0 raw3452step0Labels permutation56 hz
    mixedMoment B raw3452step1 raw3452step1Labels = mixedMoment B raw3452step2 raw3452step2Labels := by
      have ha : raw3452step2 = (fun i j => raw3452step1 (permutation22 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3452step2 raw3452step1; decide +kernel
      have hl : raw3452step2Labels = raw3452step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3452step1 raw3452step1Labels permutation22 permutation4
    mixedMoment B raw3452step2 raw3452step2Labels = mixedMoment B raw3452step3 raw3452step3Labels := by
      have ha : raw3452step3 = -raw3452step2 := by apply Matrix.ext; change ∀ i j, raw3452step3 i j = -(raw3452step2 i j); unfold raw3452step3 raw3452step2; decide +kernel
      have hl : raw3452step3Labels = raw3452step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3452step3 raw3452step3Labels = mixedMoment B raw3452step4 raw3452step4Labels := by
      have ha : raw3452step4 = raw3452step3 := by apply Matrix.ext; unfold raw3452step4 raw3452step3; decide +kernel
      have hl : raw3452step3Labels = labelEmbedding7 ∘ raw3452step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3452step3 raw3452step3Labels raw3452step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4844 node4844Labels := by rfl

def raw3453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3453Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![-1, 1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3453step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3453step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 3, -3], ![3, -3, 0]]
def raw3453step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3453step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -2, 3], ![-3, 3, 0]]
def raw3453step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3453step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3453step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3453step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 2, -3], ![3, -3, 0]]
def raw3453step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3453 raw3453Labels = mixedMoment B node4844 node4844Labels := by
  calc
    mixedMoment B raw3453 raw3453Labels = mixedMoment B raw3453step0 raw3453step0Labels := by
      have hz : ∀ j, raw3453 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3453step0 = (fun i j => raw3453 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3453step0 raw3453; decide +kernel
      have hl : raw3453step0Labels = raw3453Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3453 raw3453Labels permutation346 hz
    mixedMoment B raw3453step0 raw3453step0Labels = mixedMoment B raw3453step1 raw3453step1Labels := by
      have hz : ∀ j, raw3453step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3453step1 = (fun i j => raw3453step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3453step1 raw3453step0; decide +kernel
      have hl : raw3453step1Labels = raw3453step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3453step0 raw3453step0Labels permutation56 hz
    mixedMoment B raw3453step1 raw3453step1Labels = mixedMoment B raw3453step2 raw3453step2Labels := by
      have ha : raw3453step2 = (fun i j => raw3453step1 (permutation22 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3453step2 raw3453step1; decide +kernel
      have hl : raw3453step2Labels = raw3453step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3453step1 raw3453step1Labels permutation22 permutation4
    mixedMoment B raw3453step2 raw3453step2Labels = mixedMoment B raw3453step3 raw3453step3Labels := by
      have ha : raw3453step3 = -raw3453step2 := by apply Matrix.ext; change ∀ i j, raw3453step3 i j = -(raw3453step2 i j); unfold raw3453step3 raw3453step2; decide +kernel
      have hl : raw3453step3Labels = raw3453step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3453step3 raw3453step3Labels = mixedMoment B raw3453step4 raw3453step4Labels := by
      have ha : raw3453step4 = raw3453step3 := by apply Matrix.ext; unfold raw3453step4 raw3453step3; decide +kernel
      have hl : raw3453step3Labels = labelEmbedding7 ∘ raw3453step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3453step3 raw3453step3Labels raw3453step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4844 node4844Labels := by rfl

def raw3454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 4, -3], ![3, -3, 0]]
def raw3454Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3454step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![-1, 4, -3], ![3, -3, 0]]
def raw3454step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3454step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![-1, 4, -3], ![3, -3, 0]]
def raw3454step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3454step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 4, -3], ![3, -3, 0]]
def raw3454step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3454step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![4, -1, -3], ![-1, -2, 3], ![-3, 3, 0]]
def raw3454step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3454step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 2, -3], ![3, -3, 0]]
def raw3454step4Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3454step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 2, -3], ![3, -3, 0]]
def raw3454step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3454 raw3454Labels = mixedMoment B node4508 node4508Labels := by
  calc
    mixedMoment B raw3454 raw3454Labels = mixedMoment B raw3454step0 raw3454step0Labels := by
      have hz : ∀ j, raw3454 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3454step0 = (fun i j => raw3454 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3454step0 raw3454; decide +kernel
      have hl : raw3454step0Labels = raw3454Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3454 raw3454Labels permutation434 hz
    mixedMoment B raw3454step0 raw3454step0Labels = mixedMoment B raw3454step1 raw3454step1Labels := by
      have hz : ∀ j, raw3454step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3454step1 = (fun i j => raw3454step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3454step1 raw3454step0; decide +kernel
      have hl : raw3454step1Labels = raw3454step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3454step0 raw3454step0Labels permutation80 hz
    mixedMoment B raw3454step1 raw3454step1Labels = mixedMoment B raw3454step2 raw3454step2Labels := by
      have hz : ∀ j, raw3454step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3454step2 = (fun i j => raw3454step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3454step2 raw3454step1; decide +kernel
      have hl : raw3454step2Labels = raw3454step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3454step1 raw3454step1Labels permutation14 hz
    mixedMoment B raw3454step2 raw3454step2Labels = mixedMoment B raw3454step3 raw3454step3Labels := by
      have ha : raw3454step3 = (fun i j => raw3454step2 (permutation4 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3454step3 raw3454step2; decide +kernel
      have hl : raw3454step3Labels = raw3454step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3454step2 raw3454step2Labels permutation4 permutation4
    mixedMoment B raw3454step3 raw3454step3Labels = mixedMoment B raw3454step4 raw3454step4Labels := by
      have ha : raw3454step4 = -raw3454step3 := by apply Matrix.ext; change ∀ i j, raw3454step4 i j = -(raw3454step3 i j); unfold raw3454step4 raw3454step3; decide +kernel
      have hl : raw3454step4Labels = raw3454step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3454step4 raw3454step4Labels = mixedMoment B raw3454step5 raw3454step5Labels := by
      have ha : raw3454step5 = raw3454step4 := by apply Matrix.ext; unfold raw3454step5 raw3454step4; decide +kernel
      have hl : raw3454step4Labels = labelEmbedding7 ∘ raw3454step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3454step4 raw3454step4Labels raw3454step5Labels labelEmbedding7 hl
    _ = mixedMoment B node4508 node4508Labels := by rfl

def raw3455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]
def raw3455Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3455step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]
def raw3455step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3455step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 0, 0], ![0, 3, -3], ![2, -2, 0]]
def raw3455step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3455step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 3, -3], ![2, -2, 0]]
def raw3455step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3455step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw3455step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3455step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![3, -2, -1]]
def raw3455step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3455 raw3455Labels = mixedMoment B node4899 node4899Labels := by
  calc
    mixedMoment B raw3455 raw3455Labels = mixedMoment B raw3455step0 raw3455step0Labels := by
      have hz : ∀ j, raw3455 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3455step0 = (fun i j => raw3455 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3455step0 raw3455; decide +kernel
      have hl : raw3455step0Labels = raw3455Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3455 raw3455Labels permutation434 hz
    mixedMoment B raw3455step0 raw3455step0Labels = mixedMoment B raw3455step1 raw3455step1Labels := by
      have hz : ∀ j, raw3455step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3455step1 = (fun i j => raw3455step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3455step1 raw3455step0; decide +kernel
      have hl : raw3455step1Labels = raw3455step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3455step0 raw3455step0Labels permutation80 hz
    mixedMoment B raw3455step1 raw3455step1Labels = mixedMoment B raw3455step2 raw3455step2Labels := by
      have hz : ∀ j, raw3455step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3455step2 = (fun i j => raw3455step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3455step2 raw3455step1; decide +kernel
      have hl : raw3455step2Labels = raw3455step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3455step1 raw3455step1Labels permutation14 hz
    mixedMoment B raw3455step2 raw3455step2Labels = mixedMoment B raw3455step3 raw3455step3Labels := by
      have ha : raw3455step3 = (fun i j => raw3455step2 (permutation5 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3455step3 raw3455step2; decide +kernel
      have hl : raw3455step3Labels = raw3455step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3455step2 raw3455step2Labels permutation5 permutation6
    mixedMoment B raw3455step3 raw3455step3Labels = mixedMoment B raw3455step4 raw3455step4Labels := by
      have ha : raw3455step4 = raw3455step3 := by apply Matrix.ext; unfold raw3455step4 raw3455step3; decide +kernel
      have hl : raw3455step3Labels = labelEmbedding9 ∘ raw3455step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3455step3 raw3455step3Labels raw3455step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4899 node4899Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
