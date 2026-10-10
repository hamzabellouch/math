import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw20352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20352Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20352step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20352step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20352step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20352step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20352step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20352step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20352 raw20352Labels = mixedMoment B node4551 node4551Labels := by
  calc
    mixedMoment B raw20352 raw20352Labels = mixedMoment B raw20352step0 raw20352step0Labels := by
      have hz : ∀ j, raw20352 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20352step0 = (fun i j => raw20352 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20352step0 raw20352; decide +kernel
      have hl : raw20352step0Labels = raw20352Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20352 raw20352Labels permutation434 hz
    mixedMoment B raw20352step0 raw20352step0Labels = mixedMoment B raw20352step1 raw20352step1Labels := by
      have ha : raw20352step1 = (fun i j => raw20352step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20352step1 raw20352step0; decide +kernel
      have hl : raw20352step1Labels = raw20352step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20352step0 raw20352step0Labels permutation38 permutation3
    mixedMoment B raw20352step1 raw20352step1Labels = mixedMoment B raw20352step2 raw20352step2Labels := by
      have ha : raw20352step2 = raw20352step1 := by apply Matrix.ext; unfold raw20352step2 raw20352step1; decide +kernel
      have hl : raw20352step1Labels = labelEmbedding6 ∘ raw20352step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20352step1 raw20352step1Labels raw20352step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4551 node4551Labels := by rfl

def raw20353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20353Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20353step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20353step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20353step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20353step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20353step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20353step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20353 raw20353Labels = mixedMoment B node4551 node4551Labels := by
  calc
    mixedMoment B raw20353 raw20353Labels = mixedMoment B raw20353step0 raw20353step0Labels := by
      have hz : ∀ j, raw20353 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20353step0 = (fun i j => raw20353 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20353step0 raw20353; decide +kernel
      have hl : raw20353step0Labels = raw20353Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20353 raw20353Labels permutation346 hz
    mixedMoment B raw20353step0 raw20353step0Labels = mixedMoment B raw20353step1 raw20353step1Labels := by
      have ha : raw20353step1 = (fun i j => raw20353step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20353step1 raw20353step0; decide +kernel
      have hl : raw20353step1Labels = raw20353step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20353step0 raw20353step0Labels permutation38 permutation3
    mixedMoment B raw20353step1 raw20353step1Labels = mixedMoment B raw20353step2 raw20353step2Labels := by
      have ha : raw20353step2 = raw20353step1 := by apply Matrix.ext; unfold raw20353step2 raw20353step1; decide +kernel
      have hl : raw20353step1Labels = labelEmbedding6 ∘ raw20353step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20353step1 raw20353step1Labels raw20353step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4551 node4551Labels := by rfl

def raw20354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20354Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20354step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20354step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20354step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20354step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20354step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20354step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20354step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20354step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20354 raw20354Labels = mixedMoment B node4183 node4183Labels := by
  calc
    mixedMoment B raw20354 raw20354Labels = mixedMoment B raw20354step0 raw20354step0Labels := by
      have hz : ∀ j, raw20354 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20354step0 = (fun i j => raw20354 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20354step0 raw20354; decide +kernel
      have hl : raw20354step0Labels = raw20354Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20354 raw20354Labels permutation434 hz
    mixedMoment B raw20354step0 raw20354step0Labels = mixedMoment B raw20354step1 raw20354step1Labels := by
      have hz : ∀ j, raw20354step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20354step1 = (fun i j => raw20354step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20354step1 raw20354step0; decide +kernel
      have hl : raw20354step1Labels = raw20354step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20354step0 raw20354step0Labels permutation56 hz
    mixedMoment B raw20354step1 raw20354step1Labels = mixedMoment B raw20354step2 raw20354step2Labels := by
      have ha : raw20354step2 = (fun i j => raw20354step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20354step2 raw20354step1; decide +kernel
      have hl : raw20354step2Labels = raw20354step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20354step1 raw20354step1Labels permutation8 permutation3
    mixedMoment B raw20354step2 raw20354step2Labels = mixedMoment B raw20354step3 raw20354step3Labels := by
      have ha : raw20354step3 = raw20354step2 := by apply Matrix.ext; unfold raw20354step3 raw20354step2; decide +kernel
      have hl : raw20354step2Labels = labelEmbedding6 ∘ raw20354step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20354step2 raw20354step2Labels raw20354step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4183 node4183Labels := by rfl

def raw20355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20355Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20355step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20355step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20355step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20355step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20355step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20355 raw20355Labels = mixedMoment B node4551 node4551Labels := by
  calc
    mixedMoment B raw20355 raw20355Labels = mixedMoment B raw20355step0 raw20355step0Labels := by
      have hz : ∀ j, raw20355 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20355step0 = (fun i j => raw20355 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20355step0 raw20355; decide +kernel
      have hl : raw20355step0Labels = raw20355Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20355 raw20355Labels permutation434 hz
    mixedMoment B raw20355step0 raw20355step0Labels = mixedMoment B raw20355step1 raw20355step1Labels := by
      have ha : raw20355step1 = (fun i j => raw20355step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20355step1 raw20355step0; decide +kernel
      have hl : raw20355step1Labels = raw20355step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20355step0 raw20355step0Labels permutation32 permutation3
    mixedMoment B raw20355step1 raw20355step1Labels = mixedMoment B raw20355step2 raw20355step2Labels := by
      have ha : raw20355step2 = raw20355step1 := by apply Matrix.ext; unfold raw20355step2 raw20355step1; decide +kernel
      have hl : raw20355step1Labels = labelEmbedding6 ∘ raw20355step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20355step1 raw20355step1Labels raw20355step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4551 node4551Labels := by rfl

def raw20356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20356Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20356step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20356step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20356step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20356step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20356step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20356step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20356 raw20356Labels = mixedMoment B node4551 node4551Labels := by
  calc
    mixedMoment B raw20356 raw20356Labels = mixedMoment B raw20356step0 raw20356step0Labels := by
      have hz : ∀ j, raw20356 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20356step0 = (fun i j => raw20356 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20356step0 raw20356; decide +kernel
      have hl : raw20356step0Labels = raw20356Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20356 raw20356Labels permutation265 hz
    mixedMoment B raw20356step0 raw20356step0Labels = mixedMoment B raw20356step1 raw20356step1Labels := by
      have ha : raw20356step1 = (fun i j => raw20356step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20356step1 raw20356step0; decide +kernel
      have hl : raw20356step1Labels = raw20356step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20356step0 raw20356step0Labels permutation38 permutation3
    mixedMoment B raw20356step1 raw20356step1Labels = mixedMoment B raw20356step2 raw20356step2Labels := by
      have ha : raw20356step2 = raw20356step1 := by apply Matrix.ext; unfold raw20356step2 raw20356step1; decide +kernel
      have hl : raw20356step1Labels = labelEmbedding6 ∘ raw20356step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20356step1 raw20356step1Labels raw20356step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4551 node4551Labels := by rfl

def raw20357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20357Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20357step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20357step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20357step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20357step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20357step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20357step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20357step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20357step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20357 raw20357Labels = mixedMoment B node4183 node4183Labels := by
  calc
    mixedMoment B raw20357 raw20357Labels = mixedMoment B raw20357step0 raw20357step0Labels := by
      have hz : ∀ j, raw20357 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20357step0 = (fun i j => raw20357 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20357step0 raw20357; decide +kernel
      have hl : raw20357step0Labels = raw20357Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20357 raw20357Labels permutation346 hz
    mixedMoment B raw20357step0 raw20357step0Labels = mixedMoment B raw20357step1 raw20357step1Labels := by
      have hz : ∀ j, raw20357step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20357step1 = (fun i j => raw20357step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20357step1 raw20357step0; decide +kernel
      have hl : raw20357step1Labels = raw20357step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20357step0 raw20357step0Labels permutation56 hz
    mixedMoment B raw20357step1 raw20357step1Labels = mixedMoment B raw20357step2 raw20357step2Labels := by
      have ha : raw20357step2 = (fun i j => raw20357step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20357step2 raw20357step1; decide +kernel
      have hl : raw20357step2Labels = raw20357step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20357step1 raw20357step1Labels permutation8 permutation3
    mixedMoment B raw20357step2 raw20357step2Labels = mixedMoment B raw20357step3 raw20357step3Labels := by
      have ha : raw20357step3 = raw20357step2 := by apply Matrix.ext; unfold raw20357step3 raw20357step2; decide +kernel
      have hl : raw20357step2Labels = labelEmbedding6 ∘ raw20357step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20357step2 raw20357step2Labels raw20357step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4183 node4183Labels := by rfl

def raw20358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20358Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20358step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20358step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20358step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20358step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20358step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20358 raw20358Labels = mixedMoment B node4551 node4551Labels := by
  calc
    mixedMoment B raw20358 raw20358Labels = mixedMoment B raw20358step0 raw20358step0Labels := by
      have hz : ∀ j, raw20358 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20358step0 = (fun i j => raw20358 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20358step0 raw20358; decide +kernel
      have hl : raw20358step0Labels = raw20358Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20358 raw20358Labels permutation346 hz
    mixedMoment B raw20358step0 raw20358step0Labels = mixedMoment B raw20358step1 raw20358step1Labels := by
      have ha : raw20358step1 = (fun i j => raw20358step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20358step1 raw20358step0; decide +kernel
      have hl : raw20358step1Labels = raw20358step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20358step0 raw20358step0Labels permutation32 permutation3
    mixedMoment B raw20358step1 raw20358step1Labels = mixedMoment B raw20358step2 raw20358step2Labels := by
      have ha : raw20358step2 = raw20358step1 := by apply Matrix.ext; unfold raw20358step2 raw20358step1; decide +kernel
      have hl : raw20358step1Labels = labelEmbedding6 ∘ raw20358step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20358step1 raw20358step1Labels raw20358step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4551 node4551Labels := by rfl

def raw20359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20359Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20359step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20359step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20359step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20359step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20359step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20359step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20359 raw20359Labels = mixedMoment B node4551 node4551Labels := by
  calc
    mixedMoment B raw20359 raw20359Labels = mixedMoment B raw20359step0 raw20359step0Labels := by
      have hz : ∀ j, raw20359 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20359step0 = (fun i j => raw20359 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20359step0 raw20359; decide +kernel
      have hl : raw20359step0Labels = raw20359Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20359 raw20359Labels permutation265 hz
    mixedMoment B raw20359step0 raw20359step0Labels = mixedMoment B raw20359step1 raw20359step1Labels := by
      have ha : raw20359step1 = (fun i j => raw20359step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20359step1 raw20359step0; decide +kernel
      have hl : raw20359step1Labels = raw20359step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20359step0 raw20359step0Labels permutation32 permutation3
    mixedMoment B raw20359step1 raw20359step1Labels = mixedMoment B raw20359step2 raw20359step2Labels := by
      have ha : raw20359step2 = raw20359step1 := by apply Matrix.ext; unfold raw20359step2 raw20359step1; decide +kernel
      have hl : raw20359step1Labels = labelEmbedding6 ∘ raw20359step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20359step1 raw20359step1Labels raw20359step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4551 node4551Labels := by rfl

def raw20360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw20360Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw20360step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20360step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw20360step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20360step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -2, 0], ![3, -1, -2]]
def raw20360step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20360step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![3, -2, -1]]
def raw20360step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20360step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![3, -2, -1]]
def raw20360step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20360 raw20360Labels = mixedMoment B node4192 node4192Labels := by
  calc
    mixedMoment B raw20360 raw20360Labels = mixedMoment B raw20360step0 raw20360step0Labels := by
      have hz : ∀ j, raw20360 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20360step0 = (fun i j => raw20360 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20360step0 raw20360; decide +kernel
      have hl : raw20360step0Labels = raw20360Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20360 raw20360Labels permutation434 hz
    mixedMoment B raw20360step0 raw20360step0Labels = mixedMoment B raw20360step1 raw20360step1Labels := by
      have hz : ∀ j, raw20360step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20360step1 = (fun i j => raw20360step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20360step1 raw20360step0; decide +kernel
      have hl : raw20360step1Labels = raw20360step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20360step0 raw20360step0Labels permutation80 hz
    mixedMoment B raw20360step1 raw20360step1Labels = mixedMoment B raw20360step2 raw20360step2Labels := by
      have hz : ∀ j, raw20360step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20360step2 = (fun i j => raw20360step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20360step2 raw20360step1; decide +kernel
      have hl : raw20360step2Labels = raw20360step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20360step1 raw20360step1Labels permutation14 hz
    mixedMoment B raw20360step2 raw20360step2Labels = mixedMoment B raw20360step3 raw20360step3Labels := by
      have ha : raw20360step3 = (fun i j => raw20360step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20360step3 raw20360step2; decide +kernel
      have hl : raw20360step3Labels = raw20360step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20360step2 raw20360step2Labels permutation2 permutation3
    mixedMoment B raw20360step3 raw20360step3Labels = mixedMoment B raw20360step4 raw20360step4Labels := by
      have ha : raw20360step4 = raw20360step3 := by apply Matrix.ext; unfold raw20360step4 raw20360step3; decide +kernel
      have hl : raw20360step3Labels = labelEmbedding6 ∘ raw20360step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20360step3 raw20360step3Labels raw20360step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4192 node4192Labels := by rfl

def raw20361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw20361Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20361step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw20361step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20361step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw20361step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20361step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw20361step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20361step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw20361step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20361 raw20361Labels = mixedMoment B node4559 node4559Labels := by
  calc
    mixedMoment B raw20361 raw20361Labels = mixedMoment B raw20361step0 raw20361step0Labels := by
      have hz : ∀ j, raw20361 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20361step0 = (fun i j => raw20361 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20361step0 raw20361; decide +kernel
      have hl : raw20361step0Labels = raw20361Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20361 raw20361Labels permutation434 hz
    mixedMoment B raw20361step0 raw20361step0Labels = mixedMoment B raw20361step1 raw20361step1Labels := by
      have hz : ∀ j, raw20361step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20361step1 = (fun i j => raw20361step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20361step1 raw20361step0; decide +kernel
      have hl : raw20361step1Labels = raw20361step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20361step0 raw20361step0Labels permutation80 hz
    mixedMoment B raw20361step1 raw20361step1Labels = mixedMoment B raw20361step2 raw20361step2Labels := by
      have ha : raw20361step2 = (fun i j => raw20361step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20361step2 raw20361step1; decide +kernel
      have hl : raw20361step2Labels = raw20361step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20361step1 raw20361step1Labels permutation8 permutation3
    mixedMoment B raw20361step2 raw20361step2Labels = mixedMoment B raw20361step3 raw20361step3Labels := by
      have ha : raw20361step3 = raw20361step2 := by apply Matrix.ext; unfold raw20361step3 raw20361step2; decide +kernel
      have hl : raw20361step2Labels = labelEmbedding6 ∘ raw20361step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20361step2 raw20361step2Labels raw20361step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4559 node4559Labels := by rfl

def raw20362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw20362Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20362step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw20362step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20362step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw20362step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20362step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw20362step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20362step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw20362step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20362 raw20362Labels = mixedMoment B node4559 node4559Labels := by
  calc
    mixedMoment B raw20362 raw20362Labels = mixedMoment B raw20362step0 raw20362step0Labels := by
      have hz : ∀ j, raw20362 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20362step0 = (fun i j => raw20362 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20362step0 raw20362; decide +kernel
      have hl : raw20362step0Labels = raw20362Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20362 raw20362Labels permutation434 hz
    mixedMoment B raw20362step0 raw20362step0Labels = mixedMoment B raw20362step1 raw20362step1Labels := by
      have hz : ∀ j, raw20362step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20362step1 = (fun i j => raw20362step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20362step1 raw20362step0; decide +kernel
      have hl : raw20362step1Labels = raw20362step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20362step0 raw20362step0Labels permutation56 hz
    mixedMoment B raw20362step1 raw20362step1Labels = mixedMoment B raw20362step2 raw20362step2Labels := by
      have ha : raw20362step2 = (fun i j => raw20362step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20362step2 raw20362step1; decide +kernel
      have hl : raw20362step2Labels = raw20362step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20362step1 raw20362step1Labels permutation8 permutation3
    mixedMoment B raw20362step2 raw20362step2Labels = mixedMoment B raw20362step3 raw20362step3Labels := by
      have ha : raw20362step3 = raw20362step2 := by apply Matrix.ext; unfold raw20362step3 raw20362step2; decide +kernel
      have hl : raw20362step2Labels = labelEmbedding6 ∘ raw20362step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20362step2 raw20362step2Labels raw20362step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4559 node4559Labels := by rfl

def raw20363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw20363Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw20363step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20363step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw20363step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20363step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw20363step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20363step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw20363step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20363 raw20363Labels = mixedMoment B node4559 node4559Labels := by
  calc
    mixedMoment B raw20363 raw20363Labels = mixedMoment B raw20363step0 raw20363step0Labels := by
      have hz : ∀ j, raw20363 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20363step0 = (fun i j => raw20363 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20363step0 raw20363; decide +kernel
      have hl : raw20363step0Labels = raw20363Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20363 raw20363Labels permutation346 hz
    mixedMoment B raw20363step0 raw20363step0Labels = mixedMoment B raw20363step1 raw20363step1Labels := by
      have hz : ∀ j, raw20363step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20363step1 = (fun i j => raw20363step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20363step1 raw20363step0; decide +kernel
      have hl : raw20363step1Labels = raw20363step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20363step0 raw20363step0Labels permutation56 hz
    mixedMoment B raw20363step1 raw20363step1Labels = mixedMoment B raw20363step2 raw20363step2Labels := by
      have ha : raw20363step2 = (fun i j => raw20363step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20363step2 raw20363step1; decide +kernel
      have hl : raw20363step2Labels = raw20363step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20363step1 raw20363step1Labels permutation8 permutation3
    mixedMoment B raw20363step2 raw20363step2Labels = mixedMoment B raw20363step3 raw20363step3Labels := by
      have ha : raw20363step3 = raw20363step2 := by apply Matrix.ext; unfold raw20363step3 raw20363step2; decide +kernel
      have hl : raw20363step2Labels = labelEmbedding6 ∘ raw20363step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20363step2 raw20363step2Labels raw20363step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4559 node4559Labels := by rfl

def raw20364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20364Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20364step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20364step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20364step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20364step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw20364step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20364 raw20364Labels = mixedMoment B node2965 node2965Labels := by
  calc
    mixedMoment B raw20364 raw20364Labels = mixedMoment B raw20364step0 raw20364step0Labels := by
      have hz : ∀ j, raw20364 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20364step0 = (fun i j => raw20364 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20364step0 raw20364; decide +kernel
      have hl : raw20364step0Labels = raw20364Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20364 raw20364Labels permutation434 hz
    mixedMoment B raw20364step0 raw20364step0Labels = mixedMoment B raw20364step1 raw20364step1Labels := by
      have hz : ∀ j, raw20364step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20364step1 = (fun i j => raw20364step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20364step1 raw20364step0; decide +kernel
      have hl : raw20364step1Labels = raw20364step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20364step0 raw20364step0Labels permutation80 hz
    mixedMoment B raw20364step1 raw20364step1Labels = mixedMoment B raw20364step2 raw20364step2Labels := by
      have ha : raw20364step2 = (fun i j => raw20364step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20364step2 raw20364step1; decide +kernel
      have hl : raw20364step2Labels = raw20364step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20364step1 raw20364step1Labels permutation8 permutation3
    _ = mixedMoment B node2965 node2965Labels := by rfl

def raw20365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20365Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20365step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20365step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20365step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20365step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw20365step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20365 raw20365Labels = mixedMoment B node2965 node2965Labels := by
  calc
    mixedMoment B raw20365 raw20365Labels = mixedMoment B raw20365step0 raw20365step0Labels := by
      have hz : ∀ j, raw20365 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20365step0 = (fun i j => raw20365 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20365step0 raw20365; decide +kernel
      have hl : raw20365step0Labels = raw20365Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20365 raw20365Labels permutation434 hz
    mixedMoment B raw20365step0 raw20365step0Labels = mixedMoment B raw20365step1 raw20365step1Labels := by
      have hz : ∀ j, raw20365step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20365step1 = (fun i j => raw20365step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20365step1 raw20365step0; decide +kernel
      have hl : raw20365step1Labels = raw20365step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20365step0 raw20365step0Labels permutation56 hz
    mixedMoment B raw20365step1 raw20365step1Labels = mixedMoment B raw20365step2 raw20365step2Labels := by
      have ha : raw20365step2 = (fun i j => raw20365step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20365step2 raw20365step1; decide +kernel
      have hl : raw20365step2Labels = raw20365step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20365step1 raw20365step1Labels permutation8 permutation3
    _ = mixedMoment B node2965 node2965Labels := by rfl

def raw20366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20366Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20366step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20366step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20366step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20366step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![3, -2, -1]]
def raw20366step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20366 raw20366Labels = mixedMoment B node2965 node2965Labels := by
  calc
    mixedMoment B raw20366 raw20366Labels = mixedMoment B raw20366step0 raw20366step0Labels := by
      have hz : ∀ j, raw20366 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20366step0 = (fun i j => raw20366 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20366step0 raw20366; decide +kernel
      have hl : raw20366step0Labels = raw20366Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20366 raw20366Labels permutation346 hz
    mixedMoment B raw20366step0 raw20366step0Labels = mixedMoment B raw20366step1 raw20366step1Labels := by
      have hz : ∀ j, raw20366step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20366step1 = (fun i j => raw20366step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20366step1 raw20366step0; decide +kernel
      have hl : raw20366step1Labels = raw20366step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20366step0 raw20366step0Labels permutation56 hz
    mixedMoment B raw20366step1 raw20366step1Labels = mixedMoment B raw20366step2 raw20366step2Labels := by
      have ha : raw20366step2 = (fun i j => raw20366step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20366step2 raw20366step1; decide +kernel
      have hl : raw20366step2Labels = raw20366step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20366step1 raw20366step1Labels permutation8 permutation3
    _ = mixedMoment B node2965 node2965Labels := by rfl

def raw20367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20367Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20367step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20367step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20367step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20367step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20367step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20367 raw20367Labels = mixedMoment B node611 node611Labels := by
  calc
    mixedMoment B raw20367 raw20367Labels = mixedMoment B raw20367step0 raw20367step0Labels := by
      have hz : ∀ j, raw20367 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20367step0 = (fun i j => raw20367 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20367step0 raw20367; decide +kernel
      have hl : raw20367step0Labels = raw20367Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20367 raw20367Labels permutation434 hz
    mixedMoment B raw20367step0 raw20367step0Labels = mixedMoment B raw20367step1 raw20367step1Labels := by
      have hz : ∀ j, raw20367step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20367step1 = (fun i j => raw20367step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20367step1 raw20367step0; decide +kernel
      have hl : raw20367step1Labels = raw20367step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20367step0 raw20367step0Labels permutation80 hz
    mixedMoment B raw20367step1 raw20367step1Labels = mixedMoment B raw20367step2 raw20367step2Labels := by
      have ha : raw20367step2 = (fun i j => raw20367step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20367step2 raw20367step1; decide +kernel
      have hl : raw20367step2Labels = raw20367step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20367step1 raw20367step1Labels permutation8 permutation3
    _ = mixedMoment B node611 node611Labels := by rfl

def raw20368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20368Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20368step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20368step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20368step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20368 raw20368Labels = mixedMoment B node1136 node1136Labels := by
  calc
    mixedMoment B raw20368 raw20368Labels = mixedMoment B raw20368step0 raw20368step0Labels := by
      have hz : ∀ j, raw20368 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20368step0 = (fun i j => raw20368 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20368step0 raw20368; decide +kernel
      have hl : raw20368step0Labels = raw20368Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20368 raw20368Labels permutation434 hz
    mixedMoment B raw20368step0 raw20368step0Labels = mixedMoment B raw20368step1 raw20368step1Labels := by
      have ha : raw20368step1 = (fun i j => raw20368step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20368step1 raw20368step0; decide +kernel
      have hl : raw20368step1Labels = raw20368step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20368step0 raw20368step0Labels permutation38 permutation3
    _ = mixedMoment B node1136 node1136Labels := by rfl

def raw20369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20369Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20369step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20369step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20369step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20369step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20369 raw20369Labels = mixedMoment B node1136 node1136Labels := by
  calc
    mixedMoment B raw20369 raw20369Labels = mixedMoment B raw20369step0 raw20369step0Labels := by
      have hz : ∀ j, raw20369 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20369step0 = (fun i j => raw20369 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20369step0 raw20369; decide +kernel
      have hl : raw20369step0Labels = raw20369Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20369 raw20369Labels permutation346 hz
    mixedMoment B raw20369step0 raw20369step0Labels = mixedMoment B raw20369step1 raw20369step1Labels := by
      have ha : raw20369step1 = (fun i j => raw20369step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20369step1 raw20369step0; decide +kernel
      have hl : raw20369step1Labels = raw20369step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20369step0 raw20369step0Labels permutation38 permutation3
    _ = mixedMoment B node1136 node1136Labels := by rfl

def raw20370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw20370Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20370step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw20370step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20370step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw20370step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20370step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw20370step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20370 raw20370Labels = mixedMoment B node1305 node1305Labels := by
  calc
    mixedMoment B raw20370 raw20370Labels = mixedMoment B raw20370step0 raw20370step0Labels := by
      have hz : ∀ j, raw20370 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20370step0 = (fun i j => raw20370 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20370step0 raw20370; decide +kernel
      have hl : raw20370step0Labels = raw20370Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20370 raw20370Labels permutation434 hz
    mixedMoment B raw20370step0 raw20370step0Labels = mixedMoment B raw20370step1 raw20370step1Labels := by
      have hz : ∀ j, raw20370step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20370step1 = (fun i j => raw20370step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20370step1 raw20370step0; decide +kernel
      have hl : raw20370step1Labels = raw20370step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20370step0 raw20370step0Labels permutation80 hz
    mixedMoment B raw20370step1 raw20370step1Labels = mixedMoment B raw20370step2 raw20370step2Labels := by
      have ha : raw20370step2 = (fun i j => raw20370step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20370step2 raw20370step1; decide +kernel
      have hl : raw20370step2Labels = raw20370step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20370step1 raw20370step1Labels permutation8 permutation3
    _ = mixedMoment B node1305 node1305Labels := by rfl

def raw20371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20371Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20371step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20371step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20371step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20371step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20371step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20371 raw20371Labels = mixedMoment B node611 node611Labels := by
  calc
    mixedMoment B raw20371 raw20371Labels = mixedMoment B raw20371step0 raw20371step0Labels := by
      have hz : ∀ j, raw20371 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20371step0 = (fun i j => raw20371 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20371step0 raw20371; decide +kernel
      have hl : raw20371step0Labels = raw20371Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20371 raw20371Labels permutation434 hz
    mixedMoment B raw20371step0 raw20371step0Labels = mixedMoment B raw20371step1 raw20371step1Labels := by
      have hz : ∀ j, raw20371step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20371step1 = (fun i j => raw20371step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20371step1 raw20371step0; decide +kernel
      have hl : raw20371step1Labels = raw20371step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20371step0 raw20371step0Labels permutation56 hz
    mixedMoment B raw20371step1 raw20371step1Labels = mixedMoment B raw20371step2 raw20371step2Labels := by
      have ha : raw20371step2 = (fun i j => raw20371step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20371step2 raw20371step1; decide +kernel
      have hl : raw20371step2Labels = raw20371step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20371step1 raw20371step1Labels permutation8 permutation3
    _ = mixedMoment B node611 node611Labels := by rfl

def raw20372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20372Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20372step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20372step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20372step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20372 raw20372Labels = mixedMoment B node1136 node1136Labels := by
  calc
    mixedMoment B raw20372 raw20372Labels = mixedMoment B raw20372step0 raw20372step0Labels := by
      have hz : ∀ j, raw20372 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20372step0 = (fun i j => raw20372 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20372step0 raw20372; decide +kernel
      have hl : raw20372step0Labels = raw20372Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20372 raw20372Labels permutation434 hz
    mixedMoment B raw20372step0 raw20372step0Labels = mixedMoment B raw20372step1 raw20372step1Labels := by
      have ha : raw20372step1 = (fun i j => raw20372step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20372step1 raw20372step0; decide +kernel
      have hl : raw20372step1Labels = raw20372step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20372step0 raw20372step0Labels permutation32 permutation3
    _ = mixedMoment B node1136 node1136Labels := by rfl

def raw20373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20373Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20373step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20373step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20373step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20373 raw20373Labels = mixedMoment B node1136 node1136Labels := by
  calc
    mixedMoment B raw20373 raw20373Labels = mixedMoment B raw20373step0 raw20373step0Labels := by
      have hz : ∀ j, raw20373 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20373step0 = (fun i j => raw20373 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20373step0 raw20373; decide +kernel
      have hl : raw20373step0Labels = raw20373Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20373 raw20373Labels permutation265 hz
    mixedMoment B raw20373step0 raw20373step0Labels = mixedMoment B raw20373step1 raw20373step1Labels := by
      have ha : raw20373step1 = (fun i j => raw20373step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20373step1 raw20373step0; decide +kernel
      have hl : raw20373step1Labels = raw20373step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20373step0 raw20373step0Labels permutation38 permutation3
    _ = mixedMoment B node1136 node1136Labels := by rfl

def raw20374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw20374Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw20374step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20374step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw20374step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20374step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw20374step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20374 raw20374Labels = mixedMoment B node1305 node1305Labels := by
  calc
    mixedMoment B raw20374 raw20374Labels = mixedMoment B raw20374step0 raw20374step0Labels := by
      have hz : ∀ j, raw20374 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20374step0 = (fun i j => raw20374 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20374step0 raw20374; decide +kernel
      have hl : raw20374step0Labels = raw20374Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20374 raw20374Labels permutation434 hz
    mixedMoment B raw20374step0 raw20374step0Labels = mixedMoment B raw20374step1 raw20374step1Labels := by
      have hz : ∀ j, raw20374step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20374step1 = (fun i j => raw20374step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20374step1 raw20374step0; decide +kernel
      have hl : raw20374step1Labels = raw20374step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20374step0 raw20374step0Labels permutation56 hz
    mixedMoment B raw20374step1 raw20374step1Labels = mixedMoment B raw20374step2 raw20374step2Labels := by
      have ha : raw20374step2 = (fun i j => raw20374step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20374step2 raw20374step1; decide +kernel
      have hl : raw20374step2Labels = raw20374step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20374step1 raw20374step1Labels permutation8 permutation3
    _ = mixedMoment B node1305 node1305Labels := by rfl

def raw20375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20375Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20375step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20375step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20375step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20375step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20375step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20375 raw20375Labels = mixedMoment B node611 node611Labels := by
  calc
    mixedMoment B raw20375 raw20375Labels = mixedMoment B raw20375step0 raw20375step0Labels := by
      have hz : ∀ j, raw20375 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20375step0 = (fun i j => raw20375 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20375step0 raw20375; decide +kernel
      have hl : raw20375step0Labels = raw20375Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20375 raw20375Labels permutation346 hz
    mixedMoment B raw20375step0 raw20375step0Labels = mixedMoment B raw20375step1 raw20375step1Labels := by
      have hz : ∀ j, raw20375step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20375step1 = (fun i j => raw20375step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20375step1 raw20375step0; decide +kernel
      have hl : raw20375step1Labels = raw20375step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20375step0 raw20375step0Labels permutation56 hz
    mixedMoment B raw20375step1 raw20375step1Labels = mixedMoment B raw20375step2 raw20375step2Labels := by
      have ha : raw20375step2 = (fun i j => raw20375step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20375step2 raw20375step1; decide +kernel
      have hl : raw20375step2Labels = raw20375step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20375step1 raw20375step1Labels permutation8 permutation3
    _ = mixedMoment B node611 node611Labels := by rfl

def raw20376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20376Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20376step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20376step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20376step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20376 raw20376Labels = mixedMoment B node1136 node1136Labels := by
  calc
    mixedMoment B raw20376 raw20376Labels = mixedMoment B raw20376step0 raw20376step0Labels := by
      have hz : ∀ j, raw20376 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20376step0 = (fun i j => raw20376 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20376step0 raw20376; decide +kernel
      have hl : raw20376step0Labels = raw20376Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20376 raw20376Labels permutation346 hz
    mixedMoment B raw20376step0 raw20376step0Labels = mixedMoment B raw20376step1 raw20376step1Labels := by
      have ha : raw20376step1 = (fun i j => raw20376step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20376step1 raw20376step0; decide +kernel
      have hl : raw20376step1Labels = raw20376step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20376step0 raw20376step0Labels permutation32 permutation3
    _ = mixedMoment B node1136 node1136Labels := by rfl

def raw20377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20377Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20377step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw20377step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20377step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20377step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20377 raw20377Labels = mixedMoment B node1136 node1136Labels := by
  calc
    mixedMoment B raw20377 raw20377Labels = mixedMoment B raw20377step0 raw20377step0Labels := by
      have hz : ∀ j, raw20377 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20377step0 = (fun i j => raw20377 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20377step0 raw20377; decide +kernel
      have hl : raw20377step0Labels = raw20377Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20377 raw20377Labels permutation265 hz
    mixedMoment B raw20377step0 raw20377step0Labels = mixedMoment B raw20377step1 raw20377step1Labels := by
      have ha : raw20377step1 = (fun i j => raw20377step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20377step1 raw20377step0; decide +kernel
      have hl : raw20377step1Labels = raw20377step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20377step0 raw20377step0Labels permutation32 permutation3
    _ = mixedMoment B node1136 node1136Labels := by rfl

def raw20378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw20378Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20378step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw20378step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20378step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw20378step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20378step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -2, 0], ![3, -1, -2]]
def raw20378step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20378step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, 0, -2], ![3, -2, -1]]
def raw20378step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20378 raw20378Labels = mixedMoment B node620 node620Labels := by
  calc
    mixedMoment B raw20378 raw20378Labels = mixedMoment B raw20378step0 raw20378step0Labels := by
      have hz : ∀ j, raw20378 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20378step0 = (fun i j => raw20378 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20378step0 raw20378; decide +kernel
      have hl : raw20378step0Labels = raw20378Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20378 raw20378Labels permutation434 hz
    mixedMoment B raw20378step0 raw20378step0Labels = mixedMoment B raw20378step1 raw20378step1Labels := by
      have hz : ∀ j, raw20378step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20378step1 = (fun i j => raw20378step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20378step1 raw20378step0; decide +kernel
      have hl : raw20378step1Labels = raw20378step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20378step0 raw20378step0Labels permutation80 hz
    mixedMoment B raw20378step1 raw20378step1Labels = mixedMoment B raw20378step2 raw20378step2Labels := by
      have hz : ∀ j, raw20378step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20378step2 = (fun i j => raw20378step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20378step2 raw20378step1; decide +kernel
      have hl : raw20378step2Labels = raw20378step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20378step1 raw20378step1Labels permutation14 hz
    mixedMoment B raw20378step2 raw20378step2Labels = mixedMoment B raw20378step3 raw20378step3Labels := by
      have ha : raw20378step3 = (fun i j => raw20378step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20378step3 raw20378step2; decide +kernel
      have hl : raw20378step3Labels = raw20378step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20378step2 raw20378step2Labels permutation2 permutation3
    _ = mixedMoment B node620 node620Labels := by rfl

def raw20379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw20379Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20379step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw20379step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20379step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw20379step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20379step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw20379step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20379 raw20379Labels = mixedMoment B node1145 node1145Labels := by
  calc
    mixedMoment B raw20379 raw20379Labels = mixedMoment B raw20379step0 raw20379step0Labels := by
      have hz : ∀ j, raw20379 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20379step0 = (fun i j => raw20379 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20379step0 raw20379; decide +kernel
      have hl : raw20379step0Labels = raw20379Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20379 raw20379Labels permutation434 hz
    mixedMoment B raw20379step0 raw20379step0Labels = mixedMoment B raw20379step1 raw20379step1Labels := by
      have hz : ∀ j, raw20379step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20379step1 = (fun i j => raw20379step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20379step1 raw20379step0; decide +kernel
      have hl : raw20379step1Labels = raw20379step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20379step0 raw20379step0Labels permutation80 hz
    mixedMoment B raw20379step1 raw20379step1Labels = mixedMoment B raw20379step2 raw20379step2Labels := by
      have ha : raw20379step2 = (fun i j => raw20379step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20379step2 raw20379step1; decide +kernel
      have hl : raw20379step2Labels = raw20379step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20379step1 raw20379step1Labels permutation8 permutation3
    _ = mixedMoment B node1145 node1145Labels := by rfl

def raw20380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, -1, -2]]
def raw20380Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20380step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw20380step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20380step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw20380step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20380step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw20380step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20380 raw20380Labels = mixedMoment B node1145 node1145Labels := by
  calc
    mixedMoment B raw20380 raw20380Labels = mixedMoment B raw20380step0 raw20380step0Labels := by
      have hz : ∀ j, raw20380 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20380step0 = (fun i j => raw20380 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20380step0 raw20380; decide +kernel
      have hl : raw20380step0Labels = raw20380Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20380 raw20380Labels permutation434 hz
    mixedMoment B raw20380step0 raw20380step0Labels = mixedMoment B raw20380step1 raw20380step1Labels := by
      have hz : ∀ j, raw20380step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20380step1 = (fun i j => raw20380step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20380step1 raw20380step0; decide +kernel
      have hl : raw20380step1Labels = raw20380step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20380step0 raw20380step0Labels permutation56 hz
    mixedMoment B raw20380step1 raw20380step1Labels = mixedMoment B raw20380step2 raw20380step2Labels := by
      have ha : raw20380step2 = (fun i j => raw20380step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20380step2 raw20380step1; decide +kernel
      have hl : raw20380step2Labels = raw20380step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20380step1 raw20380step1Labels permutation8 permutation3
    _ = mixedMoment B node1145 node1145Labels := by rfl

def raw20381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw20381Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw20381step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20381step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -2, 0], ![3, -1, -2]]
def raw20381step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20381step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, 0, -2], ![3, -2, -1]]
def raw20381step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20381 raw20381Labels = mixedMoment B node1145 node1145Labels := by
  calc
    mixedMoment B raw20381 raw20381Labels = mixedMoment B raw20381step0 raw20381step0Labels := by
      have hz : ∀ j, raw20381 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20381step0 = (fun i j => raw20381 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20381step0 raw20381; decide +kernel
      have hl : raw20381step0Labels = raw20381Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20381 raw20381Labels permutation346 hz
    mixedMoment B raw20381step0 raw20381step0Labels = mixedMoment B raw20381step1 raw20381step1Labels := by
      have hz : ∀ j, raw20381step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20381step1 = (fun i j => raw20381step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20381step1 raw20381step0; decide +kernel
      have hl : raw20381step1Labels = raw20381step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20381step0 raw20381step0Labels permutation56 hz
    mixedMoment B raw20381step1 raw20381step1Labels = mixedMoment B raw20381step2 raw20381step2Labels := by
      have ha : raw20381step2 = (fun i j => raw20381step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20381step2 raw20381step1; decide +kernel
      have hl : raw20381step2Labels = raw20381step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20381step1 raw20381step1Labels permutation8 permutation3
    _ = mixedMoment B node1145 node1145Labels := by rfl

def raw20382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw20382Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20382step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw20382step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20382step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -2, 0], ![2, 0, -2]]
def raw20382step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20382step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw20382step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20382step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -2, 0], ![2, 0, -2]]
def raw20382step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20382 raw20382Labels = mixedMoment B node1311 node1311Labels := by
  calc
    mixedMoment B raw20382 raw20382Labels = mixedMoment B raw20382step0 raw20382step0Labels := by
      have hz : ∀ j, raw20382 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20382step0 = (fun i j => raw20382 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20382step0 raw20382; decide +kernel
      have hl : raw20382step0Labels = raw20382Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20382 raw20382Labels permutation434 hz
    mixedMoment B raw20382step0 raw20382step0Labels = mixedMoment B raw20382step1 raw20382step1Labels := by
      have hz : ∀ j, raw20382step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20382step1 = (fun i j => raw20382step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20382step1 raw20382step0; decide +kernel
      have hl : raw20382step1Labels = raw20382step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20382step0 raw20382step0Labels permutation80 hz
    mixedMoment B raw20382step1 raw20382step1Labels = mixedMoment B raw20382step2 raw20382step2Labels := by
      have hz : ∀ j, raw20382step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20382step2 = (fun i j => raw20382step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20382step2 raw20382step1; decide +kernel
      have hl : raw20382step2Labels = raw20382step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20382step1 raw20382step1Labels permutation14 hz
    mixedMoment B raw20382step2 raw20382step2Labels = mixedMoment B raw20382step3 raw20382step3Labels := by
      have ha : raw20382step3 = (fun i j => raw20382step2 (permutation3 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20382step3 raw20382step2; decide +kernel
      have hl : raw20382step3Labels = raw20382step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20382step2 raw20382step2Labels permutation3 permutation3
    _ = mixedMoment B node1311 node1311Labels := by rfl

def raw20383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw20383Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20383step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw20383step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20383step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![4, -2, -2]]
def raw20383step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20383step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![4, -2, -2]]
def raw20383step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20383step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 2, 2], ![4, -2, -2]]
def raw20383step3Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20383step4 : Matrix (Fin 2) (Fin 3) ℤ := ![![-4, 2, 2], ![4, -2, -2]]
def raw20383step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20383 raw20383Labels = mixedMoment B node1313 node1313Labels := by
  calc
    mixedMoment B raw20383 raw20383Labels = mixedMoment B raw20383step0 raw20383step0Labels := by
      have hz : ∀ j, raw20383 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw20383step0 = (fun i j => raw20383 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw20383step0 raw20383; decide +kernel
      have hl : raw20383step0Labels = raw20383Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20383 raw20383Labels permutation520 hz
    mixedMoment B raw20383step0 raw20383step0Labels = mixedMoment B raw20383step1 raw20383step1Labels := by
      have hz : ∀ j, raw20383step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw20383step1 = (fun i j => raw20383step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw20383step1 raw20383step0; decide +kernel
      have hl : raw20383step1Labels = raw20383step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20383step0 raw20383step0Labels permutation104 hz
    mixedMoment B raw20383step1 raw20383step1Labels = mixedMoment B raw20383step2 raw20383step2Labels := by
      have hz : ∀ j, raw20383step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw20383step2 = (fun i j => raw20383step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw20383step2 raw20383step1; decide +kernel
      have hl : raw20383step2Labels = raw20383step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20383step1 raw20383step1Labels permutation20 hz
    mixedMoment B raw20383step2 raw20383step2Labels = mixedMoment B raw20383step3 raw20383step3Labels := by
      have hz : ∀ j, raw20383step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw20383step3 = (fun i j => raw20383step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw20383step3 raw20383step2; decide +kernel
      have hl : raw20383step3Labels = raw20383step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20383step2 raw20383step2Labels permutation4 hz
    mixedMoment B raw20383step3 raw20383step3Labels = mixedMoment B raw20383step4 raw20383step4Labels := by
      have ha : raw20383step4 = (fun i j => raw20383step3 (permutation0 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20383step4 raw20383step3; decide +kernel
      have hl : raw20383step4Labels = raw20383step3Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20383step3 raw20383step3Labels permutation0 permutation3
    _ = mixedMoment B node1313 node1313Labels := by rfl

def raw20384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20384Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20384step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20384step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20384step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20384step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20384step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20384step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20384step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20384step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20384 raw20384Labels = mixedMoment B node4177 node4177Labels := by
  calc
    mixedMoment B raw20384 raw20384Labels = mixedMoment B raw20384step0 raw20384step0Labels := by
      have hz : ∀ j, raw20384 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20384step0 = (fun i j => raw20384 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20384step0 raw20384; decide +kernel
      have hl : raw20384step0Labels = raw20384Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20384 raw20384Labels permutation434 hz
    mixedMoment B raw20384step0 raw20384step0Labels = mixedMoment B raw20384step1 raw20384step1Labels := by
      have hz : ∀ j, raw20384step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20384step1 = (fun i j => raw20384step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20384step1 raw20384step0; decide +kernel
      have hl : raw20384step1Labels = raw20384step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20384step0 raw20384step0Labels permutation80 hz
    mixedMoment B raw20384step1 raw20384step1Labels = mixedMoment B raw20384step2 raw20384step2Labels := by
      have ha : raw20384step2 = (fun i j => raw20384step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20384step2 raw20384step1; decide +kernel
      have hl : raw20384step2Labels = raw20384step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20384step1 raw20384step1Labels permutation10 permutation3
    mixedMoment B raw20384step2 raw20384step2Labels = mixedMoment B raw20384step3 raw20384step3Labels := by
      have ha : raw20384step3 = raw20384step2 := by apply Matrix.ext; unfold raw20384step3 raw20384step2; decide +kernel
      have hl : raw20384step2Labels = labelEmbedding6 ∘ raw20384step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20384step2 raw20384step2Labels raw20384step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4177 node4177Labels := by rfl

def raw20385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20385Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20385step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20385step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20385step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20385step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20385step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20385 raw20385Labels = mixedMoment B node4546 node4546Labels := by
  calc
    mixedMoment B raw20385 raw20385Labels = mixedMoment B raw20385step0 raw20385step0Labels := by
      have hz : ∀ j, raw20385 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20385step0 = (fun i j => raw20385 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20385step0 raw20385; decide +kernel
      have hl : raw20385step0Labels = raw20385Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20385 raw20385Labels permutation434 hz
    mixedMoment B raw20385step0 raw20385step0Labels = mixedMoment B raw20385step1 raw20385step1Labels := by
      have ha : raw20385step1 = (fun i j => raw20385step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20385step1 raw20385step0; decide +kernel
      have hl : raw20385step1Labels = raw20385step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20385step0 raw20385step0Labels permutation40 permutation3
    mixedMoment B raw20385step1 raw20385step1Labels = mixedMoment B raw20385step2 raw20385step2Labels := by
      have ha : raw20385step2 = raw20385step1 := by apply Matrix.ext; unfold raw20385step2 raw20385step1; decide +kernel
      have hl : raw20385step1Labels = labelEmbedding6 ∘ raw20385step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20385step1 raw20385step1Labels raw20385step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4546 node4546Labels := by rfl

def raw20386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20386Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20386step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20386step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20386step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20386step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20386step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20386 raw20386Labels = mixedMoment B node4546 node4546Labels := by
  calc
    mixedMoment B raw20386 raw20386Labels = mixedMoment B raw20386step0 raw20386step0Labels := by
      have hz : ∀ j, raw20386 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20386step0 = (fun i j => raw20386 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20386step0 raw20386; decide +kernel
      have hl : raw20386step0Labels = raw20386Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20386 raw20386Labels permutation346 hz
    mixedMoment B raw20386step0 raw20386step0Labels = mixedMoment B raw20386step1 raw20386step1Labels := by
      have ha : raw20386step1 = (fun i j => raw20386step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20386step1 raw20386step0; decide +kernel
      have hl : raw20386step1Labels = raw20386step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20386step0 raw20386step0Labels permutation40 permutation3
    mixedMoment B raw20386step1 raw20386step1Labels = mixedMoment B raw20386step2 raw20386step2Labels := by
      have ha : raw20386step2 = raw20386step1 := by apply Matrix.ext; unfold raw20386step2 raw20386step1; decide +kernel
      have hl : raw20386step1Labels = labelEmbedding6 ∘ raw20386step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20386step1 raw20386step1Labels raw20386step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4546 node4546Labels := by rfl

def raw20387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20387Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20387step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20387step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20387step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20387step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20387step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20387step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20387step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20387step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20387 raw20387Labels = mixedMoment B node4177 node4177Labels := by
  calc
    mixedMoment B raw20387 raw20387Labels = mixedMoment B raw20387step0 raw20387step0Labels := by
      have hz : ∀ j, raw20387 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20387step0 = (fun i j => raw20387 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20387step0 raw20387; decide +kernel
      have hl : raw20387step0Labels = raw20387Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20387 raw20387Labels permutation434 hz
    mixedMoment B raw20387step0 raw20387step0Labels = mixedMoment B raw20387step1 raw20387step1Labels := by
      have hz : ∀ j, raw20387step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20387step1 = (fun i j => raw20387step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20387step1 raw20387step0; decide +kernel
      have hl : raw20387step1Labels = raw20387step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20387step0 raw20387step0Labels permutation56 hz
    mixedMoment B raw20387step1 raw20387step1Labels = mixedMoment B raw20387step2 raw20387step2Labels := by
      have ha : raw20387step2 = (fun i j => raw20387step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20387step2 raw20387step1; decide +kernel
      have hl : raw20387step2Labels = raw20387step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20387step1 raw20387step1Labels permutation10 permutation3
    mixedMoment B raw20387step2 raw20387step2Labels = mixedMoment B raw20387step3 raw20387step3Labels := by
      have ha : raw20387step3 = raw20387step2 := by apply Matrix.ext; unfold raw20387step3 raw20387step2; decide +kernel
      have hl : raw20387step2Labels = labelEmbedding6 ∘ raw20387step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20387step2 raw20387step2Labels raw20387step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4177 node4177Labels := by rfl

def raw20388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20388Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20388step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20388step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20388step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20388step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20388step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20388 raw20388Labels = mixedMoment B node4546 node4546Labels := by
  calc
    mixedMoment B raw20388 raw20388Labels = mixedMoment B raw20388step0 raw20388step0Labels := by
      have hz : ∀ j, raw20388 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20388step0 = (fun i j => raw20388 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20388step0 raw20388; decide +kernel
      have hl : raw20388step0Labels = raw20388Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20388 raw20388Labels permutation434 hz
    mixedMoment B raw20388step0 raw20388step0Labels = mixedMoment B raw20388step1 raw20388step1Labels := by
      have ha : raw20388step1 = (fun i j => raw20388step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20388step1 raw20388step0; decide +kernel
      have hl : raw20388step1Labels = raw20388step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20388step0 raw20388step0Labels permutation34 permutation3
    mixedMoment B raw20388step1 raw20388step1Labels = mixedMoment B raw20388step2 raw20388step2Labels := by
      have ha : raw20388step2 = raw20388step1 := by apply Matrix.ext; unfold raw20388step2 raw20388step1; decide +kernel
      have hl : raw20388step1Labels = labelEmbedding6 ∘ raw20388step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20388step1 raw20388step1Labels raw20388step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4546 node4546Labels := by rfl

def raw20389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20389Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20389step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20389step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20389step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20389step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20389step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20389step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20389 raw20389Labels = mixedMoment B node4546 node4546Labels := by
  calc
    mixedMoment B raw20389 raw20389Labels = mixedMoment B raw20389step0 raw20389step0Labels := by
      have hz : ∀ j, raw20389 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20389step0 = (fun i j => raw20389 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20389step0 raw20389; decide +kernel
      have hl : raw20389step0Labels = raw20389Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20389 raw20389Labels permutation265 hz
    mixedMoment B raw20389step0 raw20389step0Labels = mixedMoment B raw20389step1 raw20389step1Labels := by
      have ha : raw20389step1 = (fun i j => raw20389step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20389step1 raw20389step0; decide +kernel
      have hl : raw20389step1Labels = raw20389step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20389step0 raw20389step0Labels permutation40 permutation3
    mixedMoment B raw20389step1 raw20389step1Labels = mixedMoment B raw20389step2 raw20389step2Labels := by
      have ha : raw20389step2 = raw20389step1 := by apply Matrix.ext; unfold raw20389step2 raw20389step1; decide +kernel
      have hl : raw20389step1Labels = labelEmbedding6 ∘ raw20389step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20389step1 raw20389step1Labels raw20389step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4546 node4546Labels := by rfl

def raw20390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20390Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20390step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20390step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20390step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20390step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20390step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20390step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20390step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20390step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20390 raw20390Labels = mixedMoment B node4177 node4177Labels := by
  calc
    mixedMoment B raw20390 raw20390Labels = mixedMoment B raw20390step0 raw20390step0Labels := by
      have hz : ∀ j, raw20390 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20390step0 = (fun i j => raw20390 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20390step0 raw20390; decide +kernel
      have hl : raw20390step0Labels = raw20390Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20390 raw20390Labels permutation346 hz
    mixedMoment B raw20390step0 raw20390step0Labels = mixedMoment B raw20390step1 raw20390step1Labels := by
      have hz : ∀ j, raw20390step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20390step1 = (fun i j => raw20390step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20390step1 raw20390step0; decide +kernel
      have hl : raw20390step1Labels = raw20390step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20390step0 raw20390step0Labels permutation56 hz
    mixedMoment B raw20390step1 raw20390step1Labels = mixedMoment B raw20390step2 raw20390step2Labels := by
      have ha : raw20390step2 = (fun i j => raw20390step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20390step2 raw20390step1; decide +kernel
      have hl : raw20390step2Labels = raw20390step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20390step1 raw20390step1Labels permutation10 permutation3
    mixedMoment B raw20390step2 raw20390step2Labels = mixedMoment B raw20390step3 raw20390step3Labels := by
      have ha : raw20390step3 = raw20390step2 := by apply Matrix.ext; unfold raw20390step3 raw20390step2; decide +kernel
      have hl : raw20390step2Labels = labelEmbedding6 ∘ raw20390step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20390step2 raw20390step2Labels raw20390step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4177 node4177Labels := by rfl

def raw20391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20391Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20391step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20391step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20391step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20391step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20391step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20391step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20391 raw20391Labels = mixedMoment B node4546 node4546Labels := by
  calc
    mixedMoment B raw20391 raw20391Labels = mixedMoment B raw20391step0 raw20391step0Labels := by
      have hz : ∀ j, raw20391 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20391step0 = (fun i j => raw20391 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20391step0 raw20391; decide +kernel
      have hl : raw20391step0Labels = raw20391Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20391 raw20391Labels permutation346 hz
    mixedMoment B raw20391step0 raw20391step0Labels = mixedMoment B raw20391step1 raw20391step1Labels := by
      have ha : raw20391step1 = (fun i j => raw20391step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20391step1 raw20391step0; decide +kernel
      have hl : raw20391step1Labels = raw20391step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20391step0 raw20391step0Labels permutation34 permutation3
    mixedMoment B raw20391step1 raw20391step1Labels = mixedMoment B raw20391step2 raw20391step2Labels := by
      have ha : raw20391step2 = raw20391step1 := by apply Matrix.ext; unfold raw20391step2 raw20391step1; decide +kernel
      have hl : raw20391step1Labels = labelEmbedding6 ∘ raw20391step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20391step1 raw20391step1Labels raw20391step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4546 node4546Labels := by rfl

def raw20392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20392Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20392step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20392step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20392step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20392step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20392step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20392step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20392 raw20392Labels = mixedMoment B node4546 node4546Labels := by
  calc
    mixedMoment B raw20392 raw20392Labels = mixedMoment B raw20392step0 raw20392step0Labels := by
      have hz : ∀ j, raw20392 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20392step0 = (fun i j => raw20392 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20392step0 raw20392; decide +kernel
      have hl : raw20392step0Labels = raw20392Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20392 raw20392Labels permutation265 hz
    mixedMoment B raw20392step0 raw20392step0Labels = mixedMoment B raw20392step1 raw20392step1Labels := by
      have ha : raw20392step1 = (fun i j => raw20392step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20392step1 raw20392step0; decide +kernel
      have hl : raw20392step1Labels = raw20392step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20392step0 raw20392step0Labels permutation34 permutation3
    mixedMoment B raw20392step1 raw20392step1Labels = mixedMoment B raw20392step2 raw20392step2Labels := by
      have ha : raw20392step2 = raw20392step1 := by apply Matrix.ext; unfold raw20392step2 raw20392step1; decide +kernel
      have hl : raw20392step1Labels = labelEmbedding6 ∘ raw20392step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20392step1 raw20392step1Labels raw20392step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4546 node4546Labels := by rfl

def raw20393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw20393Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20393step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw20393step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20393step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw20393step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20393step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -1, -1], ![3, -2, -1]]
def raw20393step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20393step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -1, -1], ![3, -1, -2]]
def raw20393step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20393step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -1, -1], ![3, -1, -2]]
def raw20393step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20393 raw20393Labels = mixedMoment B node4191 node4191Labels := by
  calc
    mixedMoment B raw20393 raw20393Labels = mixedMoment B raw20393step0 raw20393step0Labels := by
      have hz : ∀ j, raw20393 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20393step0 = (fun i j => raw20393 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20393step0 raw20393; decide +kernel
      have hl : raw20393step0Labels = raw20393Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20393 raw20393Labels permutation434 hz
    mixedMoment B raw20393step0 raw20393step0Labels = mixedMoment B raw20393step1 raw20393step1Labels := by
      have hz : ∀ j, raw20393step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20393step1 = (fun i j => raw20393step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20393step1 raw20393step0; decide +kernel
      have hl : raw20393step1Labels = raw20393step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20393step0 raw20393step0Labels permutation80 hz
    mixedMoment B raw20393step1 raw20393step1Labels = mixedMoment B raw20393step2 raw20393step2Labels := by
      have hz : ∀ j, raw20393step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20393step2 = (fun i j => raw20393step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20393step2 raw20393step1; decide +kernel
      have hl : raw20393step2Labels = raw20393step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20393step1 raw20393step1Labels permutation14 hz
    mixedMoment B raw20393step2 raw20393step2Labels = mixedMoment B raw20393step3 raw20393step3Labels := by
      have ha : raw20393step3 = (fun i j => raw20393step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20393step3 raw20393step2; decide +kernel
      have hl : raw20393step3Labels = raw20393step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20393step2 raw20393step2Labels permutation2 permutation3
    mixedMoment B raw20393step3 raw20393step3Labels = mixedMoment B raw20393step4 raw20393step4Labels := by
      have ha : raw20393step4 = raw20393step3 := by apply Matrix.ext; unfold raw20393step4 raw20393step3; decide +kernel
      have hl : raw20393step3Labels = labelEmbedding6 ∘ raw20393step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20393step3 raw20393step3Labels raw20393step4Labels labelEmbedding6 hl
    _ = mixedMoment B node4191 node4191Labels := by rfl

def raw20394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw20394Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20394step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw20394step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20394step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw20394step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20394step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20394step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20394step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20394step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20394 raw20394Labels = mixedMoment B node4558 node4558Labels := by
  calc
    mixedMoment B raw20394 raw20394Labels = mixedMoment B raw20394step0 raw20394step0Labels := by
      have hz : ∀ j, raw20394 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20394step0 = (fun i j => raw20394 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20394step0 raw20394; decide +kernel
      have hl : raw20394step0Labels = raw20394Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20394 raw20394Labels permutation434 hz
    mixedMoment B raw20394step0 raw20394step0Labels = mixedMoment B raw20394step1 raw20394step1Labels := by
      have hz : ∀ j, raw20394step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20394step1 = (fun i j => raw20394step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20394step1 raw20394step0; decide +kernel
      have hl : raw20394step1Labels = raw20394step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20394step0 raw20394step0Labels permutation80 hz
    mixedMoment B raw20394step1 raw20394step1Labels = mixedMoment B raw20394step2 raw20394step2Labels := by
      have ha : raw20394step2 = (fun i j => raw20394step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20394step2 raw20394step1; decide +kernel
      have hl : raw20394step2Labels = raw20394step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20394step1 raw20394step1Labels permutation8 permutation3
    mixedMoment B raw20394step2 raw20394step2Labels = mixedMoment B raw20394step3 raw20394step3Labels := by
      have ha : raw20394step3 = raw20394step2 := by apply Matrix.ext; unfold raw20394step3 raw20394step2; decide +kernel
      have hl : raw20394step2Labels = labelEmbedding6 ∘ raw20394step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20394step2 raw20394step2Labels raw20394step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4558 node4558Labels := by rfl

def raw20395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw20395Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw20395step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20395step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw20395step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20395step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20395step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20395step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20395step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20395 raw20395Labels = mixedMoment B node4558 node4558Labels := by
  calc
    mixedMoment B raw20395 raw20395Labels = mixedMoment B raw20395step0 raw20395step0Labels := by
      have hz : ∀ j, raw20395 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20395step0 = (fun i j => raw20395 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20395step0 raw20395; decide +kernel
      have hl : raw20395step0Labels = raw20395Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20395 raw20395Labels permutation434 hz
    mixedMoment B raw20395step0 raw20395step0Labels = mixedMoment B raw20395step1 raw20395step1Labels := by
      have hz : ∀ j, raw20395step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20395step1 = (fun i j => raw20395step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20395step1 raw20395step0; decide +kernel
      have hl : raw20395step1Labels = raw20395step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20395step0 raw20395step0Labels permutation56 hz
    mixedMoment B raw20395step1 raw20395step1Labels = mixedMoment B raw20395step2 raw20395step2Labels := by
      have ha : raw20395step2 = (fun i j => raw20395step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20395step2 raw20395step1; decide +kernel
      have hl : raw20395step2Labels = raw20395step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20395step1 raw20395step1Labels permutation8 permutation3
    mixedMoment B raw20395step2 raw20395step2Labels = mixedMoment B raw20395step3 raw20395step3Labels := by
      have ha : raw20395step3 = raw20395step2 := by apply Matrix.ext; unfold raw20395step3 raw20395step2; decide +kernel
      have hl : raw20395step2Labels = labelEmbedding6 ∘ raw20395step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20395step2 raw20395step2Labels raw20395step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4558 node4558Labels := by rfl

def raw20396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw20396Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20396step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw20396step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20396step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw20396step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20396step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20396step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw20396step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20396step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20396 raw20396Labels = mixedMoment B node4558 node4558Labels := by
  calc
    mixedMoment B raw20396 raw20396Labels = mixedMoment B raw20396step0 raw20396step0Labels := by
      have hz : ∀ j, raw20396 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20396step0 = (fun i j => raw20396 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20396step0 raw20396; decide +kernel
      have hl : raw20396step0Labels = raw20396Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20396 raw20396Labels permutation346 hz
    mixedMoment B raw20396step0 raw20396step0Labels = mixedMoment B raw20396step1 raw20396step1Labels := by
      have hz : ∀ j, raw20396step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20396step1 = (fun i j => raw20396step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20396step1 raw20396step0; decide +kernel
      have hl : raw20396step1Labels = raw20396step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20396step0 raw20396step0Labels permutation56 hz
    mixedMoment B raw20396step1 raw20396step1Labels = mixedMoment B raw20396step2 raw20396step2Labels := by
      have ha : raw20396step2 = (fun i j => raw20396step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20396step2 raw20396step1; decide +kernel
      have hl : raw20396step2Labels = raw20396step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20396step1 raw20396step1Labels permutation8 permutation3
    mixedMoment B raw20396step2 raw20396step2Labels = mixedMoment B raw20396step3 raw20396step3Labels := by
      have ha : raw20396step3 = raw20396step2 := by apply Matrix.ext; unfold raw20396step3 raw20396step2; decide +kernel
      have hl : raw20396step2Labels = labelEmbedding6 ∘ raw20396step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20396step2 raw20396step2Labels raw20396step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4558 node4558Labels := by rfl

def raw20397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20397Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20397step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20397step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20397step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20397step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20397step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20397 raw20397Labels = mixedMoment B node605 node605Labels := by
  calc
    mixedMoment B raw20397 raw20397Labels = mixedMoment B raw20397step0 raw20397step0Labels := by
      have hz : ∀ j, raw20397 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20397step0 = (fun i j => raw20397 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20397step0 raw20397; decide +kernel
      have hl : raw20397step0Labels = raw20397Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20397 raw20397Labels permutation434 hz
    mixedMoment B raw20397step0 raw20397step0Labels = mixedMoment B raw20397step1 raw20397step1Labels := by
      have hz : ∀ j, raw20397step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20397step1 = (fun i j => raw20397step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20397step1 raw20397step0; decide +kernel
      have hl : raw20397step1Labels = raw20397step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20397step0 raw20397step0Labels permutation80 hz
    mixedMoment B raw20397step1 raw20397step1Labels = mixedMoment B raw20397step2 raw20397step2Labels := by
      have ha : raw20397step2 = (fun i j => raw20397step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20397step2 raw20397step1; decide +kernel
      have hl : raw20397step2Labels = raw20397step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20397step1 raw20397step1Labels permutation10 permutation3
    _ = mixedMoment B node605 node605Labels := by rfl

def raw20398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20398Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20398step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20398step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20398step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20398step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20398 raw20398Labels = mixedMoment B node1131 node1131Labels := by
  calc
    mixedMoment B raw20398 raw20398Labels = mixedMoment B raw20398step0 raw20398step0Labels := by
      have hz : ∀ j, raw20398 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20398step0 = (fun i j => raw20398 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20398step0 raw20398; decide +kernel
      have hl : raw20398step0Labels = raw20398Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20398 raw20398Labels permutation434 hz
    mixedMoment B raw20398step0 raw20398step0Labels = mixedMoment B raw20398step1 raw20398step1Labels := by
      have ha : raw20398step1 = (fun i j => raw20398step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20398step1 raw20398step0; decide +kernel
      have hl : raw20398step1Labels = raw20398step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20398step0 raw20398step0Labels permutation40 permutation3
    _ = mixedMoment B node1131 node1131Labels := by rfl

def raw20399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20399Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20399step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20399step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20399step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20399 raw20399Labels = mixedMoment B node1131 node1131Labels := by
  calc
    mixedMoment B raw20399 raw20399Labels = mixedMoment B raw20399step0 raw20399step0Labels := by
      have hz : ∀ j, raw20399 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20399step0 = (fun i j => raw20399 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20399step0 raw20399; decide +kernel
      have hl : raw20399step0Labels = raw20399Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20399 raw20399Labels permutation346 hz
    mixedMoment B raw20399step0 raw20399step0Labels = mixedMoment B raw20399step1 raw20399step1Labels := by
      have ha : raw20399step1 = (fun i j => raw20399step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20399step1 raw20399step0; decide +kernel
      have hl : raw20399step1Labels = raw20399step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20399step0 raw20399step0Labels permutation40 permutation3
    _ = mixedMoment B node1131 node1131Labels := by rfl

def raw20400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw20400Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw20400step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20400step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw20400step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20400step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw20400step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20400 raw20400Labels = mixedMoment B node1301 node1301Labels := by
  calc
    mixedMoment B raw20400 raw20400Labels = mixedMoment B raw20400step0 raw20400step0Labels := by
      have hz : ∀ j, raw20400 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20400step0 = (fun i j => raw20400 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20400step0 raw20400; decide +kernel
      have hl : raw20400step0Labels = raw20400Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20400 raw20400Labels permutation434 hz
    mixedMoment B raw20400step0 raw20400step0Labels = mixedMoment B raw20400step1 raw20400step1Labels := by
      have hz : ∀ j, raw20400step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20400step1 = (fun i j => raw20400step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20400step1 raw20400step0; decide +kernel
      have hl : raw20400step1Labels = raw20400step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20400step0 raw20400step0Labels permutation80 hz
    mixedMoment B raw20400step1 raw20400step1Labels = mixedMoment B raw20400step2 raw20400step2Labels := by
      have ha : raw20400step2 = (fun i j => raw20400step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20400step2 raw20400step1; decide +kernel
      have hl : raw20400step2Labels = raw20400step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20400step1 raw20400step1Labels permutation10 permutation3
    _ = mixedMoment B node1301 node1301Labels := by rfl

def raw20401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20401Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20401step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20401step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20401step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20401step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20401step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20401 raw20401Labels = mixedMoment B node605 node605Labels := by
  calc
    mixedMoment B raw20401 raw20401Labels = mixedMoment B raw20401step0 raw20401step0Labels := by
      have hz : ∀ j, raw20401 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20401step0 = (fun i j => raw20401 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20401step0 raw20401; decide +kernel
      have hl : raw20401step0Labels = raw20401Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20401 raw20401Labels permutation434 hz
    mixedMoment B raw20401step0 raw20401step0Labels = mixedMoment B raw20401step1 raw20401step1Labels := by
      have hz : ∀ j, raw20401step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20401step1 = (fun i j => raw20401step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20401step1 raw20401step0; decide +kernel
      have hl : raw20401step1Labels = raw20401step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20401step0 raw20401step0Labels permutation56 hz
    mixedMoment B raw20401step1 raw20401step1Labels = mixedMoment B raw20401step2 raw20401step2Labels := by
      have ha : raw20401step2 = (fun i j => raw20401step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20401step2 raw20401step1; decide +kernel
      have hl : raw20401step2Labels = raw20401step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20401step1 raw20401step1Labels permutation10 permutation3
    _ = mixedMoment B node605 node605Labels := by rfl

def raw20402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20402Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20402step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20402step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20402step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20402step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20402 raw20402Labels = mixedMoment B node1131 node1131Labels := by
  calc
    mixedMoment B raw20402 raw20402Labels = mixedMoment B raw20402step0 raw20402step0Labels := by
      have hz : ∀ j, raw20402 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20402step0 = (fun i j => raw20402 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20402step0 raw20402; decide +kernel
      have hl : raw20402step0Labels = raw20402Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20402 raw20402Labels permutation434 hz
    mixedMoment B raw20402step0 raw20402step0Labels = mixedMoment B raw20402step1 raw20402step1Labels := by
      have ha : raw20402step1 = (fun i j => raw20402step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20402step1 raw20402step0; decide +kernel
      have hl : raw20402step1Labels = raw20402step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20402step0 raw20402step0Labels permutation34 permutation3
    _ = mixedMoment B node1131 node1131Labels := by rfl

def raw20403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20403Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20403step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20403step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20403step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20403 raw20403Labels = mixedMoment B node1131 node1131Labels := by
  calc
    mixedMoment B raw20403 raw20403Labels = mixedMoment B raw20403step0 raw20403step0Labels := by
      have hz : ∀ j, raw20403 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20403step0 = (fun i j => raw20403 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20403step0 raw20403; decide +kernel
      have hl : raw20403step0Labels = raw20403Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20403 raw20403Labels permutation265 hz
    mixedMoment B raw20403step0 raw20403step0Labels = mixedMoment B raw20403step1 raw20403step1Labels := by
      have ha : raw20403step1 = (fun i j => raw20403step0 (permutation40 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20403step1 raw20403step0; decide +kernel
      have hl : raw20403step1Labels = raw20403step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20403step0 raw20403step0Labels permutation40 permutation3
    _ = mixedMoment B node1131 node1131Labels := by rfl

def raw20404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw20404Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw20404step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20404step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw20404step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20404step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw20404step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20404 raw20404Labels = mixedMoment B node1301 node1301Labels := by
  calc
    mixedMoment B raw20404 raw20404Labels = mixedMoment B raw20404step0 raw20404step0Labels := by
      have hz : ∀ j, raw20404 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20404step0 = (fun i j => raw20404 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20404step0 raw20404; decide +kernel
      have hl : raw20404step0Labels = raw20404Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20404 raw20404Labels permutation434 hz
    mixedMoment B raw20404step0 raw20404step0Labels = mixedMoment B raw20404step1 raw20404step1Labels := by
      have hz : ∀ j, raw20404step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20404step1 = (fun i j => raw20404step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20404step1 raw20404step0; decide +kernel
      have hl : raw20404step1Labels = raw20404step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20404step0 raw20404step0Labels permutation56 hz
    mixedMoment B raw20404step1 raw20404step1Labels = mixedMoment B raw20404step2 raw20404step2Labels := by
      have ha : raw20404step2 = (fun i j => raw20404step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20404step2 raw20404step1; decide +kernel
      have hl : raw20404step2Labels = raw20404step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20404step1 raw20404step1Labels permutation10 permutation3
    _ = mixedMoment B node1301 node1301Labels := by rfl

def raw20405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20405Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20405step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20405step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20405step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20405step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20405step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20405step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20405 raw20405Labels = mixedMoment B node605 node605Labels := by
  calc
    mixedMoment B raw20405 raw20405Labels = mixedMoment B raw20405step0 raw20405step0Labels := by
      have hz : ∀ j, raw20405 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20405step0 = (fun i j => raw20405 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20405step0 raw20405; decide +kernel
      have hl : raw20405step0Labels = raw20405Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20405 raw20405Labels permutation346 hz
    mixedMoment B raw20405step0 raw20405step0Labels = mixedMoment B raw20405step1 raw20405step1Labels := by
      have hz : ∀ j, raw20405step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20405step1 = (fun i j => raw20405step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20405step1 raw20405step0; decide +kernel
      have hl : raw20405step1Labels = raw20405step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20405step0 raw20405step0Labels permutation56 hz
    mixedMoment B raw20405step1 raw20405step1Labels = mixedMoment B raw20405step2 raw20405step2Labels := by
      have ha : raw20405step2 = (fun i j => raw20405step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20405step2 raw20405step1; decide +kernel
      have hl : raw20405step2Labels = raw20405step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20405step1 raw20405step1Labels permutation10 permutation3
    _ = mixedMoment B node605 node605Labels := by rfl

def raw20406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20406Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20406step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20406step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20406step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20406 raw20406Labels = mixedMoment B node1131 node1131Labels := by
  calc
    mixedMoment B raw20406 raw20406Labels = mixedMoment B raw20406step0 raw20406step0Labels := by
      have hz : ∀ j, raw20406 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20406step0 = (fun i j => raw20406 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20406step0 raw20406; decide +kernel
      have hl : raw20406step0Labels = raw20406Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20406 raw20406Labels permutation346 hz
    mixedMoment B raw20406step0 raw20406step0Labels = mixedMoment B raw20406step1 raw20406step1Labels := by
      have ha : raw20406step1 = (fun i j => raw20406step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20406step1 raw20406step0; decide +kernel
      have hl : raw20406step1Labels = raw20406step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20406step0 raw20406step0Labels permutation34 permutation3
    _ = mixedMoment B node1131 node1131Labels := by rfl

def raw20407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20407Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20407step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw20407step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20407step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw20407step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20407 raw20407Labels = mixedMoment B node1131 node1131Labels := by
  calc
    mixedMoment B raw20407 raw20407Labels = mixedMoment B raw20407step0 raw20407step0Labels := by
      have hz : ∀ j, raw20407 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20407step0 = (fun i j => raw20407 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20407step0 raw20407; decide +kernel
      have hl : raw20407step0Labels = raw20407Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20407 raw20407Labels permutation265 hz
    mixedMoment B raw20407step0 raw20407step0Labels = mixedMoment B raw20407step1 raw20407step1Labels := by
      have ha : raw20407step1 = (fun i j => raw20407step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20407step1 raw20407step0; decide +kernel
      have hl : raw20407step1Labels = raw20407step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20407step0 raw20407step0Labels permutation34 permutation3
    _ = mixedMoment B node1131 node1131Labels := by rfl

def raw20408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw20408Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw20408step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20408step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw20408step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20408step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw20408step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20408 raw20408Labels = mixedMoment B node1301 node1301Labels := by
  calc
    mixedMoment B raw20408 raw20408Labels = mixedMoment B raw20408step0 raw20408step0Labels := by
      have hz : ∀ j, raw20408 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20408step0 = (fun i j => raw20408 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20408step0 raw20408; decide +kernel
      have hl : raw20408step0Labels = raw20408Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20408 raw20408Labels permutation346 hz
    mixedMoment B raw20408step0 raw20408step0Labels = mixedMoment B raw20408step1 raw20408step1Labels := by
      have hz : ∀ j, raw20408step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20408step1 = (fun i j => raw20408step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20408step1 raw20408step0; decide +kernel
      have hl : raw20408step1Labels = raw20408step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20408step0 raw20408step0Labels permutation56 hz
    mixedMoment B raw20408step1 raw20408step1Labels = mixedMoment B raw20408step2 raw20408step2Labels := by
      have ha : raw20408step2 = (fun i j => raw20408step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20408step2 raw20408step1; decide +kernel
      have hl : raw20408step2Labels = raw20408step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20408step1 raw20408step1Labels permutation10 permutation3
    _ = mixedMoment B node1301 node1301Labels := by rfl

def raw20409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw20409Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw20409step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20409step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw20409step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20409step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -1, -1], ![3, -2, -1]]
def raw20409step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20409step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-5, 2, 3], ![2, -1, -1], ![3, -1, -2]]
def raw20409step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20409 raw20409Labels = mixedMoment B node619 node619Labels := by
  calc
    mixedMoment B raw20409 raw20409Labels = mixedMoment B raw20409step0 raw20409step0Labels := by
      have hz : ∀ j, raw20409 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20409step0 = (fun i j => raw20409 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20409step0 raw20409; decide +kernel
      have hl : raw20409step0Labels = raw20409Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20409 raw20409Labels permutation434 hz
    mixedMoment B raw20409step0 raw20409step0Labels = mixedMoment B raw20409step1 raw20409step1Labels := by
      have hz : ∀ j, raw20409step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20409step1 = (fun i j => raw20409step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20409step1 raw20409step0; decide +kernel
      have hl : raw20409step1Labels = raw20409step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20409step0 raw20409step0Labels permutation80 hz
    mixedMoment B raw20409step1 raw20409step1Labels = mixedMoment B raw20409step2 raw20409step2Labels := by
      have hz : ∀ j, raw20409step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20409step2 = (fun i j => raw20409step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20409step2 raw20409step1; decide +kernel
      have hl : raw20409step2Labels = raw20409step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20409step1 raw20409step1Labels permutation14 hz
    mixedMoment B raw20409step2 raw20409step2Labels = mixedMoment B raw20409step3 raw20409step3Labels := by
      have ha : raw20409step3 = (fun i j => raw20409step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20409step3 raw20409step2; decide +kernel
      have hl : raw20409step3Labels = raw20409step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20409step2 raw20409step2Labels permutation2 permutation3
    _ = mixedMoment B node619 node619Labels := by rfl

def raw20410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw20410Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20410step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw20410step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20410step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw20410step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20410step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20410step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20410 raw20410Labels = mixedMoment B node1144 node1144Labels := by
  calc
    mixedMoment B raw20410 raw20410Labels = mixedMoment B raw20410step0 raw20410step0Labels := by
      have hz : ∀ j, raw20410 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20410step0 = (fun i j => raw20410 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20410step0 raw20410; decide +kernel
      have hl : raw20410step0Labels = raw20410Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20410 raw20410Labels permutation434 hz
    mixedMoment B raw20410step0 raw20410step0Labels = mixedMoment B raw20410step1 raw20410step1Labels := by
      have hz : ∀ j, raw20410step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20410step1 = (fun i j => raw20410step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20410step1 raw20410step0; decide +kernel
      have hl : raw20410step1Labels = raw20410step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20410step0 raw20410step0Labels permutation80 hz
    mixedMoment B raw20410step1 raw20410step1Labels = mixedMoment B raw20410step2 raw20410step2Labels := by
      have ha : raw20410step2 = (fun i j => raw20410step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20410step2 raw20410step1; decide +kernel
      have hl : raw20410step2Labels = raw20410step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20410step1 raw20410step1Labels permutation8 permutation3
    _ = mixedMoment B node1144 node1144Labels := by rfl

def raw20411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![3, -2, -1]]
def raw20411Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20411step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw20411step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20411step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw20411step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20411step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20411step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20411 raw20411Labels = mixedMoment B node1144 node1144Labels := by
  calc
    mixedMoment B raw20411 raw20411Labels = mixedMoment B raw20411step0 raw20411step0Labels := by
      have hz : ∀ j, raw20411 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20411step0 = (fun i j => raw20411 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20411step0 raw20411; decide +kernel
      have hl : raw20411step0Labels = raw20411Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20411 raw20411Labels permutation434 hz
    mixedMoment B raw20411step0 raw20411step0Labels = mixedMoment B raw20411step1 raw20411step1Labels := by
      have hz : ∀ j, raw20411step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20411step1 = (fun i j => raw20411step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20411step1 raw20411step0; decide +kernel
      have hl : raw20411step1Labels = raw20411step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20411step0 raw20411step0Labels permutation56 hz
    mixedMoment B raw20411step1 raw20411step1Labels = mixedMoment B raw20411step2 raw20411step2Labels := by
      have ha : raw20411step2 = (fun i j => raw20411step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20411step2 raw20411step1; decide +kernel
      have hl : raw20411step2Labels = raw20411step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20411step1 raw20411step1Labels permutation8 permutation3
    _ = mixedMoment B node1144 node1144Labels := by rfl

def raw20412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw20412Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20412step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw20412step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20412step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -1, -1], ![3, -2, -1]]
def raw20412step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20412step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -1, -1], ![3, -1, -2]]
def raw20412step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20412 raw20412Labels = mixedMoment B node1144 node1144Labels := by
  calc
    mixedMoment B raw20412 raw20412Labels = mixedMoment B raw20412step0 raw20412step0Labels := by
      have hz : ∀ j, raw20412 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20412step0 = (fun i j => raw20412 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20412step0 raw20412; decide +kernel
      have hl : raw20412step0Labels = raw20412Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20412 raw20412Labels permutation346 hz
    mixedMoment B raw20412step0 raw20412step0Labels = mixedMoment B raw20412step1 raw20412step1Labels := by
      have hz : ∀ j, raw20412step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20412step1 = (fun i j => raw20412step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20412step1 raw20412step0; decide +kernel
      have hl : raw20412step1Labels = raw20412step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20412step0 raw20412step0Labels permutation56 hz
    mixedMoment B raw20412step1 raw20412step1Labels = mixedMoment B raw20412step2 raw20412step2Labels := by
      have ha : raw20412step2 = (fun i j => raw20412step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20412step2 raw20412step1; decide +kernel
      have hl : raw20412step2Labels = raw20412step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20412step1 raw20412step1Labels permutation8 permutation3
    _ = mixedMoment B node1144 node1144Labels := by rfl

def raw20413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw20413Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw20413step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20413step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -1, -1], ![2, -1, -1]]
def raw20413step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20413step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw20413step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw20413step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![2, -1, -1]]
def raw20413step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20413 raw20413Labels = mixedMoment B node1312 node1312Labels := by
  calc
    mixedMoment B raw20413 raw20413Labels = mixedMoment B raw20413step0 raw20413step0Labels := by
      have hz : ∀ j, raw20413 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20413step0 = (fun i j => raw20413 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20413step0 raw20413; decide +kernel
      have hl : raw20413step0Labels = raw20413Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20413 raw20413Labels permutation434 hz
    mixedMoment B raw20413step0 raw20413step0Labels = mixedMoment B raw20413step1 raw20413step1Labels := by
      have hz : ∀ j, raw20413step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20413step1 = (fun i j => raw20413step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20413step1 raw20413step0; decide +kernel
      have hl : raw20413step1Labels = raw20413step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20413step0 raw20413step0Labels permutation80 hz
    mixedMoment B raw20413step1 raw20413step1Labels = mixedMoment B raw20413step2 raw20413step2Labels := by
      have hz : ∀ j, raw20413step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20413step2 = (fun i j => raw20413step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20413step2 raw20413step1; decide +kernel
      have hl : raw20413step2Labels = raw20413step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20413step1 raw20413step1Labels permutation14 hz
    mixedMoment B raw20413step2 raw20413step2Labels = mixedMoment B raw20413step3 raw20413step3Labels := by
      have ha : raw20413step3 = (fun i j => raw20413step2 (permutation2 i) (permutation3 j)) := by apply Matrix.ext; unfold raw20413step3 raw20413step2; decide +kernel
      have hl : raw20413step3Labels = raw20413step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20413step2 raw20413step2Labels permutation2 permutation3
    _ = mixedMoment B node1312 node1312Labels := by rfl

def raw20414 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20414Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20414step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20414step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20414step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20414step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20414step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20414step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw20414step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20414step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20414 raw20414Labels = mixedMoment B node4463 node4463Labels := by
  calc
    mixedMoment B raw20414 raw20414Labels = mixedMoment B raw20414step0 raw20414step0Labels := by
      have hz : ∀ j, raw20414 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20414step0 = (fun i j => raw20414 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20414step0 raw20414; decide +kernel
      have hl : raw20414step0Labels = raw20414Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20414 raw20414Labels permutation434 hz
    mixedMoment B raw20414step0 raw20414step0Labels = mixedMoment B raw20414step1 raw20414step1Labels := by
      have hz : ∀ j, raw20414step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20414step1 = (fun i j => raw20414step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20414step1 raw20414step0; decide +kernel
      have hl : raw20414step1Labels = raw20414step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20414step0 raw20414step0Labels permutation80 hz
    mixedMoment B raw20414step1 raw20414step1Labels = mixedMoment B raw20414step2 raw20414step2Labels := by
      have ha : raw20414step2 = (fun i j => raw20414step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20414step2 raw20414step1; decide +kernel
      have hl : raw20414step2Labels = raw20414step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20414step1 raw20414step1Labels permutation8 permutation7
    mixedMoment B raw20414step2 raw20414step2Labels = mixedMoment B raw20414step3 raw20414step3Labels := by
      have ha : raw20414step3 = raw20414step2 := by apply Matrix.ext; unfold raw20414step3 raw20414step2; decide +kernel
      have hl : raw20414step2Labels = labelEmbedding10 ∘ raw20414step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20414step2 raw20414step2Labels raw20414step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4463 node4463Labels := by rfl

def raw20415 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20415Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20415step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20415step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20415step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20415step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20415step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20415step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw20415step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20415step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20415 raw20415Labels = mixedMoment B node4463 node4463Labels := by
  calc
    mixedMoment B raw20415 raw20415Labels = mixedMoment B raw20415step0 raw20415step0Labels := by
      have hz : ∀ j, raw20415 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20415step0 = (fun i j => raw20415 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20415step0 raw20415; decide +kernel
      have hl : raw20415step0Labels = raw20415Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20415 raw20415Labels permutation434 hz
    mixedMoment B raw20415step0 raw20415step0Labels = mixedMoment B raw20415step1 raw20415step1Labels := by
      have hz : ∀ j, raw20415step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20415step1 = (fun i j => raw20415step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20415step1 raw20415step0; decide +kernel
      have hl : raw20415step1Labels = raw20415step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20415step0 raw20415step0Labels permutation56 hz
    mixedMoment B raw20415step1 raw20415step1Labels = mixedMoment B raw20415step2 raw20415step2Labels := by
      have ha : raw20415step2 = (fun i j => raw20415step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20415step2 raw20415step1; decide +kernel
      have hl : raw20415step2Labels = raw20415step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20415step1 raw20415step1Labels permutation8 permutation7
    mixedMoment B raw20415step2 raw20415step2Labels = mixedMoment B raw20415step3 raw20415step3Labels := by
      have ha : raw20415step3 = raw20415step2 := by apply Matrix.ext; unfold raw20415step3 raw20415step2; decide +kernel
      have hl : raw20415step2Labels = labelEmbedding10 ∘ raw20415step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20415step2 raw20415step2Labels raw20415step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4463 node4463Labels := by rfl

def raw20416 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20416Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20416step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20416step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20416step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20416step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20416step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw20416step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20416step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20416 raw20416Labels = mixedMoment B node4463 node4463Labels := by
  calc
    mixedMoment B raw20416 raw20416Labels = mixedMoment B raw20416step0 raw20416step0Labels := by
      have hz : ∀ j, raw20416 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20416step0 = (fun i j => raw20416 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20416step0 raw20416; decide +kernel
      have hl : raw20416step0Labels = raw20416Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20416 raw20416Labels permutation346 hz
    mixedMoment B raw20416step0 raw20416step0Labels = mixedMoment B raw20416step1 raw20416step1Labels := by
      have hz : ∀ j, raw20416step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20416step1 = (fun i j => raw20416step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20416step1 raw20416step0; decide +kernel
      have hl : raw20416step1Labels = raw20416step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20416step0 raw20416step0Labels permutation56 hz
    mixedMoment B raw20416step1 raw20416step1Labels = mixedMoment B raw20416step2 raw20416step2Labels := by
      have ha : raw20416step2 = (fun i j => raw20416step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20416step2 raw20416step1; decide +kernel
      have hl : raw20416step2Labels = raw20416step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20416step1 raw20416step1Labels permutation8 permutation7
    mixedMoment B raw20416step2 raw20416step2Labels = mixedMoment B raw20416step3 raw20416step3Labels := by
      have ha : raw20416step3 = raw20416step2 := by apply Matrix.ext; unfold raw20416step3 raw20416step2; decide +kernel
      have hl : raw20416step2Labels = labelEmbedding10 ∘ raw20416step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20416step2 raw20416step2Labels raw20416step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4463 node4463Labels := by rfl

def raw20417 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20417Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20417step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20417step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20417step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20417step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 1, 1], ![-1, -2, 3]]
def raw20417step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20417step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw20417step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw20417step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw20417step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20417 raw20417Labels = mixedMoment B node4507 node4507Labels := by
  calc
    mixedMoment B raw20417 raw20417Labels = mixedMoment B raw20417step0 raw20417step0Labels := by
      have hz : ∀ j, raw20417 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20417step0 = (fun i j => raw20417 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20417step0 raw20417; decide +kernel
      have hl : raw20417step0Labels = raw20417Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20417 raw20417Labels permutation434 hz
    mixedMoment B raw20417step0 raw20417step0Labels = mixedMoment B raw20417step1 raw20417step1Labels := by
      have hz : ∀ j, raw20417step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20417step1 = (fun i j => raw20417step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20417step1 raw20417step0; decide +kernel
      have hl : raw20417step1Labels = raw20417step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20417step0 raw20417step0Labels permutation80 hz
    mixedMoment B raw20417step1 raw20417step1Labels = mixedMoment B raw20417step2 raw20417step2Labels := by
      have hz : ∀ j, raw20417step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20417step2 = (fun i j => raw20417step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20417step2 raw20417step1; decide +kernel
      have hl : raw20417step2Labels = raw20417step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20417step1 raw20417step1Labels permutation14 hz
    mixedMoment B raw20417step2 raw20417step2Labels = mixedMoment B raw20417step3 raw20417step3Labels := by
      have ha : raw20417step3 = (fun i j => raw20417step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20417step3 raw20417step2; decide +kernel
      have hl : raw20417step3Labels = raw20417step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20417step2 raw20417step2Labels permutation2 permutation7
    mixedMoment B raw20417step3 raw20417step3Labels = mixedMoment B raw20417step4 raw20417step4Labels := by
      have ha : raw20417step4 = raw20417step3 := by apply Matrix.ext; unfold raw20417step4 raw20417step3; decide +kernel
      have hl : raw20417step3Labels = labelEmbedding10 ∘ raw20417step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20417step3 raw20417step3Labels raw20417step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4507 node4507Labels := by rfl

def raw20418 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20418Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20418step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20418step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20418step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20418step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-2, -1, 3]]
def raw20418step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20418step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![3, -1, -2]]
def raw20418step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw20418step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![3, -1, -2]]
def raw20418step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20418 raw20418Labels = mixedMoment B node4505 node4505Labels := by
  calc
    mixedMoment B raw20418 raw20418Labels = mixedMoment B raw20418step0 raw20418step0Labels := by
      have hz : ∀ j, raw20418 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20418step0 = (fun i j => raw20418 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20418step0 raw20418; decide +kernel
      have hl : raw20418step0Labels = raw20418Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20418 raw20418Labels permutation434 hz
    mixedMoment B raw20418step0 raw20418step0Labels = mixedMoment B raw20418step1 raw20418step1Labels := by
      have hz : ∀ j, raw20418step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20418step1 = (fun i j => raw20418step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20418step1 raw20418step0; decide +kernel
      have hl : raw20418step1Labels = raw20418step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20418step0 raw20418step0Labels permutation80 hz
    mixedMoment B raw20418step1 raw20418step1Labels = mixedMoment B raw20418step2 raw20418step2Labels := by
      have hz : ∀ j, raw20418step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20418step2 = (fun i j => raw20418step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20418step2 raw20418step1; decide +kernel
      have hl : raw20418step2Labels = raw20418step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20418step1 raw20418step1Labels permutation14 hz
    mixedMoment B raw20418step2 raw20418step2Labels = mixedMoment B raw20418step3 raw20418step3Labels := by
      have ha : raw20418step3 = (fun i j => raw20418step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20418step3 raw20418step2; decide +kernel
      have hl : raw20418step3Labels = raw20418step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20418step2 raw20418step2Labels permutation2 permutation7
    mixedMoment B raw20418step3 raw20418step3Labels = mixedMoment B raw20418step4 raw20418step4Labels := by
      have ha : raw20418step4 = raw20418step3 := by apply Matrix.ext; unfold raw20418step4 raw20418step3; decide +kernel
      have hl : raw20418step3Labels = labelEmbedding10 ∘ raw20418step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20418step3 raw20418step3Labels raw20418step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4505 node4505Labels := by rfl

def raw20419 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20419Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20419step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20419step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20419step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20419step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20419step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20419step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20419step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20419 raw20419Labels = mixedMoment B node4460 node4460Labels := by
  calc
    mixedMoment B raw20419 raw20419Labels = mixedMoment B raw20419step0 raw20419step0Labels := by
      have hz : ∀ j, raw20419 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20419step0 = (fun i j => raw20419 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20419step0 raw20419; decide +kernel
      have hl : raw20419step0Labels = raw20419Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20419 raw20419Labels permutation434 hz
    mixedMoment B raw20419step0 raw20419step0Labels = mixedMoment B raw20419step1 raw20419step1Labels := by
      have hz : ∀ j, raw20419step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20419step1 = (fun i j => raw20419step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20419step1 raw20419step0; decide +kernel
      have hl : raw20419step1Labels = raw20419step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20419step0 raw20419step0Labels permutation80 hz
    mixedMoment B raw20419step1 raw20419step1Labels = mixedMoment B raw20419step2 raw20419step2Labels := by
      have ha : raw20419step2 = (fun i j => raw20419step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20419step2 raw20419step1; decide +kernel
      have hl : raw20419step2Labels = raw20419step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20419step1 raw20419step1Labels permutation8 permutation6
    mixedMoment B raw20419step2 raw20419step2Labels = mixedMoment B raw20419step3 raw20419step3Labels := by
      have ha : raw20419step3 = raw20419step2 := by apply Matrix.ext; unfold raw20419step3 raw20419step2; decide +kernel
      have hl : raw20419step2Labels = labelEmbedding9 ∘ raw20419step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20419step2 raw20419step2Labels raw20419step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4460 node4460Labels := by rfl

def raw20420 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20420Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20420step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20420step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20420step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20420step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20420step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20420 raw20420Labels = mixedMoment B node4591 node4591Labels := by
  calc
    mixedMoment B raw20420 raw20420Labels = mixedMoment B raw20420step0 raw20420step0Labels := by
      have hz : ∀ j, raw20420 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20420step0 = (fun i j => raw20420 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20420step0 raw20420; decide +kernel
      have hl : raw20420step0Labels = raw20420Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20420 raw20420Labels permutation434 hz
    mixedMoment B raw20420step0 raw20420step0Labels = mixedMoment B raw20420step1 raw20420step1Labels := by
      have ha : raw20420step1 = (fun i j => raw20420step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20420step1 raw20420step0; decide +kernel
      have hl : raw20420step1Labels = raw20420step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20420step0 raw20420step0Labels permutation38 permutation6
    mixedMoment B raw20420step1 raw20420step1Labels = mixedMoment B raw20420step2 raw20420step2Labels := by
      have ha : raw20420step2 = raw20420step1 := by apply Matrix.ext; unfold raw20420step2 raw20420step1; decide +kernel
      have hl : raw20420step1Labels = labelEmbedding9 ∘ raw20420step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20420step1 raw20420step1Labels raw20420step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4591 node4591Labels := by rfl

def raw20421 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20421Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20421step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20421step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20421step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20421step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20421step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20421step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20421 raw20421Labels = mixedMoment B node4591 node4591Labels := by
  calc
    mixedMoment B raw20421 raw20421Labels = mixedMoment B raw20421step0 raw20421step0Labels := by
      have hz : ∀ j, raw20421 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20421step0 = (fun i j => raw20421 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20421step0 raw20421; decide +kernel
      have hl : raw20421step0Labels = raw20421Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20421 raw20421Labels permutation346 hz
    mixedMoment B raw20421step0 raw20421step0Labels = mixedMoment B raw20421step1 raw20421step1Labels := by
      have ha : raw20421step1 = (fun i j => raw20421step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20421step1 raw20421step0; decide +kernel
      have hl : raw20421step1Labels = raw20421step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20421step0 raw20421step0Labels permutation38 permutation6
    mixedMoment B raw20421step1 raw20421step1Labels = mixedMoment B raw20421step2 raw20421step2Labels := by
      have ha : raw20421step2 = raw20421step1 := by apply Matrix.ext; unfold raw20421step2 raw20421step1; decide +kernel
      have hl : raw20421step1Labels = labelEmbedding9 ∘ raw20421step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20421step1 raw20421step1Labels raw20421step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4591 node4591Labels := by rfl

def raw20422 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20422Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20422step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20422step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20422step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20422step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20422step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw20422step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw20422step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw20422step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20422 raw20422Labels = mixedMoment B node4609 node4609Labels := by
  calc
    mixedMoment B raw20422 raw20422Labels = mixedMoment B raw20422step0 raw20422step0Labels := by
      have hz : ∀ j, raw20422 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20422step0 = (fun i j => raw20422 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20422step0 raw20422; decide +kernel
      have hl : raw20422step0Labels = raw20422Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20422 raw20422Labels permutation434 hz
    mixedMoment B raw20422step0 raw20422step0Labels = mixedMoment B raw20422step1 raw20422step1Labels := by
      have hz : ∀ j, raw20422step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20422step1 = (fun i j => raw20422step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20422step1 raw20422step0; decide +kernel
      have hl : raw20422step1Labels = raw20422step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20422step0 raw20422step0Labels permutation80 hz
    mixedMoment B raw20422step1 raw20422step1Labels = mixedMoment B raw20422step2 raw20422step2Labels := by
      have ha : raw20422step2 = (fun i j => raw20422step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20422step2 raw20422step1; decide +kernel
      have hl : raw20422step2Labels = raw20422step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20422step1 raw20422step1Labels permutation8 permutation7
    mixedMoment B raw20422step2 raw20422step2Labels = mixedMoment B raw20422step3 raw20422step3Labels := by
      have ha : raw20422step3 = raw20422step2 := by apply Matrix.ext; unfold raw20422step3 raw20422step2; decide +kernel
      have hl : raw20422step2Labels = labelEmbedding10 ∘ raw20422step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20422step2 raw20422step2Labels raw20422step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4609 node4609Labels := by rfl

def raw20423 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20423Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20423step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20423step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20423step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20423step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20423step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20423step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw20423step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20423step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20423 raw20423Labels = mixedMoment B node4608 node4608Labels := by
  calc
    mixedMoment B raw20423 raw20423Labels = mixedMoment B raw20423step0 raw20423step0Labels := by
      have hz : ∀ j, raw20423 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20423step0 = (fun i j => raw20423 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20423step0 raw20423; decide +kernel
      have hl : raw20423step0Labels = raw20423Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20423 raw20423Labels permutation434 hz
    mixedMoment B raw20423step0 raw20423step0Labels = mixedMoment B raw20423step1 raw20423step1Labels := by
      have hz : ∀ j, raw20423step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20423step1 = (fun i j => raw20423step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20423step1 raw20423step0; decide +kernel
      have hl : raw20423step1Labels = raw20423step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20423step0 raw20423step0Labels permutation80 hz
    mixedMoment B raw20423step1 raw20423step1Labels = mixedMoment B raw20423step2 raw20423step2Labels := by
      have ha : raw20423step2 = (fun i j => raw20423step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20423step2 raw20423step1; decide +kernel
      have hl : raw20423step2Labels = raw20423step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20423step1 raw20423step1Labels permutation8 permutation7
    mixedMoment B raw20423step2 raw20423step2Labels = mixedMoment B raw20423step3 raw20423step3Labels := by
      have ha : raw20423step3 = raw20423step2 := by apply Matrix.ext; unfold raw20423step3 raw20423step2; decide +kernel
      have hl : raw20423step2Labels = labelEmbedding10 ∘ raw20423step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20423step2 raw20423step2Labels raw20423step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4608 node4608Labels := by rfl

def raw20424 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20424Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20424step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20424step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20424step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20424step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20424step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20424step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20424step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20424step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20424 raw20424Labels = mixedMoment B node4460 node4460Labels := by
  calc
    mixedMoment B raw20424 raw20424Labels = mixedMoment B raw20424step0 raw20424step0Labels := by
      have hz : ∀ j, raw20424 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20424step0 = (fun i j => raw20424 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20424step0 raw20424; decide +kernel
      have hl : raw20424step0Labels = raw20424Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20424 raw20424Labels permutation434 hz
    mixedMoment B raw20424step0 raw20424step0Labels = mixedMoment B raw20424step1 raw20424step1Labels := by
      have hz : ∀ j, raw20424step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20424step1 = (fun i j => raw20424step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20424step1 raw20424step0; decide +kernel
      have hl : raw20424step1Labels = raw20424step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20424step0 raw20424step0Labels permutation56 hz
    mixedMoment B raw20424step1 raw20424step1Labels = mixedMoment B raw20424step2 raw20424step2Labels := by
      have ha : raw20424step2 = (fun i j => raw20424step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20424step2 raw20424step1; decide +kernel
      have hl : raw20424step2Labels = raw20424step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20424step1 raw20424step1Labels permutation8 permutation6
    mixedMoment B raw20424step2 raw20424step2Labels = mixedMoment B raw20424step3 raw20424step3Labels := by
      have ha : raw20424step3 = raw20424step2 := by apply Matrix.ext; unfold raw20424step3 raw20424step2; decide +kernel
      have hl : raw20424step2Labels = labelEmbedding9 ∘ raw20424step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20424step2 raw20424step2Labels raw20424step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4460 node4460Labels := by rfl

def raw20425 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20425Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20425step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20425step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20425step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20425step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20425step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20425 raw20425Labels = mixedMoment B node4591 node4591Labels := by
  calc
    mixedMoment B raw20425 raw20425Labels = mixedMoment B raw20425step0 raw20425step0Labels := by
      have hz : ∀ j, raw20425 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20425step0 = (fun i j => raw20425 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20425step0 raw20425; decide +kernel
      have hl : raw20425step0Labels = raw20425Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20425 raw20425Labels permutation434 hz
    mixedMoment B raw20425step0 raw20425step0Labels = mixedMoment B raw20425step1 raw20425step1Labels := by
      have ha : raw20425step1 = (fun i j => raw20425step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20425step1 raw20425step0; decide +kernel
      have hl : raw20425step1Labels = raw20425step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20425step0 raw20425step0Labels permutation32 permutation6
    mixedMoment B raw20425step1 raw20425step1Labels = mixedMoment B raw20425step2 raw20425step2Labels := by
      have ha : raw20425step2 = raw20425step1 := by apply Matrix.ext; unfold raw20425step2 raw20425step1; decide +kernel
      have hl : raw20425step1Labels = labelEmbedding9 ∘ raw20425step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20425step1 raw20425step1Labels raw20425step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4591 node4591Labels := by rfl

def raw20426 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20426Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20426step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20426step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20426step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20426step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20426step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20426step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20426 raw20426Labels = mixedMoment B node4591 node4591Labels := by
  calc
    mixedMoment B raw20426 raw20426Labels = mixedMoment B raw20426step0 raw20426step0Labels := by
      have hz : ∀ j, raw20426 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20426step0 = (fun i j => raw20426 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20426step0 raw20426; decide +kernel
      have hl : raw20426step0Labels = raw20426Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20426 raw20426Labels permutation265 hz
    mixedMoment B raw20426step0 raw20426step0Labels = mixedMoment B raw20426step1 raw20426step1Labels := by
      have ha : raw20426step1 = (fun i j => raw20426step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20426step1 raw20426step0; decide +kernel
      have hl : raw20426step1Labels = raw20426step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20426step0 raw20426step0Labels permutation38 permutation6
    mixedMoment B raw20426step1 raw20426step1Labels = mixedMoment B raw20426step2 raw20426step2Labels := by
      have ha : raw20426step2 = raw20426step1 := by apply Matrix.ext; unfold raw20426step2 raw20426step1; decide +kernel
      have hl : raw20426step1Labels = labelEmbedding9 ∘ raw20426step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20426step1 raw20426step1Labels raw20426step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4591 node4591Labels := by rfl

def raw20427 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20427Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20427step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20427step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20427step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20427step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20427step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw20427step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw20427step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw20427step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20427 raw20427Labels = mixedMoment B node4609 node4609Labels := by
  calc
    mixedMoment B raw20427 raw20427Labels = mixedMoment B raw20427step0 raw20427step0Labels := by
      have hz : ∀ j, raw20427 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20427step0 = (fun i j => raw20427 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20427step0 raw20427; decide +kernel
      have hl : raw20427step0Labels = raw20427Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20427 raw20427Labels permutation434 hz
    mixedMoment B raw20427step0 raw20427step0Labels = mixedMoment B raw20427step1 raw20427step1Labels := by
      have hz : ∀ j, raw20427step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20427step1 = (fun i j => raw20427step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20427step1 raw20427step0; decide +kernel
      have hl : raw20427step1Labels = raw20427step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20427step0 raw20427step0Labels permutation56 hz
    mixedMoment B raw20427step1 raw20427step1Labels = mixedMoment B raw20427step2 raw20427step2Labels := by
      have ha : raw20427step2 = (fun i j => raw20427step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20427step2 raw20427step1; decide +kernel
      have hl : raw20427step2Labels = raw20427step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20427step1 raw20427step1Labels permutation8 permutation7
    mixedMoment B raw20427step2 raw20427step2Labels = mixedMoment B raw20427step3 raw20427step3Labels := by
      have ha : raw20427step3 = raw20427step2 := by apply Matrix.ext; unfold raw20427step3 raw20427step2; decide +kernel
      have hl : raw20427step2Labels = labelEmbedding10 ∘ raw20427step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20427step2 raw20427step2Labels raw20427step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4609 node4609Labels := by rfl

def raw20428 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20428Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20428step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20428step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20428step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20428step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20428step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20428step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw20428step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20428step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20428 raw20428Labels = mixedMoment B node4608 node4608Labels := by
  calc
    mixedMoment B raw20428 raw20428Labels = mixedMoment B raw20428step0 raw20428step0Labels := by
      have hz : ∀ j, raw20428 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20428step0 = (fun i j => raw20428 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20428step0 raw20428; decide +kernel
      have hl : raw20428step0Labels = raw20428Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20428 raw20428Labels permutation434 hz
    mixedMoment B raw20428step0 raw20428step0Labels = mixedMoment B raw20428step1 raw20428step1Labels := by
      have hz : ∀ j, raw20428step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20428step1 = (fun i j => raw20428step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20428step1 raw20428step0; decide +kernel
      have hl : raw20428step1Labels = raw20428step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20428step0 raw20428step0Labels permutation56 hz
    mixedMoment B raw20428step1 raw20428step1Labels = mixedMoment B raw20428step2 raw20428step2Labels := by
      have ha : raw20428step2 = (fun i j => raw20428step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20428step2 raw20428step1; decide +kernel
      have hl : raw20428step2Labels = raw20428step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20428step1 raw20428step1Labels permutation8 permutation7
    mixedMoment B raw20428step2 raw20428step2Labels = mixedMoment B raw20428step3 raw20428step3Labels := by
      have ha : raw20428step3 = raw20428step2 := by apply Matrix.ext; unfold raw20428step3 raw20428step2; decide +kernel
      have hl : raw20428step2Labels = labelEmbedding10 ∘ raw20428step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20428step2 raw20428step2Labels raw20428step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4608 node4608Labels := by rfl

def raw20429 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20429Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20429step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20429step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20429step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20429step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20429step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20429step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20429step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20429step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20429 raw20429Labels = mixedMoment B node4460 node4460Labels := by
  calc
    mixedMoment B raw20429 raw20429Labels = mixedMoment B raw20429step0 raw20429step0Labels := by
      have hz : ∀ j, raw20429 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20429step0 = (fun i j => raw20429 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20429step0 raw20429; decide +kernel
      have hl : raw20429step0Labels = raw20429Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20429 raw20429Labels permutation346 hz
    mixedMoment B raw20429step0 raw20429step0Labels = mixedMoment B raw20429step1 raw20429step1Labels := by
      have hz : ∀ j, raw20429step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20429step1 = (fun i j => raw20429step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20429step1 raw20429step0; decide +kernel
      have hl : raw20429step1Labels = raw20429step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20429step0 raw20429step0Labels permutation56 hz
    mixedMoment B raw20429step1 raw20429step1Labels = mixedMoment B raw20429step2 raw20429step2Labels := by
      have ha : raw20429step2 = (fun i j => raw20429step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20429step2 raw20429step1; decide +kernel
      have hl : raw20429step2Labels = raw20429step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20429step1 raw20429step1Labels permutation8 permutation6
    mixedMoment B raw20429step2 raw20429step2Labels = mixedMoment B raw20429step3 raw20429step3Labels := by
      have ha : raw20429step3 = raw20429step2 := by apply Matrix.ext; unfold raw20429step3 raw20429step2; decide +kernel
      have hl : raw20429step2Labels = labelEmbedding9 ∘ raw20429step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20429step2 raw20429step2Labels raw20429step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4460 node4460Labels := by rfl

def raw20430 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20430Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20430step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20430step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20430step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20430step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20430step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20430 raw20430Labels = mixedMoment B node4591 node4591Labels := by
  calc
    mixedMoment B raw20430 raw20430Labels = mixedMoment B raw20430step0 raw20430step0Labels := by
      have hz : ∀ j, raw20430 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20430step0 = (fun i j => raw20430 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20430step0 raw20430; decide +kernel
      have hl : raw20430step0Labels = raw20430Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20430 raw20430Labels permutation346 hz
    mixedMoment B raw20430step0 raw20430step0Labels = mixedMoment B raw20430step1 raw20430step1Labels := by
      have ha : raw20430step1 = (fun i j => raw20430step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20430step1 raw20430step0; decide +kernel
      have hl : raw20430step1Labels = raw20430step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20430step0 raw20430step0Labels permutation32 permutation6
    mixedMoment B raw20430step1 raw20430step1Labels = mixedMoment B raw20430step2 raw20430step2Labels := by
      have ha : raw20430step2 = raw20430step1 := by apply Matrix.ext; unfold raw20430step2 raw20430step1; decide +kernel
      have hl : raw20430step1Labels = labelEmbedding9 ∘ raw20430step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20430step1 raw20430step1Labels raw20430step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4591 node4591Labels := by rfl

def raw20431 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20431Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20431step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20431step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20431step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20431step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw20431step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20431 raw20431Labels = mixedMoment B node4591 node4591Labels := by
  calc
    mixedMoment B raw20431 raw20431Labels = mixedMoment B raw20431step0 raw20431step0Labels := by
      have hz : ∀ j, raw20431 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20431step0 = (fun i j => raw20431 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20431step0 raw20431; decide +kernel
      have hl : raw20431step0Labels = raw20431Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20431 raw20431Labels permutation265 hz
    mixedMoment B raw20431step0 raw20431step0Labels = mixedMoment B raw20431step1 raw20431step1Labels := by
      have ha : raw20431step1 = (fun i j => raw20431step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20431step1 raw20431step0; decide +kernel
      have hl : raw20431step1Labels = raw20431step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20431step0 raw20431step0Labels permutation32 permutation6
    mixedMoment B raw20431step1 raw20431step1Labels = mixedMoment B raw20431step2 raw20431step2Labels := by
      have ha : raw20431step2 = raw20431step1 := by apply Matrix.ext; unfold raw20431step2 raw20431step1; decide +kernel
      have hl : raw20431step1Labels = labelEmbedding9 ∘ raw20431step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20431step1 raw20431step1Labels raw20431step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4591 node4591Labels := by rfl

def raw20432 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20432Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20432step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20432step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20432step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20432step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20432step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw20432step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw20432step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw20432step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20432 raw20432Labels = mixedMoment B node4609 node4609Labels := by
  calc
    mixedMoment B raw20432 raw20432Labels = mixedMoment B raw20432step0 raw20432step0Labels := by
      have hz : ∀ j, raw20432 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20432step0 = (fun i j => raw20432 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20432step0 raw20432; decide +kernel
      have hl : raw20432step0Labels = raw20432Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20432 raw20432Labels permutation346 hz
    mixedMoment B raw20432step0 raw20432step0Labels = mixedMoment B raw20432step1 raw20432step1Labels := by
      have hz : ∀ j, raw20432step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20432step1 = (fun i j => raw20432step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20432step1 raw20432step0; decide +kernel
      have hl : raw20432step1Labels = raw20432step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20432step0 raw20432step0Labels permutation56 hz
    mixedMoment B raw20432step1 raw20432step1Labels = mixedMoment B raw20432step2 raw20432step2Labels := by
      have ha : raw20432step2 = (fun i j => raw20432step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20432step2 raw20432step1; decide +kernel
      have hl : raw20432step2Labels = raw20432step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20432step1 raw20432step1Labels permutation8 permutation7
    mixedMoment B raw20432step2 raw20432step2Labels = mixedMoment B raw20432step3 raw20432step3Labels := by
      have ha : raw20432step3 = raw20432step2 := by apply Matrix.ext; unfold raw20432step3 raw20432step2; decide +kernel
      have hl : raw20432step2Labels = labelEmbedding10 ∘ raw20432step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20432step2 raw20432step2Labels raw20432step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4609 node4609Labels := by rfl

def raw20433 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20433Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20433step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20433step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20433step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20433step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20433step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20433step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw20433step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20433step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20433 raw20433Labels = mixedMoment B node4608 node4608Labels := by
  calc
    mixedMoment B raw20433 raw20433Labels = mixedMoment B raw20433step0 raw20433step0Labels := by
      have hz : ∀ j, raw20433 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20433step0 = (fun i j => raw20433 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20433step0 raw20433; decide +kernel
      have hl : raw20433step0Labels = raw20433Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20433 raw20433Labels permutation346 hz
    mixedMoment B raw20433step0 raw20433step0Labels = mixedMoment B raw20433step1 raw20433step1Labels := by
      have hz : ∀ j, raw20433step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20433step1 = (fun i j => raw20433step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20433step1 raw20433step0; decide +kernel
      have hl : raw20433step1Labels = raw20433step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20433step0 raw20433step0Labels permutation56 hz
    mixedMoment B raw20433step1 raw20433step1Labels = mixedMoment B raw20433step2 raw20433step2Labels := by
      have ha : raw20433step2 = (fun i j => raw20433step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20433step2 raw20433step1; decide +kernel
      have hl : raw20433step2Labels = raw20433step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20433step1 raw20433step1Labels permutation8 permutation7
    mixedMoment B raw20433step2 raw20433step2Labels = mixedMoment B raw20433step3 raw20433step3Labels := by
      have ha : raw20433step3 = raw20433step2 := by apply Matrix.ext; unfold raw20433step3 raw20433step2; decide +kernel
      have hl : raw20433step2Labels = labelEmbedding10 ∘ raw20433step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20433step2 raw20433step2Labels raw20433step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4608 node4608Labels := by rfl

def raw20434 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20434Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20434step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20434step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20434step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20434step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20434step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![-1, -2, 3]]
def raw20434step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20434step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![3, -1, -2]]
def raw20434step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20434step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![3, -1, -2]]
def raw20434step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20434 raw20434Labels = mixedMoment B node4505 node4505Labels := by
  calc
    mixedMoment B raw20434 raw20434Labels = mixedMoment B raw20434step0 raw20434step0Labels := by
      have hz : ∀ j, raw20434 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20434step0 = (fun i j => raw20434 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20434step0 raw20434; decide +kernel
      have hl : raw20434step0Labels = raw20434Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20434 raw20434Labels permutation434 hz
    mixedMoment B raw20434step0 raw20434step0Labels = mixedMoment B raw20434step1 raw20434step1Labels := by
      have hz : ∀ j, raw20434step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20434step1 = (fun i j => raw20434step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20434step1 raw20434step0; decide +kernel
      have hl : raw20434step1Labels = raw20434step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20434step0 raw20434step0Labels permutation80 hz
    mixedMoment B raw20434step1 raw20434step1Labels = mixedMoment B raw20434step2 raw20434step2Labels := by
      have hz : ∀ j, raw20434step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20434step2 = (fun i j => raw20434step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20434step2 raw20434step1; decide +kernel
      have hl : raw20434step2Labels = raw20434step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20434step1 raw20434step1Labels permutation14 hz
    mixedMoment B raw20434step2 raw20434step2Labels = mixedMoment B raw20434step3 raw20434step3Labels := by
      have ha : raw20434step3 = (fun i j => raw20434step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20434step3 raw20434step2; decide +kernel
      have hl : raw20434step3Labels = raw20434step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20434step2 raw20434step2Labels permutation2 permutation6
    mixedMoment B raw20434step3 raw20434step3Labels = mixedMoment B raw20434step4 raw20434step4Labels := by
      have ha : raw20434step4 = raw20434step3 := by apply Matrix.ext; unfold raw20434step4 raw20434step3; decide +kernel
      have hl : raw20434step3Labels = labelEmbedding9 ∘ raw20434step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20434step3 raw20434step3Labels raw20434step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4505 node4505Labels := by rfl

def raw20435 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20435Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20435step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20435step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20435step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20435step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20435step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20435step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20435step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20435 raw20435Labels = mixedMoment B node4608 node4608Labels := by
  calc
    mixedMoment B raw20435 raw20435Labels = mixedMoment B raw20435step0 raw20435step0Labels := by
      have hz : ∀ j, raw20435 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20435step0 = (fun i j => raw20435 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20435step0 raw20435; decide +kernel
      have hl : raw20435step0Labels = raw20435Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20435 raw20435Labels permutation434 hz
    mixedMoment B raw20435step0 raw20435step0Labels = mixedMoment B raw20435step1 raw20435step1Labels := by
      have hz : ∀ j, raw20435step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20435step1 = (fun i j => raw20435step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20435step1 raw20435step0; decide +kernel
      have hl : raw20435step1Labels = raw20435step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20435step0 raw20435step0Labels permutation80 hz
    mixedMoment B raw20435step1 raw20435step1Labels = mixedMoment B raw20435step2 raw20435step2Labels := by
      have ha : raw20435step2 = (fun i j => raw20435step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20435step2 raw20435step1; decide +kernel
      have hl : raw20435step2Labels = raw20435step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20435step1 raw20435step1Labels permutation8 permutation6
    mixedMoment B raw20435step2 raw20435step2Labels = mixedMoment B raw20435step3 raw20435step3Labels := by
      have ha : raw20435step3 = raw20435step2 := by apply Matrix.ext; unfold raw20435step3 raw20435step2; decide +kernel
      have hl : raw20435step2Labels = labelEmbedding9 ∘ raw20435step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20435step2 raw20435step2Labels raw20435step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4608 node4608Labels := by rfl

def raw20436 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20436Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20436step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20436step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20436step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20436step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20436step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20436step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20436step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20436step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20436 raw20436Labels = mixedMoment B node4608 node4608Labels := by
  calc
    mixedMoment B raw20436 raw20436Labels = mixedMoment B raw20436step0 raw20436step0Labels := by
      have hz : ∀ j, raw20436 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20436step0 = (fun i j => raw20436 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20436step0 raw20436; decide +kernel
      have hl : raw20436step0Labels = raw20436Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20436 raw20436Labels permutation434 hz
    mixedMoment B raw20436step0 raw20436step0Labels = mixedMoment B raw20436step1 raw20436step1Labels := by
      have hz : ∀ j, raw20436step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20436step1 = (fun i j => raw20436step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20436step1 raw20436step0; decide +kernel
      have hl : raw20436step1Labels = raw20436step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20436step0 raw20436step0Labels permutation56 hz
    mixedMoment B raw20436step1 raw20436step1Labels = mixedMoment B raw20436step2 raw20436step2Labels := by
      have ha : raw20436step2 = (fun i j => raw20436step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20436step2 raw20436step1; decide +kernel
      have hl : raw20436step2Labels = raw20436step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20436step1 raw20436step1Labels permutation8 permutation6
    mixedMoment B raw20436step2 raw20436step2Labels = mixedMoment B raw20436step3 raw20436step3Labels := by
      have ha : raw20436step3 = raw20436step2 := by apply Matrix.ext; unfold raw20436step3 raw20436step2; decide +kernel
      have hl : raw20436step2Labels = labelEmbedding9 ∘ raw20436step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20436step2 raw20436step2Labels raw20436step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4608 node4608Labels := by rfl

def raw20437 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20437Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20437step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20437step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20437step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20437step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20437step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20437step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20437step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20437step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20437 raw20437Labels = mixedMoment B node4608 node4608Labels := by
  calc
    mixedMoment B raw20437 raw20437Labels = mixedMoment B raw20437step0 raw20437step0Labels := by
      have hz : ∀ j, raw20437 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20437step0 = (fun i j => raw20437 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20437step0 raw20437; decide +kernel
      have hl : raw20437step0Labels = raw20437Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20437 raw20437Labels permutation346 hz
    mixedMoment B raw20437step0 raw20437step0Labels = mixedMoment B raw20437step1 raw20437step1Labels := by
      have hz : ∀ j, raw20437step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20437step1 = (fun i j => raw20437step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20437step1 raw20437step0; decide +kernel
      have hl : raw20437step1Labels = raw20437step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20437step0 raw20437step0Labels permutation56 hz
    mixedMoment B raw20437step1 raw20437step1Labels = mixedMoment B raw20437step2 raw20437step2Labels := by
      have ha : raw20437step2 = (fun i j => raw20437step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20437step2 raw20437step1; decide +kernel
      have hl : raw20437step2Labels = raw20437step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20437step1 raw20437step1Labels permutation8 permutation6
    mixedMoment B raw20437step2 raw20437step2Labels = mixedMoment B raw20437step3 raw20437step3Labels := by
      have ha : raw20437step3 = raw20437step2 := by apply Matrix.ext; unfold raw20437step3 raw20437step2; decide +kernel
      have hl : raw20437step2Labels = labelEmbedding9 ∘ raw20437step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20437step2 raw20437step2Labels raw20437step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4608 node4608Labels := by rfl

def raw20438 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20438Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20438step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20438step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20438step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20438step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20438step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![-2, -1, 3]]
def raw20438step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20438step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw20438step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw20438step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw20438step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20438 raw20438Labels = mixedMoment B node4625 node4625Labels := by
  calc
    mixedMoment B raw20438 raw20438Labels = mixedMoment B raw20438step0 raw20438step0Labels := by
      have hz : ∀ j, raw20438 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20438step0 = (fun i j => raw20438 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20438step0 raw20438; decide +kernel
      have hl : raw20438step0Labels = raw20438Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20438 raw20438Labels permutation434 hz
    mixedMoment B raw20438step0 raw20438step0Labels = mixedMoment B raw20438step1 raw20438step1Labels := by
      have hz : ∀ j, raw20438step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20438step1 = (fun i j => raw20438step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20438step1 raw20438step0; decide +kernel
      have hl : raw20438step1Labels = raw20438step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20438step0 raw20438step0Labels permutation80 hz
    mixedMoment B raw20438step1 raw20438step1Labels = mixedMoment B raw20438step2 raw20438step2Labels := by
      have hz : ∀ j, raw20438step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20438step2 = (fun i j => raw20438step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20438step2 raw20438step1; decide +kernel
      have hl : raw20438step2Labels = raw20438step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20438step1 raw20438step1Labels permutation14 hz
    mixedMoment B raw20438step2 raw20438step2Labels = mixedMoment B raw20438step3 raw20438step3Labels := by
      have ha : raw20438step3 = (fun i j => raw20438step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20438step3 raw20438step2; decide +kernel
      have hl : raw20438step3Labels = raw20438step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20438step2 raw20438step2Labels permutation2 permutation7
    mixedMoment B raw20438step3 raw20438step3Labels = mixedMoment B raw20438step4 raw20438step4Labels := by
      have ha : raw20438step4 = raw20438step3 := by apply Matrix.ext; unfold raw20438step4 raw20438step3; decide +kernel
      have hl : raw20438step3Labels = labelEmbedding10 ∘ raw20438step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20438step3 raw20438step3Labels raw20438step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4625 node4625Labels := by rfl

def raw20439 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20439Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20439step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20439step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20439step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20439step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20439step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![0, -3, 3]]
def raw20439step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20439step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw20439step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20439step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![3, 0, -3]]
def raw20439step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20439 raw20439Labels = mixedMoment B node4501 node4501Labels := by
  calc
    mixedMoment B raw20439 raw20439Labels = mixedMoment B raw20439step0 raw20439step0Labels := by
      have hz : ∀ j, raw20439 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20439step0 = (fun i j => raw20439 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20439step0 raw20439; decide +kernel
      have hl : raw20439step0Labels = raw20439Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20439 raw20439Labels permutation434 hz
    mixedMoment B raw20439step0 raw20439step0Labels = mixedMoment B raw20439step1 raw20439step1Labels := by
      have hz : ∀ j, raw20439step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20439step1 = (fun i j => raw20439step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20439step1 raw20439step0; decide +kernel
      have hl : raw20439step1Labels = raw20439step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20439step0 raw20439step0Labels permutation80 hz
    mixedMoment B raw20439step1 raw20439step1Labels = mixedMoment B raw20439step2 raw20439step2Labels := by
      have hz : ∀ j, raw20439step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20439step2 = (fun i j => raw20439step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20439step2 raw20439step1; decide +kernel
      have hl : raw20439step2Labels = raw20439step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20439step1 raw20439step1Labels permutation14 hz
    mixedMoment B raw20439step2 raw20439step2Labels = mixedMoment B raw20439step3 raw20439step3Labels := by
      have ha : raw20439step3 = (fun i j => raw20439step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20439step3 raw20439step2; decide +kernel
      have hl : raw20439step3Labels = raw20439step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20439step2 raw20439step2Labels permutation2 permutation6
    mixedMoment B raw20439step3 raw20439step3Labels = mixedMoment B raw20439step4 raw20439step4Labels := by
      have ha : raw20439step4 = raw20439step3 := by apply Matrix.ext; unfold raw20439step4 raw20439step3; decide +kernel
      have hl : raw20439step3Labels = labelEmbedding9 ∘ raw20439step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20439step3 raw20439step3Labels raw20439step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4501 node4501Labels := by rfl

def raw20440 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20440Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20440step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20440step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20440step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20440step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20440step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20440step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20440step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20440 raw20440Labels = mixedMoment B node4605 node4605Labels := by
  calc
    mixedMoment B raw20440 raw20440Labels = mixedMoment B raw20440step0 raw20440step0Labels := by
      have hz : ∀ j, raw20440 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20440step0 = (fun i j => raw20440 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20440step0 raw20440; decide +kernel
      have hl : raw20440step0Labels = raw20440Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20440 raw20440Labels permutation434 hz
    mixedMoment B raw20440step0 raw20440step0Labels = mixedMoment B raw20440step1 raw20440step1Labels := by
      have hz : ∀ j, raw20440step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20440step1 = (fun i j => raw20440step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20440step1 raw20440step0; decide +kernel
      have hl : raw20440step1Labels = raw20440step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20440step0 raw20440step0Labels permutation80 hz
    mixedMoment B raw20440step1 raw20440step1Labels = mixedMoment B raw20440step2 raw20440step2Labels := by
      have ha : raw20440step2 = (fun i j => raw20440step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20440step2 raw20440step1; decide +kernel
      have hl : raw20440step2Labels = raw20440step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20440step1 raw20440step1Labels permutation8 permutation6
    mixedMoment B raw20440step2 raw20440step2Labels = mixedMoment B raw20440step3 raw20440step3Labels := by
      have ha : raw20440step3 = raw20440step2 := by apply Matrix.ext; unfold raw20440step3 raw20440step2; decide +kernel
      have hl : raw20440step2Labels = labelEmbedding9 ∘ raw20440step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20440step2 raw20440step2Labels raw20440step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4605 node4605Labels := by rfl

def raw20441 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20441Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20441step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20441step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20441step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20441step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20441step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20441step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20441step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20441 raw20441Labels = mixedMoment B node4605 node4605Labels := by
  calc
    mixedMoment B raw20441 raw20441Labels = mixedMoment B raw20441step0 raw20441step0Labels := by
      have hz : ∀ j, raw20441 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20441step0 = (fun i j => raw20441 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20441step0 raw20441; decide +kernel
      have hl : raw20441step0Labels = raw20441Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20441 raw20441Labels permutation434 hz
    mixedMoment B raw20441step0 raw20441step0Labels = mixedMoment B raw20441step1 raw20441step1Labels := by
      have hz : ∀ j, raw20441step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20441step1 = (fun i j => raw20441step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20441step1 raw20441step0; decide +kernel
      have hl : raw20441step1Labels = raw20441step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20441step0 raw20441step0Labels permutation56 hz
    mixedMoment B raw20441step1 raw20441step1Labels = mixedMoment B raw20441step2 raw20441step2Labels := by
      have ha : raw20441step2 = (fun i j => raw20441step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20441step2 raw20441step1; decide +kernel
      have hl : raw20441step2Labels = raw20441step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20441step1 raw20441step1Labels permutation8 permutation6
    mixedMoment B raw20441step2 raw20441step2Labels = mixedMoment B raw20441step3 raw20441step3Labels := by
      have ha : raw20441step3 = raw20441step2 := by apply Matrix.ext; unfold raw20441step3 raw20441step2; decide +kernel
      have hl : raw20441step2Labels = labelEmbedding9 ∘ raw20441step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20441step2 raw20441step2Labels raw20441step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4605 node4605Labels := by rfl

def raw20442 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20442Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20442step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20442step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20442step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20442step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20442step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20442step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![3, 0, -3]]
def raw20442step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20442 raw20442Labels = mixedMoment B node4605 node4605Labels := by
  calc
    mixedMoment B raw20442 raw20442Labels = mixedMoment B raw20442step0 raw20442step0Labels := by
      have hz : ∀ j, raw20442 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20442step0 = (fun i j => raw20442 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20442step0 raw20442; decide +kernel
      have hl : raw20442step0Labels = raw20442Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20442 raw20442Labels permutation346 hz
    mixedMoment B raw20442step0 raw20442step0Labels = mixedMoment B raw20442step1 raw20442step1Labels := by
      have hz : ∀ j, raw20442step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20442step1 = (fun i j => raw20442step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20442step1 raw20442step0; decide +kernel
      have hl : raw20442step1Labels = raw20442step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20442step0 raw20442step0Labels permutation56 hz
    mixedMoment B raw20442step1 raw20442step1Labels = mixedMoment B raw20442step2 raw20442step2Labels := by
      have ha : raw20442step2 = (fun i j => raw20442step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20442step2 raw20442step1; decide +kernel
      have hl : raw20442step2Labels = raw20442step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20442step1 raw20442step1Labels permutation8 permutation6
    mixedMoment B raw20442step2 raw20442step2Labels = mixedMoment B raw20442step3 raw20442step3Labels := by
      have ha : raw20442step3 = raw20442step2 := by apply Matrix.ext; unfold raw20442step3 raw20442step2; decide +kernel
      have hl : raw20442step2Labels = labelEmbedding9 ∘ raw20442step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20442step2 raw20442step2Labels raw20442step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4605 node4605Labels := by rfl

def raw20443 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20443Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20443step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20443step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20443step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20443step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 1, 1], ![0, -3, 3]]
def raw20443step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw20443step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw20443step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw20443step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![3, 0, -3]]
def raw20443step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical20443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20443 raw20443Labels = mixedMoment B node4621 node4621Labels := by
  calc
    mixedMoment B raw20443 raw20443Labels = mixedMoment B raw20443step0 raw20443step0Labels := by
      have hz : ∀ j, raw20443 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20443step0 = (fun i j => raw20443 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20443step0 raw20443; decide +kernel
      have hl : raw20443step0Labels = raw20443Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20443 raw20443Labels permutation434 hz
    mixedMoment B raw20443step0 raw20443step0Labels = mixedMoment B raw20443step1 raw20443step1Labels := by
      have hz : ∀ j, raw20443step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20443step1 = (fun i j => raw20443step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20443step1 raw20443step0; decide +kernel
      have hl : raw20443step1Labels = raw20443step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20443step0 raw20443step0Labels permutation80 hz
    mixedMoment B raw20443step1 raw20443step1Labels = mixedMoment B raw20443step2 raw20443step2Labels := by
      have hz : ∀ j, raw20443step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20443step2 = (fun i j => raw20443step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20443step2 raw20443step1; decide +kernel
      have hl : raw20443step2Labels = raw20443step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20443step1 raw20443step1Labels permutation14 hz
    mixedMoment B raw20443step2 raw20443step2Labels = mixedMoment B raw20443step3 raw20443step3Labels := by
      have ha : raw20443step3 = (fun i j => raw20443step2 (permutation2 i) (permutation6 j)) := by apply Matrix.ext; unfold raw20443step3 raw20443step2; decide +kernel
      have hl : raw20443step3Labels = raw20443step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20443step2 raw20443step2Labels permutation2 permutation6
    mixedMoment B raw20443step3 raw20443step3Labels = mixedMoment B raw20443step4 raw20443step4Labels := by
      have ha : raw20443step4 = raw20443step3 := by apply Matrix.ext; unfold raw20443step4 raw20443step3; decide +kernel
      have hl : raw20443step3Labels = labelEmbedding9 ∘ raw20443step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20443step3 raw20443step3Labels raw20443step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4621 node4621Labels := by rfl

def raw20444 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20444Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20444step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20444step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20444step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20444step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20444step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20444step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20444step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20444step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20444 raw20444Labels = mixedMoment B node1046 node1046Labels := by
  calc
    mixedMoment B raw20444 raw20444Labels = mixedMoment B raw20444step0 raw20444step0Labels := by
      have hz : ∀ j, raw20444 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20444step0 = (fun i j => raw20444 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20444step0 raw20444; decide +kernel
      have hl : raw20444step0Labels = raw20444Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20444 raw20444Labels permutation434 hz
    mixedMoment B raw20444step0 raw20444step0Labels = mixedMoment B raw20444step1 raw20444step1Labels := by
      have hz : ∀ j, raw20444step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20444step1 = (fun i j => raw20444step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20444step1 raw20444step0; decide +kernel
      have hl : raw20444step1Labels = raw20444step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20444step0 raw20444step0Labels permutation80 hz
    mixedMoment B raw20444step1 raw20444step1Labels = mixedMoment B raw20444step2 raw20444step2Labels := by
      have ha : raw20444step2 = (fun i j => raw20444step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20444step2 raw20444step1; decide +kernel
      have hl : raw20444step2Labels = raw20444step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20444step1 raw20444step1Labels permutation8 permutation7
    mixedMoment B raw20444step2 raw20444step2Labels = mixedMoment B raw20444step3 raw20444step3Labels := by
      have ha : raw20444step3 = raw20444step2 := by apply Matrix.ext; unfold raw20444step3 raw20444step2; decide +kernel
      have hl : raw20444step2Labels = labelEmbedding1 ∘ raw20444step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20444step2 raw20444step2Labels raw20444step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1046 node1046Labels := by rfl

def raw20445 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20445Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20445step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20445step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20445step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20445step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20445step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20445step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20445step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20445 raw20445Labels = mixedMoment B node1046 node1046Labels := by
  calc
    mixedMoment B raw20445 raw20445Labels = mixedMoment B raw20445step0 raw20445step0Labels := by
      have hz : ∀ j, raw20445 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20445step0 = (fun i j => raw20445 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20445step0 raw20445; decide +kernel
      have hl : raw20445step0Labels = raw20445Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20445 raw20445Labels permutation434 hz
    mixedMoment B raw20445step0 raw20445step0Labels = mixedMoment B raw20445step1 raw20445step1Labels := by
      have hz : ∀ j, raw20445step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20445step1 = (fun i j => raw20445step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20445step1 raw20445step0; decide +kernel
      have hl : raw20445step1Labels = raw20445step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20445step0 raw20445step0Labels permutation56 hz
    mixedMoment B raw20445step1 raw20445step1Labels = mixedMoment B raw20445step2 raw20445step2Labels := by
      have ha : raw20445step2 = (fun i j => raw20445step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20445step2 raw20445step1; decide +kernel
      have hl : raw20445step2Labels = raw20445step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20445step1 raw20445step1Labels permutation8 permutation7
    mixedMoment B raw20445step2 raw20445step2Labels = mixedMoment B raw20445step3 raw20445step3Labels := by
      have ha : raw20445step3 = raw20445step2 := by apply Matrix.ext; unfold raw20445step3 raw20445step2; decide +kernel
      have hl : raw20445step2Labels = labelEmbedding1 ∘ raw20445step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20445step2 raw20445step2Labels raw20445step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1046 node1046Labels := by rfl

def raw20446 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20446Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20446step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20446step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20446step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20446step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20446step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20446step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20446step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20446 raw20446Labels = mixedMoment B node1046 node1046Labels := by
  calc
    mixedMoment B raw20446 raw20446Labels = mixedMoment B raw20446step0 raw20446step0Labels := by
      have hz : ∀ j, raw20446 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20446step0 = (fun i j => raw20446 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20446step0 raw20446; decide +kernel
      have hl : raw20446step0Labels = raw20446Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20446 raw20446Labels permutation346 hz
    mixedMoment B raw20446step0 raw20446step0Labels = mixedMoment B raw20446step1 raw20446step1Labels := by
      have hz : ∀ j, raw20446step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20446step1 = (fun i j => raw20446step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20446step1 raw20446step0; decide +kernel
      have hl : raw20446step1Labels = raw20446step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20446step0 raw20446step0Labels permutation56 hz
    mixedMoment B raw20446step1 raw20446step1Labels = mixedMoment B raw20446step2 raw20446step2Labels := by
      have ha : raw20446step2 = (fun i j => raw20446step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20446step2 raw20446step1; decide +kernel
      have hl : raw20446step2Labels = raw20446step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20446step1 raw20446step1Labels permutation8 permutation7
    mixedMoment B raw20446step2 raw20446step2Labels = mixedMoment B raw20446step3 raw20446step3Labels := by
      have ha : raw20446step3 = raw20446step2 := by apply Matrix.ext; unfold raw20446step3 raw20446step2; decide +kernel
      have hl : raw20446step2Labels = labelEmbedding1 ∘ raw20446step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20446step2 raw20446step2Labels raw20446step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1046 node1046Labels := by rfl

def raw20447 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20447Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20447step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20447step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20447step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20447step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20447step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 1, 1], ![-1, -2, 3]]
def raw20447step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20447step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw20447step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20447step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 1, -2], ![3, -2, -1]]
def raw20447step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20447 raw20447Labels = mixedMoment B node1091 node1091Labels := by
  calc
    mixedMoment B raw20447 raw20447Labels = mixedMoment B raw20447step0 raw20447step0Labels := by
      have hz : ∀ j, raw20447 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20447step0 = (fun i j => raw20447 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20447step0 raw20447; decide +kernel
      have hl : raw20447step0Labels = raw20447Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20447 raw20447Labels permutation434 hz
    mixedMoment B raw20447step0 raw20447step0Labels = mixedMoment B raw20447step1 raw20447step1Labels := by
      have hz : ∀ j, raw20447step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20447step1 = (fun i j => raw20447step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20447step1 raw20447step0; decide +kernel
      have hl : raw20447step1Labels = raw20447step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20447step0 raw20447step0Labels permutation80 hz
    mixedMoment B raw20447step1 raw20447step1Labels = mixedMoment B raw20447step2 raw20447step2Labels := by
      have hz : ∀ j, raw20447step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20447step2 = (fun i j => raw20447step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20447step2 raw20447step1; decide +kernel
      have hl : raw20447step2Labels = raw20447step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20447step1 raw20447step1Labels permutation14 hz
    mixedMoment B raw20447step2 raw20447step2Labels = mixedMoment B raw20447step3 raw20447step3Labels := by
      have ha : raw20447step3 = (fun i j => raw20447step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20447step3 raw20447step2; decide +kernel
      have hl : raw20447step3Labels = raw20447step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20447step2 raw20447step2Labels permutation2 permutation7
    mixedMoment B raw20447step3 raw20447step3Labels = mixedMoment B raw20447step4 raw20447step4Labels := by
      have ha : raw20447step4 = raw20447step3 := by apply Matrix.ext; unfold raw20447step4 raw20447step3; decide +kernel
      have hl : raw20447step3Labels = labelEmbedding1 ∘ raw20447step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20447step3 raw20447step3Labels raw20447step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1091 node1091Labels := by rfl

def raw20448 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20448Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20448step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20448step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20448step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20448step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20448step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-2, -1, 3]]
def raw20448step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20448step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![3, -1, -2]]
def raw20448step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20448step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![3, -1, -2]]
def raw20448step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20448 raw20448Labels = mixedMoment B node1089 node1089Labels := by
  calc
    mixedMoment B raw20448 raw20448Labels = mixedMoment B raw20448step0 raw20448step0Labels := by
      have hz : ∀ j, raw20448 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20448step0 = (fun i j => raw20448 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20448step0 raw20448; decide +kernel
      have hl : raw20448step0Labels = raw20448Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20448 raw20448Labels permutation434 hz
    mixedMoment B raw20448step0 raw20448step0Labels = mixedMoment B raw20448step1 raw20448step1Labels := by
      have hz : ∀ j, raw20448step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20448step1 = (fun i j => raw20448step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20448step1 raw20448step0; decide +kernel
      have hl : raw20448step1Labels = raw20448step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20448step0 raw20448step0Labels permutation80 hz
    mixedMoment B raw20448step1 raw20448step1Labels = mixedMoment B raw20448step2 raw20448step2Labels := by
      have hz : ∀ j, raw20448step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20448step2 = (fun i j => raw20448step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20448step2 raw20448step1; decide +kernel
      have hl : raw20448step2Labels = raw20448step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20448step1 raw20448step1Labels permutation14 hz
    mixedMoment B raw20448step2 raw20448step2Labels = mixedMoment B raw20448step3 raw20448step3Labels := by
      have ha : raw20448step3 = (fun i j => raw20448step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20448step3 raw20448step2; decide +kernel
      have hl : raw20448step3Labels = raw20448step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20448step2 raw20448step2Labels permutation2 permutation7
    mixedMoment B raw20448step3 raw20448step3Labels = mixedMoment B raw20448step4 raw20448step4Labels := by
      have ha : raw20448step4 = raw20448step3 := by apply Matrix.ext; unfold raw20448step4 raw20448step3; decide +kernel
      have hl : raw20448step3Labels = labelEmbedding1 ∘ raw20448step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20448step3 raw20448step3Labels raw20448step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1089 node1089Labels := by rfl

def raw20449 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20449Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20449step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20449step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20449step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20449step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20449step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw20449step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20449step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw20449step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20449 raw20449Labels = mixedMoment B node1416 node1416Labels := by
  calc
    mixedMoment B raw20449 raw20449Labels = mixedMoment B raw20449step0 raw20449step0Labels := by
      have hz : ∀ j, raw20449 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20449step0 = (fun i j => raw20449 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20449step0 raw20449; decide +kernel
      have hl : raw20449step0Labels = raw20449Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20449 raw20449Labels permutation434 hz
    mixedMoment B raw20449step0 raw20449step0Labels = mixedMoment B raw20449step1 raw20449step1Labels := by
      have hz : ∀ j, raw20449step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20449step1 = (fun i j => raw20449step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20449step1 raw20449step0; decide +kernel
      have hl : raw20449step1Labels = raw20449step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20449step0 raw20449step0Labels permutation80 hz
    mixedMoment B raw20449step1 raw20449step1Labels = mixedMoment B raw20449step2 raw20449step2Labels := by
      have ha : raw20449step2 = (fun i j => raw20449step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20449step2 raw20449step1; decide +kernel
      have hl : raw20449step2Labels = raw20449step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20449step1 raw20449step1Labels permutation8 permutation7
    mixedMoment B raw20449step2 raw20449step2Labels = mixedMoment B raw20449step3 raw20449step3Labels := by
      have ha : raw20449step3 = raw20449step2 := by apply Matrix.ext; unfold raw20449step3 raw20449step2; decide +kernel
      have hl : raw20449step2Labels = labelEmbedding1 ∘ raw20449step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20449step2 raw20449step2Labels raw20449step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1416 node1416Labels := by rfl

def raw20450 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20450Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20450step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20450step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20450step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20450step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20450step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20450 raw20450Labels = mixedMoment B node1217 node1217Labels := by
  calc
    mixedMoment B raw20450 raw20450Labels = mixedMoment B raw20450step0 raw20450step0Labels := by
      have hz : ∀ j, raw20450 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20450step0 = (fun i j => raw20450 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20450step0 raw20450; decide +kernel
      have hl : raw20450step0Labels = raw20450Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20450 raw20450Labels permutation434 hz
    mixedMoment B raw20450step0 raw20450step0Labels = mixedMoment B raw20450step1 raw20450step1Labels := by
      have ha : raw20450step1 = (fun i j => raw20450step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20450step1 raw20450step0; decide +kernel
      have hl : raw20450step1Labels = raw20450step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20450step0 raw20450step0Labels permutation32 permutation7
    mixedMoment B raw20450step1 raw20450step1Labels = mixedMoment B raw20450step2 raw20450step2Labels := by
      have ha : raw20450step2 = raw20450step1 := by apply Matrix.ext; unfold raw20450step2 raw20450step1; decide +kernel
      have hl : raw20450step1Labels = labelEmbedding1 ∘ raw20450step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20450step1 raw20450step1Labels raw20450step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1217 node1217Labels := by rfl

def raw20451 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20451Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20451step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20451step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20451step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20451step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20451step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20451step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20451 raw20451Labels = mixedMoment B node1217 node1217Labels := by
  calc
    mixedMoment B raw20451 raw20451Labels = mixedMoment B raw20451step0 raw20451step0Labels := by
      have hz : ∀ j, raw20451 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20451step0 = (fun i j => raw20451 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20451step0 raw20451; decide +kernel
      have hl : raw20451step0Labels = raw20451Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20451 raw20451Labels permutation346 hz
    mixedMoment B raw20451step0 raw20451step0Labels = mixedMoment B raw20451step1 raw20451step1Labels := by
      have ha : raw20451step1 = (fun i j => raw20451step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20451step1 raw20451step0; decide +kernel
      have hl : raw20451step1Labels = raw20451step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20451step0 raw20451step0Labels permutation32 permutation7
    mixedMoment B raw20451step1 raw20451step1Labels = mixedMoment B raw20451step2 raw20451step2Labels := by
      have ha : raw20451step2 = raw20451step1 := by apply Matrix.ext; unfold raw20451step2 raw20451step1; decide +kernel
      have hl : raw20451step1Labels = labelEmbedding1 ∘ raw20451step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20451step1 raw20451step1Labels raw20451step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1217 node1217Labels := by rfl

def raw20452 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20452Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20452step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20452step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20452step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20452step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20452step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw20452step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20452step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw20452step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20452 raw20452Labels = mixedMoment B node1243 node1243Labels := by
  calc
    mixedMoment B raw20452 raw20452Labels = mixedMoment B raw20452step0 raw20452step0Labels := by
      have hz : ∀ j, raw20452 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20452step0 = (fun i j => raw20452 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20452step0 raw20452; decide +kernel
      have hl : raw20452step0Labels = raw20452Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20452 raw20452Labels permutation434 hz
    mixedMoment B raw20452step0 raw20452step0Labels = mixedMoment B raw20452step1 raw20452step1Labels := by
      have hz : ∀ j, raw20452step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20452step1 = (fun i j => raw20452step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20452step1 raw20452step0; decide +kernel
      have hl : raw20452step1Labels = raw20452step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20452step0 raw20452step0Labels permutation80 hz
    mixedMoment B raw20452step1 raw20452step1Labels = mixedMoment B raw20452step2 raw20452step2Labels := by
      have ha : raw20452step2 = (fun i j => raw20452step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20452step2 raw20452step1; decide +kernel
      have hl : raw20452step2Labels = raw20452step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20452step1 raw20452step1Labels permutation8 permutation7
    mixedMoment B raw20452step2 raw20452step2Labels = mixedMoment B raw20452step3 raw20452step3Labels := by
      have ha : raw20452step3 = raw20452step2 := by apply Matrix.ext; unfold raw20452step3 raw20452step2; decide +kernel
      have hl : raw20452step2Labels = labelEmbedding1 ∘ raw20452step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20452step2 raw20452step2Labels raw20452step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1243 node1243Labels := by rfl

def raw20453 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20453Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20453step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20453step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20453step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20453step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20453step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20453step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20453step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20453 raw20453Labels = mixedMoment B node1242 node1242Labels := by
  calc
    mixedMoment B raw20453 raw20453Labels = mixedMoment B raw20453step0 raw20453step0Labels := by
      have hz : ∀ j, raw20453 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20453step0 = (fun i j => raw20453 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20453step0 raw20453; decide +kernel
      have hl : raw20453step0Labels = raw20453Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20453 raw20453Labels permutation434 hz
    mixedMoment B raw20453step0 raw20453step0Labels = mixedMoment B raw20453step1 raw20453step1Labels := by
      have hz : ∀ j, raw20453step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20453step1 = (fun i j => raw20453step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20453step1 raw20453step0; decide +kernel
      have hl : raw20453step1Labels = raw20453step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20453step0 raw20453step0Labels permutation80 hz
    mixedMoment B raw20453step1 raw20453step1Labels = mixedMoment B raw20453step2 raw20453step2Labels := by
      have ha : raw20453step2 = (fun i j => raw20453step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20453step2 raw20453step1; decide +kernel
      have hl : raw20453step2Labels = raw20453step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20453step1 raw20453step1Labels permutation8 permutation7
    mixedMoment B raw20453step2 raw20453step2Labels = mixedMoment B raw20453step3 raw20453step3Labels := by
      have ha : raw20453step3 = raw20453step2 := by apply Matrix.ext; unfold raw20453step3 raw20453step2; decide +kernel
      have hl : raw20453step2Labels = labelEmbedding1 ∘ raw20453step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20453step2 raw20453step2Labels raw20453step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1242 node1242Labels := by rfl

def raw20454 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20454Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20454step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20454step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20454step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20454step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20454step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw20454step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20454step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw20454step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20454 raw20454Labels = mixedMoment B node1416 node1416Labels := by
  calc
    mixedMoment B raw20454 raw20454Labels = mixedMoment B raw20454step0 raw20454step0Labels := by
      have hz : ∀ j, raw20454 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20454step0 = (fun i j => raw20454 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20454step0 raw20454; decide +kernel
      have hl : raw20454step0Labels = raw20454Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20454 raw20454Labels permutation434 hz
    mixedMoment B raw20454step0 raw20454step0Labels = mixedMoment B raw20454step1 raw20454step1Labels := by
      have hz : ∀ j, raw20454step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20454step1 = (fun i j => raw20454step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20454step1 raw20454step0; decide +kernel
      have hl : raw20454step1Labels = raw20454step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20454step0 raw20454step0Labels permutation56 hz
    mixedMoment B raw20454step1 raw20454step1Labels = mixedMoment B raw20454step2 raw20454step2Labels := by
      have ha : raw20454step2 = (fun i j => raw20454step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20454step2 raw20454step1; decide +kernel
      have hl : raw20454step2Labels = raw20454step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20454step1 raw20454step1Labels permutation8 permutation7
    mixedMoment B raw20454step2 raw20454step2Labels = mixedMoment B raw20454step3 raw20454step3Labels := by
      have ha : raw20454step3 = raw20454step2 := by apply Matrix.ext; unfold raw20454step3 raw20454step2; decide +kernel
      have hl : raw20454step2Labels = labelEmbedding1 ∘ raw20454step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20454step2 raw20454step2Labels raw20454step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1416 node1416Labels := by rfl

def raw20455 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20455Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20455step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20455step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20455step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20455step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20455step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20455step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20455 raw20455Labels = mixedMoment B node1217 node1217Labels := by
  calc
    mixedMoment B raw20455 raw20455Labels = mixedMoment B raw20455step0 raw20455step0Labels := by
      have hz : ∀ j, raw20455 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20455step0 = (fun i j => raw20455 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20455step0 raw20455; decide +kernel
      have hl : raw20455step0Labels = raw20455Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20455 raw20455Labels permutation434 hz
    mixedMoment B raw20455step0 raw20455step0Labels = mixedMoment B raw20455step1 raw20455step1Labels := by
      have ha : raw20455step1 = (fun i j => raw20455step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20455step1 raw20455step0; decide +kernel
      have hl : raw20455step1Labels = raw20455step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20455step0 raw20455step0Labels permutation38 permutation7
    mixedMoment B raw20455step1 raw20455step1Labels = mixedMoment B raw20455step2 raw20455step2Labels := by
      have ha : raw20455step2 = raw20455step1 := by apply Matrix.ext; unfold raw20455step2 raw20455step1; decide +kernel
      have hl : raw20455step1Labels = labelEmbedding1 ∘ raw20455step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20455step1 raw20455step1Labels raw20455step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1217 node1217Labels := by rfl

def raw20456 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20456Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20456step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20456step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20456step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20456step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20456step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20456step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20456 raw20456Labels = mixedMoment B node1217 node1217Labels := by
  calc
    mixedMoment B raw20456 raw20456Labels = mixedMoment B raw20456step0 raw20456step0Labels := by
      have hz : ∀ j, raw20456 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20456step0 = (fun i j => raw20456 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20456step0 raw20456; decide +kernel
      have hl : raw20456step0Labels = raw20456Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20456 raw20456Labels permutation265 hz
    mixedMoment B raw20456step0 raw20456step0Labels = mixedMoment B raw20456step1 raw20456step1Labels := by
      have ha : raw20456step1 = (fun i j => raw20456step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20456step1 raw20456step0; decide +kernel
      have hl : raw20456step1Labels = raw20456step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20456step0 raw20456step0Labels permutation32 permutation7
    mixedMoment B raw20456step1 raw20456step1Labels = mixedMoment B raw20456step2 raw20456step2Labels := by
      have ha : raw20456step2 = raw20456step1 := by apply Matrix.ext; unfold raw20456step2 raw20456step1; decide +kernel
      have hl : raw20456step1Labels = labelEmbedding1 ∘ raw20456step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20456step1 raw20456step1Labels raw20456step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1217 node1217Labels := by rfl

def raw20457 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20457Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20457step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20457step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20457step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20457step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20457step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw20457step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20457step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw20457step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20457 raw20457Labels = mixedMoment B node1243 node1243Labels := by
  calc
    mixedMoment B raw20457 raw20457Labels = mixedMoment B raw20457step0 raw20457step0Labels := by
      have hz : ∀ j, raw20457 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20457step0 = (fun i j => raw20457 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20457step0 raw20457; decide +kernel
      have hl : raw20457step0Labels = raw20457Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20457 raw20457Labels permutation434 hz
    mixedMoment B raw20457step0 raw20457step0Labels = mixedMoment B raw20457step1 raw20457step1Labels := by
      have hz : ∀ j, raw20457step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20457step1 = (fun i j => raw20457step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20457step1 raw20457step0; decide +kernel
      have hl : raw20457step1Labels = raw20457step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20457step0 raw20457step0Labels permutation56 hz
    mixedMoment B raw20457step1 raw20457step1Labels = mixedMoment B raw20457step2 raw20457step2Labels := by
      have ha : raw20457step2 = (fun i j => raw20457step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20457step2 raw20457step1; decide +kernel
      have hl : raw20457step2Labels = raw20457step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20457step1 raw20457step1Labels permutation8 permutation7
    mixedMoment B raw20457step2 raw20457step2Labels = mixedMoment B raw20457step3 raw20457step3Labels := by
      have ha : raw20457step3 = raw20457step2 := by apply Matrix.ext; unfold raw20457step3 raw20457step2; decide +kernel
      have hl : raw20457step2Labels = labelEmbedding1 ∘ raw20457step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20457step2 raw20457step2Labels raw20457step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1243 node1243Labels := by rfl

def raw20458 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20458Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20458step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20458step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20458step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20458step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20458step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20458step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20458step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20458step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20458 raw20458Labels = mixedMoment B node1242 node1242Labels := by
  calc
    mixedMoment B raw20458 raw20458Labels = mixedMoment B raw20458step0 raw20458step0Labels := by
      have hz : ∀ j, raw20458 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20458step0 = (fun i j => raw20458 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20458step0 raw20458; decide +kernel
      have hl : raw20458step0Labels = raw20458Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20458 raw20458Labels permutation434 hz
    mixedMoment B raw20458step0 raw20458step0Labels = mixedMoment B raw20458step1 raw20458step1Labels := by
      have hz : ∀ j, raw20458step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20458step1 = (fun i j => raw20458step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20458step1 raw20458step0; decide +kernel
      have hl : raw20458step1Labels = raw20458step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20458step0 raw20458step0Labels permutation56 hz
    mixedMoment B raw20458step1 raw20458step1Labels = mixedMoment B raw20458step2 raw20458step2Labels := by
      have ha : raw20458step2 = (fun i j => raw20458step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20458step2 raw20458step1; decide +kernel
      have hl : raw20458step2Labels = raw20458step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20458step1 raw20458step1Labels permutation8 permutation7
    mixedMoment B raw20458step2 raw20458step2Labels = mixedMoment B raw20458step3 raw20458step3Labels := by
      have ha : raw20458step3 = raw20458step2 := by apply Matrix.ext; unfold raw20458step3 raw20458step2; decide +kernel
      have hl : raw20458step2Labels = labelEmbedding1 ∘ raw20458step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20458step2 raw20458step2Labels raw20458step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1242 node1242Labels := by rfl

def raw20459 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20459Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20459step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20459step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20459step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20459step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20459step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw20459step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20459step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, 0, -1], ![3, -2, -1]]
def raw20459step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20459 raw20459Labels = mixedMoment B node1416 node1416Labels := by
  calc
    mixedMoment B raw20459 raw20459Labels = mixedMoment B raw20459step0 raw20459step0Labels := by
      have hz : ∀ j, raw20459 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20459step0 = (fun i j => raw20459 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20459step0 raw20459; decide +kernel
      have hl : raw20459step0Labels = raw20459Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20459 raw20459Labels permutation346 hz
    mixedMoment B raw20459step0 raw20459step0Labels = mixedMoment B raw20459step1 raw20459step1Labels := by
      have hz : ∀ j, raw20459step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20459step1 = (fun i j => raw20459step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20459step1 raw20459step0; decide +kernel
      have hl : raw20459step1Labels = raw20459step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20459step0 raw20459step0Labels permutation56 hz
    mixedMoment B raw20459step1 raw20459step1Labels = mixedMoment B raw20459step2 raw20459step2Labels := by
      have ha : raw20459step2 = (fun i j => raw20459step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20459step2 raw20459step1; decide +kernel
      have hl : raw20459step2Labels = raw20459step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20459step1 raw20459step1Labels permutation8 permutation7
    mixedMoment B raw20459step2 raw20459step2Labels = mixedMoment B raw20459step3 raw20459step3Labels := by
      have ha : raw20459step3 = raw20459step2 := by apply Matrix.ext; unfold raw20459step3 raw20459step2; decide +kernel
      have hl : raw20459step2Labels = labelEmbedding1 ∘ raw20459step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20459step2 raw20459step2Labels raw20459step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1416 node1416Labels := by rfl

def raw20460 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20460Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20460step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20460step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20460step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20460step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20460step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20460step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20460 raw20460Labels = mixedMoment B node1217 node1217Labels := by
  calc
    mixedMoment B raw20460 raw20460Labels = mixedMoment B raw20460step0 raw20460step0Labels := by
      have hz : ∀ j, raw20460 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20460step0 = (fun i j => raw20460 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20460step0 raw20460; decide +kernel
      have hl : raw20460step0Labels = raw20460Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20460 raw20460Labels permutation346 hz
    mixedMoment B raw20460step0 raw20460step0Labels = mixedMoment B raw20460step1 raw20460step1Labels := by
      have ha : raw20460step1 = (fun i j => raw20460step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20460step1 raw20460step0; decide +kernel
      have hl : raw20460step1Labels = raw20460step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20460step0 raw20460step0Labels permutation38 permutation7
    mixedMoment B raw20460step1 raw20460step1Labels = mixedMoment B raw20460step2 raw20460step2Labels := by
      have ha : raw20460step2 = raw20460step1 := by apply Matrix.ext; unfold raw20460step2 raw20460step1; decide +kernel
      have hl : raw20460step1Labels = labelEmbedding1 ∘ raw20460step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20460step1 raw20460step1Labels raw20460step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1217 node1217Labels := by rfl

def raw20461 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20461Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20461step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20461step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20461step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20461step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20461step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw20461step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20461 raw20461Labels = mixedMoment B node1217 node1217Labels := by
  calc
    mixedMoment B raw20461 raw20461Labels = mixedMoment B raw20461step0 raw20461step0Labels := by
      have hz : ∀ j, raw20461 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw20461step0 = (fun i j => raw20461 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw20461step0 raw20461; decide +kernel
      have hl : raw20461step0Labels = raw20461Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20461 raw20461Labels permutation265 hz
    mixedMoment B raw20461step0 raw20461step0Labels = mixedMoment B raw20461step1 raw20461step1Labels := by
      have ha : raw20461step1 = (fun i j => raw20461step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20461step1 raw20461step0; decide +kernel
      have hl : raw20461step1Labels = raw20461step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20461step0 raw20461step0Labels permutation38 permutation7
    mixedMoment B raw20461step1 raw20461step1Labels = mixedMoment B raw20461step2 raw20461step2Labels := by
      have ha : raw20461step2 = raw20461step1 := by apply Matrix.ext; unfold raw20461step2 raw20461step1; decide +kernel
      have hl : raw20461step1Labels = labelEmbedding1 ∘ raw20461step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20461step1 raw20461step1Labels raw20461step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1217 node1217Labels := by rfl

def raw20462 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20462Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20462step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20462step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20462step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20462step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20462step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw20462step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20462step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw20462step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20462 raw20462Labels = mixedMoment B node1243 node1243Labels := by
  calc
    mixedMoment B raw20462 raw20462Labels = mixedMoment B raw20462step0 raw20462step0Labels := by
      have hz : ∀ j, raw20462 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20462step0 = (fun i j => raw20462 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20462step0 raw20462; decide +kernel
      have hl : raw20462step0Labels = raw20462Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20462 raw20462Labels permutation346 hz
    mixedMoment B raw20462step0 raw20462step0Labels = mixedMoment B raw20462step1 raw20462step1Labels := by
      have hz : ∀ j, raw20462step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20462step1 = (fun i j => raw20462step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20462step1 raw20462step0; decide +kernel
      have hl : raw20462step1Labels = raw20462step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20462step0 raw20462step0Labels permutation56 hz
    mixedMoment B raw20462step1 raw20462step1Labels = mixedMoment B raw20462step2 raw20462step2Labels := by
      have ha : raw20462step2 = (fun i j => raw20462step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20462step2 raw20462step1; decide +kernel
      have hl : raw20462step2Labels = raw20462step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20462step1 raw20462step1Labels permutation8 permutation7
    mixedMoment B raw20462step2 raw20462step2Labels = mixedMoment B raw20462step3 raw20462step3Labels := by
      have ha : raw20462step3 = raw20462step2 := by apply Matrix.ext; unfold raw20462step3 raw20462step2; decide +kernel
      have hl : raw20462step2Labels = labelEmbedding1 ∘ raw20462step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20462step2 raw20462step2Labels raw20462step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1243 node1243Labels := by rfl

def raw20463 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20463Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20463step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20463step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20463step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20463step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20463step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20463step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20463step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw20463step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20463 raw20463Labels = mixedMoment B node1242 node1242Labels := by
  calc
    mixedMoment B raw20463 raw20463Labels = mixedMoment B raw20463step0 raw20463step0Labels := by
      have hz : ∀ j, raw20463 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20463step0 = (fun i j => raw20463 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20463step0 raw20463; decide +kernel
      have hl : raw20463step0Labels = raw20463Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20463 raw20463Labels permutation346 hz
    mixedMoment B raw20463step0 raw20463step0Labels = mixedMoment B raw20463step1 raw20463step1Labels := by
      have hz : ∀ j, raw20463step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20463step1 = (fun i j => raw20463step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20463step1 raw20463step0; decide +kernel
      have hl : raw20463step1Labels = raw20463step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20463step0 raw20463step0Labels permutation56 hz
    mixedMoment B raw20463step1 raw20463step1Labels = mixedMoment B raw20463step2 raw20463step2Labels := by
      have ha : raw20463step2 = (fun i j => raw20463step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20463step2 raw20463step1; decide +kernel
      have hl : raw20463step2Labels = raw20463step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20463step1 raw20463step1Labels permutation8 permutation7
    mixedMoment B raw20463step2 raw20463step2Labels = mixedMoment B raw20463step3 raw20463step3Labels := by
      have ha : raw20463step3 = raw20463step2 := by apply Matrix.ext; unfold raw20463step3 raw20463step2; decide +kernel
      have hl : raw20463step2Labels = labelEmbedding1 ∘ raw20463step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20463step2 raw20463step2Labels raw20463step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1242 node1242Labels := by rfl

def raw20464 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20464Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20464step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20464step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20464step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20464step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20464step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![-1, -2, 3]]
def raw20464step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20464step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![3, -2, -1]]
def raw20464step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20464step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -1, 0], ![3, -2, -1]]
def raw20464step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20464 raw20464Labels = mixedMoment B node1450 node1450Labels := by
  calc
    mixedMoment B raw20464 raw20464Labels = mixedMoment B raw20464step0 raw20464step0Labels := by
      have hz : ∀ j, raw20464 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20464step0 = (fun i j => raw20464 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20464step0 raw20464; decide +kernel
      have hl : raw20464step0Labels = raw20464Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20464 raw20464Labels permutation434 hz
    mixedMoment B raw20464step0 raw20464step0Labels = mixedMoment B raw20464step1 raw20464step1Labels := by
      have hz : ∀ j, raw20464step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20464step1 = (fun i j => raw20464step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20464step1 raw20464step0; decide +kernel
      have hl : raw20464step1Labels = raw20464step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20464step0 raw20464step0Labels permutation80 hz
    mixedMoment B raw20464step1 raw20464step1Labels = mixedMoment B raw20464step2 raw20464step2Labels := by
      have hz : ∀ j, raw20464step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20464step2 = (fun i j => raw20464step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20464step2 raw20464step1; decide +kernel
      have hl : raw20464step2Labels = raw20464step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20464step1 raw20464step1Labels permutation14 hz
    mixedMoment B raw20464step2 raw20464step2Labels = mixedMoment B raw20464step3 raw20464step3Labels := by
      have ha : raw20464step3 = (fun i j => raw20464step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20464step3 raw20464step2; decide +kernel
      have hl : raw20464step3Labels = raw20464step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20464step2 raw20464step2Labels permutation2 permutation7
    mixedMoment B raw20464step3 raw20464step3Labels = mixedMoment B raw20464step4 raw20464step4Labels := by
      have ha : raw20464step4 = raw20464step3 := by apply Matrix.ext; unfold raw20464step4 raw20464step3; decide +kernel
      have hl : raw20464step3Labels = labelEmbedding1 ∘ raw20464step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20464step3 raw20464step3Labels raw20464step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1450 node1450Labels := by rfl

def raw20465 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20465Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20465step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20465step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20465step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20465step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20465step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20465step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20465step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20465step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20465 raw20465Labels = mixedMoment B node1269 node1269Labels := by
  calc
    mixedMoment B raw20465 raw20465Labels = mixedMoment B raw20465step0 raw20465step0Labels := by
      have hz : ∀ j, raw20465 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20465step0 = (fun i j => raw20465 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20465step0 raw20465; decide +kernel
      have hl : raw20465step0Labels = raw20465Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20465 raw20465Labels permutation434 hz
    mixedMoment B raw20465step0 raw20465step0Labels = mixedMoment B raw20465step1 raw20465step1Labels := by
      have hz : ∀ j, raw20465step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20465step1 = (fun i j => raw20465step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20465step1 raw20465step0; decide +kernel
      have hl : raw20465step1Labels = raw20465step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20465step0 raw20465step0Labels permutation80 hz
    mixedMoment B raw20465step1 raw20465step1Labels = mixedMoment B raw20465step2 raw20465step2Labels := by
      have ha : raw20465step2 = (fun i j => raw20465step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20465step2 raw20465step1; decide +kernel
      have hl : raw20465step2Labels = raw20465step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20465step1 raw20465step1Labels permutation8 permutation7
    mixedMoment B raw20465step2 raw20465step2Labels = mixedMoment B raw20465step3 raw20465step3Labels := by
      have ha : raw20465step3 = raw20465step2 := by apply Matrix.ext; unfold raw20465step3 raw20465step2; decide +kernel
      have hl : raw20465step2Labels = labelEmbedding1 ∘ raw20465step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20465step2 raw20465step2Labels raw20465step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1269 node1269Labels := by rfl

def raw20466 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20466Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20466step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20466step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20466step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20466step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20466step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20466step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20466step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20466step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20466 raw20466Labels = mixedMoment B node1269 node1269Labels := by
  calc
    mixedMoment B raw20466 raw20466Labels = mixedMoment B raw20466step0 raw20466step0Labels := by
      have hz : ∀ j, raw20466 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20466step0 = (fun i j => raw20466 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20466step0 raw20466; decide +kernel
      have hl : raw20466step0Labels = raw20466Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20466 raw20466Labels permutation434 hz
    mixedMoment B raw20466step0 raw20466step0Labels = mixedMoment B raw20466step1 raw20466step1Labels := by
      have hz : ∀ j, raw20466step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20466step1 = (fun i j => raw20466step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20466step1 raw20466step0; decide +kernel
      have hl : raw20466step1Labels = raw20466step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20466step0 raw20466step0Labels permutation56 hz
    mixedMoment B raw20466step1 raw20466step1Labels = mixedMoment B raw20466step2 raw20466step2Labels := by
      have ha : raw20466step2 = (fun i j => raw20466step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20466step2 raw20466step1; decide +kernel
      have hl : raw20466step2Labels = raw20466step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20466step1 raw20466step1Labels permutation8 permutation7
    mixedMoment B raw20466step2 raw20466step2Labels = mixedMoment B raw20466step3 raw20466step3Labels := by
      have ha : raw20466step3 = raw20466step2 := by apply Matrix.ext; unfold raw20466step3 raw20466step2; decide +kernel
      have hl : raw20466step2Labels = labelEmbedding1 ∘ raw20466step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20466step2 raw20466step2Labels raw20466step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1269 node1269Labels := by rfl

def raw20467 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20467Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20467step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20467step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20467step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20467step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20467step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20467step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20467step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw20467step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20467 raw20467Labels = mixedMoment B node1269 node1269Labels := by
  calc
    mixedMoment B raw20467 raw20467Labels = mixedMoment B raw20467step0 raw20467step0Labels := by
      have hz : ∀ j, raw20467 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20467step0 = (fun i j => raw20467 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20467step0 raw20467; decide +kernel
      have hl : raw20467step0Labels = raw20467Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20467 raw20467Labels permutation346 hz
    mixedMoment B raw20467step0 raw20467step0Labels = mixedMoment B raw20467step1 raw20467step1Labels := by
      have hz : ∀ j, raw20467step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20467step1 = (fun i j => raw20467step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20467step1 raw20467step0; decide +kernel
      have hl : raw20467step1Labels = raw20467step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20467step0 raw20467step0Labels permutation56 hz
    mixedMoment B raw20467step1 raw20467step1Labels = mixedMoment B raw20467step2 raw20467step2Labels := by
      have ha : raw20467step2 = (fun i j => raw20467step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20467step2 raw20467step1; decide +kernel
      have hl : raw20467step2Labels = raw20467step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20467step1 raw20467step1Labels permutation8 permutation7
    mixedMoment B raw20467step2 raw20467step2Labels = mixedMoment B raw20467step3 raw20467step3Labels := by
      have ha : raw20467step3 = raw20467step2 := by apply Matrix.ext; unfold raw20467step3 raw20467step2; decide +kernel
      have hl : raw20467step2Labels = labelEmbedding1 ∘ raw20467step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20467step2 raw20467step2Labels raw20467step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1269 node1269Labels := by rfl

def raw20468 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20468Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20468step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20468step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![-2, -1, 3]]
def raw20468step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20468step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![-2, -1, 3]]
def raw20468step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20468step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw20468step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20468step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![3, -1, -2]]
def raw20468step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20468 raw20468Labels = mixedMoment B node1304 node1304Labels := by
  calc
    mixedMoment B raw20468 raw20468Labels = mixedMoment B raw20468step0 raw20468step0Labels := by
      have hz : ∀ j, raw20468 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20468step0 = (fun i j => raw20468 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20468step0 raw20468; decide +kernel
      have hl : raw20468step0Labels = raw20468Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20468 raw20468Labels permutation434 hz
    mixedMoment B raw20468step0 raw20468step0Labels = mixedMoment B raw20468step1 raw20468step1Labels := by
      have hz : ∀ j, raw20468step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20468step1 = (fun i j => raw20468step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20468step1 raw20468step0; decide +kernel
      have hl : raw20468step1Labels = raw20468step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20468step0 raw20468step0Labels permutation80 hz
    mixedMoment B raw20468step1 raw20468step1Labels = mixedMoment B raw20468step2 raw20468step2Labels := by
      have hz : ∀ j, raw20468step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20468step2 = (fun i j => raw20468step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20468step2 raw20468step1; decide +kernel
      have hl : raw20468step2Labels = raw20468step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20468step1 raw20468step1Labels permutation14 hz
    mixedMoment B raw20468step2 raw20468step2Labels = mixedMoment B raw20468step3 raw20468step3Labels := by
      have ha : raw20468step3 = (fun i j => raw20468step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20468step3 raw20468step2; decide +kernel
      have hl : raw20468step3Labels = raw20468step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20468step2 raw20468step2Labels permutation2 permutation7
    mixedMoment B raw20468step3 raw20468step3Labels = mixedMoment B raw20468step4 raw20468step4Labels := by
      have ha : raw20468step4 = raw20468step3 := by apply Matrix.ext; unfold raw20468step4 raw20468step3; decide +kernel
      have hl : raw20468step3Labels = labelEmbedding1 ∘ raw20468step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20468step3 raw20468step3Labels raw20468step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1304 node1304Labels := by rfl

def raw20469 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20469Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20469step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20469step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20469step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20469step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20469step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![0, -3, 3]]
def raw20469step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20469step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![3, -3, 0]]
def raw20469step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20469step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![3, -3, 0]]
def raw20469step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20469 raw20469Labels = mixedMoment B node1452 node1452Labels := by
  calc
    mixedMoment B raw20469 raw20469Labels = mixedMoment B raw20469step0 raw20469step0Labels := by
      have hz : ∀ j, raw20469 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20469step0 = (fun i j => raw20469 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20469step0 raw20469; decide +kernel
      have hl : raw20469step0Labels = raw20469Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20469 raw20469Labels permutation434 hz
    mixedMoment B raw20469step0 raw20469step0Labels = mixedMoment B raw20469step1 raw20469step1Labels := by
      have hz : ∀ j, raw20469step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20469step1 = (fun i j => raw20469step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20469step1 raw20469step0; decide +kernel
      have hl : raw20469step1Labels = raw20469step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20469step0 raw20469step0Labels permutation80 hz
    mixedMoment B raw20469step1 raw20469step1Labels = mixedMoment B raw20469step2 raw20469step2Labels := by
      have hz : ∀ j, raw20469step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20469step2 = (fun i j => raw20469step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20469step2 raw20469step1; decide +kernel
      have hl : raw20469step2Labels = raw20469step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20469step1 raw20469step1Labels permutation14 hz
    mixedMoment B raw20469step2 raw20469step2Labels = mixedMoment B raw20469step3 raw20469step3Labels := by
      have ha : raw20469step3 = (fun i j => raw20469step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20469step3 raw20469step2; decide +kernel
      have hl : raw20469step3Labels = raw20469step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20469step2 raw20469step2Labels permutation2 permutation7
    mixedMoment B raw20469step3 raw20469step3Labels = mixedMoment B raw20469step4 raw20469step4Labels := by
      have ha : raw20469step4 = raw20469step3 := by apply Matrix.ext; unfold raw20469step4 raw20469step3; decide +kernel
      have hl : raw20469step3Labels = labelEmbedding1 ∘ raw20469step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20469step3 raw20469step3Labels raw20469step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1452 node1452Labels := by rfl

def raw20470 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20470Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20470step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20470step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20470step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20470step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20470step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20470step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20470step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20470 raw20470Labels = mixedMoment B node1271 node1271Labels := by
  calc
    mixedMoment B raw20470 raw20470Labels = mixedMoment B raw20470step0 raw20470step0Labels := by
      have hz : ∀ j, raw20470 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20470step0 = (fun i j => raw20470 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20470step0 raw20470; decide +kernel
      have hl : raw20470step0Labels = raw20470Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20470 raw20470Labels permutation434 hz
    mixedMoment B raw20470step0 raw20470step0Labels = mixedMoment B raw20470step1 raw20470step1Labels := by
      have hz : ∀ j, raw20470step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20470step1 = (fun i j => raw20470step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20470step1 raw20470step0; decide +kernel
      have hl : raw20470step1Labels = raw20470step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20470step0 raw20470step0Labels permutation80 hz
    mixedMoment B raw20470step1 raw20470step1Labels = mixedMoment B raw20470step2 raw20470step2Labels := by
      have ha : raw20470step2 = (fun i j => raw20470step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20470step2 raw20470step1; decide +kernel
      have hl : raw20470step2Labels = raw20470step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20470step1 raw20470step1Labels permutation8 permutation7
    mixedMoment B raw20470step2 raw20470step2Labels = mixedMoment B raw20470step3 raw20470step3Labels := by
      have ha : raw20470step3 = raw20470step2 := by apply Matrix.ext; unfold raw20470step3 raw20470step2; decide +kernel
      have hl : raw20470step2Labels = labelEmbedding1 ∘ raw20470step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20470step2 raw20470step2Labels raw20470step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1271 node1271Labels := by rfl

def raw20471 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20471Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20471step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20471step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20471step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20471step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20471step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20471step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20471step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20471step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20471 raw20471Labels = mixedMoment B node1271 node1271Labels := by
  calc
    mixedMoment B raw20471 raw20471Labels = mixedMoment B raw20471step0 raw20471step0Labels := by
      have hz : ∀ j, raw20471 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20471step0 = (fun i j => raw20471 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20471step0 raw20471; decide +kernel
      have hl : raw20471step0Labels = raw20471Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20471 raw20471Labels permutation434 hz
    mixedMoment B raw20471step0 raw20471step0Labels = mixedMoment B raw20471step1 raw20471step1Labels := by
      have hz : ∀ j, raw20471step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20471step1 = (fun i j => raw20471step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20471step1 raw20471step0; decide +kernel
      have hl : raw20471step1Labels = raw20471step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20471step0 raw20471step0Labels permutation56 hz
    mixedMoment B raw20471step1 raw20471step1Labels = mixedMoment B raw20471step2 raw20471step2Labels := by
      have ha : raw20471step2 = (fun i j => raw20471step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20471step2 raw20471step1; decide +kernel
      have hl : raw20471step2Labels = raw20471step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20471step1 raw20471step1Labels permutation8 permutation7
    mixedMoment B raw20471step2 raw20471step2Labels = mixedMoment B raw20471step3 raw20471step3Labels := by
      have ha : raw20471step3 = raw20471step2 := by apply Matrix.ext; unfold raw20471step3 raw20471step2; decide +kernel
      have hl : raw20471step2Labels = labelEmbedding1 ∘ raw20471step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20471step2 raw20471step2Labels raw20471step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1271 node1271Labels := by rfl

def raw20472 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20472Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20472step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20472step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20472step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw20472step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20472step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20472step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20472step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw20472step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20472 raw20472Labels = mixedMoment B node1271 node1271Labels := by
  calc
    mixedMoment B raw20472 raw20472Labels = mixedMoment B raw20472step0 raw20472step0Labels := by
      have hz : ∀ j, raw20472 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20472step0 = (fun i j => raw20472 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20472step0 raw20472; decide +kernel
      have hl : raw20472step0Labels = raw20472Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20472 raw20472Labels permutation346 hz
    mixedMoment B raw20472step0 raw20472step0Labels = mixedMoment B raw20472step1 raw20472step1Labels := by
      have hz : ∀ j, raw20472step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20472step1 = (fun i j => raw20472step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20472step1 raw20472step0; decide +kernel
      have hl : raw20472step1Labels = raw20472step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20472step0 raw20472step0Labels permutation56 hz
    mixedMoment B raw20472step1 raw20472step1Labels = mixedMoment B raw20472step2 raw20472step2Labels := by
      have ha : raw20472step2 = (fun i j => raw20472step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20472step2 raw20472step1; decide +kernel
      have hl : raw20472step2Labels = raw20472step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20472step1 raw20472step1Labels permutation8 permutation7
    mixedMoment B raw20472step2 raw20472step2Labels = mixedMoment B raw20472step3 raw20472step3Labels := by
      have ha : raw20472step3 = raw20472step2 := by apply Matrix.ext; unfold raw20472step3 raw20472step2; decide +kernel
      have hl : raw20472step2Labels = labelEmbedding1 ∘ raw20472step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20472step2 raw20472step2Labels raw20472step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1271 node1271Labels := by rfl

def raw20473 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20473Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20473step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20473step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20473step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 1, 1], ![0, -3, 3]]
def raw20473step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20473step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 1, 1], ![0, -3, 3]]
def raw20473step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw20473step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![3, -3, 0]]
def raw20473step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw20473step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 1, -2], ![3, -3, 0]]
def raw20473step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20473 raw20473Labels = mixedMoment B node1308 node1308Labels := by
  calc
    mixedMoment B raw20473 raw20473Labels = mixedMoment B raw20473step0 raw20473step0Labels := by
      have hz : ∀ j, raw20473 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20473step0 = (fun i j => raw20473 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20473step0 raw20473; decide +kernel
      have hl : raw20473step0Labels = raw20473Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20473 raw20473Labels permutation434 hz
    mixedMoment B raw20473step0 raw20473step0Labels = mixedMoment B raw20473step1 raw20473step1Labels := by
      have hz : ∀ j, raw20473step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20473step1 = (fun i j => raw20473step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20473step1 raw20473step0; decide +kernel
      have hl : raw20473step1Labels = raw20473step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20473step0 raw20473step0Labels permutation80 hz
    mixedMoment B raw20473step1 raw20473step1Labels = mixedMoment B raw20473step2 raw20473step2Labels := by
      have hz : ∀ j, raw20473step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20473step2 = (fun i j => raw20473step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20473step2 raw20473step1; decide +kernel
      have hl : raw20473step2Labels = raw20473step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20473step1 raw20473step1Labels permutation14 hz
    mixedMoment B raw20473step2 raw20473step2Labels = mixedMoment B raw20473step3 raw20473step3Labels := by
      have ha : raw20473step3 = (fun i j => raw20473step2 (permutation2 i) (permutation7 j)) := by apply Matrix.ext; unfold raw20473step3 raw20473step2; decide +kernel
      have hl : raw20473step3Labels = raw20473step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20473step2 raw20473step2Labels permutation2 permutation7
    mixedMoment B raw20473step3 raw20473step3Labels = mixedMoment B raw20473step4 raw20473step4Labels := by
      have ha : raw20473step4 = raw20473step3 := by apply Matrix.ext; unfold raw20473step4 raw20473step3; decide +kernel
      have hl : raw20473step3Labels = labelEmbedding1 ∘ raw20473step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw20473step3 raw20473step3Labels raw20473step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1308 node1308Labels := by rfl

def raw20474 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20474Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20474step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20474step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20474step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20474step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20474step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw20474step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20474 raw20474Labels = mixedMoment B node1750 node1750Labels := by
  calc
    mixedMoment B raw20474 raw20474Labels = mixedMoment B raw20474step0 raw20474step0Labels := by
      have hz : ∀ j, raw20474 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20474step0 = (fun i j => raw20474 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20474step0 raw20474; decide +kernel
      have hl : raw20474step0Labels = raw20474Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20474 raw20474Labels permutation434 hz
    mixedMoment B raw20474step0 raw20474step0Labels = mixedMoment B raw20474step1 raw20474step1Labels := by
      have hz : ∀ j, raw20474step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20474step1 = (fun i j => raw20474step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20474step1 raw20474step0; decide +kernel
      have hl : raw20474step1Labels = raw20474step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20474step0 raw20474step0Labels permutation56 hz
    mixedMoment B raw20474step1 raw20474step1Labels = mixedMoment B raw20474step2 raw20474step2Labels := by
      have ha : raw20474step2 = -raw20474step1 := by apply Matrix.ext; change ∀ i j, raw20474step2 i j = -(raw20474step1 i j); unfold raw20474step2 raw20474step1; decide +kernel
      have hl : raw20474step2Labels = raw20474step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1750 node1750Labels := by rfl

def raw20475 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20475Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20475step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20475step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20475step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20475step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20475step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw20475step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20475 raw20475Labels = mixedMoment B node1750 node1750Labels := by
  calc
    mixedMoment B raw20475 raw20475Labels = mixedMoment B raw20475step0 raw20475step0Labels := by
      have hz : ∀ j, raw20475 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw20475step0 = (fun i j => raw20475 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw20475step0 raw20475; decide +kernel
      have hl : raw20475step0Labels = raw20475Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20475 raw20475Labels permutation346 hz
    mixedMoment B raw20475step0 raw20475step0Labels = mixedMoment B raw20475step1 raw20475step1Labels := by
      have hz : ∀ j, raw20475step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw20475step1 = (fun i j => raw20475step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw20475step1 raw20475step0; decide +kernel
      have hl : raw20475step1Labels = raw20475step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20475step0 raw20475step0Labels permutation56 hz
    mixedMoment B raw20475step1 raw20475step1Labels = mixedMoment B raw20475step2 raw20475step2Labels := by
      have ha : raw20475step2 = -raw20475step1 := by apply Matrix.ext; change ∀ i j, raw20475step2 i j = -(raw20475step1 i j); unfold raw20475step2 raw20475step1; decide +kernel
      have hl : raw20475step2Labels = raw20475step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1750 node1750Labels := by rfl

def raw20476 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20476Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20476step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20476step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20476step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 1, 1], ![-1, -2, 3]]
def raw20476step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20476step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 1, 1], ![-1, -2, 3]]
def raw20476step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20476step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, -2, 3], ![-2, 1, 1]]
def raw20476step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20476step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 2, -3], ![2, -1, -1]]
def raw20476step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20476 raw20476Labels = mixedMoment B node1756 node1756Labels := by
  calc
    mixedMoment B raw20476 raw20476Labels = mixedMoment B raw20476step0 raw20476step0Labels := by
      have hz : ∀ j, raw20476 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20476step0 = (fun i j => raw20476 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20476step0 raw20476; decide +kernel
      have hl : raw20476step0Labels = raw20476Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20476 raw20476Labels permutation434 hz
    mixedMoment B raw20476step0 raw20476step0Labels = mixedMoment B raw20476step1 raw20476step1Labels := by
      have hz : ∀ j, raw20476step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20476step1 = (fun i j => raw20476step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20476step1 raw20476step0; decide +kernel
      have hl : raw20476step1Labels = raw20476step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20476step0 raw20476step0Labels permutation80 hz
    mixedMoment B raw20476step1 raw20476step1Labels = mixedMoment B raw20476step2 raw20476step2Labels := by
      have hz : ∀ j, raw20476step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20476step2 = (fun i j => raw20476step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20476step2 raw20476step1; decide +kernel
      have hl : raw20476step2Labels = raw20476step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20476step1 raw20476step1Labels permutation14 hz
    mixedMoment B raw20476step2 raw20476step2Labels = mixedMoment B raw20476step3 raw20476step3Labels := by
      have ha : raw20476step3 = (fun i j => raw20476step2 (permutation3 i) (permutation2 j)) := by apply Matrix.ext; unfold raw20476step3 raw20476step2; decide +kernel
      have hl : raw20476step3Labels = raw20476step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20476step2 raw20476step2Labels permutation3 permutation2
    mixedMoment B raw20476step3 raw20476step3Labels = mixedMoment B raw20476step4 raw20476step4Labels := by
      have ha : raw20476step4 = -raw20476step3 := by apply Matrix.ext; change ∀ i j, raw20476step4 i j = -(raw20476step3 i j); unfold raw20476step4 raw20476step3; decide +kernel
      have hl : raw20476step4Labels = raw20476step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1756 node1756Labels := by rfl

def raw20477 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20477Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20477step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20477step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20477step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw20477step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20477step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-2, -1, 3]]
def raw20477step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20477step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 0, -1], ![2, 1, -3]]
def raw20477step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20477 raw20477Labels = mixedMoment B node1754 node1754Labels := by
  calc
    mixedMoment B raw20477 raw20477Labels = mixedMoment B raw20477step0 raw20477step0Labels := by
      have hz : ∀ j, raw20477 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20477step0 = (fun i j => raw20477 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20477step0 raw20477; decide +kernel
      have hl : raw20477step0Labels = raw20477Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20477 raw20477Labels permutation434 hz
    mixedMoment B raw20477step0 raw20477step0Labels = mixedMoment B raw20477step1 raw20477step1Labels := by
      have hz : ∀ j, raw20477step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20477step1 = (fun i j => raw20477step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20477step1 raw20477step0; decide +kernel
      have hl : raw20477step1Labels = raw20477step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20477step0 raw20477step0Labels permutation80 hz
    mixedMoment B raw20477step1 raw20477step1Labels = mixedMoment B raw20477step2 raw20477step2Labels := by
      have hz : ∀ j, raw20477step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20477step2 = (fun i j => raw20477step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20477step2 raw20477step1; decide +kernel
      have hl : raw20477step2Labels = raw20477step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20477step1 raw20477step1Labels permutation14 hz
    mixedMoment B raw20477step2 raw20477step2Labels = mixedMoment B raw20477step3 raw20477step3Labels := by
      have ha : raw20477step3 = -raw20477step2 := by apply Matrix.ext; change ∀ i j, raw20477step3 i j = -(raw20477step2 i j); unfold raw20477step3 raw20477step2; decide +kernel
      have hl : raw20477step3Labels = raw20477step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1754 node1754Labels := by rfl

def raw20478 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20478Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20478step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20478step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20478step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw20478step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20478step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![-1, 1, 0], ![-2, -1, 3]]
def raw20478step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20478step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw20478step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20478 raw20478Labels = mixedMoment B node1725 node1725Labels := by
  calc
    mixedMoment B raw20478 raw20478Labels = mixedMoment B raw20478step0 raw20478step0Labels := by
      have hz : ∀ j, raw20478 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20478step0 = (fun i j => raw20478 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20478step0 raw20478; decide +kernel
      have hl : raw20478step0Labels = raw20478Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20478 raw20478Labels permutation434 hz
    mixedMoment B raw20478step0 raw20478step0Labels = mixedMoment B raw20478step1 raw20478step1Labels := by
      have hz : ∀ j, raw20478step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20478step1 = (fun i j => raw20478step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20478step1 raw20478step0; decide +kernel
      have hl : raw20478step1Labels = raw20478step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20478step0 raw20478step0Labels permutation80 hz
    mixedMoment B raw20478step1 raw20478step1Labels = mixedMoment B raw20478step2 raw20478step2Labels := by
      have ha : raw20478step2 = (fun i j => raw20478step1 (permutation10 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20478step2 raw20478step1; decide +kernel
      have hl : raw20478step2Labels = raw20478step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20478step1 raw20478step1Labels permutation10 permutation4
    mixedMoment B raw20478step2 raw20478step2Labels = mixedMoment B raw20478step3 raw20478step3Labels := by
      have ha : raw20478step3 = -raw20478step2 := by apply Matrix.ext; change ∀ i j, raw20478step3 i j = -(raw20478step2 i j); unfold raw20478step3 raw20478step2; decide +kernel
      have hl : raw20478step3Labels = raw20478step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1725 node1725Labels := by rfl

def raw20479 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20479Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20479step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20479step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20479step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw20479step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20479step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![-1, -2, 3]]
def raw20479step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20479step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![-2, -1, 3]]
def raw20479step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw20479step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, -1, 4], ![1, 0, -1], ![2, 1, -3]]
def raw20479step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical20479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw20479 raw20479Labels = mixedMoment B node1754 node1754Labels := by
  calc
    mixedMoment B raw20479 raw20479Labels = mixedMoment B raw20479step0 raw20479step0Labels := by
      have hz : ∀ j, raw20479 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw20479step0 = (fun i j => raw20479 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw20479step0 raw20479; decide +kernel
      have hl : raw20479step0Labels = raw20479Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20479 raw20479Labels permutation434 hz
    mixedMoment B raw20479step0 raw20479step0Labels = mixedMoment B raw20479step1 raw20479step1Labels := by
      have hz : ∀ j, raw20479step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw20479step1 = (fun i j => raw20479step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw20479step1 raw20479step0; decide +kernel
      have hl : raw20479step1Labels = raw20479step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20479step0 raw20479step0Labels permutation80 hz
    mixedMoment B raw20479step1 raw20479step1Labels = mixedMoment B raw20479step2 raw20479step2Labels := by
      have hz : ∀ j, raw20479step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw20479step2 = (fun i j => raw20479step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw20479step2 raw20479step1; decide +kernel
      have hl : raw20479step2Labels = raw20479step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw20479step1 raw20479step1Labels permutation14 hz
    mixedMoment B raw20479step2 raw20479step2Labels = mixedMoment B raw20479step3 raw20479step3Labels := by
      have ha : raw20479step3 = (fun i j => raw20479step2 (permutation2 i) (permutation4 j)) := by apply Matrix.ext; unfold raw20479step3 raw20479step2; decide +kernel
      have hl : raw20479step3Labels = raw20479step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw20479step2 raw20479step2Labels permutation2 permutation4
    mixedMoment B raw20479step3 raw20479step3Labels = mixedMoment B raw20479step4 raw20479step4Labels := by
      have ha : raw20479step4 = -raw20479step3 := by apply Matrix.ext; change ∀ i j, raw20479step4 i j = -(raw20479step3 i j); unfold raw20479step4 raw20479step3; decide +kernel
      have hl : raw20479step4Labels = raw20479step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1754 node1754Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
