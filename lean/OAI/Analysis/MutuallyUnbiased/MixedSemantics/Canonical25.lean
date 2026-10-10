import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes64
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw3200 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3200Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3200step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3200step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3200step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3200step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3200step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3200step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3200step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3200 raw3200Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw3200 raw3200Labels = mixedMoment B raw3200step0 raw3200step0Labels := by
      have hz : ∀ j, raw3200 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3200step0 = (fun i j => raw3200 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3200step0 raw3200; decide +kernel
      have hl : raw3200step0Labels = raw3200Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3200 raw3200Labels permutation346 hz
    mixedMoment B raw3200step0 raw3200step0Labels = mixedMoment B raw3200step1 raw3200step1Labels := by
      have ha : raw3200step1 = (fun i j => raw3200step0 (permutation59 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3200step1 raw3200step0; decide +kernel
      have hl : raw3200step1Labels = raw3200step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3200step0 raw3200step0Labels permutation59 permutation5
    mixedMoment B raw3200step1 raw3200step1Labels = mixedMoment B raw3200step2 raw3200step2Labels := by
      have ha : raw3200step2 = -raw3200step1 := by apply Matrix.ext; change ∀ i j, raw3200step2 i j = -(raw3200step1 i j); unfold raw3200step2 raw3200step1; decide +kernel
      have hl : raw3200step2Labels = raw3200step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3200step2 raw3200step2Labels = mixedMoment B raw3200step3 raw3200step3Labels := by
      have ha : raw3200step3 = raw3200step2 := by apply Matrix.ext; unfold raw3200step3 raw3200step2; decide +kernel
      have hl : raw3200step2Labels = labelEmbedding8 ∘ raw3200step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3200step2 raw3200step2Labels raw3200step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw3201 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3201Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3201step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3201step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3201step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3201step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3201 raw3201Labels = mixedMoment B node5489 node5489Labels := by
  calc
    mixedMoment B raw3201 raw3201Labels = mixedMoment B raw3201step0 raw3201step0Labels := by
      have ha : raw3201step0 = (fun i j => raw3201 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3201step0 raw3201; decide +kernel
      have hl : raw3201step0Labels = raw3201Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3201 raw3201Labels permutation152 permutation6
    mixedMoment B raw3201step0 raw3201step0Labels = mixedMoment B raw3201step1 raw3201step1Labels := by
      have ha : raw3201step1 = raw3201step0 := by apply Matrix.ext; unfold raw3201step1 raw3201step0; decide +kernel
      have hl : raw3201step0Labels = labelEmbedding9 ∘ raw3201step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3201step0 raw3201step0Labels raw3201step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5489 node5489Labels := by rfl

def raw3202 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3202Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3202step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3202step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3202step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3202step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3202step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3202step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3202step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3202step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3202 raw3202Labels = mixedMoment B node5493 node5493Labels := by
  calc
    mixedMoment B raw3202 raw3202Labels = mixedMoment B raw3202step0 raw3202step0Labels := by
      have hz : ∀ j, raw3202 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3202step0 = (fun i j => raw3202 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3202step0 raw3202; decide +kernel
      have hl : raw3202step0Labels = raw3202Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3202 raw3202Labels permutation434 hz
    mixedMoment B raw3202step0 raw3202step0Labels = mixedMoment B raw3202step1 raw3202step1Labels := by
      have hz : ∀ j, raw3202step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3202step1 = (fun i j => raw3202step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3202step1 raw3202step0; decide +kernel
      have hl : raw3202step1Labels = raw3202step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3202step0 raw3202step0Labels permutation80 hz
    mixedMoment B raw3202step1 raw3202step1Labels = mixedMoment B raw3202step2 raw3202step2Labels := by
      have ha : raw3202step2 = (fun i j => raw3202step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3202step2 raw3202step1; decide +kernel
      have hl : raw3202step2Labels = raw3202step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3202step1 raw3202step1Labels permutation8 permutation6
    mixedMoment B raw3202step2 raw3202step2Labels = mixedMoment B raw3202step3 raw3202step3Labels := by
      have ha : raw3202step3 = raw3202step2 := by apply Matrix.ext; unfold raw3202step3 raw3202step2; decide +kernel
      have hl : raw3202step2Labels = labelEmbedding9 ∘ raw3202step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3202step2 raw3202step2Labels raw3202step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5493 node5493Labels := by rfl

def raw3203 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1]]
def raw3203Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1]]
def raw3203step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3203step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3203step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3203step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3203step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3203 raw3203Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw3203 raw3203Labels = mixedMoment B raw3203step0 raw3203step0Labels := by
      have hz : ∀ j, raw3203 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3203step0 = (fun i j => raw3203 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3203step0 raw3203; decide +kernel
      have hl : raw3203step0Labels = raw3203Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3203 raw3203Labels permutation346 hz
    mixedMoment B raw3203step0 raw3203step0Labels = mixedMoment B raw3203step1 raw3203step1Labels := by
      have ha : raw3203step1 = (fun i j => raw3203step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3203step1 raw3203step0; decide +kernel
      have hl : raw3203step1Labels = raw3203step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3203step0 raw3203step0Labels permutation33 permutation6
    mixedMoment B raw3203step1 raw3203step1Labels = mixedMoment B raw3203step2 raw3203step2Labels := by
      have ha : raw3203step2 = raw3203step1 := by apply Matrix.ext; unfold raw3203step2 raw3203step1; decide +kernel
      have hl : raw3203step1Labels = labelEmbedding9 ∘ raw3203step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3203step1 raw3203step1Labels raw3203step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw3204 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1]]
def raw3204Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3204step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1]]
def raw3204step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3204step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3204step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3204step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3204step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3204step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3204step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3204 raw3204Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw3204 raw3204Labels = mixedMoment B raw3204step0 raw3204step0Labels := by
      have hz : ∀ j, raw3204 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3204step0 = (fun i j => raw3204 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3204step0 raw3204; decide +kernel
      have hl : raw3204step0Labels = raw3204Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3204 raw3204Labels permutation346 hz
    mixedMoment B raw3204step0 raw3204step0Labels = mixedMoment B raw3204step1 raw3204step1Labels := by
      have ha : raw3204step1 = (fun i j => raw3204step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3204step1 raw3204step0; decide +kernel
      have hl : raw3204step1Labels = raw3204step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3204step0 raw3204step0Labels permutation34 permutation4
    mixedMoment B raw3204step1 raw3204step1Labels = mixedMoment B raw3204step2 raw3204step2Labels := by
      have ha : raw3204step2 = -raw3204step1 := by apply Matrix.ext; change ∀ i j, raw3204step2 i j = -(raw3204step1 i j); unfold raw3204step2 raw3204step1; decide +kernel
      have hl : raw3204step2Labels = raw3204step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3204step2 raw3204step2Labels = mixedMoment B raw3204step3 raw3204step3Labels := by
      have ha : raw3204step3 = raw3204step2 := by apply Matrix.ext; unfold raw3204step3 raw3204step2; decide +kernel
      have hl : raw3204step2Labels = labelEmbedding7 ∘ raw3204step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3204step2 raw3204step2Labels raw3204step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw3205 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1]]
def raw3205Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 2, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1]]
def raw3205step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3205step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3205step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3205step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3205step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3205 raw3205Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw3205 raw3205Labels = mixedMoment B raw3205step0 raw3205step0Labels := by
      have hz : ∀ j, raw3205 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3205step0 = (fun i j => raw3205 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3205step0 raw3205; decide +kernel
      have hl : raw3205step0Labels = raw3205Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3205 raw3205Labels permutation346 hz
    mixedMoment B raw3205step0 raw3205step0Labels = mixedMoment B raw3205step1 raw3205step1Labels := by
      have ha : raw3205step1 = (fun i j => raw3205step0 (permutation68 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3205step1 raw3205step0; decide +kernel
      have hl : raw3205step1Labels = raw3205step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3205step0 raw3205step0Labels permutation68 permutation3
    mixedMoment B raw3205step1 raw3205step1Labels = mixedMoment B raw3205step2 raw3205step2Labels := by
      have ha : raw3205step2 = raw3205step1 := by apply Matrix.ext; unfold raw3205step2 raw3205step1; decide +kernel
      have hl : raw3205step1Labels = labelEmbedding6 ∘ raw3205step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3205step1 raw3205step1Labels raw3205step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw3206 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1]]
def raw3206Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3206step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3206step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3206step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3206step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3206 raw3206Labels = mixedMoment B node5481 node5481Labels := by
  calc
    mixedMoment B raw3206 raw3206Labels = mixedMoment B raw3206step0 raw3206step0Labels := by
      have ha : raw3206step0 = (fun i j => raw3206 (permutation659 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3206step0 raw3206; decide +kernel
      have hl : raw3206step0Labels = raw3206Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3206 raw3206Labels permutation659 permutation5
    mixedMoment B raw3206step0 raw3206step0Labels = mixedMoment B raw3206step1 raw3206step1Labels := by
      have ha : raw3206step1 = raw3206step0 := by apply Matrix.ext; unfold raw3206step1 raw3206step0; decide +kernel
      have hl : raw3206step0Labels = labelEmbedding8 ∘ raw3206step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3206step0 raw3206step0Labels raw3206step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5481 node5481Labels := by rfl

def raw3207 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1]]
def raw3207Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3207step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1]]
def raw3207step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3207step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1]]
def raw3207step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3207step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3207step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3207step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3207step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3207 raw3207Labels = mixedMoment B node5492 node5492Labels := by
  calc
    mixedMoment B raw3207 raw3207Labels = mixedMoment B raw3207step0 raw3207step0Labels := by
      have hz : ∀ j, raw3207 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3207step0 = (fun i j => raw3207 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3207step0 raw3207; decide +kernel
      have hl : raw3207step0Labels = raw3207Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3207 raw3207Labels permutation434 hz
    mixedMoment B raw3207step0 raw3207step0Labels = mixedMoment B raw3207step1 raw3207step1Labels := by
      have hz : ∀ j, raw3207step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3207step1 = (fun i j => raw3207step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3207step1 raw3207step0; decide +kernel
      have hl : raw3207step1Labels = raw3207step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3207step0 raw3207step0Labels permutation80 hz
    mixedMoment B raw3207step1 raw3207step1Labels = mixedMoment B raw3207step2 raw3207step2Labels := by
      have ha : raw3207step2 = (fun i j => raw3207step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3207step2 raw3207step1; decide +kernel
      have hl : raw3207step2Labels = raw3207step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3207step1 raw3207step1Labels permutation31 permutation4
    mixedMoment B raw3207step2 raw3207step2Labels = mixedMoment B raw3207step3 raw3207step3Labels := by
      have ha : raw3207step3 = raw3207step2 := by apply Matrix.ext; unfold raw3207step3 raw3207step2; decide +kernel
      have hl : raw3207step2Labels = labelEmbedding7 ∘ raw3207step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3207step2 raw3207step2Labels raw3207step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5492 node5492Labels := by rfl

def raw3208 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![1, -2, 1]]
def raw3208Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![-2, 1, 1], ![1, -2, 1]]
def raw3208step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3208step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3208step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3208step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3208step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3208 raw3208Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw3208 raw3208Labels = mixedMoment B raw3208step0 raw3208step0Labels := by
      have hz : ∀ j, raw3208 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3208step0 = (fun i j => raw3208 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3208step0 raw3208; decide +kernel
      have hl : raw3208step0Labels = raw3208Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3208 raw3208Labels permutation346 hz
    mixedMoment B raw3208step0 raw3208step0Labels = mixedMoment B raw3208step1 raw3208step1Labels := by
      have ha : raw3208step1 = (fun i j => raw3208step0 (permutation110 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3208step1 raw3208step0; decide +kernel
      have hl : raw3208step1Labels = raw3208step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3208step0 raw3208step0Labels permutation110 permutation3
    mixedMoment B raw3208step1 raw3208step1Labels = mixedMoment B raw3208step2 raw3208step2Labels := by
      have ha : raw3208step2 = raw3208step1 := by apply Matrix.ext; unfold raw3208step2 raw3208step1; decide +kernel
      have hl : raw3208step1Labels = labelEmbedding6 ∘ raw3208step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3208step1 raw3208step1Labels raw3208step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5484 node5484Labels := by rfl

def raw3209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3209Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3209step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3209step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3209step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3209step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3209step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3209step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3209step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3209step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3209 raw3209Labels = mixedMoment B node5492 node5492Labels := by
  calc
    mixedMoment B raw3209 raw3209Labels = mixedMoment B raw3209step0 raw3209step0Labels := by
      have hz : ∀ j, raw3209 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3209step0 = (fun i j => raw3209 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3209step0 raw3209; decide +kernel
      have hl : raw3209step0Labels = raw3209Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3209 raw3209Labels permutation434 hz
    mixedMoment B raw3209step0 raw3209step0Labels = mixedMoment B raw3209step1 raw3209step1Labels := by
      have hz : ∀ j, raw3209step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3209step1 = (fun i j => raw3209step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3209step1 raw3209step0; decide +kernel
      have hl : raw3209step1Labels = raw3209step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3209step0 raw3209step0Labels permutation80 hz
    mixedMoment B raw3209step1 raw3209step1Labels = mixedMoment B raw3209step2 raw3209step2Labels := by
      have ha : raw3209step2 = (fun i j => raw3209step1 (permutation20 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3209step2 raw3209step1; decide +kernel
      have hl : raw3209step2Labels = raw3209step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3209step1 raw3209step1Labels permutation20 permutation4
    mixedMoment B raw3209step2 raw3209step2Labels = mixedMoment B raw3209step3 raw3209step3Labels := by
      have ha : raw3209step3 = raw3209step2 := by apply Matrix.ext; unfold raw3209step3 raw3209step2; decide +kernel
      have hl : raw3209step2Labels = labelEmbedding7 ∘ raw3209step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3209step2 raw3209step2Labels raw3209step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5492 node5492Labels := by rfl

def raw3210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3210Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3210step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3210step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3210step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3210step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3210step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3210step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3210step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3210 raw3210Labels = mixedMoment B node5492 node5492Labels := by
  calc
    mixedMoment B raw3210 raw3210Labels = mixedMoment B raw3210step0 raw3210step0Labels := by
      have hz : ∀ j, raw3210 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3210step0 = (fun i j => raw3210 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3210step0 raw3210; decide +kernel
      have hl : raw3210step0Labels = raw3210Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3210 raw3210Labels permutation434 hz
    mixedMoment B raw3210step0 raw3210step0Labels = mixedMoment B raw3210step1 raw3210step1Labels := by
      have hz : ∀ j, raw3210step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3210step1 = (fun i j => raw3210step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3210step1 raw3210step0; decide +kernel
      have hl : raw3210step1Labels = raw3210step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3210step0 raw3210step0Labels permutation56 hz
    mixedMoment B raw3210step1 raw3210step1Labels = mixedMoment B raw3210step2 raw3210step2Labels := by
      have ha : raw3210step2 = (fun i j => raw3210step1 (permutation20 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3210step2 raw3210step1; decide +kernel
      have hl : raw3210step2Labels = raw3210step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3210step1 raw3210step1Labels permutation20 permutation4
    mixedMoment B raw3210step2 raw3210step2Labels = mixedMoment B raw3210step3 raw3210step3Labels := by
      have ha : raw3210step3 = raw3210step2 := by apply Matrix.ext; unfold raw3210step3 raw3210step2; decide +kernel
      have hl : raw3210step2Labels = labelEmbedding7 ∘ raw3210step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3210step2 raw3210step2Labels raw3210step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5492 node5492Labels := by rfl

def raw3211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3211Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3211step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3211step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3211step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3211step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3211step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3211step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3211step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3211step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3211 raw3211Labels = mixedMoment B node5492 node5492Labels := by
  calc
    mixedMoment B raw3211 raw3211Labels = mixedMoment B raw3211step0 raw3211step0Labels := by
      have hz : ∀ j, raw3211 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3211step0 = (fun i j => raw3211 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3211step0 raw3211; decide +kernel
      have hl : raw3211step0Labels = raw3211Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3211 raw3211Labels permutation346 hz
    mixedMoment B raw3211step0 raw3211step0Labels = mixedMoment B raw3211step1 raw3211step1Labels := by
      have hz : ∀ j, raw3211step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3211step1 = (fun i j => raw3211step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3211step1 raw3211step0; decide +kernel
      have hl : raw3211step1Labels = raw3211step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3211step0 raw3211step0Labels permutation56 hz
    mixedMoment B raw3211step1 raw3211step1Labels = mixedMoment B raw3211step2 raw3211step2Labels := by
      have ha : raw3211step2 = (fun i j => raw3211step1 (permutation20 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3211step2 raw3211step1; decide +kernel
      have hl : raw3211step2Labels = raw3211step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3211step1 raw3211step1Labels permutation20 permutation4
    mixedMoment B raw3211step2 raw3211step2Labels = mixedMoment B raw3211step3 raw3211step3Labels := by
      have ha : raw3211step3 = raw3211step2 := by apply Matrix.ext; unfold raw3211step3 raw3211step2; decide +kernel
      have hl : raw3211step2Labels = labelEmbedding7 ∘ raw3211step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3211step2 raw3211step2Labels raw3211step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5492 node5492Labels := by rfl

def raw3212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 2, -2]]
def raw3212Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3212step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 2, -2]]
def raw3212step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3212step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![1, -2, 1], ![0, 2, -2]]
def raw3212step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3212step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 0, 1], ![1, -2, 1], ![0, 2, -2]]
def raw3212step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3212step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-2, 1, 1]]
def raw3212step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3212step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw3212step4Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3212step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw3212step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3212 raw3212Labels = mixedMoment B node5455 node5455Labels := by
  calc
    mixedMoment B raw3212 raw3212Labels = mixedMoment B raw3212step0 raw3212step0Labels := by
      have hz : ∀ j, raw3212 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3212step0 = (fun i j => raw3212 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3212step0 raw3212; decide +kernel
      have hl : raw3212step0Labels = raw3212Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3212 raw3212Labels permutation434 hz
    mixedMoment B raw3212step0 raw3212step0Labels = mixedMoment B raw3212step1 raw3212step1Labels := by
      have hz : ∀ j, raw3212step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3212step1 = (fun i j => raw3212step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3212step1 raw3212step0; decide +kernel
      have hl : raw3212step1Labels = raw3212step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3212step0 raw3212step0Labels permutation80 hz
    mixedMoment B raw3212step1 raw3212step1Labels = mixedMoment B raw3212step2 raw3212step2Labels := by
      have hz : ∀ j, raw3212step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3212step2 = (fun i j => raw3212step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3212step2 raw3212step1; decide +kernel
      have hl : raw3212step2Labels = raw3212step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3212step1 raw3212step1Labels permutation14 hz
    mixedMoment B raw3212step2 raw3212step2Labels = mixedMoment B raw3212step3 raw3212step3Labels := by
      have ha : raw3212step3 = (fun i j => raw3212step2 (permutation6 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3212step3 raw3212step2; decide +kernel
      have hl : raw3212step3Labels = raw3212step2Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3212step2 raw3212step2Labels permutation6 permutation4
    mixedMoment B raw3212step3 raw3212step3Labels = mixedMoment B raw3212step4 raw3212step4Labels := by
      have ha : raw3212step4 = -raw3212step3 := by apply Matrix.ext; change ∀ i j, raw3212step4 i j = -(raw3212step3 i j); unfold raw3212step4 raw3212step3; decide +kernel
      have hl : raw3212step4Labels = raw3212step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3212step4 raw3212step4Labels = mixedMoment B raw3212step5 raw3212step5Labels := by
      have ha : raw3212step5 = raw3212step4 := by apply Matrix.ext; unfold raw3212step5 raw3212step4; decide +kernel
      have hl : raw3212step4Labels = labelEmbedding7 ∘ raw3212step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3212step4 raw3212step4Labels raw3212step5Labels labelEmbedding7 hl
    _ = mixedMoment B node5455 node5455Labels := by rfl

def raw3213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3213Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3213step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3213step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3213step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3213step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3213step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3213step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3213step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3213 raw3213Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw3213 raw3213Labels = mixedMoment B raw3213step0 raw3213step0Labels := by
      have hz : ∀ j, raw3213 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3213step0 = (fun i j => raw3213 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3213step0 raw3213; decide +kernel
      have hl : raw3213step0Labels = raw3213Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3213 raw3213Labels permutation434 hz
    mixedMoment B raw3213step0 raw3213step0Labels = mixedMoment B raw3213step1 raw3213step1Labels := by
      have hz : ∀ j, raw3213step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3213step1 = (fun i j => raw3213step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3213step1 raw3213step0; decide +kernel
      have hl : raw3213step1Labels = raw3213step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3213step0 raw3213step0Labels permutation80 hz
    mixedMoment B raw3213step1 raw3213step1Labels = mixedMoment B raw3213step2 raw3213step2Labels := by
      have ha : raw3213step2 = (fun i j => raw3213step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3213step2 raw3213step1; decide +kernel
      have hl : raw3213step2Labels = raw3213step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3213step1 raw3213step1Labels permutation12 permutation3
    mixedMoment B raw3213step2 raw3213step2Labels = mixedMoment B raw3213step3 raw3213step3Labels := by
      have ha : raw3213step3 = raw3213step2 := by apply Matrix.ext; unfold raw3213step3 raw3213step2; decide +kernel
      have hl : raw3213step2Labels = labelEmbedding6 ∘ raw3213step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3213step2 raw3213step2Labels raw3213step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

def raw3214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3214Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3214step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3214step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3214step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3214step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3214step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3214 raw3214Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw3214 raw3214Labels = mixedMoment B raw3214step0 raw3214step0Labels := by
      have hz : ∀ j, raw3214 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3214step0 = (fun i j => raw3214 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3214step0 raw3214; decide +kernel
      have hl : raw3214step0Labels = raw3214Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3214 raw3214Labels permutation434 hz
    mixedMoment B raw3214step0 raw3214step0Labels = mixedMoment B raw3214step1 raw3214step1Labels := by
      have ha : raw3214step1 = (fun i j => raw3214step0 (permutation42 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3214step1 raw3214step0; decide +kernel
      have hl : raw3214step1Labels = raw3214step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3214step0 raw3214step0Labels permutation42 permutation3
    mixedMoment B raw3214step1 raw3214step1Labels = mixedMoment B raw3214step2 raw3214step2Labels := by
      have ha : raw3214step2 = raw3214step1 := by apply Matrix.ext; unfold raw3214step2 raw3214step1; decide +kernel
      have hl : raw3214step1Labels = labelEmbedding6 ∘ raw3214step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3214step1 raw3214step1Labels raw3214step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5484 node5484Labels := by rfl

def raw3215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3215Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3215step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3215step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3215step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3215step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3215step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3215step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3215 raw3215Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw3215 raw3215Labels = mixedMoment B raw3215step0 raw3215step0Labels := by
      have hz : ∀ j, raw3215 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3215step0 = (fun i j => raw3215 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3215step0 raw3215; decide +kernel
      have hl : raw3215step0Labels = raw3215Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3215 raw3215Labels permutation346 hz
    mixedMoment B raw3215step0 raw3215step0Labels = mixedMoment B raw3215step1 raw3215step1Labels := by
      have ha : raw3215step1 = (fun i j => raw3215step0 (permutation42 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3215step1 raw3215step0; decide +kernel
      have hl : raw3215step1Labels = raw3215step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3215step0 raw3215step0Labels permutation42 permutation3
    mixedMoment B raw3215step1 raw3215step1Labels = mixedMoment B raw3215step2 raw3215step2Labels := by
      have ha : raw3215step2 = raw3215step1 := by apply Matrix.ext; unfold raw3215step2 raw3215step1; decide +kernel
      have hl : raw3215step1Labels = labelEmbedding6 ∘ raw3215step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3215step1 raw3215step1Labels raw3215step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5484 node5484Labels := by rfl

def raw3216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 2, -2]]
def raw3216Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![0, 2, -2]]
def raw3216step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3216step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![1, -2, 1], ![0, 2, -2]]
def raw3216step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3216step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3216step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3216step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3216step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3216step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3216step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3216 raw3216Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw3216 raw3216Labels = mixedMoment B raw3216step0 raw3216step0Labels := by
      have hz : ∀ j, raw3216 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3216step0 = (fun i j => raw3216 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3216step0 raw3216; decide +kernel
      have hl : raw3216step0Labels = raw3216Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3216 raw3216Labels permutation434 hz
    mixedMoment B raw3216step0 raw3216step0Labels = mixedMoment B raw3216step1 raw3216step1Labels := by
      have hz : ∀ j, raw3216step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3216step1 = (fun i j => raw3216step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3216step1 raw3216step0; decide +kernel
      have hl : raw3216step1Labels = raw3216step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3216step0 raw3216step0Labels permutation80 hz
    mixedMoment B raw3216step1 raw3216step1Labels = mixedMoment B raw3216step2 raw3216step2Labels := by
      have ha : raw3216step2 = (fun i j => raw3216step1 (permutation26 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3216step2 raw3216step1; decide +kernel
      have hl : raw3216step2Labels = raw3216step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3216step1 raw3216step1Labels permutation26 permutation4
    mixedMoment B raw3216step2 raw3216step2Labels = mixedMoment B raw3216step3 raw3216step3Labels := by
      have ha : raw3216step3 = -raw3216step2 := by apply Matrix.ext; change ∀ i j, raw3216step3 i j = -(raw3216step2 i j); unfold raw3216step3 raw3216step2; decide +kernel
      have hl : raw3216step3Labels = raw3216step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3216step3 raw3216step3Labels = mixedMoment B raw3216step4 raw3216step4Labels := by
      have ha : raw3216step4 = raw3216step3 := by apply Matrix.ext; unfold raw3216step4 raw3216step3; decide +kernel
      have hl : raw3216step3Labels = labelEmbedding7 ∘ raw3216step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3216step3 raw3216step3Labels raw3216step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5451 node5451Labels := by rfl

def raw3217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3217Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3217step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3217step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3217step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3217step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3217step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3217step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3217step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3217 raw3217Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw3217 raw3217Labels = mixedMoment B raw3217step0 raw3217step0Labels := by
      have hz : ∀ j, raw3217 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3217step0 = (fun i j => raw3217 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3217step0 raw3217; decide +kernel
      have hl : raw3217step0Labels = raw3217Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3217 raw3217Labels permutation434 hz
    mixedMoment B raw3217step0 raw3217step0Labels = mixedMoment B raw3217step1 raw3217step1Labels := by
      have hz : ∀ j, raw3217step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3217step1 = (fun i j => raw3217step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3217step1 raw3217step0; decide +kernel
      have hl : raw3217step1Labels = raw3217step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3217step0 raw3217step0Labels permutation56 hz
    mixedMoment B raw3217step1 raw3217step1Labels = mixedMoment B raw3217step2 raw3217step2Labels := by
      have ha : raw3217step2 = (fun i j => raw3217step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3217step2 raw3217step1; decide +kernel
      have hl : raw3217step2Labels = raw3217step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3217step1 raw3217step1Labels permutation12 permutation3
    mixedMoment B raw3217step2 raw3217step2Labels = mixedMoment B raw3217step3 raw3217step3Labels := by
      have ha : raw3217step3 = raw3217step2 := by apply Matrix.ext; unfold raw3217step3 raw3217step2; decide +kernel
      have hl : raw3217step2Labels = labelEmbedding6 ∘ raw3217step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3217step2 raw3217step2Labels raw3217step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

def raw3218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3218Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3218step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3218step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3218step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3218step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3218step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3218step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3218 raw3218Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw3218 raw3218Labels = mixedMoment B raw3218step0 raw3218step0Labels := by
      have hz : ∀ j, raw3218 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3218step0 = (fun i j => raw3218 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3218step0 raw3218; decide +kernel
      have hl : raw3218step0Labels = raw3218Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3218 raw3218Labels permutation434 hz
    mixedMoment B raw3218step0 raw3218step0Labels = mixedMoment B raw3218step1 raw3218step1Labels := by
      have ha : raw3218step1 = (fun i j => raw3218step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3218step1 raw3218step0; decide +kernel
      have hl : raw3218step1Labels = raw3218step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3218step0 raw3218step0Labels permutation36 permutation3
    mixedMoment B raw3218step1 raw3218step1Labels = mixedMoment B raw3218step2 raw3218step2Labels := by
      have ha : raw3218step2 = raw3218step1 := by apply Matrix.ext; unfold raw3218step2 raw3218step1; decide +kernel
      have hl : raw3218step1Labels = labelEmbedding6 ∘ raw3218step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3218step1 raw3218step1Labels raw3218step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5484 node5484Labels := by rfl

def raw3219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3219Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3219step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3219step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3219step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3219step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3219step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3219step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3219 raw3219Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw3219 raw3219Labels = mixedMoment B raw3219step0 raw3219step0Labels := by
      have hz : ∀ j, raw3219 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3219step0 = (fun i j => raw3219 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3219step0 raw3219; decide +kernel
      have hl : raw3219step0Labels = raw3219Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3219 raw3219Labels permutation265 hz
    mixedMoment B raw3219step0 raw3219step0Labels = mixedMoment B raw3219step1 raw3219step1Labels := by
      have ha : raw3219step1 = (fun i j => raw3219step0 (permutation42 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3219step1 raw3219step0; decide +kernel
      have hl : raw3219step1Labels = raw3219step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3219step0 raw3219step0Labels permutation42 permutation3
    mixedMoment B raw3219step1 raw3219step1Labels = mixedMoment B raw3219step2 raw3219step2Labels := by
      have ha : raw3219step2 = raw3219step1 := by apply Matrix.ext; unfold raw3219step2 raw3219step1; decide +kernel
      have hl : raw3219step1Labels = labelEmbedding6 ∘ raw3219step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3219step1 raw3219step1Labels raw3219step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5484 node5484Labels := by rfl

def raw3220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -2, 1], ![0, 2, -2]]
def raw3220Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3220step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![0, 2, -2]]
def raw3220step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3220step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![1, -2, 1], ![0, 2, -2]]
def raw3220step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3220step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3220step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3220step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3220step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3220step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3220step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3220 raw3220Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw3220 raw3220Labels = mixedMoment B raw3220step0 raw3220step0Labels := by
      have hz : ∀ j, raw3220 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3220step0 = (fun i j => raw3220 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3220step0 raw3220; decide +kernel
      have hl : raw3220step0Labels = raw3220Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3220 raw3220Labels permutation434 hz
    mixedMoment B raw3220step0 raw3220step0Labels = mixedMoment B raw3220step1 raw3220step1Labels := by
      have hz : ∀ j, raw3220step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3220step1 = (fun i j => raw3220step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3220step1 raw3220step0; decide +kernel
      have hl : raw3220step1Labels = raw3220step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3220step0 raw3220step0Labels permutation56 hz
    mixedMoment B raw3220step1 raw3220step1Labels = mixedMoment B raw3220step2 raw3220step2Labels := by
      have ha : raw3220step2 = (fun i j => raw3220step1 (permutation26 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3220step2 raw3220step1; decide +kernel
      have hl : raw3220step2Labels = raw3220step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3220step1 raw3220step1Labels permutation26 permutation4
    mixedMoment B raw3220step2 raw3220step2Labels = mixedMoment B raw3220step3 raw3220step3Labels := by
      have ha : raw3220step3 = -raw3220step2 := by apply Matrix.ext; change ∀ i j, raw3220step3 i j = -(raw3220step2 i j); unfold raw3220step3 raw3220step2; decide +kernel
      have hl : raw3220step3Labels = raw3220step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3220step3 raw3220step3Labels = mixedMoment B raw3220step4 raw3220step4Labels := by
      have ha : raw3220step4 = raw3220step3 := by apply Matrix.ext; unfold raw3220step4 raw3220step3; decide +kernel
      have hl : raw3220step3Labels = labelEmbedding7 ∘ raw3220step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3220step3 raw3220step3Labels raw3220step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5451 node5451Labels := by rfl

def raw3221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3221Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3221step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3221step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3221step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3221step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3221step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3221step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3221step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3221step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3221 raw3221Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw3221 raw3221Labels = mixedMoment B raw3221step0 raw3221step0Labels := by
      have hz : ∀ j, raw3221 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3221step0 = (fun i j => raw3221 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3221step0 raw3221; decide +kernel
      have hl : raw3221step0Labels = raw3221Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3221 raw3221Labels permutation346 hz
    mixedMoment B raw3221step0 raw3221step0Labels = mixedMoment B raw3221step1 raw3221step1Labels := by
      have hz : ∀ j, raw3221step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3221step1 = (fun i j => raw3221step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3221step1 raw3221step0; decide +kernel
      have hl : raw3221step1Labels = raw3221step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3221step0 raw3221step0Labels permutation56 hz
    mixedMoment B raw3221step1 raw3221step1Labels = mixedMoment B raw3221step2 raw3221step2Labels := by
      have ha : raw3221step2 = (fun i j => raw3221step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3221step2 raw3221step1; decide +kernel
      have hl : raw3221step2Labels = raw3221step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3221step1 raw3221step1Labels permutation12 permutation3
    mixedMoment B raw3221step2 raw3221step2Labels = mixedMoment B raw3221step3 raw3221step3Labels := by
      have ha : raw3221step3 = raw3221step2 := by apply Matrix.ext; unfold raw3221step3 raw3221step2; decide +kernel
      have hl : raw3221step2Labels = labelEmbedding6 ∘ raw3221step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3221step2 raw3221step2Labels raw3221step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

def raw3222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3222Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3222step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3222step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3222step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3222step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3222step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3222 raw3222Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw3222 raw3222Labels = mixedMoment B raw3222step0 raw3222step0Labels := by
      have hz : ∀ j, raw3222 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3222step0 = (fun i j => raw3222 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3222step0 raw3222; decide +kernel
      have hl : raw3222step0Labels = raw3222Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3222 raw3222Labels permutation346 hz
    mixedMoment B raw3222step0 raw3222step0Labels = mixedMoment B raw3222step1 raw3222step1Labels := by
      have ha : raw3222step1 = (fun i j => raw3222step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3222step1 raw3222step0; decide +kernel
      have hl : raw3222step1Labels = raw3222step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3222step0 raw3222step0Labels permutation36 permutation3
    mixedMoment B raw3222step1 raw3222step1Labels = mixedMoment B raw3222step2 raw3222step2Labels := by
      have ha : raw3222step2 = raw3222step1 := by apply Matrix.ext; unfold raw3222step2 raw3222step1; decide +kernel
      have hl : raw3222step1Labels = labelEmbedding6 ∘ raw3222step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3222step1 raw3222step1Labels raw3222step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5484 node5484Labels := by rfl

def raw3223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3223Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw3223step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3223step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3223step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3223step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3223step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3223 raw3223Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw3223 raw3223Labels = mixedMoment B raw3223step0 raw3223step0Labels := by
      have hz : ∀ j, raw3223 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3223step0 = (fun i j => raw3223 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3223step0 raw3223; decide +kernel
      have hl : raw3223step0Labels = raw3223Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3223 raw3223Labels permutation265 hz
    mixedMoment B raw3223step0 raw3223step0Labels = mixedMoment B raw3223step1 raw3223step1Labels := by
      have ha : raw3223step1 = (fun i j => raw3223step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3223step1 raw3223step0; decide +kernel
      have hl : raw3223step1Labels = raw3223step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3223step0 raw3223step0Labels permutation36 permutation3
    mixedMoment B raw3223step1 raw3223step1Labels = mixedMoment B raw3223step2 raw3223step2Labels := by
      have ha : raw3223step2 = raw3223step1 := by apply Matrix.ext; unfold raw3223step2 raw3223step1; decide +kernel
      have hl : raw3223step1Labels = labelEmbedding6 ∘ raw3223step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3223step1 raw3223step1Labels raw3223step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5484 node5484Labels := by rfl

def raw3224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![0, 2, -2]]
def raw3224Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3224step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -2, 1], ![0, 2, -2]]
def raw3224step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3224step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![1, -2, 1], ![0, 2, -2]]
def raw3224step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3224step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3224step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3224step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3224step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3224step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3224step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3224 raw3224Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw3224 raw3224Labels = mixedMoment B raw3224step0 raw3224step0Labels := by
      have hz : ∀ j, raw3224 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3224step0 = (fun i j => raw3224 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3224step0 raw3224; decide +kernel
      have hl : raw3224step0Labels = raw3224Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3224 raw3224Labels permutation346 hz
    mixedMoment B raw3224step0 raw3224step0Labels = mixedMoment B raw3224step1 raw3224step1Labels := by
      have hz : ∀ j, raw3224step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3224step1 = (fun i j => raw3224step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3224step1 raw3224step0; decide +kernel
      have hl : raw3224step1Labels = raw3224step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3224step0 raw3224step0Labels permutation56 hz
    mixedMoment B raw3224step1 raw3224step1Labels = mixedMoment B raw3224step2 raw3224step2Labels := by
      have ha : raw3224step2 = (fun i j => raw3224step1 (permutation26 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3224step2 raw3224step1; decide +kernel
      have hl : raw3224step2Labels = raw3224step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3224step1 raw3224step1Labels permutation26 permutation4
    mixedMoment B raw3224step2 raw3224step2Labels = mixedMoment B raw3224step3 raw3224step3Labels := by
      have ha : raw3224step3 = -raw3224step2 := by apply Matrix.ext; change ∀ i j, raw3224step3 i j = -(raw3224step2 i j); unfold raw3224step3 raw3224step2; decide +kernel
      have hl : raw3224step3Labels = raw3224step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3224step3 raw3224step3Labels = mixedMoment B raw3224step4 raw3224step4Labels := by
      have ha : raw3224step4 = raw3224step3 := by apply Matrix.ext; unfold raw3224step4 raw3224step3; decide +kernel
      have hl : raw3224step3Labels = labelEmbedding7 ∘ raw3224step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3224step3 raw3224step3Labels raw3224step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5451 node5451Labels := by rfl

def raw3225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw3225Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3225step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw3225step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3225step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw3225step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3225step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 2, 1], ![2, -3, 1], ![1, 1, -2]]
def raw3225step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3225step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw3225step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3225step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw3225step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3225 raw3225Labels = mixedMoment B node5305 node5305Labels := by
  calc
    mixedMoment B raw3225 raw3225Labels = mixedMoment B raw3225step0 raw3225step0Labels := by
      have hz : ∀ j, raw3225 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3225step0 = (fun i j => raw3225 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3225step0 raw3225; decide +kernel
      have hl : raw3225step0Labels = raw3225Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3225 raw3225Labels permutation434 hz
    mixedMoment B raw3225step0 raw3225step0Labels = mixedMoment B raw3225step1 raw3225step1Labels := by
      have hz : ∀ j, raw3225step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3225step1 = (fun i j => raw3225step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3225step1 raw3225step0; decide +kernel
      have hl : raw3225step1Labels = raw3225step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3225step0 raw3225step0Labels permutation80 hz
    mixedMoment B raw3225step1 raw3225step1Labels = mixedMoment B raw3225step2 raw3225step2Labels := by
      have hz : ∀ j, raw3225step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3225step2 = (fun i j => raw3225step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3225step2 raw3225step1; decide +kernel
      have hl : raw3225step2Labels = raw3225step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3225step1 raw3225step1Labels permutation14 hz
    mixedMoment B raw3225step2 raw3225step2Labels = mixedMoment B raw3225step3 raw3225step3Labels := by
      have ha : raw3225step3 = (fun i j => raw3225step2 (permutation3 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3225step3 raw3225step2; decide +kernel
      have hl : raw3225step3Labels = raw3225step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3225step2 raw3225step2Labels permutation3 permutation3
    mixedMoment B raw3225step3 raw3225step3Labels = mixedMoment B raw3225step4 raw3225step4Labels := by
      have ha : raw3225step4 = raw3225step3 := by apply Matrix.ext; unfold raw3225step4 raw3225step3; decide +kernel
      have hl : raw3225step3Labels = labelEmbedding6 ∘ raw3225step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3225step3 raw3225step3Labels raw3225step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5305 node5305Labels := by rfl

def raw3226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw3226Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw3226step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3226step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![2, -3, 1], ![1, 1, -2]]
def raw3226step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3226step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3226step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3226step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3226step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3226 raw3226Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw3226 raw3226Labels = mixedMoment B raw3226step0 raw3226step0Labels := by
      have hz : ∀ j, raw3226 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3226step0 = (fun i j => raw3226 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3226step0 raw3226; decide +kernel
      have hl : raw3226step0Labels = raw3226Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3226 raw3226Labels permutation434 hz
    mixedMoment B raw3226step0 raw3226step0Labels = mixedMoment B raw3226step1 raw3226step1Labels := by
      have hz : ∀ j, raw3226step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3226step1 = (fun i j => raw3226step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3226step1 raw3226step0; decide +kernel
      have hl : raw3226step1Labels = raw3226step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3226step0 raw3226step0Labels permutation80 hz
    mixedMoment B raw3226step1 raw3226step1Labels = mixedMoment B raw3226step2 raw3226step2Labels := by
      have ha : raw3226step2 = (fun i j => raw3226step1 (permutation25 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3226step2 raw3226step1; decide +kernel
      have hl : raw3226step2Labels = raw3226step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3226step1 raw3226step1Labels permutation25 permutation5
    mixedMoment B raw3226step2 raw3226step2Labels = mixedMoment B raw3226step3 raw3226step3Labels := by
      have ha : raw3226step3 = raw3226step2 := by apply Matrix.ext; unfold raw3226step3 raw3226step2; decide +kernel
      have hl : raw3226step2Labels = labelEmbedding8 ∘ raw3226step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3226step2 raw3226step2Labels raw3226step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

def raw3227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw3227Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![1, 1, -2]]
def raw3227step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3227step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![2, -3, 1], ![1, 1, -2]]
def raw3227step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3227step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3227step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3227step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3227step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3227 raw3227Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw3227 raw3227Labels = mixedMoment B raw3227step0 raw3227step0Labels := by
      have hz : ∀ j, raw3227 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3227step0 = (fun i j => raw3227 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3227step0 raw3227; decide +kernel
      have hl : raw3227step0Labels = raw3227Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3227 raw3227Labels permutation434 hz
    mixedMoment B raw3227step0 raw3227step0Labels = mixedMoment B raw3227step1 raw3227step1Labels := by
      have hz : ∀ j, raw3227step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3227step1 = (fun i j => raw3227step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3227step1 raw3227step0; decide +kernel
      have hl : raw3227step1Labels = raw3227step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3227step0 raw3227step0Labels permutation56 hz
    mixedMoment B raw3227step1 raw3227step1Labels = mixedMoment B raw3227step2 raw3227step2Labels := by
      have ha : raw3227step2 = (fun i j => raw3227step1 (permutation25 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3227step2 raw3227step1; decide +kernel
      have hl : raw3227step2Labels = raw3227step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3227step1 raw3227step1Labels permutation25 permutation5
    mixedMoment B raw3227step2 raw3227step2Labels = mixedMoment B raw3227step3 raw3227step3Labels := by
      have ha : raw3227step3 = raw3227step2 := by apply Matrix.ext; unfold raw3227step3 raw3227step2; decide +kernel
      have hl : raw3227step2Labels = labelEmbedding8 ∘ raw3227step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3227step2 raw3227step2Labels raw3227step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

def raw3228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![1, 1, -2]]
def raw3228Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3228step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![2, -3, 1], ![1, 1, -2]]
def raw3228step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3228step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![2, -3, 1], ![1, 1, -2]]
def raw3228step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3228step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3228step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3228step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw3228step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3228 raw3228Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw3228 raw3228Labels = mixedMoment B raw3228step0 raw3228step0Labels := by
      have hz : ∀ j, raw3228 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3228step0 = (fun i j => raw3228 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3228step0 raw3228; decide +kernel
      have hl : raw3228step0Labels = raw3228Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3228 raw3228Labels permutation346 hz
    mixedMoment B raw3228step0 raw3228step0Labels = mixedMoment B raw3228step1 raw3228step1Labels := by
      have hz : ∀ j, raw3228step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3228step1 = (fun i j => raw3228step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3228step1 raw3228step0; decide +kernel
      have hl : raw3228step1Labels = raw3228step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3228step0 raw3228step0Labels permutation56 hz
    mixedMoment B raw3228step1 raw3228step1Labels = mixedMoment B raw3228step2 raw3228step2Labels := by
      have ha : raw3228step2 = (fun i j => raw3228step1 (permutation25 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3228step2 raw3228step1; decide +kernel
      have hl : raw3228step2Labels = raw3228step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3228step1 raw3228step1Labels permutation25 permutation5
    mixedMoment B raw3228step2 raw3228step2Labels = mixedMoment B raw3228step3 raw3228step3Labels := by
      have ha : raw3228step3 = raw3228step2 := by apply Matrix.ext; unfold raw3228step3 raw3228step2; decide +kernel
      have hl : raw3228step2Labels = labelEmbedding8 ∘ raw3228step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3228step2 raw3228step2Labels raw3228step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

def raw3229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![0, 2, -2]]
def raw3229Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![2, -3, 1], ![0, 2, -2]]
def raw3229step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3229step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![2, -3, 1], ![0, 2, -2]]
def raw3229step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3229step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![2, -3, 1], ![0, 2, -2]]
def raw3229step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3229step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw3229step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3229step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 1, -2], ![2, -2, 0]]
def raw3229step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3229 raw3229Labels = mixedMoment B node5310 node5310Labels := by
  calc
    mixedMoment B raw3229 raw3229Labels = mixedMoment B raw3229step0 raw3229step0Labels := by
      have hz : ∀ j, raw3229 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3229step0 = (fun i j => raw3229 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3229step0 raw3229; decide +kernel
      have hl : raw3229step0Labels = raw3229Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3229 raw3229Labels permutation434 hz
    mixedMoment B raw3229step0 raw3229step0Labels = mixedMoment B raw3229step1 raw3229step1Labels := by
      have hz : ∀ j, raw3229step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3229step1 = (fun i j => raw3229step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3229step1 raw3229step0; decide +kernel
      have hl : raw3229step1Labels = raw3229step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3229step0 raw3229step0Labels permutation80 hz
    mixedMoment B raw3229step1 raw3229step1Labels = mixedMoment B raw3229step2 raw3229step2Labels := by
      have hz : ∀ j, raw3229step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3229step2 = (fun i j => raw3229step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3229step2 raw3229step1; decide +kernel
      have hl : raw3229step2Labels = raw3229step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3229step1 raw3229step1Labels permutation14 hz
    mixedMoment B raw3229step2 raw3229step2Labels = mixedMoment B raw3229step3 raw3229step3Labels := by
      have ha : raw3229step3 = (fun i j => raw3229step2 (permutation4 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3229step3 raw3229step2; decide +kernel
      have hl : raw3229step3Labels = raw3229step2Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3229step2 raw3229step2Labels permutation4 permutation5
    mixedMoment B raw3229step3 raw3229step3Labels = mixedMoment B raw3229step4 raw3229step4Labels := by
      have ha : raw3229step4 = raw3229step3 := by apply Matrix.ext; unfold raw3229step4 raw3229step3; decide +kernel
      have hl : raw3229step3Labels = labelEmbedding8 ∘ raw3229step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3229step3 raw3229step3Labels raw3229step4Labels labelEmbedding8 hl
    _ = mixedMoment B node5310 node5310Labels := by rfl

def raw3230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw3230Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3230step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw3230step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3230step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw3230step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3230step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![2, 0, -2]]
def raw3230step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3230step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-2, 1, 1]]
def raw3230step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3230step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw3230step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3230 raw3230Labels = mixedMoment B node5455 node5455Labels := by
  calc
    mixedMoment B raw3230 raw3230Labels = mixedMoment B raw3230step0 raw3230step0Labels := by
      have hz : ∀ j, raw3230 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3230step0 = (fun i j => raw3230 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3230step0 raw3230; decide +kernel
      have hl : raw3230step0Labels = raw3230Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3230 raw3230Labels permutation434 hz
    mixedMoment B raw3230step0 raw3230step0Labels = mixedMoment B raw3230step1 raw3230step1Labels := by
      have hz : ∀ j, raw3230step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3230step1 = (fun i j => raw3230step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3230step1 raw3230step0; decide +kernel
      have hl : raw3230step1Labels = raw3230step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3230step0 raw3230step0Labels permutation80 hz
    mixedMoment B raw3230step1 raw3230step1Labels = mixedMoment B raw3230step2 raw3230step2Labels := by
      have hz : ∀ j, raw3230step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3230step2 = (fun i j => raw3230step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3230step2 raw3230step1; decide +kernel
      have hl : raw3230step2Labels = raw3230step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3230step1 raw3230step1Labels permutation14 hz
    mixedMoment B raw3230step2 raw3230step2Labels = mixedMoment B raw3230step3 raw3230step3Labels := by
      have ha : raw3230step3 = (fun i j => raw3230step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3230step3 raw3230step2; decide +kernel
      have hl : raw3230step3Labels = raw3230step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3230step2 raw3230step2Labels permutation7 permutation2
    mixedMoment B raw3230step3 raw3230step3Labels = mixedMoment B raw3230step4 raw3230step4Labels := by
      have ha : raw3230step4 = -raw3230step3 := by apply Matrix.ext; change ∀ i j, raw3230step4 i j = -(raw3230step3 i j); unfold raw3230step4 raw3230step3; decide +kernel
      have hl : raw3230step4Labels = raw3230step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5455 node5455Labels := by rfl

def raw3231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3231Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3231step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3231step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3231step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3231step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3231step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3231 raw3231Labels = mixedMoment B node5499 node5499Labels := by
  calc
    mixedMoment B raw3231 raw3231Labels = mixedMoment B raw3231step0 raw3231step0Labels := by
      have hz : ∀ j, raw3231 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3231step0 = (fun i j => raw3231 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3231step0 raw3231; decide +kernel
      have hl : raw3231step0Labels = raw3231Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3231 raw3231Labels permutation346 hz
    mixedMoment B raw3231step0 raw3231step0Labels = mixedMoment B raw3231step1 raw3231step1Labels := by
      have ha : raw3231step1 = (fun i j => raw3231step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3231step1 raw3231step0; decide +kernel
      have hl : raw3231step1Labels = raw3231step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3231step0 raw3231step0Labels permutation127 permutation2
    mixedMoment B raw3231step1 raw3231step1Labels = mixedMoment B raw3231step2 raw3231step2Labels := by
      have ha : raw3231step2 = -raw3231step1 := by apply Matrix.ext; change ∀ i j, raw3231step2 i j = -(raw3231step1 i j); unfold raw3231step2 raw3231step1; decide +kernel
      have hl : raw3231step2Labels = raw3231step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5499 node5499Labels := by rfl

def raw3232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3232Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3232step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3232step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 0, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3232step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3232step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3232step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3232 raw3232Labels = mixedMoment B node5499 node5499Labels := by
  calc
    mixedMoment B raw3232 raw3232Labels = mixedMoment B raw3232step0 raw3232step0Labels := by
      have hz : ∀ j, raw3232 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3232step0 = (fun i j => raw3232 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3232step0 raw3232; decide +kernel
      have hl : raw3232step0Labels = raw3232Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3232 raw3232Labels permutation265 hz
    mixedMoment B raw3232step0 raw3232step0Labels = mixedMoment B raw3232step1 raw3232step1Labels := by
      have ha : raw3232step1 = (fun i j => raw3232step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3232step1 raw3232step0; decide +kernel
      have hl : raw3232step1Labels = raw3232step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3232step0 raw3232step0Labels permutation127 permutation2
    mixedMoment B raw3232step1 raw3232step1Labels = mixedMoment B raw3232step2 raw3232step2Labels := by
      have ha : raw3232step2 = -raw3232step1 := by apply Matrix.ext; change ∀ i j, raw3232step2 i j = -(raw3232step1 i j); unfold raw3232step2 raw3232step1; decide +kernel
      have hl : raw3232step2Labels = raw3232step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5499 node5499Labels := by rfl

def raw3233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3233Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3233step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3233step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3233step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3233step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw3233step2Labels : Fin 2 → Fin 3 := ![0, 2]

def raw3233step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw3233step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical3233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3233 raw3233Labels = mixedMoment B node4096 node4096Labels := by
  calc
    mixedMoment B raw3233 raw3233Labels = mixedMoment B raw3233step0 raw3233step0Labels := by
      have hz : ∀ j, raw3233 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3233step0 = (fun i j => raw3233 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3233step0 raw3233; decide +kernel
      have hl : raw3233step0Labels = raw3233Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3233 raw3233Labels permutation346 hz
    mixedMoment B raw3233step0 raw3233step0Labels = mixedMoment B raw3233step1 raw3233step1Labels := by
      have hz : ∀ j, raw3233step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3233step1 = (fun i j => raw3233step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3233step1 raw3233step0; decide +kernel
      have hl : raw3233step1Labels = raw3233step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3233step0 raw3233step0Labels permutation56 hz
    mixedMoment B raw3233step1 raw3233step1Labels = mixedMoment B raw3233step2 raw3233step2Labels := by
      have hz : ∀ i, raw3233step1 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw3233step2 = (fun i j => raw3233step1 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw3233step2 raw3233step1; decide +kernel
      have hl : raw3233step2Labels = (fun j => raw3233step1Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3233step1 raw3233step1Labels permutation4 hz
    mixedMoment B raw3233step2 raw3233step2Labels = mixedMoment B raw3233step3 raw3233step3Labels := by
      have ha : raw3233step3 = raw3233step2 := by apply Matrix.ext; unfold raw3233step3 raw3233step2; decide +kernel
      have hl : raw3233step2Labels = labelEmbedding2 ∘ raw3233step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3233step2 raw3233step2Labels raw3233step3Labels labelEmbedding2 hl
    _ = mixedMoment B node4096 node4096Labels := by rfl

def raw3234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3234Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3234step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3234step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3234step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3234step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3234step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3234step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3234step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3234 raw3234Labels = mixedMoment B node5501 node5501Labels := by
  calc
    mixedMoment B raw3234 raw3234Labels = mixedMoment B raw3234step0 raw3234step0Labels := by
      have hz : ∀ j, raw3234 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3234step0 = (fun i j => raw3234 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3234step0 raw3234; decide +kernel
      have hl : raw3234step0Labels = raw3234Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3234 raw3234Labels permutation346 hz
    mixedMoment B raw3234step0 raw3234step0Labels = mixedMoment B raw3234step1 raw3234step1Labels := by
      have hz : ∀ j, raw3234step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3234step1 = (fun i j => raw3234step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3234step1 raw3234step0; decide +kernel
      have hl : raw3234step1Labels = raw3234step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3234step0 raw3234step0Labels permutation56 hz
    mixedMoment B raw3234step1 raw3234step1Labels = mixedMoment B raw3234step2 raw3234step2Labels := by
      have ha : raw3234step2 = (fun i j => raw3234step1 (permutation24 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3234step2 raw3234step1; decide +kernel
      have hl : raw3234step2Labels = raw3234step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3234step1 raw3234step1Labels permutation24 permutation6
    mixedMoment B raw3234step2 raw3234step2Labels = mixedMoment B raw3234step3 raw3234step3Labels := by
      have ha : raw3234step3 = raw3234step2 := by apply Matrix.ext; unfold raw3234step3 raw3234step2; decide +kernel
      have hl : raw3234step2Labels = labelEmbedding9 ∘ raw3234step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3234step2 raw3234step2Labels raw3234step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5501 node5501Labels := by rfl

def raw3235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3235Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3235step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3235step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3235step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3235step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3235step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3235step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3235step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3235 raw3235Labels = mixedMoment B node5501 node5501Labels := by
  calc
    mixedMoment B raw3235 raw3235Labels = mixedMoment B raw3235step0 raw3235step0Labels := by
      have hz : ∀ j, raw3235 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3235step0 = (fun i j => raw3235 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3235step0 raw3235; decide +kernel
      have hl : raw3235step0Labels = raw3235Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3235 raw3235Labels permutation346 hz
    mixedMoment B raw3235step0 raw3235step0Labels = mixedMoment B raw3235step1 raw3235step1Labels := by
      have hz : ∀ j, raw3235step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3235step1 = (fun i j => raw3235step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3235step1 raw3235step0; decide +kernel
      have hl : raw3235step1Labels = raw3235step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3235step0 raw3235step0Labels permutation56 hz
    mixedMoment B raw3235step1 raw3235step1Labels = mixedMoment B raw3235step2 raw3235step2Labels := by
      have ha : raw3235step2 = (fun i j => raw3235step1 (permutation30 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3235step2 raw3235step1; decide +kernel
      have hl : raw3235step2Labels = raw3235step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3235step1 raw3235step1Labels permutation30 permutation6
    mixedMoment B raw3235step2 raw3235step2Labels = mixedMoment B raw3235step3 raw3235step3Labels := by
      have ha : raw3235step3 = raw3235step2 := by apply Matrix.ext; unfold raw3235step3 raw3235step2; decide +kernel
      have hl : raw3235step2Labels = labelEmbedding9 ∘ raw3235step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3235step2 raw3235step2Labels raw3235step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5501 node5501Labels := by rfl

def raw3236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3236Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3236step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3236step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3236step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3236step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3236step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3236step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3236 raw3236Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw3236 raw3236Labels = mixedMoment B raw3236step0 raw3236step0Labels := by
      have hz : ∀ j, raw3236 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3236step0 = (fun i j => raw3236 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3236step0 raw3236; decide +kernel
      have hl : raw3236step0Labels = raw3236Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3236 raw3236Labels permutation346 hz
    mixedMoment B raw3236step0 raw3236step0Labels = mixedMoment B raw3236step1 raw3236step1Labels := by
      have ha : raw3236step1 = (fun i j => raw3236step0 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3236step1 raw3236step0; decide +kernel
      have hl : raw3236step1Labels = raw3236step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3236step0 raw3236step0Labels permutation41 permutation3
    mixedMoment B raw3236step1 raw3236step1Labels = mixedMoment B raw3236step2 raw3236step2Labels := by
      have ha : raw3236step2 = raw3236step1 := by apply Matrix.ext; unfold raw3236step2 raw3236step1; decide +kernel
      have hl : raw3236step1Labels = labelEmbedding6 ∘ raw3236step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3236step1 raw3236step1Labels raw3236step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw3237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3237Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3237step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3237step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3237step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3237step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3237 raw3237Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw3237 raw3237Labels = mixedMoment B raw3237step0 raw3237step0Labels := by
      have ha : raw3237step0 = (fun i j => raw3237 (permutation185 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3237step0 raw3237; decide +kernel
      have hl : raw3237step0Labels = raw3237Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3237 raw3237Labels permutation185 permutation3
    mixedMoment B raw3237step0 raw3237step0Labels = mixedMoment B raw3237step1 raw3237step1Labels := by
      have ha : raw3237step1 = raw3237step0 := by apply Matrix.ext; unfold raw3237step1 raw3237step0; decide +kernel
      have hl : raw3237step0Labels = labelEmbedding6 ∘ raw3237step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3237step0 raw3237step0Labels raw3237step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw3238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3238Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3238step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3238step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3238step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3238step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3238 raw3238Labels = mixedMoment B node5486 node5486Labels := by
  calc
    mixedMoment B raw3238 raw3238Labels = mixedMoment B raw3238step0 raw3238step0Labels := by
      have hz : ∀ j, raw3238 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3238step0 = (fun i j => raw3238 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3238step0 raw3238; decide +kernel
      have hl : raw3238step0Labels = raw3238Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3238 raw3238Labels permutation346 hz
    mixedMoment B raw3238step0 raw3238step0Labels = mixedMoment B raw3238step1 raw3238step1Labels := by
      have ha : raw3238step1 = (fun i j => raw3238step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3238step1 raw3238step0; decide +kernel
      have hl : raw3238step1Labels = raw3238step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3238step0 raw3238step0Labels permutation38 permutation2
    _ = mixedMoment B node5486 node5486Labels := by rfl

def raw3239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3239Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3239step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3239step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3239step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3239step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3239 raw3239Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw3239 raw3239Labels = mixedMoment B raw3239step0 raw3239step0Labels := by
      have hz : ∀ j, raw3239 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3239step0 = (fun i j => raw3239 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3239step0 raw3239; decide +kernel
      have hl : raw3239step0Labels = raw3239Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3239 raw3239Labels permutation346 hz
    mixedMoment B raw3239step0 raw3239step0Labels = mixedMoment B raw3239step1 raw3239step1Labels := by
      have ha : raw3239step1 = (fun i j => raw3239step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3239step1 raw3239step0; decide +kernel
      have hl : raw3239step1Labels = raw3239step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3239step0 raw3239step0Labels permutation40 permutation2
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw3240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3240Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3240step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3240step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3240step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3240 raw3240Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw3240 raw3240Labels = mixedMoment B raw3240step0 raw3240step0Labels := by
      have hz : ∀ j, raw3240 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3240step0 = (fun i j => raw3240 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3240step0 raw3240; decide +kernel
      have hl : raw3240step0Labels = raw3240Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3240 raw3240Labels permutation346 hz
    mixedMoment B raw3240step0 raw3240step0Labels = mixedMoment B raw3240step1 raw3240step1Labels := by
      have ha : raw3240step1 = (fun i j => raw3240step0 (permutation42 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3240step1 raw3240step0; decide +kernel
      have hl : raw3240step1Labels = raw3240step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3240step0 raw3240step0Labels permutation42 permutation2
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw3241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3241Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3241step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3241step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3241step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3241step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3241step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3241step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3241 raw3241Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw3241 raw3241Labels = mixedMoment B raw3241step0 raw3241step0Labels := by
      have hz : ∀ j, raw3241 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3241step0 = (fun i j => raw3241 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3241step0 raw3241; decide +kernel
      have hl : raw3241step0Labels = raw3241Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3241 raw3241Labels permutation265 hz
    mixedMoment B raw3241step0 raw3241step0Labels = mixedMoment B raw3241step1 raw3241step1Labels := by
      have ha : raw3241step1 = (fun i j => raw3241step0 (permutation41 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3241step1 raw3241step0; decide +kernel
      have hl : raw3241step1Labels = raw3241step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3241step0 raw3241step0Labels permutation41 permutation3
    mixedMoment B raw3241step1 raw3241step1Labels = mixedMoment B raw3241step2 raw3241step2Labels := by
      have ha : raw3241step2 = raw3241step1 := by apply Matrix.ext; unfold raw3241step2 raw3241step1; decide +kernel
      have hl : raw3241step1Labels = labelEmbedding6 ∘ raw3241step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3241step1 raw3241step1Labels raw3241step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw3242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3242Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3242step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3242step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3242step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3242step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3242 raw3242Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw3242 raw3242Labels = mixedMoment B raw3242step0 raw3242step0Labels := by
      have ha : raw3242step0 = (fun i j => raw3242 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3242step0 raw3242; decide +kernel
      have hl : raw3242step0Labels = raw3242Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3242 raw3242Labels permutation161 permutation3
    mixedMoment B raw3242step0 raw3242step0Labels = mixedMoment B raw3242step1 raw3242step1Labels := by
      have ha : raw3242step1 = raw3242step0 := by apply Matrix.ext; unfold raw3242step1 raw3242step0; decide +kernel
      have hl : raw3242step0Labels = labelEmbedding6 ∘ raw3242step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3242step0 raw3242step0Labels raw3242step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw3243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3243Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3243step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3243step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3243step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3243 raw3243Labels = mixedMoment B node5486 node5486Labels := by
  calc
    mixedMoment B raw3243 raw3243Labels = mixedMoment B raw3243step0 raw3243step0Labels := by
      have hz : ∀ j, raw3243 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3243step0 = (fun i j => raw3243 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3243step0 raw3243; decide +kernel
      have hl : raw3243step0Labels = raw3243Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3243 raw3243Labels permutation265 hz
    mixedMoment B raw3243step0 raw3243step0Labels = mixedMoment B raw3243step1 raw3243step1Labels := by
      have ha : raw3243step1 = (fun i j => raw3243step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3243step1 raw3243step0; decide +kernel
      have hl : raw3243step1Labels = raw3243step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3243step0 raw3243step0Labels permutation38 permutation2
    _ = mixedMoment B node5486 node5486Labels := by rfl

def raw3244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3244Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3244step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3244step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3244step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3244 raw3244Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw3244 raw3244Labels = mixedMoment B raw3244step0 raw3244step0Labels := by
      have hz : ∀ j, raw3244 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3244step0 = (fun i j => raw3244 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3244step0 raw3244; decide +kernel
      have hl : raw3244step0Labels = raw3244Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3244 raw3244Labels permutation265 hz
    mixedMoment B raw3244step0 raw3244step0Labels = mixedMoment B raw3244step1 raw3244step1Labels := by
      have ha : raw3244step1 = (fun i j => raw3244step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3244step1 raw3244step0; decide +kernel
      have hl : raw3244step1Labels = raw3244step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3244step0 raw3244step0Labels permutation40 permutation2
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw3245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3245Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3245step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3245step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3245step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3245 raw3245Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw3245 raw3245Labels = mixedMoment B raw3245step0 raw3245step0Labels := by
      have hz : ∀ j, raw3245 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3245step0 = (fun i j => raw3245 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3245step0 raw3245; decide +kernel
      have hl : raw3245step0Labels = raw3245Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3245 raw3245Labels permutation265 hz
    mixedMoment B raw3245step0 raw3245step0Labels = mixedMoment B raw3245step1 raw3245step1Labels := by
      have ha : raw3245step1 = (fun i j => raw3245step0 (permutation42 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3245step1 raw3245step0; decide +kernel
      have hl : raw3245step1Labels = raw3245step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3245step0 raw3245step0Labels permutation42 permutation2
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw3246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3246Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3246step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3246step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3246step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3246step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3246step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3246step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3246step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3246step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3246 raw3246Labels = mixedMoment B node5306 node5306Labels := by
  calc
    mixedMoment B raw3246 raw3246Labels = mixedMoment B raw3246step0 raw3246step0Labels := by
      have hz : ∀ j, raw3246 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3246step0 = (fun i j => raw3246 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3246step0 raw3246; decide +kernel
      have hl : raw3246step0Labels = raw3246Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3246 raw3246Labels permutation346 hz
    mixedMoment B raw3246step0 raw3246step0Labels = mixedMoment B raw3246step1 raw3246step1Labels := by
      have hz : ∀ j, raw3246step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3246step1 = (fun i j => raw3246step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3246step1 raw3246step0; decide +kernel
      have hl : raw3246step1Labels = raw3246step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3246step0 raw3246step0Labels permutation56 hz
    mixedMoment B raw3246step1 raw3246step1Labels = mixedMoment B raw3246step2 raw3246step2Labels := by
      have ha : raw3246step2 = (fun i j => raw3246step1 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3246step2 raw3246step1; decide +kernel
      have hl : raw3246step2Labels = raw3246step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3246step1 raw3246step1Labels permutation11 permutation3
    mixedMoment B raw3246step2 raw3246step2Labels = mixedMoment B raw3246step3 raw3246step3Labels := by
      have ha : raw3246step3 = raw3246step2 := by apply Matrix.ext; unfold raw3246step3 raw3246step2; decide +kernel
      have hl : raw3246step2Labels = labelEmbedding6 ∘ raw3246step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3246step2 raw3246step2Labels raw3246step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5306 node5306Labels := by rfl

def raw3247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3247Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3247step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3247step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3247step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3247step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3247step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3247step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3247 raw3247Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw3247 raw3247Labels = mixedMoment B raw3247step0 raw3247step0Labels := by
      have hz : ∀ j, raw3247 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3247step0 = (fun i j => raw3247 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3247step0 raw3247; decide +kernel
      have hl : raw3247step0Labels = raw3247Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3247 raw3247Labels permutation346 hz
    mixedMoment B raw3247step0 raw3247step0Labels = mixedMoment B raw3247step1 raw3247step1Labels := by
      have ha : raw3247step1 = (fun i j => raw3247step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3247step1 raw3247step0; decide +kernel
      have hl : raw3247step1Labels = raw3247step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3247step0 raw3247step0Labels permutation35 permutation3
    mixedMoment B raw3247step1 raw3247step1Labels = mixedMoment B raw3247step2 raw3247step2Labels := by
      have ha : raw3247step2 = raw3247step1 := by apply Matrix.ext; unfold raw3247step2 raw3247step1; decide +kernel
      have hl : raw3247step1Labels = labelEmbedding6 ∘ raw3247step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3247step1 raw3247step1Labels raw3247step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5485 node5485Labels := by rfl

def raw3248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3248Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3248step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3248step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3248step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3248step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3248step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3248 raw3248Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw3248 raw3248Labels = mixedMoment B raw3248step0 raw3248step0Labels := by
      have hz : ∀ j, raw3248 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3248step0 = (fun i j => raw3248 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3248step0 raw3248; decide +kernel
      have hl : raw3248step0Labels = raw3248Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3248 raw3248Labels permutation265 hz
    mixedMoment B raw3248step0 raw3248step0Labels = mixedMoment B raw3248step1 raw3248step1Labels := by
      have ha : raw3248step1 = (fun i j => raw3248step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3248step1 raw3248step0; decide +kernel
      have hl : raw3248step1Labels = raw3248step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3248step0 raw3248step0Labels permutation35 permutation3
    mixedMoment B raw3248step1 raw3248step1Labels = mixedMoment B raw3248step2 raw3248step2Labels := by
      have ha : raw3248step2 = raw3248step1 := by apply Matrix.ext; unfold raw3248step2 raw3248step1; decide +kernel
      have hl : raw3248step1Labels = labelEmbedding6 ∘ raw3248step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3248step1 raw3248step1Labels raw3248step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5485 node5485Labels := by rfl

def raw3249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3249Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3249step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3249step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3249step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1]]
def raw3249step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3249step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3249step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3249step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3249step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3249 raw3249Labels = mixedMoment B node5492 node5492Labels := by
  calc
    mixedMoment B raw3249 raw3249Labels = mixedMoment B raw3249step0 raw3249step0Labels := by
      have hz : ∀ j, raw3249 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3249step0 = (fun i j => raw3249 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3249step0 raw3249; decide +kernel
      have hl : raw3249step0Labels = raw3249Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3249 raw3249Labels permutation346 hz
    mixedMoment B raw3249step0 raw3249step0Labels = mixedMoment B raw3249step1 raw3249step1Labels := by
      have hz : ∀ j, raw3249step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3249step1 = (fun i j => raw3249step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3249step1 raw3249step0; decide +kernel
      have hl : raw3249step1Labels = raw3249step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3249step0 raw3249step0Labels permutation56 hz
    mixedMoment B raw3249step1 raw3249step1Labels = mixedMoment B raw3249step2 raw3249step2Labels := by
      have ha : raw3249step2 = (fun i j => raw3249step1 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3249step2 raw3249step1; decide +kernel
      have hl : raw3249step2Labels = raw3249step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3249step1 raw3249step1Labels permutation11 permutation3
    mixedMoment B raw3249step2 raw3249step2Labels = mixedMoment B raw3249step3 raw3249step3Labels := by
      have ha : raw3249step3 = raw3249step2 := by apply Matrix.ext; unfold raw3249step3 raw3249step2; decide +kernel
      have hl : raw3249step2Labels = labelEmbedding6 ∘ raw3249step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3249step2 raw3249step2Labels raw3249step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5492 node5492Labels := by rfl

def raw3250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3250Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3250step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3250step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1]]
def raw3250step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3250step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3250step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3250step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3250step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3250 raw3250Labels = mixedMoment B node5492 node5492Labels := by
  calc
    mixedMoment B raw3250 raw3250Labels = mixedMoment B raw3250step0 raw3250step0Labels := by
      have hz : ∀ j, raw3250 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3250step0 = (fun i j => raw3250 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3250step0 raw3250; decide +kernel
      have hl : raw3250step0Labels = raw3250Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3250 raw3250Labels permutation346 hz
    mixedMoment B raw3250step0 raw3250step0Labels = mixedMoment B raw3250step1 raw3250step1Labels := by
      have hz : ∀ j, raw3250step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3250step1 = (fun i j => raw3250step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3250step1 raw3250step0; decide +kernel
      have hl : raw3250step1Labels = raw3250step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3250step0 raw3250step0Labels permutation56 hz
    mixedMoment B raw3250step1 raw3250step1Labels = mixedMoment B raw3250step2 raw3250step2Labels := by
      have ha : raw3250step2 = (fun i j => raw3250step1 (permutation13 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3250step2 raw3250step1; decide +kernel
      have hl : raw3250step2Labels = raw3250step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3250step1 raw3250step1Labels permutation13 permutation3
    mixedMoment B raw3250step2 raw3250step2Labels = mixedMoment B raw3250step3 raw3250step3Labels := by
      have ha : raw3250step3 = raw3250step2 := by apply Matrix.ext; unfold raw3250step3 raw3250step2; decide +kernel
      have hl : raw3250step2Labels = labelEmbedding6 ∘ raw3250step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3250step2 raw3250step2Labels raw3250step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5492 node5492Labels := by rfl

def raw3251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3251Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3251step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3251step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3251step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3251step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3251step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3251step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3251step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3251 raw3251Labels = mixedMoment B node5293 node5293Labels := by
  calc
    mixedMoment B raw3251 raw3251Labels = mixedMoment B raw3251step0 raw3251step0Labels := by
      have hz : ∀ j, raw3251 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3251step0 = (fun i j => raw3251 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3251step0 raw3251; decide +kernel
      have hl : raw3251step0Labels = raw3251Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3251 raw3251Labels permutation346 hz
    mixedMoment B raw3251step0 raw3251step0Labels = mixedMoment B raw3251step1 raw3251step1Labels := by
      have hz : ∀ j, raw3251step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3251step1 = (fun i j => raw3251step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3251step1 raw3251step0; decide +kernel
      have hl : raw3251step1Labels = raw3251step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3251step0 raw3251step0Labels permutation56 hz
    mixedMoment B raw3251step1 raw3251step1Labels = mixedMoment B raw3251step2 raw3251step2Labels := by
      have ha : raw3251step2 = (fun i j => raw3251step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3251step2 raw3251step1; decide +kernel
      have hl : raw3251step2Labels = raw3251step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3251step1 raw3251step1Labels permutation9 permutation3
    mixedMoment B raw3251step2 raw3251step2Labels = mixedMoment B raw3251step3 raw3251step3Labels := by
      have ha : raw3251step3 = raw3251step2 := by apply Matrix.ext; unfold raw3251step3 raw3251step2; decide +kernel
      have hl : raw3251step2Labels = labelEmbedding6 ∘ raw3251step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3251step2 raw3251step2Labels raw3251step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5293 node5293Labels := by rfl

def raw3252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3252Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3252step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3252step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3252step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3252step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3252step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3252 raw3252Labels = mixedMoment B node5483 node5483Labels := by
  calc
    mixedMoment B raw3252 raw3252Labels = mixedMoment B raw3252step0 raw3252step0Labels := by
      have hz : ∀ j, raw3252 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3252step0 = (fun i j => raw3252 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3252step0 raw3252; decide +kernel
      have hl : raw3252step0Labels = raw3252Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3252 raw3252Labels permutation346 hz
    mixedMoment B raw3252step0 raw3252step0Labels = mixedMoment B raw3252step1 raw3252step1Labels := by
      have ha : raw3252step1 = (fun i j => raw3252step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3252step1 raw3252step0; decide +kernel
      have hl : raw3252step1Labels = raw3252step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3252step0 raw3252step0Labels permutation127 permutation2
    mixedMoment B raw3252step1 raw3252step1Labels = mixedMoment B raw3252step2 raw3252step2Labels := by
      have ha : raw3252step2 = -raw3252step1 := by apply Matrix.ext; change ∀ i j, raw3252step2 i j = -(raw3252step1 i j); unfold raw3252step2 raw3252step1; decide +kernel
      have hl : raw3252step2Labels = raw3252step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5483 node5483Labels := by rfl

def raw3253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3253Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3253step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3253step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3253step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3253step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3253step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3253 raw3253Labels = mixedMoment B node5483 node5483Labels := by
  calc
    mixedMoment B raw3253 raw3253Labels = mixedMoment B raw3253step0 raw3253step0Labels := by
      have hz : ∀ j, raw3253 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3253step0 = (fun i j => raw3253 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3253step0 raw3253; decide +kernel
      have hl : raw3253step0Labels = raw3253Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3253 raw3253Labels permutation265 hz
    mixedMoment B raw3253step0 raw3253step0Labels = mixedMoment B raw3253step1 raw3253step1Labels := by
      have ha : raw3253step1 = (fun i j => raw3253step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3253step1 raw3253step0; decide +kernel
      have hl : raw3253step1Labels = raw3253step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3253step0 raw3253step0Labels permutation127 permutation2
    mixedMoment B raw3253step1 raw3253step1Labels = mixedMoment B raw3253step2 raw3253step2Labels := by
      have ha : raw3253step2 = -raw3253step1 := by apply Matrix.ext; change ∀ i j, raw3253step2 i j = -(raw3253step1 i j); unfold raw3253step2 raw3253step1; decide +kernel
      have hl : raw3253step2Labels = raw3253step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5483 node5483Labels := by rfl

def raw3254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3254Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3254step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3254step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3254step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1]]
def raw3254step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3254step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3254step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3254 raw3254Labels = mixedMoment B node5487 node5487Labels := by
  calc
    mixedMoment B raw3254 raw3254Labels = mixedMoment B raw3254step0 raw3254step0Labels := by
      have hz : ∀ j, raw3254 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3254step0 = (fun i j => raw3254 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3254step0 raw3254; decide +kernel
      have hl : raw3254step0Labels = raw3254Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3254 raw3254Labels permutation346 hz
    mixedMoment B raw3254step0 raw3254step0Labels = mixedMoment B raw3254step1 raw3254step1Labels := by
      have hz : ∀ j, raw3254step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3254step1 = (fun i j => raw3254step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3254step1 raw3254step0; decide +kernel
      have hl : raw3254step1Labels = raw3254step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3254step0 raw3254step0Labels permutation56 hz
    mixedMoment B raw3254step1 raw3254step1Labels = mixedMoment B raw3254step2 raw3254step2Labels := by
      have ha : raw3254step2 = (fun i j => raw3254step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3254step2 raw3254step1; decide +kernel
      have hl : raw3254step2Labels = raw3254step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3254step1 raw3254step1Labels permutation9 permutation2
    _ = mixedMoment B node5487 node5487Labels := by rfl

def raw3255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1]]
def raw3255Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1]]
def raw3255step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3255step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1]]
def raw3255step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3255step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw3255step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3255 raw3255Labels = mixedMoment B node5491 node5491Labels := by
  calc
    mixedMoment B raw3255 raw3255Labels = mixedMoment B raw3255step0 raw3255step0Labels := by
      have hz : ∀ j, raw3255 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3255step0 = (fun i j => raw3255 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3255step0 raw3255; decide +kernel
      have hl : raw3255step0Labels = raw3255Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3255 raw3255Labels permutation346 hz
    mixedMoment B raw3255step0 raw3255step0Labels = mixedMoment B raw3255step1 raw3255step1Labels := by
      have hz : ∀ j, raw3255step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3255step1 = (fun i j => raw3255step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3255step1 raw3255step0; decide +kernel
      have hl : raw3255step1Labels = raw3255step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3255step0 raw3255step0Labels permutation56 hz
    mixedMoment B raw3255step1 raw3255step1Labels = mixedMoment B raw3255step2 raw3255step2Labels := by
      have ha : raw3255step2 = (fun i j => raw3255step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3255step2 raw3255step1; decide +kernel
      have hl : raw3255step2Labels = raw3255step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3255step1 raw3255step1Labels permutation9 permutation2
    _ = mixedMoment B node5491 node5491Labels := by rfl

def raw3256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3256Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3256step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3256step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3256step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3256step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3256step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3256step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3256step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3256 raw3256Labels = mixedMoment B node5293 node5293Labels := by
  calc
    mixedMoment B raw3256 raw3256Labels = mixedMoment B raw3256step0 raw3256step0Labels := by
      have hz : ∀ j, raw3256 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3256step0 = (fun i j => raw3256 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3256step0 raw3256; decide +kernel
      have hl : raw3256step0Labels = raw3256Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3256 raw3256Labels permutation346 hz
    mixedMoment B raw3256step0 raw3256step0Labels = mixedMoment B raw3256step1 raw3256step1Labels := by
      have hz : ∀ j, raw3256step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3256step1 = (fun i j => raw3256step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3256step1 raw3256step0; decide +kernel
      have hl : raw3256step1Labels = raw3256step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3256step0 raw3256step0Labels permutation56 hz
    mixedMoment B raw3256step1 raw3256step1Labels = mixedMoment B raw3256step2 raw3256step2Labels := by
      have ha : raw3256step2 = (fun i j => raw3256step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3256step2 raw3256step1; decide +kernel
      have hl : raw3256step2Labels = raw3256step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3256step1 raw3256step1Labels permutation8 permutation3
    mixedMoment B raw3256step2 raw3256step2Labels = mixedMoment B raw3256step3 raw3256step3Labels := by
      have ha : raw3256step3 = raw3256step2 := by apply Matrix.ext; unfold raw3256step3 raw3256step2; decide +kernel
      have hl : raw3256step2Labels = labelEmbedding6 ∘ raw3256step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3256step2 raw3256step2Labels raw3256step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5293 node5293Labels := by rfl

def raw3257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3257Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3257step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3257step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3257step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3257step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3257step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3257step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3257 raw3257Labels = mixedMoment B node5483 node5483Labels := by
  calc
    mixedMoment B raw3257 raw3257Labels = mixedMoment B raw3257step0 raw3257step0Labels := by
      have hz : ∀ j, raw3257 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3257step0 = (fun i j => raw3257 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3257step0 raw3257; decide +kernel
      have hl : raw3257step0Labels = raw3257Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3257 raw3257Labels permutation346 hz
    mixedMoment B raw3257step0 raw3257step0Labels = mixedMoment B raw3257step1 raw3257step1Labels := by
      have ha : raw3257step1 = (fun i j => raw3257step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3257step1 raw3257step0; decide +kernel
      have hl : raw3257step1Labels = raw3257step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3257step0 raw3257step0Labels permutation151 permutation2
    mixedMoment B raw3257step1 raw3257step1Labels = mixedMoment B raw3257step2 raw3257step2Labels := by
      have ha : raw3257step2 = -raw3257step1 := by apply Matrix.ext; change ∀ i j, raw3257step2 i j = -(raw3257step1 i j); unfold raw3257step2 raw3257step1; decide +kernel
      have hl : raw3257step2Labels = raw3257step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5483 node5483Labels := by rfl

def raw3258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3258Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3258step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3258step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3258step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3258step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3258step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3258step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3258 raw3258Labels = mixedMoment B node5483 node5483Labels := by
  calc
    mixedMoment B raw3258 raw3258Labels = mixedMoment B raw3258step0 raw3258step0Labels := by
      have hz : ∀ j, raw3258 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3258step0 = (fun i j => raw3258 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3258step0 raw3258; decide +kernel
      have hl : raw3258step0Labels = raw3258Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3258 raw3258Labels permutation265 hz
    mixedMoment B raw3258step0 raw3258step0Labels = mixedMoment B raw3258step1 raw3258step1Labels := by
      have ha : raw3258step1 = (fun i j => raw3258step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3258step1 raw3258step0; decide +kernel
      have hl : raw3258step1Labels = raw3258step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3258step0 raw3258step0Labels permutation151 permutation2
    mixedMoment B raw3258step1 raw3258step1Labels = mixedMoment B raw3258step2 raw3258step2Labels := by
      have ha : raw3258step2 = -raw3258step1 := by apply Matrix.ext; change ∀ i j, raw3258step2 i j = -(raw3258step1 i j); unfold raw3258step2 raw3258step1; decide +kernel
      have hl : raw3258step2Labels = raw3258step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5483 node5483Labels := by rfl

def raw3259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3259Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3259step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3259step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3259step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw3259step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3259 raw3259Labels = mixedMoment B node5487 node5487Labels := by
  calc
    mixedMoment B raw3259 raw3259Labels = mixedMoment B raw3259step0 raw3259step0Labels := by
      have hz : ∀ j, raw3259 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3259step0 = (fun i j => raw3259 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3259step0 raw3259; decide +kernel
      have hl : raw3259step0Labels = raw3259Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3259 raw3259Labels permutation346 hz
    mixedMoment B raw3259step0 raw3259step0Labels = mixedMoment B raw3259step1 raw3259step1Labels := by
      have hz : ∀ j, raw3259step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3259step1 = (fun i j => raw3259step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3259step1 raw3259step0; decide +kernel
      have hl : raw3259step1Labels = raw3259step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3259step0 raw3259step0Labels permutation56 hz
    _ = mixedMoment B node5487 node5487Labels := by rfl

def raw3260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw3260Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw3260step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3260step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw3260step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3260 raw3260Labels = mixedMoment B node5491 node5491Labels := by
  calc
    mixedMoment B raw3260 raw3260Labels = mixedMoment B raw3260step0 raw3260step0Labels := by
      have hz : ∀ j, raw3260 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3260step0 = (fun i j => raw3260 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3260step0 raw3260; decide +kernel
      have hl : raw3260step0Labels = raw3260Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3260 raw3260Labels permutation346 hz
    mixedMoment B raw3260step0 raw3260step0Labels = mixedMoment B raw3260step1 raw3260step1Labels := by
      have hz : ∀ j, raw3260step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3260step1 = (fun i j => raw3260step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3260step1 raw3260step0; decide +kernel
      have hl : raw3260step1Labels = raw3260step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3260step0 raw3260step0Labels permutation56 hz
    _ = mixedMoment B node5491 node5491Labels := by rfl

def raw3261 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3261Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3261step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3261step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0]]
def raw3261step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3261step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3261step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3261 raw3261Labels = mixedMoment B node5452 node5452Labels := by
  calc
    mixedMoment B raw3261 raw3261Labels = mixedMoment B raw3261step0 raw3261step0Labels := by
      have hz : ∀ j, raw3261 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3261step0 = (fun i j => raw3261 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3261step0 raw3261; decide +kernel
      have hl : raw3261step0Labels = raw3261Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3261 raw3261Labels permutation346 hz
    mixedMoment B raw3261step0 raw3261step0Labels = mixedMoment B raw3261step1 raw3261step1Labels := by
      have ha : raw3261step1 = (fun i j => raw3261step0 (permutation48 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3261step1 raw3261step0; decide +kernel
      have hl : raw3261step1Labels = raw3261step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3261step0 raw3261step0Labels permutation48 permutation2
    mixedMoment B raw3261step1 raw3261step1Labels = mixedMoment B raw3261step2 raw3261step2Labels := by
      have ha : raw3261step2 = -raw3261step1 := by apply Matrix.ext; change ∀ i j, raw3261step2 i j = -(raw3261step1 i j); unfold raw3261step2 raw3261step1; decide +kernel
      have hl : raw3261step2Labels = raw3261step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5452 node5452Labels := by rfl

def raw3262 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3262Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3262step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3262step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3262step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0]]
def raw3262step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3262step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3262step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3262 raw3262Labels = mixedMoment B node5452 node5452Labels := by
  calc
    mixedMoment B raw3262 raw3262Labels = mixedMoment B raw3262step0 raw3262step0Labels := by
      have hz : ∀ j, raw3262 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3262step0 = (fun i j => raw3262 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3262step0 raw3262; decide +kernel
      have hl : raw3262step0Labels = raw3262Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3262 raw3262Labels permutation265 hz
    mixedMoment B raw3262step0 raw3262step0Labels = mixedMoment B raw3262step1 raw3262step1Labels := by
      have ha : raw3262step1 = (fun i j => raw3262step0 (permutation48 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3262step1 raw3262step0; decide +kernel
      have hl : raw3262step1Labels = raw3262step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3262step0 raw3262step0Labels permutation48 permutation2
    mixedMoment B raw3262step1 raw3262step1Labels = mixedMoment B raw3262step2 raw3262step2Labels := by
      have ha : raw3262step2 = -raw3262step1 := by apply Matrix.ext; change ∀ i j, raw3262step2 i j = -(raw3262step1 i j); unfold raw3262step2 raw3262step1; decide +kernel
      have hl : raw3262step2Labels = raw3262step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5452 node5452Labels := by rfl

def raw3263 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3263Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3263step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3263step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3263step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3263step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw3263step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3263step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw3263step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3263 raw3263Labels = mixedMoment B node5453 node5453Labels := by
  calc
    mixedMoment B raw3263 raw3263Labels = mixedMoment B raw3263step0 raw3263step0Labels := by
      have hz : ∀ j, raw3263 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3263step0 = (fun i j => raw3263 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3263step0 raw3263; decide +kernel
      have hl : raw3263step0Labels = raw3263Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3263 raw3263Labels permutation346 hz
    mixedMoment B raw3263step0 raw3263step0Labels = mixedMoment B raw3263step1 raw3263step1Labels := by
      have hz : ∀ j, raw3263step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3263step1 = (fun i j => raw3263step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3263step1 raw3263step0; decide +kernel
      have hl : raw3263step1Labels = raw3263step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3263step0 raw3263step0Labels permutation56 hz
    mixedMoment B raw3263step1 raw3263step1Labels = mixedMoment B raw3263step2 raw3263step2Labels := by
      have ha : raw3263step2 = (fun i j => raw3263step1 (permutation11 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3263step2 raw3263step1; decide +kernel
      have hl : raw3263step2Labels = raw3263step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3263step1 raw3263step1Labels permutation11 permutation2
    mixedMoment B raw3263step2 raw3263step2Labels = mixedMoment B raw3263step3 raw3263step3Labels := by
      have ha : raw3263step3 = -raw3263step2 := by apply Matrix.ext; change ∀ i j, raw3263step3 i j = -(raw3263step2 i j); unfold raw3263step3 raw3263step2; decide +kernel
      have hl : raw3263step3Labels = raw3263step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5453 node5453Labels := by rfl

def raw3264 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3264Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3264step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3264step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3264step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3264step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3264step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3264step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3264step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3264step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3264 raw3264Labels = mixedMoment B node5454 node5454Labels := by
  calc
    mixedMoment B raw3264 raw3264Labels = mixedMoment B raw3264step0 raw3264step0Labels := by
      have hz : ∀ j, raw3264 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3264step0 = (fun i j => raw3264 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3264step0 raw3264; decide +kernel
      have hl : raw3264step0Labels = raw3264Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3264 raw3264Labels permutation346 hz
    mixedMoment B raw3264step0 raw3264step0Labels = mixedMoment B raw3264step1 raw3264step1Labels := by
      have hz : ∀ j, raw3264step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3264step1 = (fun i j => raw3264step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3264step1 raw3264step0; decide +kernel
      have hl : raw3264step1Labels = raw3264step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3264step0 raw3264step0Labels permutation56 hz
    mixedMoment B raw3264step1 raw3264step1Labels = mixedMoment B raw3264step2 raw3264step2Labels := by
      have ha : raw3264step2 = (fun i j => raw3264step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3264step2 raw3264step1; decide +kernel
      have hl : raw3264step2Labels = raw3264step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3264step1 raw3264step1Labels permutation12 permutation2
    mixedMoment B raw3264step2 raw3264step2Labels = mixedMoment B raw3264step3 raw3264step3Labels := by
      have ha : raw3264step3 = -raw3264step2 := by apply Matrix.ext; change ∀ i j, raw3264step3 i j = -(raw3264step2 i j); unfold raw3264step3 raw3264step2; decide +kernel
      have hl : raw3264step3Labels = raw3264step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5454 node5454Labels := by rfl

def raw3265 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1]]
def raw3265Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3265step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1]]
def raw3265step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3265step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1]]
def raw3265step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3265step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3265step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3265step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3265step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3265 raw3265Labels = mixedMoment B node5454 node5454Labels := by
  calc
    mixedMoment B raw3265 raw3265Labels = mixedMoment B raw3265step0 raw3265step0Labels := by
      have hz : ∀ j, raw3265 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3265step0 = (fun i j => raw3265 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3265step0 raw3265; decide +kernel
      have hl : raw3265step0Labels = raw3265Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3265 raw3265Labels permutation346 hz
    mixedMoment B raw3265step0 raw3265step0Labels = mixedMoment B raw3265step1 raw3265step1Labels := by
      have hz : ∀ j, raw3265step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3265step1 = (fun i j => raw3265step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3265step1 raw3265step0; decide +kernel
      have hl : raw3265step1Labels = raw3265step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3265step0 raw3265step0Labels permutation56 hz
    mixedMoment B raw3265step1 raw3265step1Labels = mixedMoment B raw3265step2 raw3265step2Labels := by
      have ha : raw3265step2 = (fun i j => raw3265step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3265step2 raw3265step1; decide +kernel
      have hl : raw3265step2Labels = raw3265step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3265step1 raw3265step1Labels permutation10 permutation2
    mixedMoment B raw3265step2 raw3265step2Labels = mixedMoment B raw3265step3 raw3265step3Labels := by
      have ha : raw3265step3 = -raw3265step2 := by apply Matrix.ext; change ∀ i j, raw3265step3 i j = -(raw3265step2 i j); unfold raw3265step3 raw3265step2; decide +kernel
      have hl : raw3265step3Labels = raw3265step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5454 node5454Labels := by rfl

def raw3266 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3266Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3266step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3266step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3266step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw3266step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3266step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3266step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3266step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3266step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3266 raw3266Labels = mixedMoment B node5440 node5440Labels := by
  calc
    mixedMoment B raw3266 raw3266Labels = mixedMoment B raw3266step0 raw3266step0Labels := by
      have hz : ∀ j, raw3266 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3266step0 = (fun i j => raw3266 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3266step0 raw3266; decide +kernel
      have hl : raw3266step0Labels = raw3266Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3266 raw3266Labels permutation346 hz
    mixedMoment B raw3266step0 raw3266step0Labels = mixedMoment B raw3266step1 raw3266step1Labels := by
      have ha : raw3266step1 = (fun i j => raw3266step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3266step1 raw3266step0; decide +kernel
      have hl : raw3266step1Labels = raw3266step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3266step0 raw3266step0Labels permutation38 permutation4
    mixedMoment B raw3266step1 raw3266step1Labels = mixedMoment B raw3266step2 raw3266step2Labels := by
      have ha : raw3266step2 = -raw3266step1 := by apply Matrix.ext; change ∀ i j, raw3266step2 i j = -(raw3266step1 i j); unfold raw3266step2 raw3266step1; decide +kernel
      have hl : raw3266step2Labels = raw3266step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3266step2 raw3266step2Labels = mixedMoment B raw3266step3 raw3266step3Labels := by
      have ha : raw3266step3 = raw3266step2 := by apply Matrix.ext; unfold raw3266step3 raw3266step2; decide +kernel
      have hl : raw3266step2Labels = labelEmbedding7 ∘ raw3266step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3266step2 raw3266step2Labels raw3266step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5440 node5440Labels := by rfl

def raw3267 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3267Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3267step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3267step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3267step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3267step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3267 raw3267Labels = mixedMoment B node5489 node5489Labels := by
  calc
    mixedMoment B raw3267 raw3267Labels = mixedMoment B raw3267step0 raw3267step0Labels := by
      have ha : raw3267step0 = (fun i j => raw3267 (permutation182 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3267step0 raw3267; decide +kernel
      have hl : raw3267step0Labels = raw3267Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3267 raw3267Labels permutation182 permutation6
    mixedMoment B raw3267step0 raw3267step0Labels = mixedMoment B raw3267step1 raw3267step1Labels := by
      have ha : raw3267step1 = raw3267step0 := by apply Matrix.ext; unfold raw3267step1 raw3267step0; decide +kernel
      have hl : raw3267step0Labels = labelEmbedding9 ∘ raw3267step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3267step0 raw3267step0Labels raw3267step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5489 node5489Labels := by rfl

def raw3268 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3268Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3268step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3268step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3268step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3268step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3268step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3268step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3268step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3268 raw3268Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw3268 raw3268Labels = mixedMoment B raw3268step0 raw3268step0Labels := by
      have hz : ∀ j, raw3268 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3268step0 = (fun i j => raw3268 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3268step0 raw3268; decide +kernel
      have hl : raw3268step0Labels = raw3268Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3268 raw3268Labels permutation346 hz
    mixedMoment B raw3268step0 raw3268step0Labels = mixedMoment B raw3268step1 raw3268step1Labels := by
      have ha : raw3268step1 = (fun i j => raw3268step0 (permutation83 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3268step1 raw3268step0; decide +kernel
      have hl : raw3268step1Labels = raw3268step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3268step0 raw3268step0Labels permutation83 permutation5
    mixedMoment B raw3268step1 raw3268step1Labels = mixedMoment B raw3268step2 raw3268step2Labels := by
      have ha : raw3268step2 = -raw3268step1 := by apply Matrix.ext; change ∀ i j, raw3268step2 i j = -(raw3268step1 i j); unfold raw3268step2 raw3268step1; decide +kernel
      have hl : raw3268step2Labels = raw3268step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3268step2 raw3268step2Labels = mixedMoment B raw3268step3 raw3268step3Labels := by
      have ha : raw3268step3 = raw3268step2 := by apply Matrix.ext; unfold raw3268step3 raw3268step2; decide +kernel
      have hl : raw3268step2Labels = labelEmbedding8 ∘ raw3268step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3268step2 raw3268step2Labels raw3268step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw3269 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3269Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3269step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3269step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3269step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3269step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3269step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3269step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3269 raw3269Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw3269 raw3269Labels = mixedMoment B raw3269step0 raw3269step0Labels := by
      have hz : ∀ j, raw3269 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3269step0 = (fun i j => raw3269 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3269step0 raw3269; decide +kernel
      have hl : raw3269step0Labels = raw3269Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3269 raw3269Labels permutation346 hz
    mixedMoment B raw3269step0 raw3269step0Labels = mixedMoment B raw3269step1 raw3269step1Labels := by
      have ha : raw3269step1 = (fun i j => raw3269step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3269step1 raw3269step0; decide +kernel
      have hl : raw3269step1Labels = raw3269step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3269step0 raw3269step0Labels permutation38 permutation6
    mixedMoment B raw3269step1 raw3269step1Labels = mixedMoment B raw3269step2 raw3269step2Labels := by
      have ha : raw3269step2 = raw3269step1 := by apply Matrix.ext; unfold raw3269step2 raw3269step1; decide +kernel
      have hl : raw3269step1Labels = labelEmbedding9 ∘ raw3269step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3269step1 raw3269step1Labels raw3269step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw3270 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1]]
def raw3270Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3270step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1]]
def raw3270step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3270step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3270step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3270step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3270step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3270 raw3270Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw3270 raw3270Labels = mixedMoment B raw3270step0 raw3270step0Labels := by
      have hz : ∀ j, raw3270 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3270step0 = (fun i j => raw3270 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3270step0 raw3270; decide +kernel
      have hl : raw3270step0Labels = raw3270Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3270 raw3270Labels permutation346 hz
    mixedMoment B raw3270step0 raw3270step0Labels = mixedMoment B raw3270step1 raw3270step1Labels := by
      have ha : raw3270step1 = (fun i j => raw3270step0 (permutation39 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3270step1 raw3270step0; decide +kernel
      have hl : raw3270step1Labels = raw3270step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3270step0 raw3270step0Labels permutation39 permutation6
    mixedMoment B raw3270step1 raw3270step1Labels = mixedMoment B raw3270step2 raw3270step2Labels := by
      have ha : raw3270step2 = raw3270step1 := by apply Matrix.ext; unfold raw3270step2 raw3270step1; decide +kernel
      have hl : raw3270step1Labels = labelEmbedding9 ∘ raw3270step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3270step1 raw3270step1Labels raw3270step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw3271 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3271Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3271step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3271step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3271step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw3271step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3271step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3271step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3271step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3271step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3271 raw3271Labels = mixedMoment B node5440 node5440Labels := by
  calc
    mixedMoment B raw3271 raw3271Labels = mixedMoment B raw3271step0 raw3271step0Labels := by
      have hz : ∀ j, raw3271 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3271step0 = (fun i j => raw3271 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3271step0 raw3271; decide +kernel
      have hl : raw3271step0Labels = raw3271Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3271 raw3271Labels permutation265 hz
    mixedMoment B raw3271step0 raw3271step0Labels = mixedMoment B raw3271step1 raw3271step1Labels := by
      have ha : raw3271step1 = (fun i j => raw3271step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3271step1 raw3271step0; decide +kernel
      have hl : raw3271step1Labels = raw3271step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3271step0 raw3271step0Labels permutation38 permutation4
    mixedMoment B raw3271step1 raw3271step1Labels = mixedMoment B raw3271step2 raw3271step2Labels := by
      have ha : raw3271step2 = -raw3271step1 := by apply Matrix.ext; change ∀ i j, raw3271step2 i j = -(raw3271step1 i j); unfold raw3271step2 raw3271step1; decide +kernel
      have hl : raw3271step2Labels = raw3271step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3271step2 raw3271step2Labels = mixedMoment B raw3271step3 raw3271step3Labels := by
      have ha : raw3271step3 = raw3271step2 := by apply Matrix.ext; unfold raw3271step3 raw3271step2; decide +kernel
      have hl : raw3271step2Labels = labelEmbedding7 ∘ raw3271step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3271step2 raw3271step2Labels raw3271step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5440 node5440Labels := by rfl

def raw3272 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3272Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3272step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3272step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3272step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw3272step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3272 raw3272Labels = mixedMoment B node5489 node5489Labels := by
  calc
    mixedMoment B raw3272 raw3272Labels = mixedMoment B raw3272step0 raw3272step0Labels := by
      have ha : raw3272step0 = (fun i j => raw3272 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3272step0 raw3272; decide +kernel
      have hl : raw3272step0Labels = raw3272Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3272 raw3272Labels permutation158 permutation6
    mixedMoment B raw3272step0 raw3272step0Labels = mixedMoment B raw3272step1 raw3272step1Labels := by
      have ha : raw3272step1 = raw3272step0 := by apply Matrix.ext; unfold raw3272step1 raw3272step0; decide +kernel
      have hl : raw3272step0Labels = labelEmbedding9 ∘ raw3272step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3272step0 raw3272step0Labels raw3272step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5489 node5489Labels := by rfl

def raw3273 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3273Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3273step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3273step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw3273step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3273step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3273step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3273step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3273step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3273 raw3273Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw3273 raw3273Labels = mixedMoment B raw3273step0 raw3273step0Labels := by
      have hz : ∀ j, raw3273 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3273step0 = (fun i j => raw3273 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3273step0 raw3273; decide +kernel
      have hl : raw3273step0Labels = raw3273Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3273 raw3273Labels permutation265 hz
    mixedMoment B raw3273step0 raw3273step0Labels = mixedMoment B raw3273step1 raw3273step1Labels := by
      have ha : raw3273step1 = (fun i j => raw3273step0 (permutation83 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3273step1 raw3273step0; decide +kernel
      have hl : raw3273step1Labels = raw3273step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3273step0 raw3273step0Labels permutation83 permutation5
    mixedMoment B raw3273step1 raw3273step1Labels = mixedMoment B raw3273step2 raw3273step2Labels := by
      have ha : raw3273step2 = -raw3273step1 := by apply Matrix.ext; change ∀ i j, raw3273step2 i j = -(raw3273step1 i j); unfold raw3273step2 raw3273step1; decide +kernel
      have hl : raw3273step2Labels = raw3273step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3273step2 raw3273step2Labels = mixedMoment B raw3273step3 raw3273step3Labels := by
      have ha : raw3273step3 = raw3273step2 := by apply Matrix.ext; unfold raw3273step3 raw3273step2; decide +kernel
      have hl : raw3273step2Labels = labelEmbedding8 ∘ raw3273step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3273step2 raw3273step2Labels raw3273step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw3274 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3274Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3274step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1]]
def raw3274step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3274step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3274step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3274step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3274step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3274 raw3274Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw3274 raw3274Labels = mixedMoment B raw3274step0 raw3274step0Labels := by
      have hz : ∀ j, raw3274 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3274step0 = (fun i j => raw3274 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3274step0 raw3274; decide +kernel
      have hl : raw3274step0Labels = raw3274Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3274 raw3274Labels permutation265 hz
    mixedMoment B raw3274step0 raw3274step0Labels = mixedMoment B raw3274step1 raw3274step1Labels := by
      have ha : raw3274step1 = (fun i j => raw3274step0 (permutation38 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3274step1 raw3274step0; decide +kernel
      have hl : raw3274step1Labels = raw3274step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3274step0 raw3274step0Labels permutation38 permutation6
    mixedMoment B raw3274step1 raw3274step1Labels = mixedMoment B raw3274step2 raw3274step2Labels := by
      have ha : raw3274step2 = raw3274step1 := by apply Matrix.ext; unfold raw3274step2 raw3274step1; decide +kernel
      have hl : raw3274step1Labels = labelEmbedding9 ∘ raw3274step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3274step1 raw3274step1Labels raw3274step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw3275 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1]]
def raw3275Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3275step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1]]
def raw3275step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3275step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3275step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3275step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3275step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3275 raw3275Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw3275 raw3275Labels = mixedMoment B raw3275step0 raw3275step0Labels := by
      have hz : ∀ j, raw3275 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3275step0 = (fun i j => raw3275 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3275step0 raw3275; decide +kernel
      have hl : raw3275step0Labels = raw3275Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3275 raw3275Labels permutation265 hz
    mixedMoment B raw3275step0 raw3275step0Labels = mixedMoment B raw3275step1 raw3275step1Labels := by
      have ha : raw3275step1 = (fun i j => raw3275step0 (permutation39 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3275step1 raw3275step0; decide +kernel
      have hl : raw3275step1Labels = raw3275step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3275step0 raw3275step0Labels permutation39 permutation6
    mixedMoment B raw3275step1 raw3275step1Labels = mixedMoment B raw3275step2 raw3275step2Labels := by
      have ha : raw3275step2 = raw3275step1 := by apply Matrix.ext; unfold raw3275step2 raw3275step1; decide +kernel
      have hl : raw3275step1Labels = labelEmbedding9 ∘ raw3275step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3275step1 raw3275step1Labels raw3275step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw3276 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3276Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3276step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3276step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3276step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3276step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3276step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![0, 2, -2], ![0, -1, 1], ![0, -1, 1]]
def raw3276step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3276step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![2, -2], ![-1, 1], ![-1, 1]]
def raw3276step3Labels : Fin 2 → Fin 3 := ![1, 2]

def raw3276step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw3276step4Labels : Fin 2 → Fin 3 := ![1, 2]

def raw3276step5 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw3276step5Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical3276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3276 raw3276Labels = mixedMoment B node4093 node4093Labels := by
  calc
    mixedMoment B raw3276 raw3276Labels = mixedMoment B raw3276step0 raw3276step0Labels := by
      have hz : ∀ j, raw3276 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3276step0 = (fun i j => raw3276 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3276step0 raw3276; decide +kernel
      have hl : raw3276step0Labels = raw3276Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3276 raw3276Labels permutation434 hz
    mixedMoment B raw3276step0 raw3276step0Labels = mixedMoment B raw3276step1 raw3276step1Labels := by
      have hz : ∀ j, raw3276step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3276step1 = (fun i j => raw3276step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3276step1 raw3276step0; decide +kernel
      have hl : raw3276step1Labels = raw3276step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3276step0 raw3276step0Labels permutation80 hz
    mixedMoment B raw3276step1 raw3276step1Labels = mixedMoment B raw3276step2 raw3276step2Labels := by
      have hz : ∀ j, raw3276step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3276step2 = (fun i j => raw3276step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3276step2 raw3276step1; decide +kernel
      have hl : raw3276step2Labels = raw3276step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3276step1 raw3276step1Labels permutation14 hz
    mixedMoment B raw3276step2 raw3276step2Labels = mixedMoment B raw3276step3 raw3276step3Labels := by
      have hz : ∀ i, raw3276step2 i (permutation2 0) = 0 := by decide +kernel
      have ha : raw3276step3 = (fun i j => raw3276step2 i (permutation2 j.succ)) := by apply Matrix.ext; unfold raw3276step3 raw3276step2; decide +kernel
      have hl : raw3276step3Labels = (fun j => raw3276step2Labels (permutation2 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3276step2 raw3276step2Labels permutation2 hz
    mixedMoment B raw3276step3 raw3276step3Labels = mixedMoment B raw3276step4 raw3276step4Labels := by
      have ha : raw3276step4 = -raw3276step3 := by apply Matrix.ext; change ∀ i j, raw3276step4 i j = -(raw3276step3 i j); unfold raw3276step4 raw3276step3; decide +kernel
      have hl : raw3276step4Labels = raw3276step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3276step4 raw3276step4Labels = mixedMoment B raw3276step5 raw3276step5Labels := by
      have ha : raw3276step5 = raw3276step4 := by apply Matrix.ext; unfold raw3276step5 raw3276step4; decide +kernel
      have hl : raw3276step4Labels = labelEmbedding3 ∘ raw3276step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3276step4 raw3276step4Labels raw3276step5Labels labelEmbedding3 hl
    _ = mixedMoment B node4093 node4093Labels := by rfl

def raw3277 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3277Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3277step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3277step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1]]
def raw3277step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3277step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3277step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3277step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3277step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3277 raw3277Labels = mixedMoment B node5493 node5493Labels := by
  calc
    mixedMoment B raw3277 raw3277Labels = mixedMoment B raw3277step0 raw3277step0Labels := by
      have hz : ∀ j, raw3277 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3277step0 = (fun i j => raw3277 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3277step0 raw3277; decide +kernel
      have hl : raw3277step0Labels = raw3277Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3277 raw3277Labels permutation434 hz
    mixedMoment B raw3277step0 raw3277step0Labels = mixedMoment B raw3277step1 raw3277step1Labels := by
      have hz : ∀ j, raw3277step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3277step1 = (fun i j => raw3277step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3277step1 raw3277step0; decide +kernel
      have hl : raw3277step1Labels = raw3277step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3277step0 raw3277step0Labels permutation56 hz
    mixedMoment B raw3277step1 raw3277step1Labels = mixedMoment B raw3277step2 raw3277step2Labels := by
      have ha : raw3277step2 = (fun i j => raw3277step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3277step2 raw3277step1; decide +kernel
      have hl : raw3277step2Labels = raw3277step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3277step1 raw3277step1Labels permutation8 permutation6
    mixedMoment B raw3277step2 raw3277step2Labels = mixedMoment B raw3277step3 raw3277step3Labels := by
      have ha : raw3277step3 = raw3277step2 := by apply Matrix.ext; unfold raw3277step3 raw3277step2; decide +kernel
      have hl : raw3277step2Labels = labelEmbedding9 ∘ raw3277step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3277step2 raw3277step2Labels raw3277step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5493 node5493Labels := by rfl

def raw3278 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1]]
def raw3278Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3278step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1]]
def raw3278step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3278step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1]]
def raw3278step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3278step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![1, 1, -2], ![0, -1, 1], ![-1, 0, 1]]
def raw3278step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3278step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw3278step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3278step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw3278step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3278 raw3278Labels = mixedMoment B node5495 node5495Labels := by
  calc
    mixedMoment B raw3278 raw3278Labels = mixedMoment B raw3278step0 raw3278step0Labels := by
      have hz : ∀ j, raw3278 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3278step0 = (fun i j => raw3278 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3278step0 raw3278; decide +kernel
      have hl : raw3278step0Labels = raw3278Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3278 raw3278Labels permutation434 hz
    mixedMoment B raw3278step0 raw3278step0Labels = mixedMoment B raw3278step1 raw3278step1Labels := by
      have hz : ∀ j, raw3278step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3278step1 = (fun i j => raw3278step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3278step1 raw3278step0; decide +kernel
      have hl : raw3278step1Labels = raw3278step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3278step0 raw3278step0Labels permutation80 hz
    mixedMoment B raw3278step1 raw3278step1Labels = mixedMoment B raw3278step2 raw3278step2Labels := by
      have hz : ∀ j, raw3278step1 (permutation14 0) j = 0 := by decide +kernel
      have ha : raw3278step2 = (fun i j => raw3278step1 (permutation14 i.succ) j) := by apply Matrix.ext; unfold raw3278step2 raw3278step1; decide +kernel
      have hl : raw3278step2Labels = raw3278step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3278step1 raw3278step1Labels permutation14 hz
    mixedMoment B raw3278step2 raw3278step2Labels = mixedMoment B raw3278step3 raw3278step3Labels := by
      have ha : raw3278step3 = (fun i j => raw3278step2 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3278step3 raw3278step2; decide +kernel
      have hl : raw3278step3Labels = raw3278step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3278step2 raw3278step2Labels permutation3 permutation6
    mixedMoment B raw3278step3 raw3278step3Labels = mixedMoment B raw3278step4 raw3278step4Labels := by
      have ha : raw3278step4 = raw3278step3 := by apply Matrix.ext; unfold raw3278step4 raw3278step3; decide +kernel
      have hl : raw3278step3Labels = labelEmbedding9 ∘ raw3278step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3278step3 raw3278step3Labels raw3278step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5495 node5495Labels := by rfl

def raw3279 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1]]
def raw3279Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3279step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1]]
def raw3279step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3279step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1]]
def raw3279step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3279step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw3279step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3279step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw3279step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3279step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw3279step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3279 raw3279Labels = mixedMoment B node5442 node5442Labels := by
  calc
    mixedMoment B raw3279 raw3279Labels = mixedMoment B raw3279step0 raw3279step0Labels := by
      have hz : ∀ j, raw3279 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3279step0 = (fun i j => raw3279 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3279step0 raw3279; decide +kernel
      have hl : raw3279step0Labels = raw3279Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3279 raw3279Labels permutation346 hz
    mixedMoment B raw3279step0 raw3279step0Labels = mixedMoment B raw3279step1 raw3279step1Labels := by
      have hz : ∀ j, raw3279step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3279step1 = (fun i j => raw3279step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3279step1 raw3279step0; decide +kernel
      have hl : raw3279step1Labels = raw3279step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3279step0 raw3279step0Labels permutation56 hz
    mixedMoment B raw3279step1 raw3279step1Labels = mixedMoment B raw3279step2 raw3279step2Labels := by
      have ha : raw3279step2 = (fun i j => raw3279step1 (permutation9 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3279step2 raw3279step1; decide +kernel
      have hl : raw3279step2Labels = raw3279step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3279step1 raw3279step1Labels permutation9 permutation4
    mixedMoment B raw3279step2 raw3279step2Labels = mixedMoment B raw3279step3 raw3279step3Labels := by
      have ha : raw3279step3 = -raw3279step2 := by apply Matrix.ext; change ∀ i j, raw3279step3 i j = -(raw3279step2 i j); unfold raw3279step3 raw3279step2; decide +kernel
      have hl : raw3279step3Labels = raw3279step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3279step3 raw3279step3Labels = mixedMoment B raw3279step4 raw3279step4Labels := by
      have ha : raw3279step4 = raw3279step3 := by apply Matrix.ext; unfold raw3279step4 raw3279step3; decide +kernel
      have hl : raw3279step3Labels = labelEmbedding7 ∘ raw3279step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3279step3 raw3279step3Labels raw3279step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5442 node5442Labels := by rfl

def raw3280 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1]]
def raw3280Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1]]
def raw3280step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3280step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3280step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3280step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3280step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3280 raw3280Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw3280 raw3280Labels = mixedMoment B raw3280step0 raw3280step0Labels := by
      have hz : ∀ j, raw3280 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3280step0 = (fun i j => raw3280 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3280step0 raw3280; decide +kernel
      have hl : raw3280step0Labels = raw3280Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3280 raw3280Labels permutation346 hz
    mixedMoment B raw3280step0 raw3280step0Labels = mixedMoment B raw3280step1 raw3280step1Labels := by
      have ha : raw3280step1 = (fun i j => raw3280step0 (permutation125 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3280step1 raw3280step0; decide +kernel
      have hl : raw3280step1Labels = raw3280step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3280step0 raw3280step0Labels permutation125 permutation4
    mixedMoment B raw3280step1 raw3280step1Labels = mixedMoment B raw3280step2 raw3280step2Labels := by
      have ha : raw3280step2 = raw3280step1 := by apply Matrix.ext; unfold raw3280step2 raw3280step1; decide +kernel
      have hl : raw3280step1Labels = labelEmbedding7 ∘ raw3280step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3280step1 raw3280step1Labels raw3280step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5485 node5485Labels := by rfl

def raw3281 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1]]
def raw3281Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3281step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1]]
def raw3281step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3281step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3281step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3281step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3281step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3281 raw3281Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw3281 raw3281Labels = mixedMoment B raw3281step0 raw3281step0Labels := by
      have hz : ∀ j, raw3281 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3281step0 = (fun i j => raw3281 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3281step0 raw3281; decide +kernel
      have hl : raw3281step0Labels = raw3281Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3281 raw3281Labels permutation265 hz
    mixedMoment B raw3281step0 raw3281step0Labels = mixedMoment B raw3281step1 raw3281step1Labels := by
      have ha : raw3281step1 = (fun i j => raw3281step0 (permutation125 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3281step1 raw3281step0; decide +kernel
      have hl : raw3281step1Labels = raw3281step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3281step0 raw3281step0Labels permutation125 permutation4
    mixedMoment B raw3281step1 raw3281step1Labels = mixedMoment B raw3281step2 raw3281step2Labels := by
      have ha : raw3281step2 = raw3281step1 := by apply Matrix.ext; unfold raw3281step2 raw3281step1; decide +kernel
      have hl : raw3281step1Labels = labelEmbedding7 ∘ raw3281step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3281step1 raw3281step1Labels raw3281step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5485 node5485Labels := by rfl

def raw3282 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1]]
def raw3282Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1]]
def raw3282step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3282step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 2, 0], ![1, -2, 1], ![0, -1, 1]]
def raw3282step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3282step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3282step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3282step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3282step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3282step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3282step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3282 raw3282Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw3282 raw3282Labels = mixedMoment B raw3282step0 raw3282step0Labels := by
      have hz : ∀ j, raw3282 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3282step0 = (fun i j => raw3282 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3282step0 raw3282; decide +kernel
      have hl : raw3282step0Labels = raw3282Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3282 raw3282Labels permutation346 hz
    mixedMoment B raw3282step0 raw3282step0Labels = mixedMoment B raw3282step1 raw3282step1Labels := by
      have hz : ∀ j, raw3282step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3282step1 = (fun i j => raw3282step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3282step1 raw3282step0; decide +kernel
      have hl : raw3282step1Labels = raw3282step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3282step0 raw3282step0Labels permutation56 hz
    mixedMoment B raw3282step1 raw3282step1Labels = mixedMoment B raw3282step2 raw3282step2Labels := by
      have ha : raw3282step2 = (fun i j => raw3282step1 (permutation15 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3282step2 raw3282step1; decide +kernel
      have hl : raw3282step2Labels = raw3282step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3282step1 raw3282step1Labels permutation15 permutation5
    mixedMoment B raw3282step2 raw3282step2Labels = mixedMoment B raw3282step3 raw3282step3Labels := by
      have ha : raw3282step3 = -raw3282step2 := by apply Matrix.ext; change ∀ i j, raw3282step3 i j = -(raw3282step2 i j); unfold raw3282step3 raw3282step2; decide +kernel
      have hl : raw3282step3Labels = raw3282step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3282step3 raw3282step3Labels = mixedMoment B raw3282step4 raw3282step4Labels := by
      have ha : raw3282step4 = raw3282step3 := by apply Matrix.ext; unfold raw3282step4 raw3282step3; decide +kernel
      have hl : raw3282step3Labels = labelEmbedding8 ∘ raw3282step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3282step3 raw3282step3Labels raw3282step4Labels labelEmbedding8 hl
    _ = mixedMoment B node5451 node5451Labels := by rfl

def raw3283 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1]]
def raw3283Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1]]
def raw3283step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3283step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1]]
def raw3283step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3283step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3283step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3283step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3283step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3283 raw3283Labels = mixedMoment B node5492 node5492Labels := by
  calc
    mixedMoment B raw3283 raw3283Labels = mixedMoment B raw3283step0 raw3283step0Labels := by
      have hz : ∀ j, raw3283 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3283step0 = (fun i j => raw3283 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3283step0 raw3283; decide +kernel
      have hl : raw3283step0Labels = raw3283Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3283 raw3283Labels permutation346 hz
    mixedMoment B raw3283step0 raw3283step0Labels = mixedMoment B raw3283step1 raw3283step1Labels := by
      have hz : ∀ j, raw3283step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3283step1 = (fun i j => raw3283step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3283step1 raw3283step0; decide +kernel
      have hl : raw3283step1Labels = raw3283step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3283step0 raw3283step0Labels permutation56 hz
    mixedMoment B raw3283step1 raw3283step1Labels = mixedMoment B raw3283step2 raw3283step2Labels := by
      have ha : raw3283step2 = (fun i j => raw3283step1 (permutation25 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3283step2 raw3283step1; decide +kernel
      have hl : raw3283step2Labels = raw3283step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3283step1 raw3283step1Labels permutation25 permutation4
    mixedMoment B raw3283step2 raw3283step2Labels = mixedMoment B raw3283step3 raw3283step3Labels := by
      have ha : raw3283step3 = raw3283step2 := by apply Matrix.ext; unfold raw3283step3 raw3283step2; decide +kernel
      have hl : raw3283step2Labels = labelEmbedding7 ∘ raw3283step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3283step2 raw3283step2Labels raw3283step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5492 node5492Labels := by rfl

def raw3284 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1]]
def raw3284Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3284step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1]]
def raw3284step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3284step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 2, -2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1]]
def raw3284step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3284step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw3284step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3284step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw3284step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3284step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw3284step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3284 raw3284Labels = mixedMoment B node5442 node5442Labels := by
  calc
    mixedMoment B raw3284 raw3284Labels = mixedMoment B raw3284step0 raw3284step0Labels := by
      have hz : ∀ j, raw3284 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3284step0 = (fun i j => raw3284 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3284step0 raw3284; decide +kernel
      have hl : raw3284step0Labels = raw3284Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3284 raw3284Labels permutation346 hz
    mixedMoment B raw3284step0 raw3284step0Labels = mixedMoment B raw3284step1 raw3284step1Labels := by
      have hz : ∀ j, raw3284step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3284step1 = (fun i j => raw3284step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3284step1 raw3284step0; decide +kernel
      have hl : raw3284step1Labels = raw3284step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3284step0 raw3284step0Labels permutation56 hz
    mixedMoment B raw3284step1 raw3284step1Labels = mixedMoment B raw3284step2 raw3284step2Labels := by
      have ha : raw3284step2 = (fun i j => raw3284step1 (permutation8 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3284step2 raw3284step1; decide +kernel
      have hl : raw3284step2Labels = raw3284step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3284step1 raw3284step1Labels permutation8 permutation4
    mixedMoment B raw3284step2 raw3284step2Labels = mixedMoment B raw3284step3 raw3284step3Labels := by
      have ha : raw3284step3 = -raw3284step2 := by apply Matrix.ext; change ∀ i j, raw3284step3 i j = -(raw3284step2 i j); unfold raw3284step3 raw3284step2; decide +kernel
      have hl : raw3284step3Labels = raw3284step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3284step3 raw3284step3Labels = mixedMoment B raw3284step4 raw3284step4Labels := by
      have ha : raw3284step4 = raw3284step3 := by apply Matrix.ext; unfold raw3284step4 raw3284step3; decide +kernel
      have hl : raw3284step3Labels = labelEmbedding7 ∘ raw3284step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3284step3 raw3284step3Labels raw3284step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5442 node5442Labels := by rfl

def raw3285 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1]]
def raw3285Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3285step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1]]
def raw3285step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3285step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3285step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3285step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3285step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3285 raw3285Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw3285 raw3285Labels = mixedMoment B raw3285step0 raw3285step0Labels := by
      have hz : ∀ j, raw3285 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3285step0 = (fun i j => raw3285 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3285step0 raw3285; decide +kernel
      have hl : raw3285step0Labels = raw3285Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3285 raw3285Labels permutation346 hz
    mixedMoment B raw3285step0 raw3285step0Labels = mixedMoment B raw3285step1 raw3285step1Labels := by
      have ha : raw3285step1 = (fun i j => raw3285step0 (permutation149 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3285step1 raw3285step0; decide +kernel
      have hl : raw3285step1Labels = raw3285step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3285step0 raw3285step0Labels permutation149 permutation4
    mixedMoment B raw3285step1 raw3285step1Labels = mixedMoment B raw3285step2 raw3285step2Labels := by
      have ha : raw3285step2 = raw3285step1 := by apply Matrix.ext; unfold raw3285step2 raw3285step1; decide +kernel
      have hl : raw3285step1Labels = labelEmbedding7 ∘ raw3285step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3285step1 raw3285step1Labels raw3285step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5485 node5485Labels := by rfl

def raw3286 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1]]
def raw3286Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3286step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1]]
def raw3286step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3286step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3286step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3286step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw3286step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3286 raw3286Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw3286 raw3286Labels = mixedMoment B raw3286step0 raw3286step0Labels := by
      have hz : ∀ j, raw3286 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw3286step0 = (fun i j => raw3286 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw3286step0 raw3286; decide +kernel
      have hl : raw3286step0Labels = raw3286Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3286 raw3286Labels permutation265 hz
    mixedMoment B raw3286step0 raw3286step0Labels = mixedMoment B raw3286step1 raw3286step1Labels := by
      have ha : raw3286step1 = (fun i j => raw3286step0 (permutation149 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3286step1 raw3286step0; decide +kernel
      have hl : raw3286step1Labels = raw3286step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3286step0 raw3286step0Labels permutation149 permutation4
    mixedMoment B raw3286step1 raw3286step1Labels = mixedMoment B raw3286step2 raw3286step2Labels := by
      have ha : raw3286step2 = raw3286step1 := by apply Matrix.ext; unfold raw3286step2 raw3286step1; decide +kernel
      have hl : raw3286step1Labels = labelEmbedding7 ∘ raw3286step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3286step1 raw3286step1Labels raw3286step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5485 node5485Labels := by rfl

def raw3287 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1]]
def raw3287Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1]]
def raw3287step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3287step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-2, 2, 0], ![0, -1, 1], ![1, -2, 1]]
def raw3287step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3287step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw3287step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3287step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3287step3Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw3287step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3287step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3287 raw3287Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw3287 raw3287Labels = mixedMoment B raw3287step0 raw3287step0Labels := by
      have hz : ∀ j, raw3287 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3287step0 = (fun i j => raw3287 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3287step0 raw3287; decide +kernel
      have hl : raw3287step0Labels = raw3287Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3287 raw3287Labels permutation346 hz
    mixedMoment B raw3287step0 raw3287step0Labels = mixedMoment B raw3287step1 raw3287step1Labels := by
      have hz : ∀ j, raw3287step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3287step1 = (fun i j => raw3287step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3287step1 raw3287step0; decide +kernel
      have hl : raw3287step1Labels = raw3287step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3287step0 raw3287step0Labels permutation56 hz
    mixedMoment B raw3287step1 raw3287step1Labels = mixedMoment B raw3287step2 raw3287step2Labels := by
      have ha : raw3287step2 = (fun i j => raw3287step1 (permutation14 i) (permutation5 j)) := by apply Matrix.ext; unfold raw3287step2 raw3287step1; decide +kernel
      have hl : raw3287step2Labels = raw3287step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3287step1 raw3287step1Labels permutation14 permutation5
    mixedMoment B raw3287step2 raw3287step2Labels = mixedMoment B raw3287step3 raw3287step3Labels := by
      have ha : raw3287step3 = -raw3287step2 := by apply Matrix.ext; change ∀ i j, raw3287step3 i j = -(raw3287step2 i j); unfold raw3287step3 raw3287step2; decide +kernel
      have hl : raw3287step3Labels = raw3287step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3287step3 raw3287step3Labels = mixedMoment B raw3287step4 raw3287step4Labels := by
      have ha : raw3287step4 = raw3287step3 := by apply Matrix.ext; unfold raw3287step4 raw3287step3; decide +kernel
      have hl : raw3287step3Labels = labelEmbedding8 ∘ raw3287step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3287step3 raw3287step3Labels raw3287step4Labels labelEmbedding8 hl
    _ = mixedMoment B node5451 node5451Labels := by rfl

def raw3288 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1]]
def raw3288Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3288step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1]]
def raw3288step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3288step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1]]
def raw3288step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3288step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3288step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3288step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3288step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3288 raw3288Labels = mixedMoment B node5492 node5492Labels := by
  calc
    mixedMoment B raw3288 raw3288Labels = mixedMoment B raw3288step0 raw3288step0Labels := by
      have hz : ∀ j, raw3288 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3288step0 = (fun i j => raw3288 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3288step0 raw3288; decide +kernel
      have hl : raw3288step0Labels = raw3288Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3288 raw3288Labels permutation346 hz
    mixedMoment B raw3288step0 raw3288step0Labels = mixedMoment B raw3288step1 raw3288step1Labels := by
      have hz : ∀ j, raw3288step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3288step1 = (fun i j => raw3288step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3288step1 raw3288step0; decide +kernel
      have hl : raw3288step1Labels = raw3288step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3288step0 raw3288step0Labels permutation56 hz
    mixedMoment B raw3288step1 raw3288step1Labels = mixedMoment B raw3288step2 raw3288step2Labels := by
      have ha : raw3288step2 = (fun i j => raw3288step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3288step2 raw3288step1; decide +kernel
      have hl : raw3288step2Labels = raw3288step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3288step1 raw3288step1Labels permutation31 permutation4
    mixedMoment B raw3288step2 raw3288step2Labels = mixedMoment B raw3288step3 raw3288step3Labels := by
      have ha : raw3288step3 = raw3288step2 := by apply Matrix.ext; unfold raw3288step3 raw3288step2; decide +kernel
      have hl : raw3288step2Labels = labelEmbedding7 ∘ raw3288step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3288step2 raw3288step2Labels raw3288step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5492 node5492Labels := by rfl

def raw3289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw3289Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3289step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw3289step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3289step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0]]
def raw3289step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3289step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw3289step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3289step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3289step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw3289step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw3289step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3289 raw3289Labels = mixedMoment B node5492 node5492Labels := by
  calc
    mixedMoment B raw3289 raw3289Labels = mixedMoment B raw3289step0 raw3289step0Labels := by
      have hz : ∀ j, raw3289 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3289step0 = (fun i j => raw3289 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3289step0 raw3289; decide +kernel
      have hl : raw3289step0Labels = raw3289Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3289 raw3289Labels permutation434 hz
    mixedMoment B raw3289step0 raw3289step0Labels = mixedMoment B raw3289step1 raw3289step1Labels := by
      have hz : ∀ j, raw3289step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3289step1 = (fun i j => raw3289step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3289step1 raw3289step0; decide +kernel
      have hl : raw3289step1Labels = raw3289step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3289step0 raw3289step0Labels permutation80 hz
    mixedMoment B raw3289step1 raw3289step1Labels = mixedMoment B raw3289step2 raw3289step2Labels := by
      have ha : raw3289step2 = (fun i j => raw3289step1 (permutation17 i) (permutation4 j)) := by apply Matrix.ext; unfold raw3289step2 raw3289step1; decide +kernel
      have hl : raw3289step2Labels = raw3289step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3289step1 raw3289step1Labels permutation17 permutation4
    mixedMoment B raw3289step2 raw3289step2Labels = mixedMoment B raw3289step3 raw3289step3Labels := by
      have ha : raw3289step3 = -raw3289step2 := by apply Matrix.ext; change ∀ i j, raw3289step3 i j = -(raw3289step2 i j); unfold raw3289step3 raw3289step2; decide +kernel
      have hl : raw3289step3Labels = raw3289step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3289step3 raw3289step3Labels = mixedMoment B raw3289step4 raw3289step4Labels := by
      have ha : raw3289step4 = raw3289step3 := by apply Matrix.ext; unfold raw3289step4 raw3289step3; decide +kernel
      have hl : raw3289step3Labels = labelEmbedding7 ∘ raw3289step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3289step3 raw3289step3Labels raw3289step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5492 node5492Labels := by rfl

def raw3290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw3290Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3290step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw3290step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3290step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3290step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3290step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3290step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3290step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3290step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3290 raw3290Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw3290 raw3290Labels = mixedMoment B raw3290step0 raw3290step0Labels := by
      have hz : ∀ j, raw3290 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3290step0 = (fun i j => raw3290 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3290step0 raw3290; decide +kernel
      have hl : raw3290step0Labels = raw3290Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3290 raw3290Labels permutation434 hz
    mixedMoment B raw3290step0 raw3290step0Labels = mixedMoment B raw3290step1 raw3290step1Labels := by
      have ha : raw3290step1 = (fun i j => raw3290step0 (permutation53 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3290step1 raw3290step0; decide +kernel
      have hl : raw3290step1Labels = raw3290step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3290step0 raw3290step0Labels permutation53 permutation6
    mixedMoment B raw3290step1 raw3290step1Labels = mixedMoment B raw3290step2 raw3290step2Labels := by
      have ha : raw3290step2 = -raw3290step1 := by apply Matrix.ext; change ∀ i j, raw3290step2 i j = -(raw3290step1 i j); unfold raw3290step2 raw3290step1; decide +kernel
      have hl : raw3290step2Labels = raw3290step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3290step2 raw3290step2Labels = mixedMoment B raw3290step3 raw3290step3Labels := by
      have ha : raw3290step3 = raw3290step2 := by apply Matrix.ext; unfold raw3290step3 raw3290step2; decide +kernel
      have hl : raw3290step2Labels = labelEmbedding9 ∘ raw3290step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3290step2 raw3290step2Labels raw3290step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw3291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw3291Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3291step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw3291step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3291step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3291step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3291step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3291step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3291step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3291step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3291 raw3291Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw3291 raw3291Labels = mixedMoment B raw3291step0 raw3291step0Labels := by
      have hz : ∀ j, raw3291 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3291step0 = (fun i j => raw3291 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3291step0 raw3291; decide +kernel
      have hl : raw3291step0Labels = raw3291Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3291 raw3291Labels permutation346 hz
    mixedMoment B raw3291step0 raw3291step0Labels = mixedMoment B raw3291step1 raw3291step1Labels := by
      have ha : raw3291step1 = (fun i j => raw3291step0 (permutation53 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3291step1 raw3291step0; decide +kernel
      have hl : raw3291step1Labels = raw3291step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3291step0 raw3291step0Labels permutation53 permutation6
    mixedMoment B raw3291step1 raw3291step1Labels = mixedMoment B raw3291step2 raw3291step2Labels := by
      have ha : raw3291step2 = -raw3291step1 := by apply Matrix.ext; change ∀ i j, raw3291step2 i j = -(raw3291step1 i j); unfold raw3291step2 raw3291step1; decide +kernel
      have hl : raw3291step2Labels = raw3291step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3291step2 raw3291step2Labels = mixedMoment B raw3291step3 raw3291step3Labels := by
      have ha : raw3291step3 = raw3291step2 := by apply Matrix.ext; unfold raw3291step3 raw3291step2; decide +kernel
      have hl : raw3291step2Labels = labelEmbedding9 ∘ raw3291step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3291step2 raw3291step2Labels raw3291step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw3292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0]]
def raw3292Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3292step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0]]
def raw3292step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3292step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw3292step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3292step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw3292step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3292step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3292step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3292step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw3292step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3292 raw3292Labels = mixedMoment B node5493 node5493Labels := by
  calc
    mixedMoment B raw3292 raw3292Labels = mixedMoment B raw3292step0 raw3292step0Labels := by
      have hz : ∀ j, raw3292 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3292step0 = (fun i j => raw3292 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3292step0 raw3292; decide +kernel
      have hl : raw3292step0Labels = raw3292Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3292 raw3292Labels permutation434 hz
    mixedMoment B raw3292step0 raw3292step0Labels = mixedMoment B raw3292step1 raw3292step1Labels := by
      have hz : ∀ j, raw3292step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3292step1 = (fun i j => raw3292step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3292step1 raw3292step0; decide +kernel
      have hl : raw3292step1Labels = raw3292step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3292step0 raw3292step0Labels permutation80 hz
    mixedMoment B raw3292step1 raw3292step1Labels = mixedMoment B raw3292step2 raw3292step2Labels := by
      have ha : raw3292step2 = (fun i j => raw3292step1 (permutation12 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3292step2 raw3292step1; decide +kernel
      have hl : raw3292step2Labels = raw3292step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3292step1 raw3292step1Labels permutation12 permutation6
    mixedMoment B raw3292step2 raw3292step2Labels = mixedMoment B raw3292step3 raw3292step3Labels := by
      have ha : raw3292step3 = -raw3292step2 := by apply Matrix.ext; change ∀ i j, raw3292step3 i j = -(raw3292step2 i j); unfold raw3292step3 raw3292step2; decide +kernel
      have hl : raw3292step3Labels = raw3292step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3292step3 raw3292step3Labels = mixedMoment B raw3292step4 raw3292step4Labels := by
      have ha : raw3292step4 = raw3292step3 := by apply Matrix.ext; unfold raw3292step4 raw3292step3; decide +kernel
      have hl : raw3292step3Labels = labelEmbedding9 ∘ raw3292step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3292step3 raw3292step3Labels raw3292step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5493 node5493Labels := by rfl

def raw3293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0]]
def raw3293Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1]]
def raw3293step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3293step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1]]
def raw3293step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3293step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![0, 1, -1], ![1, 0, -1]]
def raw3293step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3293step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw3293step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3293step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw3293step4Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw3293step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw3293step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3293 raw3293Labels = mixedMoment B node5495 node5495Labels := by
  calc
    mixedMoment B raw3293 raw3293Labels = mixedMoment B raw3293step0 raw3293step0Labels := by
      have hz : ∀ j, raw3293 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw3293step0 = (fun i j => raw3293 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw3293step0 raw3293; decide +kernel
      have hl : raw3293step0Labels = raw3293Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3293 raw3293Labels permutation590 hz
    mixedMoment B raw3293step0 raw3293step0Labels = mixedMoment B raw3293step1 raw3293step1Labels := by
      have hz : ∀ j, raw3293step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw3293step1 = (fun i j => raw3293step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw3293step1 raw3293step0; decide +kernel
      have hl : raw3293step1Labels = raw3293step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3293step0 raw3293step0Labels permutation104 hz
    mixedMoment B raw3293step1 raw3293step1Labels = mixedMoment B raw3293step2 raw3293step2Labels := by
      have hz : ∀ j, raw3293step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw3293step2 = (fun i j => raw3293step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw3293step2 raw3293step1; decide +kernel
      have hl : raw3293step2Labels = raw3293step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3293step1 raw3293step1Labels permutation20 hz
    mixedMoment B raw3293step2 raw3293step2Labels = mixedMoment B raw3293step3 raw3293step3Labels := by
      have ha : raw3293step3 = (fun i j => raw3293step2 (permutation3 i) (permutation6 j)) := by apply Matrix.ext; unfold raw3293step3 raw3293step2; decide +kernel
      have hl : raw3293step3Labels = raw3293step2Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3293step2 raw3293step2Labels permutation3 permutation6
    mixedMoment B raw3293step3 raw3293step3Labels = mixedMoment B raw3293step4 raw3293step4Labels := by
      have ha : raw3293step4 = -raw3293step3 := by apply Matrix.ext; change ∀ i j, raw3293step4 i j = -(raw3293step3 i j); unfold raw3293step4 raw3293step3; decide +kernel
      have hl : raw3293step4Labels = raw3293step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3293step4 raw3293step4Labels = mixedMoment B raw3293step5 raw3293step5Labels := by
      have ha : raw3293step5 = raw3293step4 := by apply Matrix.ext; unfold raw3293step5 raw3293step4; decide +kernel
      have hl : raw3293step4Labels = labelEmbedding9 ∘ raw3293step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3293step4 raw3293step4Labels raw3293step5Labels labelEmbedding9 hl
    _ = mixedMoment B node5495 node5495Labels := by rfl

def raw3294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw3294Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw3294step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3294step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw3294step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3294step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3294step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3294 raw3294Labels = mixedMoment B node5307 node5307Labels := by
  calc
    mixedMoment B raw3294 raw3294Labels = mixedMoment B raw3294step0 raw3294step0Labels := by
      have hz : ∀ j, raw3294 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3294step0 = (fun i j => raw3294 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3294step0 raw3294; decide +kernel
      have hl : raw3294step0Labels = raw3294Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3294 raw3294Labels permutation434 hz
    mixedMoment B raw3294step0 raw3294step0Labels = mixedMoment B raw3294step1 raw3294step1Labels := by
      have hz : ∀ j, raw3294step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3294step1 = (fun i j => raw3294step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3294step1 raw3294step0; decide +kernel
      have hl : raw3294step1Labels = raw3294step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3294step0 raw3294step0Labels permutation80 hz
    mixedMoment B raw3294step1 raw3294step1Labels = mixedMoment B raw3294step2 raw3294step2Labels := by
      have ha : raw3294step2 = (fun i j => raw3294step1 (permutation12 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3294step2 raw3294step1; decide +kernel
      have hl : raw3294step2Labels = raw3294step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3294step1 raw3294step1Labels permutation12 permutation2
    _ = mixedMoment B node5307 node5307Labels := by rfl

def raw3295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw3295Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3295step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw3295step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3295step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3295step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3295 raw3295Labels = mixedMoment B node5440 node5440Labels := by
  calc
    mixedMoment B raw3295 raw3295Labels = mixedMoment B raw3295step0 raw3295step0Labels := by
      have hz : ∀ j, raw3295 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3295step0 = (fun i j => raw3295 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3295step0 raw3295; decide +kernel
      have hl : raw3295step0Labels = raw3295Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3295 raw3295Labels permutation434 hz
    mixedMoment B raw3295step0 raw3295step0Labels = mixedMoment B raw3295step1 raw3295step1Labels := by
      have ha : raw3295step1 = (fun i j => raw3295step0 (permutation42 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3295step1 raw3295step0; decide +kernel
      have hl : raw3295step1Labels = raw3295step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3295step0 raw3295step0Labels permutation42 permutation2
    _ = mixedMoment B node5440 node5440Labels := by rfl

def raw3296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw3296Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3296step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw3296step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3296step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw3296step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3296 raw3296Labels = mixedMoment B node5440 node5440Labels := by
  calc
    mixedMoment B raw3296 raw3296Labels = mixedMoment B raw3296step0 raw3296step0Labels := by
      have hz : ∀ j, raw3296 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3296step0 = (fun i j => raw3296 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3296step0 raw3296; decide +kernel
      have hl : raw3296step0Labels = raw3296Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3296 raw3296Labels permutation346 hz
    mixedMoment B raw3296step0 raw3296step0Labels = mixedMoment B raw3296step1 raw3296step1Labels := by
      have ha : raw3296step1 = (fun i j => raw3296step0 (permutation42 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3296step1 raw3296step0; decide +kernel
      have hl : raw3296step1Labels = raw3296step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3296step0 raw3296step0Labels permutation42 permutation2
    _ = mixedMoment B node5440 node5440Labels := by rfl

def raw3297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0]]
def raw3297Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0]]
def raw3297step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3297step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw3297step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3297step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3297step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3297 raw3297Labels = mixedMoment B node5454 node5454Labels := by
  calc
    mixedMoment B raw3297 raw3297Labels = mixedMoment B raw3297step0 raw3297step0Labels := by
      have hz : ∀ j, raw3297 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3297step0 = (fun i j => raw3297 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3297step0 raw3297; decide +kernel
      have hl : raw3297step0Labels = raw3297Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3297 raw3297Labels permutation434 hz
    mixedMoment B raw3297step0 raw3297step0Labels = mixedMoment B raw3297step1 raw3297step1Labels := by
      have hz : ∀ j, raw3297step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3297step1 = (fun i j => raw3297step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3297step1 raw3297step0; decide +kernel
      have hl : raw3297step1Labels = raw3297step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3297step0 raw3297step0Labels permutation80 hz
    mixedMoment B raw3297step1 raw3297step1Labels = mixedMoment B raw3297step2 raw3297step2Labels := by
      have ha : raw3297step2 = (fun i j => raw3297step1 (permutation11 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3297step2 raw3297step1; decide +kernel
      have hl : raw3297step2Labels = raw3297step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3297step1 raw3297step1Labels permutation11 permutation2
    _ = mixedMoment B node5454 node5454Labels := by rfl

def raw3298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0]]
def raw3298Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1]]
def raw3298step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3298step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![0, 0, 0], ![1, 0, -1]]
def raw3298step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3298step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![1, 0, -1], ![1, 0, -1]]
def raw3298step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3298step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw3298step3Labels : Fin 2 → Fin 3 := ![0, 2]

def raw3298step4 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw3298step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical3298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3298 raw3298Labels = mixedMoment B node4093 node4093Labels := by
  calc
    mixedMoment B raw3298 raw3298Labels = mixedMoment B raw3298step0 raw3298step0Labels := by
      have hz : ∀ j, raw3298 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw3298step0 = (fun i j => raw3298 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw3298step0 raw3298; decide +kernel
      have hl : raw3298step0Labels = raw3298Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3298 raw3298Labels permutation590 hz
    mixedMoment B raw3298step0 raw3298step0Labels = mixedMoment B raw3298step1 raw3298step1Labels := by
      have hz : ∀ j, raw3298step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw3298step1 = (fun i j => raw3298step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw3298step1 raw3298step0; decide +kernel
      have hl : raw3298step1Labels = raw3298step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3298step0 raw3298step0Labels permutation104 hz
    mixedMoment B raw3298step1 raw3298step1Labels = mixedMoment B raw3298step2 raw3298step2Labels := by
      have hz : ∀ j, raw3298step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw3298step2 = (fun i j => raw3298step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw3298step2 raw3298step1; decide +kernel
      have hl : raw3298step2Labels = raw3298step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3298step1 raw3298step1Labels permutation20 hz
    mixedMoment B raw3298step2 raw3298step2Labels = mixedMoment B raw3298step3 raw3298step3Labels := by
      have hz : ∀ i, raw3298step2 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw3298step3 = (fun i j => raw3298step2 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw3298step3 raw3298step2; decide +kernel
      have hl : raw3298step3Labels = (fun j => raw3298step2Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3298step2 raw3298step2Labels permutation4 hz
    mixedMoment B raw3298step3 raw3298step3Labels = mixedMoment B raw3298step4 raw3298step4Labels := by
      have ha : raw3298step4 = raw3298step3 := by apply Matrix.ext; unfold raw3298step4 raw3298step3; decide +kernel
      have hl : raw3298step3Labels = labelEmbedding2 ∘ raw3298step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3298step3 raw3298step3Labels raw3298step4Labels labelEmbedding2 hl
    _ = mixedMoment B node4093 node4093Labels := by rfl

def raw3299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw3299Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw3299step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3299step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3299step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3299 raw3299Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw3299 raw3299Labels = mixedMoment B raw3299step0 raw3299step0Labels := by
      have hz : ∀ j, raw3299 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3299step0 = (fun i j => raw3299 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3299step0 raw3299; decide +kernel
      have hl : raw3299step0Labels = raw3299Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3299 raw3299Labels permutation434 hz
    mixedMoment B raw3299step0 raw3299step0Labels = mixedMoment B raw3299step1 raw3299step1Labels := by
      have ha : raw3299step1 = (fun i j => raw3299step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3299step1 raw3299step0; decide +kernel
      have hl : raw3299step1Labels = raw3299step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3299step0 raw3299step0Labels permutation33 permutation2
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw3300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0]]
def raw3300Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw3300step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3300step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3300step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3300 raw3300Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw3300 raw3300Labels = mixedMoment B raw3300step0 raw3300step0Labels := by
      have hz : ∀ j, raw3300 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3300step0 = (fun i j => raw3300 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3300step0 raw3300; decide +kernel
      have hl : raw3300step0Labels = raw3300Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3300 raw3300Labels permutation434 hz
    mixedMoment B raw3300step0 raw3300step0Labels = mixedMoment B raw3300step1 raw3300step1Labels := by
      have ha : raw3300step1 = (fun i j => raw3300step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3300step1 raw3300step0; decide +kernel
      have hl : raw3300step1Labels = raw3300step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3300step0 raw3300step0Labels permutation33 permutation2
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw3301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw3301Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3301step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3301step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3301 raw3301Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw3301 raw3301Labels = mixedMoment B raw3301step0 raw3301step0Labels := by
      have ha : raw3301step0 = (fun i j => raw3301 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3301step0 raw3301; decide +kernel
      have hl : raw3301step0Labels = raw3301Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3301 raw3301Labels permutation201 permutation2
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw3302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -1, 0]]
def raw3302Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0]]
def raw3302step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3302step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3302step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3302 raw3302Labels = mixedMoment B node5452 node5452Labels := by
  calc
    mixedMoment B raw3302 raw3302Labels = mixedMoment B raw3302step0 raw3302step0Labels := by
      have hz : ∀ j, raw3302 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3302step0 = (fun i j => raw3302 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3302step0 raw3302; decide +kernel
      have hl : raw3302step0Labels = raw3302Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3302 raw3302Labels permutation434 hz
    mixedMoment B raw3302step0 raw3302step0Labels = mixedMoment B raw3302step1 raw3302step1Labels := by
      have ha : raw3302step1 = (fun i j => raw3302step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3302step1 raw3302step0; decide +kernel
      have hl : raw3302step1Labels = raw3302step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3302step0 raw3302step0Labels permutation34 permutation2
    _ = mixedMoment B node5452 node5452Labels := by rfl

def raw3303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 0, 0]]
def raw3303Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1]]
def raw3303step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3303step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3303step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3303 raw3303Labels = mixedMoment B node5454 node5454Labels := by
  calc
    mixedMoment B raw3303 raw3303Labels = mixedMoment B raw3303step0 raw3303step0Labels := by
      have hz : ∀ j, raw3303 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw3303step0 = (fun i j => raw3303 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw3303step0 raw3303; decide +kernel
      have hl : raw3303step0Labels = raw3303Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3303 raw3303Labels permutation590 hz
    mixedMoment B raw3303step0 raw3303step0Labels = mixedMoment B raw3303step1 raw3303step1Labels := by
      have hz : ∀ j, raw3303step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw3303step1 = (fun i j => raw3303step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw3303step1 raw3303step0; decide +kernel
      have hl : raw3303step1Labels = raw3303step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3303step0 raw3303step0Labels permutation104 hz
    _ = mixedMoment B node5454 node5454Labels := by rfl

def raw3304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw3304Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw3304step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3304step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3304step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3304 raw3304Labels = mixedMoment B node5292 node5292Labels := by
  calc
    mixedMoment B raw3304 raw3304Labels = mixedMoment B raw3304step0 raw3304step0Labels := by
      have hz : ∀ j, raw3304 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3304step0 = (fun i j => raw3304 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3304step0 raw3304; decide +kernel
      have hl : raw3304step0Labels = raw3304Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3304 raw3304Labels permutation346 hz
    mixedMoment B raw3304step0 raw3304step0Labels = mixedMoment B raw3304step1 raw3304step1Labels := by
      have ha : raw3304step1 = (fun i j => raw3304step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3304step1 raw3304step0; decide +kernel
      have hl : raw3304step1Labels = raw3304step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3304step0 raw3304step0Labels permutation33 permutation2
    _ = mixedMoment B node5292 node5292Labels := by rfl

def raw3305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw3305Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3305step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw3305step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3305step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3305step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3305 raw3305Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw3305 raw3305Labels = mixedMoment B raw3305step0 raw3305step0Labels := by
      have hz : ∀ j, raw3305 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3305step0 = (fun i j => raw3305 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3305step0 raw3305; decide +kernel
      have hl : raw3305step0Labels = raw3305Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3305 raw3305Labels permutation346 hz
    mixedMoment B raw3305step0 raw3305step0Labels = mixedMoment B raw3305step1 raw3305step1Labels := by
      have ha : raw3305step1 = (fun i j => raw3305step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3305step1 raw3305step0; decide +kernel
      have hl : raw3305step1Labels = raw3305step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3305step0 raw3305step0Labels permutation33 permutation2
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw3306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, -1, 0]]
def raw3306Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3306step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3306step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3306 raw3306Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw3306 raw3306Labels = mixedMoment B raw3306step0 raw3306step0Labels := by
      have ha : raw3306step0 = (fun i j => raw3306 (permutation177 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3306step0 raw3306; decide +kernel
      have hl : raw3306step0Labels = raw3306Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3306 raw3306Labels permutation177 permutation2
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw3307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0]]
def raw3307Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![1, -1, 0]]
def raw3307step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3307step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw3307step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3307 raw3307Labels = mixedMoment B node5452 node5452Labels := by
  calc
    mixedMoment B raw3307 raw3307Labels = mixedMoment B raw3307step0 raw3307step0Labels := by
      have hz : ∀ j, raw3307 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3307step0 = (fun i j => raw3307 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3307step0 raw3307; decide +kernel
      have hl : raw3307step0Labels = raw3307Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3307 raw3307Labels permutation346 hz
    mixedMoment B raw3307step0 raw3307step0Labels = mixedMoment B raw3307step1 raw3307step1Labels := by
      have ha : raw3307step1 = (fun i j => raw3307step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3307step1 raw3307step0; decide +kernel
      have hl : raw3307step1Labels = raw3307step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3307step0 raw3307step0Labels permutation34 permutation2
    _ = mixedMoment B node5452 node5452Labels := by rfl

def raw3308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![0, 0, 0]]
def raw3308Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1]]
def raw3308step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3308step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw3308step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3308 raw3308Labels = mixedMoment B node5454 node5454Labels := by
  calc
    mixedMoment B raw3308 raw3308Labels = mixedMoment B raw3308step0 raw3308step0Labels := by
      have hz : ∀ j, raw3308 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw3308step0 = (fun i j => raw3308 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw3308step0 raw3308; decide +kernel
      have hl : raw3308step0Labels = raw3308Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3308 raw3308Labels permutation590 hz
    mixedMoment B raw3308step0 raw3308step0Labels = mixedMoment B raw3308step1 raw3308step1Labels := by
      have hz : ∀ j, raw3308step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3308step1 = (fun i j => raw3308step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3308step1 raw3308step0; decide +kernel
      have hl : raw3308step1Labels = raw3308step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3308step0 raw3308step0Labels permutation80 hz
    _ = mixedMoment B node5454 node5454Labels := by rfl

def raw3309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0]]
def raw3309Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0]]
def raw3309step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3309step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw3309step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3309step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3309step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3309 raw3309Labels = mixedMoment B node5293 node5293Labels := by
  calc
    mixedMoment B raw3309 raw3309Labels = mixedMoment B raw3309step0 raw3309step0Labels := by
      have hz : ∀ j, raw3309 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3309step0 = (fun i j => raw3309 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3309step0 raw3309; decide +kernel
      have hl : raw3309step0Labels = raw3309Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3309 raw3309Labels permutation434 hz
    mixedMoment B raw3309step0 raw3309step0Labels = mixedMoment B raw3309step1 raw3309step1Labels := by
      have hz : ∀ j, raw3309step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3309step1 = (fun i j => raw3309step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3309step1 raw3309step0; decide +kernel
      have hl : raw3309step1Labels = raw3309step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3309step0 raw3309step0Labels permutation80 hz
    mixedMoment B raw3309step1 raw3309step1Labels = mixedMoment B raw3309step2 raw3309step2Labels := by
      have ha : raw3309step2 = (fun i j => raw3309step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3309step2 raw3309step1; decide +kernel
      have hl : raw3309step2Labels = raw3309step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3309step1 raw3309step1Labels permutation9 permutation2
    _ = mixedMoment B node5293 node5293Labels := by rfl

def raw3310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0]]
def raw3310Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3310step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0]]
def raw3310step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3310step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![2, -1, -1], ![1, -1, 0]]
def raw3310step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3310step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3310step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3310 raw3310Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw3310 raw3310Labels = mixedMoment B raw3310step0 raw3310step0Labels := by
      have hz : ∀ j, raw3310 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3310step0 = (fun i j => raw3310 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3310step0 raw3310; decide +kernel
      have hl : raw3310step0Labels = raw3310Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3310 raw3310Labels permutation434 hz
    mixedMoment B raw3310step0 raw3310step0Labels = mixedMoment B raw3310step1 raw3310step1Labels := by
      have hz : ∀ j, raw3310step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3310step1 = (fun i j => raw3310step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3310step1 raw3310step0; decide +kernel
      have hl : raw3310step1Labels = raw3310step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3310step0 raw3310step0Labels permutation80 hz
    mixedMoment B raw3310step1 raw3310step1Labels = mixedMoment B raw3310step2 raw3310step2Labels := by
      have ha : raw3310step2 = (fun i j => raw3310step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3310step2 raw3310step1; decide +kernel
      have hl : raw3310step2Labels = raw3310step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3310step1 raw3310step1Labels permutation9 permutation2
    _ = mixedMoment B node5451 node5451Labels := by rfl

def raw3311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, -1, 0]]
def raw3311Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![1, -1, 0]]
def raw3311step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3311step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3311step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3311 raw3311Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw3311 raw3311Labels = mixedMoment B raw3311step0 raw3311step0Labels := by
      have hz : ∀ j, raw3311 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3311step0 = (fun i j => raw3311 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3311step0 raw3311; decide +kernel
      have hl : raw3311step0Labels = raw3311Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3311 raw3311Labels permutation434 hz
    mixedMoment B raw3311step0 raw3311step0Labels = mixedMoment B raw3311step1 raw3311step1Labels := by
      have ha : raw3311step1 = (fun i j => raw3311step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3311step1 raw3311step0; decide +kernel
      have hl : raw3311step1Labels = raw3311step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3311step0 raw3311step0Labels permutation39 permutation2
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw3312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![1, -1, 0]]
def raw3312Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![2, -1, -1], ![1, -1, 0]]
def raw3312step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3312step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw3312step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3312 raw3312Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw3312 raw3312Labels = mixedMoment B raw3312step0 raw3312step0Labels := by
      have hz : ∀ j, raw3312 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3312step0 = (fun i j => raw3312 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3312step0 raw3312; decide +kernel
      have hl : raw3312step0Labels = raw3312Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3312 raw3312Labels permutation346 hz
    mixedMoment B raw3312step0 raw3312step0Labels = mixedMoment B raw3312step1 raw3312step1Labels := by
      have ha : raw3312step1 = (fun i j => raw3312step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3312step1 raw3312step0; decide +kernel
      have hl : raw3312step1Labels = raw3312step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3312step0 raw3312step0Labels permutation39 permutation2
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw3313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![0, 0, 0]]
def raw3313Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3313step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1]]
def raw3313step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3313step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw3313step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3313step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw3313step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3313 raw3313Labels = mixedMoment B node5455 node5455Labels := by
  calc
    mixedMoment B raw3313 raw3313Labels = mixedMoment B raw3313step0 raw3313step0Labels := by
      have hz : ∀ j, raw3313 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw3313step0 = (fun i j => raw3313 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw3313step0 raw3313; decide +kernel
      have hl : raw3313step0Labels = raw3313Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3313 raw3313Labels permutation590 hz
    mixedMoment B raw3313step0 raw3313step0Labels = mixedMoment B raw3313step1 raw3313step1Labels := by
      have hz : ∀ j, raw3313step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw3313step1 = (fun i j => raw3313step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw3313step1 raw3313step0; decide +kernel
      have hl : raw3313step1Labels = raw3313step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3313step0 raw3313step0Labels permutation104 hz
    mixedMoment B raw3313step1 raw3313step1Labels = mixedMoment B raw3313step2 raw3313step2Labels := by
      have hz : ∀ j, raw3313step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw3313step2 = (fun i j => raw3313step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw3313step2 raw3313step1; decide +kernel
      have hl : raw3313step2Labels = raw3313step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3313step1 raw3313step1Labels permutation20 hz
    _ = mixedMoment B node5455 node5455Labels := by rfl

def raw3314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw3314Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw3314step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3314step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw3314step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3314 raw3314Labels = mixedMoment B node5294 node5294Labels := by
  calc
    mixedMoment B raw3314 raw3314Labels = mixedMoment B raw3314step0 raw3314step0Labels := by
      have hz : ∀ j, raw3314 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3314step0 = (fun i j => raw3314 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3314step0 raw3314; decide +kernel
      have hl : raw3314step0Labels = raw3314Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3314 raw3314Labels permutation434 hz
    mixedMoment B raw3314step0 raw3314step0Labels = mixedMoment B raw3314step1 raw3314step1Labels := by
      have hz : ∀ j, raw3314step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3314step1 = (fun i j => raw3314step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3314step1 raw3314step0; decide +kernel
      have hl : raw3314step1Labels = raw3314step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3314step0 raw3314step0Labels permutation80 hz
    _ = mixedMoment B node5294 node5294Labels := by rfl

def raw3315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw3315Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw3315step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3315step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw3315step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3315step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw3315step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3315step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw3315step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw3315step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw3315step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3315 raw3315Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw3315 raw3315Labels = mixedMoment B raw3315step0 raw3315step0Labels := by
      have hz : ∀ j, raw3315 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3315step0 = (fun i j => raw3315 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3315step0 raw3315; decide +kernel
      have hl : raw3315step0Labels = raw3315Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3315 raw3315Labels permutation434 hz
    mixedMoment B raw3315step0 raw3315step0Labels = mixedMoment B raw3315step1 raw3315step1Labels := by
      have hz : ∀ j, raw3315step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3315step1 = (fun i j => raw3315step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3315step1 raw3315step0; decide +kernel
      have hl : raw3315step1Labels = raw3315step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3315step0 raw3315step0Labels permutation80 hz
    mixedMoment B raw3315step1 raw3315step1Labels = mixedMoment B raw3315step2 raw3315step2Labels := by
      have ha : raw3315step2 = (fun i j => raw3315step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw3315step2 raw3315step1; decide +kernel
      have hl : raw3315step2Labels = raw3315step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3315step1 raw3315step1Labels permutation31 permutation3
    mixedMoment B raw3315step2 raw3315step2Labels = mixedMoment B raw3315step3 raw3315step3Labels := by
      have ha : raw3315step3 = -raw3315step2 := by apply Matrix.ext; change ∀ i j, raw3315step3 i j = -(raw3315step2 i j); unfold raw3315step3 raw3315step2; decide +kernel
      have hl : raw3315step3Labels = raw3315step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw3315step3 raw3315step3Labels = mixedMoment B raw3315step4 raw3315step4Labels := by
      have ha : raw3315step4 = raw3315step3 := by apply Matrix.ext; unfold raw3315step4 raw3315step3; decide +kernel
      have hl : raw3315step3Labels = labelEmbedding6 ∘ raw3315step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw3315step3 raw3315step3Labels raw3315step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw3316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -2, 0]]
def raw3316Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3316step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw3316step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3316step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw3316step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3316 raw3316Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw3316 raw3316Labels = mixedMoment B raw3316step0 raw3316step0Labels := by
      have hz : ∀ j, raw3316 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3316step0 = (fun i j => raw3316 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3316step0 raw3316; decide +kernel
      have hl : raw3316step0Labels = raw3316Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3316 raw3316Labels permutation434 hz
    mixedMoment B raw3316step0 raw3316step0Labels = mixedMoment B raw3316step1 raw3316step1Labels := by
      have ha : raw3316step1 = (fun i j => raw3316step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3316step1 raw3316step0; decide +kernel
      have hl : raw3316step1Labels = raw3316step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3316step0 raw3316step0Labels permutation38 permutation2
    _ = mixedMoment B node5435 node5435Labels := by rfl

def raw3317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw3317Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw3317step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3317step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw3317step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3317 raw3317Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw3317 raw3317Labels = mixedMoment B raw3317step0 raw3317step0Labels := by
      have hz : ∀ j, raw3317 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3317step0 = (fun i j => raw3317 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3317step0 raw3317; decide +kernel
      have hl : raw3317step0Labels = raw3317Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3317 raw3317Labels permutation346 hz
    mixedMoment B raw3317step0 raw3317step0Labels = mixedMoment B raw3317step1 raw3317step1Labels := by
      have ha : raw3317step1 = (fun i j => raw3317step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw3317step1 raw3317step0; decide +kernel
      have hl : raw3317step1Labels = raw3317step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3317step0 raw3317step0Labels permutation38 permutation2
    _ = mixedMoment B node5435 node5435Labels := by rfl

def raw3318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw3318Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![0, 1, -1], ![2, -2, 0]]
def raw3318step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw3318step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw3318step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical3318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3318 raw3318Labels = mixedMoment B node5453 node5453Labels := by
  calc
    mixedMoment B raw3318 raw3318Labels = mixedMoment B raw3318step0 raw3318step0Labels := by
      have hz : ∀ j, raw3318 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3318step0 = (fun i j => raw3318 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3318step0 raw3318; decide +kernel
      have hl : raw3318step0Labels = raw3318Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3318 raw3318Labels permutation434 hz
    mixedMoment B raw3318step0 raw3318step0Labels = mixedMoment B raw3318step1 raw3318step1Labels := by
      have hz : ∀ j, raw3318step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3318step1 = (fun i j => raw3318step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3318step1 raw3318step0; decide +kernel
      have hl : raw3318step1Labels = raw3318step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3318step0 raw3318step0Labels permutation80 hz
    _ = mixedMoment B node5453 node5453Labels := by rfl

def raw3319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3319Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3319step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3319step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3319step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3319step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw3319step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical3319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3319 raw3319Labels = mixedMoment B node4096 node4096Labels := by
  calc
    mixedMoment B raw3319 raw3319Labels = mixedMoment B raw3319step0 raw3319step0Labels := by
      have hz : ∀ j, raw3319 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3319step0 = (fun i j => raw3319 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3319step0 raw3319; decide +kernel
      have hl : raw3319step0Labels = raw3319Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3319 raw3319Labels permutation434 hz
    mixedMoment B raw3319step0 raw3319step0Labels = mixedMoment B raw3319step1 raw3319step1Labels := by
      have hz : ∀ j, raw3319step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3319step1 = (fun i j => raw3319step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3319step1 raw3319step0; decide +kernel
      have hl : raw3319step1Labels = raw3319step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3319step0 raw3319step0Labels permutation80 hz
    mixedMoment B raw3319step1 raw3319step1Labels = mixedMoment B raw3319step2 raw3319step2Labels := by
      have hz : ∀ i, raw3319step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3319step2 = (fun i j => raw3319step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3319step2 raw3319step1; decide +kernel
      have hl : raw3319step2Labels = (fun j => raw3319step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3319step1 raw3319step1Labels permutation6 hz
    _ = mixedMoment B node4096 node4096Labels := by rfl

def raw3320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3320Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3320step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3320step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3320step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3320step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3320step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw3320step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical3320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3320 raw3320Labels = mixedMoment B node4096 node4096Labels := by
  calc
    mixedMoment B raw3320 raw3320Labels = mixedMoment B raw3320step0 raw3320step0Labels := by
      have hz : ∀ j, raw3320 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3320step0 = (fun i j => raw3320 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3320step0 raw3320; decide +kernel
      have hl : raw3320step0Labels = raw3320Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3320 raw3320Labels permutation434 hz
    mixedMoment B raw3320step0 raw3320step0Labels = mixedMoment B raw3320step1 raw3320step1Labels := by
      have hz : ∀ j, raw3320step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3320step1 = (fun i j => raw3320step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3320step1 raw3320step0; decide +kernel
      have hl : raw3320step1Labels = raw3320step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3320step0 raw3320step0Labels permutation56 hz
    mixedMoment B raw3320step1 raw3320step1Labels = mixedMoment B raw3320step2 raw3320step2Labels := by
      have hz : ∀ i, raw3320step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3320step2 = (fun i j => raw3320step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3320step2 raw3320step1; decide +kernel
      have hl : raw3320step2Labels = (fun j => raw3320step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3320step1 raw3320step1Labels permutation6 hz
    _ = mixedMoment B node4096 node4096Labels := by rfl

def raw3321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3321Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3321step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3321step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3321step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3321step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3321step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![1, -1]]
def raw3321step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical3321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3321 raw3321Labels = mixedMoment B node4096 node4096Labels := by
  calc
    mixedMoment B raw3321 raw3321Labels = mixedMoment B raw3321step0 raw3321step0Labels := by
      have hz : ∀ j, raw3321 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3321step0 = (fun i j => raw3321 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3321step0 raw3321; decide +kernel
      have hl : raw3321step0Labels = raw3321Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3321 raw3321Labels permutation346 hz
    mixedMoment B raw3321step0 raw3321step0Labels = mixedMoment B raw3321step1 raw3321step1Labels := by
      have hz : ∀ j, raw3321step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3321step1 = (fun i j => raw3321step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3321step1 raw3321step0; decide +kernel
      have hl : raw3321step1Labels = raw3321step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3321step0 raw3321step0Labels permutation56 hz
    mixedMoment B raw3321step1 raw3321step1Labels = mixedMoment B raw3321step2 raw3321step2Labels := by
      have hz : ∀ i, raw3321step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3321step2 = (fun i j => raw3321step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3321step2 raw3321step1; decide +kernel
      have hl : raw3321step2Labels = (fun j => raw3321step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3321step1 raw3321step1Labels permutation6 hz
    _ = mixedMoment B node4096 node4096Labels := by rfl

def raw3322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0]]
def raw3322Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3322step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0]]
def raw3322step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3322step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0]]
def raw3322step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3322step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, 1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw3322step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3322step3 : Matrix (Fin 2) (Fin 3) ℤ := ![![-1, 1, 0], ![1, -1, 0]]
def raw3322step3Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3322step4 : Matrix (Fin 2) (Fin 2) ℤ := ![![-1, 1], ![1, -1]]
def raw3322step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical3322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3322 raw3322Labels = mixedMoment B node4097 node4097Labels := by
  calc
    mixedMoment B raw3322 raw3322Labels = mixedMoment B raw3322step0 raw3322step0Labels := by
      have hz : ∀ j, raw3322 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw3322step0 = (fun i j => raw3322 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw3322step0 raw3322; decide +kernel
      have hl : raw3322step0Labels = raw3322Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3322 raw3322Labels permutation590 hz
    mixedMoment B raw3322step0 raw3322step0Labels = mixedMoment B raw3322step1 raw3322step1Labels := by
      have hz : ∀ j, raw3322step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw3322step1 = (fun i j => raw3322step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw3322step1 raw3322step0; decide +kernel
      have hl : raw3322step1Labels = raw3322step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3322step0 raw3322step0Labels permutation104 hz
    mixedMoment B raw3322step1 raw3322step1Labels = mixedMoment B raw3322step2 raw3322step2Labels := by
      have hz : ∀ j, raw3322step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw3322step2 = (fun i j => raw3322step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw3322step2 raw3322step1; decide +kernel
      have hl : raw3322step2Labels = raw3322step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3322step1 raw3322step1Labels permutation20 hz
    mixedMoment B raw3322step2 raw3322step2Labels = mixedMoment B raw3322step3 raw3322step3Labels := by
      have hz : ∀ j, raw3322step2 (permutation4 0) j = 0 := by decide +kernel
      have ha : raw3322step3 = (fun i j => raw3322step2 (permutation4 i.succ) j) := by apply Matrix.ext; unfold raw3322step3 raw3322step2; decide +kernel
      have hl : raw3322step3Labels = raw3322step2Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3322step2 raw3322step2Labels permutation4 hz
    mixedMoment B raw3322step3 raw3322step3Labels = mixedMoment B raw3322step4 raw3322step4Labels := by
      have hz : ∀ i, raw3322step3 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3322step4 = (fun i j => raw3322step3 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3322step4 raw3322step3; decide +kernel
      have hl : raw3322step4Labels = (fun j => raw3322step3Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3322step3 raw3322step3Labels permutation6 hz
    _ = mixedMoment B node4097 node4097Labels := by rfl

def raw3323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3323Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3323step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3323step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3323step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3323step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3323step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw3323step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical3323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3323 raw3323Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw3323 raw3323Labels = mixedMoment B raw3323step0 raw3323step0Labels := by
      have hz : ∀ j, raw3323 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3323step0 = (fun i j => raw3323 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3323step0 raw3323; decide +kernel
      have hl : raw3323step0Labels = raw3323Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3323 raw3323Labels permutation434 hz
    mixedMoment B raw3323step0 raw3323step0Labels = mixedMoment B raw3323step1 raw3323step1Labels := by
      have hz : ∀ j, raw3323step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw3323step1 = (fun i j => raw3323step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw3323step1 raw3323step0; decide +kernel
      have hl : raw3323step1Labels = raw3323step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3323step0 raw3323step0Labels permutation80 hz
    mixedMoment B raw3323step1 raw3323step1Labels = mixedMoment B raw3323step2 raw3323step2Labels := by
      have hz : ∀ i, raw3323step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3323step2 = (fun i j => raw3323step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3323step2 raw3323step1; decide +kernel
      have hl : raw3323step2Labels = (fun j => raw3323step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3323step1 raw3323step1Labels permutation6 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

def raw3324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3324Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3324step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3324step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![1, -1], ![1, -1]]
def raw3324step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3324step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw3324step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical3324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3324 raw3324Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw3324 raw3324Labels = mixedMoment B raw3324step0 raw3324step0Labels := by
      have hz : ∀ j, raw3324 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3324step0 = (fun i j => raw3324 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3324step0 raw3324; decide +kernel
      have hl : raw3324step0Labels = raw3324Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3324 raw3324Labels permutation434 hz
    mixedMoment B raw3324step0 raw3324step0Labels = mixedMoment B raw3324step1 raw3324step1Labels := by
      have hz : ∀ i, raw3324step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3324step1 = (fun i j => raw3324step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3324step1 raw3324step0; decide +kernel
      have hl : raw3324step1Labels = (fun j => raw3324step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3324step0 raw3324step0Labels permutation6 hz
    mixedMoment B raw3324step1 raw3324step1Labels = mixedMoment B raw3324step2 raw3324step2Labels := by
      have ha : raw3324step2 = (fun i j => raw3324step1 (permutation38 i) (permutation0 j)) := by apply Matrix.ext; unfold raw3324step2 raw3324step1; decide +kernel
      have hl : raw3324step2Labels = raw3324step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3324step1 raw3324step1Labels permutation38 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw3325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3325Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3325step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3325step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3325step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![1, -1], ![1, -1]]
def raw3325step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw3325step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw3325step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical3325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3325 raw3325Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw3325 raw3325Labels = mixedMoment B raw3325step0 raw3325step0Labels := by
      have hz : ∀ j, raw3325 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw3325step0 = (fun i j => raw3325 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw3325step0 raw3325; decide +kernel
      have hl : raw3325step0Labels = raw3325Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3325 raw3325Labels permutation346 hz
    mixedMoment B raw3325step0 raw3325step0Labels = mixedMoment B raw3325step1 raw3325step1Labels := by
      have hz : ∀ i, raw3325step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3325step1 = (fun i j => raw3325step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3325step1 raw3325step0; decide +kernel
      have hl : raw3325step1Labels = (fun j => raw3325step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3325step0 raw3325step0Labels permutation6 hz
    mixedMoment B raw3325step1 raw3325step1Labels = mixedMoment B raw3325step2 raw3325step2Labels := by
      have ha : raw3325step2 = (fun i j => raw3325step1 (permutation38 i) (permutation0 j)) := by apply Matrix.ext; unfold raw3325step2 raw3325step1; decide +kernel
      have hl : raw3325step2Labels = raw3325step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw3325step1 raw3325step1Labels permutation38 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw3326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0]]
def raw3326Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0]]
def raw3326step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3326step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw3326step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3326step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3326step2Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3326step3 : Matrix (Fin 3) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![1, -1]]
def raw3326step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical3326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3326 raw3326Labels = mixedMoment B node4093 node4093Labels := by
  calc
    mixedMoment B raw3326 raw3326Labels = mixedMoment B raw3326step0 raw3326step0Labels := by
      have hz : ∀ j, raw3326 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw3326step0 = (fun i j => raw3326 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw3326step0 raw3326; decide +kernel
      have hl : raw3326step0Labels = raw3326Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3326 raw3326Labels permutation590 hz
    mixedMoment B raw3326step0 raw3326step0Labels = mixedMoment B raw3326step1 raw3326step1Labels := by
      have hz : ∀ j, raw3326step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw3326step1 = (fun i j => raw3326step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw3326step1 raw3326step0; decide +kernel
      have hl : raw3326step1Labels = raw3326step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3326step0 raw3326step0Labels permutation104 hz
    mixedMoment B raw3326step1 raw3326step1Labels = mixedMoment B raw3326step2 raw3326step2Labels := by
      have hz : ∀ j, raw3326step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw3326step2 = (fun i j => raw3326step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw3326step2 raw3326step1; decide +kernel
      have hl : raw3326step2Labels = raw3326step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3326step1 raw3326step1Labels permutation20 hz
    mixedMoment B raw3326step2 raw3326step2Labels = mixedMoment B raw3326step3 raw3326step3Labels := by
      have hz : ∀ i, raw3326step2 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3326step3 = (fun i j => raw3326step2 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3326step3 raw3326step2; decide +kernel
      have hl : raw3326step3Labels = (fun j => raw3326step2Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3326step2 raw3326step2Labels permutation6 hz
    _ = mixedMoment B node4093 node4093Labels := by rfl

def raw3327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3327Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3327step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3327step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw3327step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw3327step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![1, -1], ![1, -1], ![1, -1]]
def raw3327step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical3327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw3327 raw3327Labels = mixedMoment B node4083 node4083Labels := by
  calc
    mixedMoment B raw3327 raw3327Labels = mixedMoment B raw3327step0 raw3327step0Labels := by
      have hz : ∀ j, raw3327 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw3327step0 = (fun i j => raw3327 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw3327step0 raw3327; decide +kernel
      have hl : raw3327step0Labels = raw3327Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3327 raw3327Labels permutation434 hz
    mixedMoment B raw3327step0 raw3327step0Labels = mixedMoment B raw3327step1 raw3327step1Labels := by
      have hz : ∀ j, raw3327step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw3327step1 = (fun i j => raw3327step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw3327step1 raw3327step0; decide +kernel
      have hl : raw3327step1Labels = raw3327step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw3327step0 raw3327step0Labels permutation56 hz
    mixedMoment B raw3327step1 raw3327step1Labels = mixedMoment B raw3327step2 raw3327step2Labels := by
      have hz : ∀ i, raw3327step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw3327step2 = (fun i j => raw3327step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw3327step2 raw3327step1; decide +kernel
      have hl : raw3327step2Labels = (fun j => raw3327step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw3327step1 raw3327step1Labels permutation6 hz
    _ = mixedMoment B node4083 node4083Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
