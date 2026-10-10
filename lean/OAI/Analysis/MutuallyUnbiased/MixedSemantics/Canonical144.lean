import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw18432 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw18432Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18432step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18432step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18432step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18432step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18432 raw18432Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw18432 raw18432Labels = mixedMoment B raw18432step0 raw18432step0Labels := by
      have ha : raw18432step0 = (fun i j => raw18432 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18432step0 raw18432; decide +kernel
      have hl : raw18432step0Labels = raw18432Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18432 raw18432Labels permutation154 permutation6
    mixedMoment B raw18432step0 raw18432step0Labels = mixedMoment B raw18432step1 raw18432step1Labels := by
      have ha : raw18432step1 = raw18432step0 := by apply Matrix.ext; unfold raw18432step1 raw18432step0; decide +kernel
      have hl : raw18432step0Labels = labelEmbedding9 ∘ raw18432step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18432step0 raw18432step0Labels raw18432step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

def raw18433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18433Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18433step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18433step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18433step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18433step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18433step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18433step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18433 raw18433Labels = mixedMoment B node5383 node5383Labels := by
  calc
    mixedMoment B raw18433 raw18433Labels = mixedMoment B raw18433step0 raw18433step0Labels := by
      have ha : raw18433step0 = (fun i j => raw18433 (permutation289 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18433step0 raw18433; decide +kernel
      have hl : raw18433step0Labels = raw18433Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18433 raw18433Labels permutation289 permutation5
    mixedMoment B raw18433step0 raw18433step0Labels = mixedMoment B raw18433step1 raw18433step1Labels := by
      have ha : raw18433step1 = -raw18433step0 := by apply Matrix.ext; change ∀ i j, raw18433step1 i j = -(raw18433step0 i j); unfold raw18433step1 raw18433step0; decide +kernel
      have hl : raw18433step1Labels = raw18433step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18433step1 raw18433step1Labels = mixedMoment B raw18433step2 raw18433step2Labels := by
      have ha : raw18433step2 = raw18433step1 := by apply Matrix.ext; unfold raw18433step2 raw18433step1; decide +kernel
      have hl : raw18433step1Labels = labelEmbedding8 ∘ raw18433step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18433step1 raw18433step1Labels raw18433step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5383 node5383Labels := by rfl

def raw18434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18434Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18434step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw18434step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18434step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18434step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18434step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18434step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18434 raw18434Labels = mixedMoment B node5166 node5166Labels := by
  calc
    mixedMoment B raw18434 raw18434Labels = mixedMoment B raw18434step0 raw18434step0Labels := by
      have ha : raw18434step0 = (fun i j => raw18434 (permutation373 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18434step0 raw18434; decide +kernel
      have hl : raw18434step0Labels = raw18434Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18434 raw18434Labels permutation373 permutation4
    mixedMoment B raw18434step0 raw18434step0Labels = mixedMoment B raw18434step1 raw18434step1Labels := by
      have ha : raw18434step1 = -raw18434step0 := by apply Matrix.ext; change ∀ i j, raw18434step1 i j = -(raw18434step0 i j); unfold raw18434step1 raw18434step0; decide +kernel
      have hl : raw18434step1Labels = raw18434step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18434step1 raw18434step1Labels = mixedMoment B raw18434step2 raw18434step2Labels := by
      have ha : raw18434step2 = raw18434step1 := by apply Matrix.ext; unfold raw18434step2 raw18434step1; decide +kernel
      have hl : raw18434step1Labels = labelEmbedding7 ∘ raw18434step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18434step1 raw18434step1Labels raw18434step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5166 node5166Labels := by rfl

def raw18435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18435Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw18435step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18435step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw18435step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18435step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18435step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18435step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18435step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18435 raw18435Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw18435 raw18435Labels = mixedMoment B raw18435step0 raw18435step0Labels := by
      have hz : ∀ j, raw18435 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18435step0 = (fun i j => raw18435 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18435step0 raw18435; decide +kernel
      have hl : raw18435step0Labels = raw18435Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18435 raw18435Labels permutation434 hz
    mixedMoment B raw18435step0 raw18435step0Labels = mixedMoment B raw18435step1 raw18435step1Labels := by
      have ha : raw18435step1 = (fun i j => raw18435step0 (permutation89 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18435step1 raw18435step0; decide +kernel
      have hl : raw18435step1Labels = raw18435step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18435step0 raw18435step0Labels permutation89 permutation4
    mixedMoment B raw18435step1 raw18435step1Labels = mixedMoment B raw18435step2 raw18435step2Labels := by
      have ha : raw18435step2 = -raw18435step1 := by apply Matrix.ext; change ∀ i j, raw18435step2 i j = -(raw18435step1 i j); unfold raw18435step2 raw18435step1; decide +kernel
      have hl : raw18435step2Labels = raw18435step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18435step2 raw18435step2Labels = mixedMoment B raw18435step3 raw18435step3Labels := by
      have ha : raw18435step3 = raw18435step2 := by apply Matrix.ext; unfold raw18435step3 raw18435step2; decide +kernel
      have hl : raw18435step2Labels = labelEmbedding7 ∘ raw18435step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18435step2 raw18435step2Labels raw18435step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw18436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw18436Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18436step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw18436step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18436step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw18436step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18436step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18436step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18436step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18436step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18436 raw18436Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw18436 raw18436Labels = mixedMoment B raw18436step0 raw18436step0Labels := by
      have hz : ∀ j, raw18436 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18436step0 = (fun i j => raw18436 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18436step0 raw18436; decide +kernel
      have hl : raw18436step0Labels = raw18436Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18436 raw18436Labels permutation520 hz
    mixedMoment B raw18436step0 raw18436step0Labels = mixedMoment B raw18436step1 raw18436step1Labels := by
      have ha : raw18436step1 = (fun i j => raw18436step0 (permutation89 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18436step1 raw18436step0; decide +kernel
      have hl : raw18436step1Labels = raw18436step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18436step0 raw18436step0Labels permutation89 permutation4
    mixedMoment B raw18436step1 raw18436step1Labels = mixedMoment B raw18436step2 raw18436step2Labels := by
      have ha : raw18436step2 = -raw18436step1 := by apply Matrix.ext; change ∀ i j, raw18436step2 i j = -(raw18436step1 i j); unfold raw18436step2 raw18436step1; decide +kernel
      have hl : raw18436step2Labels = raw18436step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18436step2 raw18436step2Labels = mixedMoment B raw18436step3 raw18436step3Labels := by
      have ha : raw18436step3 = raw18436step2 := by apply Matrix.ext; unfold raw18436step3 raw18436step2; decide +kernel
      have hl : raw18436step2Labels = labelEmbedding7 ∘ raw18436step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18436step2 raw18436step2Labels raw18436step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw18437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw18437Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18437step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0]]
def raw18437step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18437step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw18437step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18437step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18437step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18437step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18437step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18437 raw18437Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw18437 raw18437Labels = mixedMoment B raw18437step0 raw18437step0Labels := by
      have hz : ∀ j, raw18437 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw18437step0 = (fun i j => raw18437 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw18437step0 raw18437; decide +kernel
      have hl : raw18437step0Labels = raw18437Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18437 raw18437Labels permutation590 hz
    mixedMoment B raw18437step0 raw18437step0Labels = mixedMoment B raw18437step1 raw18437step1Labels := by
      have ha : raw18437step1 = (fun i j => raw18437step0 (permutation89 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18437step1 raw18437step0; decide +kernel
      have hl : raw18437step1Labels = raw18437step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18437step0 raw18437step0Labels permutation89 permutation4
    mixedMoment B raw18437step1 raw18437step1Labels = mixedMoment B raw18437step2 raw18437step2Labels := by
      have ha : raw18437step2 = -raw18437step1 := by apply Matrix.ext; change ∀ i j, raw18437step2 i j = -(raw18437step1 i j); unfold raw18437step2 raw18437step1; decide +kernel
      have hl : raw18437step2Labels = raw18437step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18437step2 raw18437step2Labels = mixedMoment B raw18437step3 raw18437step3Labels := by
      have ha : raw18437step3 = raw18437step2 := by apply Matrix.ext; unfold raw18437step3 raw18437step2; decide +kernel
      have hl : raw18437step2Labels = labelEmbedding7 ∘ raw18437step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18437step2 raw18437step2Labels raw18437step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw18438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18438Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18438step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18438step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18438 raw18438Labels = mixedMoment B node5301 node5301Labels := by
  calc
    mixedMoment B raw18438 raw18438Labels = mixedMoment B raw18438step0 raw18438step0Labels := by
      have hz : ∀ j, raw18438 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw18438step0 = (fun i j => raw18438 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw18438step0 raw18438; decide +kernel
      have hl : raw18438step0Labels = raw18438Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18438 raw18438Labels permutation265 hz
    _ = mixedMoment B node5301 node5301Labels := by rfl

def raw18439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18439Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18439step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18439step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18439step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18439step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18439 raw18439Labels = mixedMoment B node5383 node5383Labels := by
  calc
    mixedMoment B raw18439 raw18439Labels = mixedMoment B raw18439step0 raw18439step0Labels := by
      have ha : raw18439step0 = (fun i j => raw18439 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18439step0 raw18439; decide +kernel
      have hl : raw18439step0Labels = raw18439Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18439 raw18439Labels permutation265 permutation3
    mixedMoment B raw18439step0 raw18439step0Labels = mixedMoment B raw18439step1 raw18439step1Labels := by
      have ha : raw18439step1 = raw18439step0 := by apply Matrix.ext; unfold raw18439step1 raw18439step0; decide +kernel
      have hl : raw18439step0Labels = labelEmbedding6 ∘ raw18439step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18439step0 raw18439step0Labels raw18439step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5383 node5383Labels := by rfl

def raw18440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18440Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw18440step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18440step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18440step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18440 raw18440Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw18440 raw18440Labels = mixedMoment B raw18440step0 raw18440step0Labels := by
      have hz : ∀ j, raw18440 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18440step0 = (fun i j => raw18440 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18440step0 raw18440; decide +kernel
      have hl : raw18440step0Labels = raw18440Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18440 raw18440Labels permutation434 hz
    mixedMoment B raw18440step0 raw18440step0Labels = mixedMoment B raw18440step1 raw18440step1Labels := by
      have ha : raw18440step1 = (fun i j => raw18440step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18440step1 raw18440step0; decide +kernel
      have hl : raw18440step1Labels = raw18440step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18440step0 raw18440step0Labels permutation35 permutation2
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw18441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw18441Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw18441step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18441step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18441step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18441 raw18441Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw18441 raw18441Labels = mixedMoment B raw18441step0 raw18441step0Labels := by
      have hz : ∀ j, raw18441 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18441step0 = (fun i j => raw18441 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18441step0 raw18441; decide +kernel
      have hl : raw18441step0Labels = raw18441Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18441 raw18441Labels permutation520 hz
    mixedMoment B raw18441step0 raw18441step0Labels = mixedMoment B raw18441step1 raw18441step1Labels := by
      have ha : raw18441step1 = (fun i j => raw18441step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18441step1 raw18441step0; decide +kernel
      have hl : raw18441step1Labels = raw18441step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18441step0 raw18441step0Labels permutation35 permutation2
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw18442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw18442Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw18442step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18442step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18442step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18442 raw18442Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw18442 raw18442Labels = mixedMoment B raw18442step0 raw18442step0Labels := by
      have hz : ∀ j, raw18442 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw18442step0 = (fun i j => raw18442 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw18442step0 raw18442; decide +kernel
      have hl : raw18442step0Labels = raw18442Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18442 raw18442Labels permutation590 hz
    mixedMoment B raw18442step0 raw18442step0Labels = mixedMoment B raw18442step1 raw18442step1Labels := by
      have ha : raw18442step1 = (fun i j => raw18442step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18442step1 raw18442step0; decide +kernel
      have hl : raw18442step1Labels = raw18442step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18442step0 raw18442step0Labels permutation35 permutation2
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw18443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18443Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18443step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18443step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18443step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18443step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18443 raw18443Labels = mixedMoment B node5374 node5374Labels := by
  calc
    mixedMoment B raw18443 raw18443Labels = mixedMoment B raw18443step0 raw18443step0Labels := by
      have ha : raw18443step0 = (fun i j => raw18443 (permutation268 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18443step0 raw18443; decide +kernel
      have hl : raw18443step0Labels = raw18443Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18443 raw18443Labels permutation268 permutation3
    mixedMoment B raw18443step0 raw18443step0Labels = mixedMoment B raw18443step1 raw18443step1Labels := by
      have ha : raw18443step1 = raw18443step0 := by apply Matrix.ext; unfold raw18443step1 raw18443step0; decide +kernel
      have hl : raw18443step0Labels = labelEmbedding6 ∘ raw18443step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18443step0 raw18443step0Labels raw18443step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5374 node5374Labels := by rfl

def raw18444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 3, -2], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18444Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18444step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 2, 0]]
def raw18444step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18444step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18444step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18444step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18444step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18444 raw18444Labels = mixedMoment B node5155 node5155Labels := by
  calc
    mixedMoment B raw18444 raw18444Labels = mixedMoment B raw18444step0 raw18444step0Labels := by
      have ha : raw18444step0 = (fun i j => raw18444 (permutation369 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18444step0 raw18444; decide +kernel
      have hl : raw18444step0Labels = raw18444Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18444 raw18444Labels permutation369 permutation4
    mixedMoment B raw18444step0 raw18444step0Labels = mixedMoment B raw18444step1 raw18444step1Labels := by
      have ha : raw18444step1 = -raw18444step0 := by apply Matrix.ext; change ∀ i j, raw18444step1 i j = -(raw18444step0 i j); unfold raw18444step1 raw18444step0; decide +kernel
      have hl : raw18444step1Labels = raw18444step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18444step1 raw18444step1Labels = mixedMoment B raw18444step2 raw18444step2Labels := by
      have ha : raw18444step2 = raw18444step1 := by apply Matrix.ext; unfold raw18444step2 raw18444step1; decide +kernel
      have hl : raw18444step1Labels = labelEmbedding7 ∘ raw18444step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18444step1 raw18444step1Labels raw18444step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5155 node5155Labels := by rfl

def raw18445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0]]
def raw18445Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0]]
def raw18445step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18445step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw18445step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18445step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw18445step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18445step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw18445step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18445 raw18445Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw18445 raw18445Labels = mixedMoment B raw18445step0 raw18445step0Labels := by
      have hz : ∀ j, raw18445 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18445step0 = (fun i j => raw18445 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18445step0 raw18445; decide +kernel
      have hl : raw18445step0Labels = raw18445Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18445 raw18445Labels permutation520 hz
    mixedMoment B raw18445step0 raw18445step0Labels = mixedMoment B raw18445step1 raw18445step1Labels := by
      have ha : raw18445step1 = (fun i j => raw18445step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18445step1 raw18445step0; decide +kernel
      have hl : raw18445step1Labels = raw18445step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18445step0 raw18445step0Labels permutation127 permutation3
    mixedMoment B raw18445step1 raw18445step1Labels = mixedMoment B raw18445step2 raw18445step2Labels := by
      have ha : raw18445step2 = -raw18445step1 := by apply Matrix.ext; change ∀ i j, raw18445step2 i j = -(raw18445step1 i j); unfold raw18445step2 raw18445step1; decide +kernel
      have hl : raw18445step2Labels = raw18445step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18445step2 raw18445step2Labels = mixedMoment B raw18445step3 raw18445step3Labels := by
      have ha : raw18445step3 = raw18445step2 := by apply Matrix.ext; unfold raw18445step3 raw18445step2; decide +kernel
      have hl : raw18445step2Labels = labelEmbedding6 ∘ raw18445step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18445step2 raw18445step2Labels raw18445step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

def raw18446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0]]
def raw18446Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0]]
def raw18446step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18446step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw18446step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18446step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw18446step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18446step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw18446step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18446 raw18446Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw18446 raw18446Labels = mixedMoment B raw18446step0 raw18446step0Labels := by
      have hz : ∀ j, raw18446 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw18446step0 = (fun i j => raw18446 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw18446step0 raw18446; decide +kernel
      have hl : raw18446step0Labels = raw18446Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18446 raw18446Labels permutation590 hz
    mixedMoment B raw18446step0 raw18446step0Labels = mixedMoment B raw18446step1 raw18446step1Labels := by
      have ha : raw18446step1 = (fun i j => raw18446step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18446step1 raw18446step0; decide +kernel
      have hl : raw18446step1Labels = raw18446step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18446step0 raw18446step0Labels permutation127 permutation3
    mixedMoment B raw18446step1 raw18446step1Labels = mixedMoment B raw18446step2 raw18446step2Labels := by
      have ha : raw18446step2 = -raw18446step1 := by apply Matrix.ext; change ∀ i j, raw18446step2 i j = -(raw18446step1 i j); unfold raw18446step2 raw18446step1; decide +kernel
      have hl : raw18446step2Labels = raw18446step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18446step2 raw18446step2Labels = mixedMoment B raw18446step3 raw18446step3Labels := by
      have ha : raw18446step3 = raw18446step2 := by apply Matrix.ext; unfold raw18446step3 raw18446step2; decide +kernel
      have hl : raw18446step2Labels = labelEmbedding6 ∘ raw18446step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18446step2 raw18446step2Labels raw18446step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

def raw18447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw18447Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18447step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18447step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18447step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18447step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18447 raw18447Labels = mixedMoment B node5374 node5374Labels := by
  calc
    mixedMoment B raw18447 raw18447Labels = mixedMoment B raw18447step0 raw18447step0Labels := by
      have ha : raw18447step0 = (fun i j => raw18447 (permutation266 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18447step0 raw18447; decide +kernel
      have hl : raw18447step0Labels = raw18447Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18447 raw18447Labels permutation266 permutation3
    mixedMoment B raw18447step0 raw18447step0Labels = mixedMoment B raw18447step1 raw18447step1Labels := by
      have ha : raw18447step1 = raw18447step0 := by apply Matrix.ext; unfold raw18447step1 raw18447step0; decide +kernel
      have hl : raw18447step0Labels = labelEmbedding6 ∘ raw18447step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18447step0 raw18447step0Labels raw18447step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5374 node5374Labels := by rfl

def raw18448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 3, -2], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw18448Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18448step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 2, 0]]
def raw18448step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18448step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18448step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18448step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18448step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18448 raw18448Labels = mixedMoment B node5155 node5155Labels := by
  calc
    mixedMoment B raw18448 raw18448Labels = mixedMoment B raw18448step0 raw18448step0Labels := by
      have ha : raw18448step0 = (fun i j => raw18448 (permutation368 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18448step0 raw18448; decide +kernel
      have hl : raw18448step0Labels = raw18448Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18448 raw18448Labels permutation368 permutation4
    mixedMoment B raw18448step0 raw18448step0Labels = mixedMoment B raw18448step1 raw18448step1Labels := by
      have ha : raw18448step1 = -raw18448step0 := by apply Matrix.ext; change ∀ i j, raw18448step1 i j = -(raw18448step0 i j); unfold raw18448step1 raw18448step0; decide +kernel
      have hl : raw18448step1Labels = raw18448step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18448step1 raw18448step1Labels = mixedMoment B raw18448step2 raw18448step2Labels := by
      have ha : raw18448step2 = raw18448step1 := by apply Matrix.ext; unfold raw18448step2 raw18448step1; decide +kernel
      have hl : raw18448step1Labels = labelEmbedding7 ∘ raw18448step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18448step1 raw18448step1Labels raw18448step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5155 node5155Labels := by rfl

def raw18449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw18449Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18449step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![1, -1, 0]]
def raw18449step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18449step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw18449step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18449step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw18449step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18449step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw18449step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18449 raw18449Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw18449 raw18449Labels = mixedMoment B raw18449step0 raw18449step0Labels := by
      have hz : ∀ j, raw18449 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18449step0 = (fun i j => raw18449 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18449step0 raw18449; decide +kernel
      have hl : raw18449step0Labels = raw18449Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18449 raw18449Labels permutation434 hz
    mixedMoment B raw18449step0 raw18449step0Labels = mixedMoment B raw18449step1 raw18449step1Labels := by
      have ha : raw18449step1 = (fun i j => raw18449step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18449step1 raw18449step0; decide +kernel
      have hl : raw18449step1Labels = raw18449step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18449step0 raw18449step0Labels permutation127 permutation3
    mixedMoment B raw18449step1 raw18449step1Labels = mixedMoment B raw18449step2 raw18449step2Labels := by
      have ha : raw18449step2 = -raw18449step1 := by apply Matrix.ext; change ∀ i j, raw18449step2 i j = -(raw18449step1 i j); unfold raw18449step2 raw18449step1; decide +kernel
      have hl : raw18449step2Labels = raw18449step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18449step2 raw18449step2Labels = mixedMoment B raw18449step3 raw18449step3Labels := by
      have ha : raw18449step3 = raw18449step2 := by apply Matrix.ext; unfold raw18449step3 raw18449step2; decide +kernel
      have hl : raw18449step2Labels = labelEmbedding6 ∘ raw18449step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18449step2 raw18449step2Labels raw18449step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

def raw18450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0]]
def raw18450Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18450step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw18450step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18450step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw18450step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18450step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw18450step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18450step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw18450step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18450 raw18450Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw18450 raw18450Labels = mixedMoment B raw18450step0 raw18450step0Labels := by
      have hz : ∀ j, raw18450 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw18450step0 = (fun i j => raw18450 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw18450step0 raw18450; decide +kernel
      have hl : raw18450step0Labels = raw18450Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18450 raw18450Labels permutation590 hz
    mixedMoment B raw18450step0 raw18450step0Labels = mixedMoment B raw18450step1 raw18450step1Labels := by
      have ha : raw18450step1 = (fun i j => raw18450step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18450step1 raw18450step0; decide +kernel
      have hl : raw18450step1Labels = raw18450step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18450step0 raw18450step0Labels permutation151 permutation3
    mixedMoment B raw18450step1 raw18450step1Labels = mixedMoment B raw18450step2 raw18450step2Labels := by
      have ha : raw18450step2 = -raw18450step1 := by apply Matrix.ext; change ∀ i j, raw18450step2 i j = -(raw18450step1 i j); unfold raw18450step2 raw18450step1; decide +kernel
      have hl : raw18450step2Labels = raw18450step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18450step2 raw18450step2Labels = mixedMoment B raw18450step3 raw18450step3Labels := by
      have ha : raw18450step3 = raw18450step2 := by apply Matrix.ext; unfold raw18450step3 raw18450step2; decide +kernel
      have hl : raw18450step2Labels = labelEmbedding6 ∘ raw18450step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18450step2 raw18450step2Labels raw18450step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

def raw18451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18451Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18451step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18451step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18451step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18451step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18451 raw18451Labels = mixedMoment B node5374 node5374Labels := by
  calc
    mixedMoment B raw18451 raw18451Labels = mixedMoment B raw18451step0 raw18451step0Labels := by
      have ha : raw18451step0 = (fun i j => raw18451 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18451step0 raw18451; decide +kernel
      have hl : raw18451step0Labels = raw18451Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18451 raw18451Labels permutation265 permutation3
    mixedMoment B raw18451step0 raw18451step0Labels = mixedMoment B raw18451step1 raw18451step1Labels := by
      have ha : raw18451step1 = raw18451step0 := by apply Matrix.ext; unfold raw18451step1 raw18451step0; decide +kernel
      have hl : raw18451step0Labels = labelEmbedding6 ∘ raw18451step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18451step0 raw18451step0Labels raw18451step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5374 node5374Labels := by rfl

def raw18452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18452Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18452step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 2, 0]]
def raw18452step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18452step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18452step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18452step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18452step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18452 raw18452Labels = mixedMoment B node5155 node5155Labels := by
  calc
    mixedMoment B raw18452 raw18452Labels = mixedMoment B raw18452step0 raw18452step0Labels := by
      have ha : raw18452step0 = (fun i j => raw18452 (permutation367 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18452step0 raw18452; decide +kernel
      have hl : raw18452step0Labels = raw18452Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18452 raw18452Labels permutation367 permutation4
    mixedMoment B raw18452step0 raw18452step0Labels = mixedMoment B raw18452step1 raw18452step1Labels := by
      have ha : raw18452step1 = -raw18452step0 := by apply Matrix.ext; change ∀ i j, raw18452step1 i j = -(raw18452step0 i j); unfold raw18452step1 raw18452step0; decide +kernel
      have hl : raw18452step1Labels = raw18452step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18452step1 raw18452step1Labels = mixedMoment B raw18452step2 raw18452step2Labels := by
      have ha : raw18452step2 = raw18452step1 := by apply Matrix.ext; unfold raw18452step2 raw18452step1; decide +kernel
      have hl : raw18452step1Labels = labelEmbedding7 ∘ raw18452step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18452step1 raw18452step1Labels raw18452step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5155 node5155Labels := by rfl

def raw18453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18453Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw18453step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18453step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw18453step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18453step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw18453step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18453step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw18453step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18453 raw18453Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw18453 raw18453Labels = mixedMoment B raw18453step0 raw18453step0Labels := by
      have hz : ∀ j, raw18453 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18453step0 = (fun i j => raw18453 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18453step0 raw18453; decide +kernel
      have hl : raw18453step0Labels = raw18453Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18453 raw18453Labels permutation434 hz
    mixedMoment B raw18453step0 raw18453step0Labels = mixedMoment B raw18453step1 raw18453step1Labels := by
      have ha : raw18453step1 = (fun i j => raw18453step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18453step1 raw18453step0; decide +kernel
      have hl : raw18453step1Labels = raw18453step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18453step0 raw18453step0Labels permutation151 permutation3
    mixedMoment B raw18453step1 raw18453step1Labels = mixedMoment B raw18453step2 raw18453step2Labels := by
      have ha : raw18453step2 = -raw18453step1 := by apply Matrix.ext; change ∀ i j, raw18453step2 i j = -(raw18453step1 i j); unfold raw18453step2 raw18453step1; decide +kernel
      have hl : raw18453step2Labels = raw18453step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18453step2 raw18453step2Labels = mixedMoment B raw18453step3 raw18453step3Labels := by
      have ha : raw18453step3 = raw18453step2 := by apply Matrix.ext; unfold raw18453step3 raw18453step2; decide +kernel
      have hl : raw18453step2Labels = labelEmbedding6 ∘ raw18453step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18453step2 raw18453step2Labels raw18453step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

def raw18454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw18454Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18454step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw18454step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18454step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw18454step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18454step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw18454step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18454step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw18454step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18454 raw18454Labels = mixedMoment B node5412 node5412Labels := by
  calc
    mixedMoment B raw18454 raw18454Labels = mixedMoment B raw18454step0 raw18454step0Labels := by
      have hz : ∀ j, raw18454 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18454step0 = (fun i j => raw18454 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18454step0 raw18454; decide +kernel
      have hl : raw18454step0Labels = raw18454Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18454 raw18454Labels permutation520 hz
    mixedMoment B raw18454step0 raw18454step0Labels = mixedMoment B raw18454step1 raw18454step1Labels := by
      have ha : raw18454step1 = (fun i j => raw18454step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18454step1 raw18454step0; decide +kernel
      have hl : raw18454step1Labels = raw18454step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18454step0 raw18454step0Labels permutation151 permutation3
    mixedMoment B raw18454step1 raw18454step1Labels = mixedMoment B raw18454step2 raw18454step2Labels := by
      have ha : raw18454step2 = -raw18454step1 := by apply Matrix.ext; change ∀ i j, raw18454step2 i j = -(raw18454step1 i j); unfold raw18454step2 raw18454step1; decide +kernel
      have hl : raw18454step2Labels = raw18454step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18454step2 raw18454step2Labels = mixedMoment B raw18454step3 raw18454step3Labels := by
      have ha : raw18454step3 = raw18454step2 := by apply Matrix.ext; unfold raw18454step3 raw18454step2; decide +kernel
      have hl : raw18454step2Labels = labelEmbedding6 ∘ raw18454step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18454step2 raw18454step2Labels raw18454step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5412 node5412Labels := by rfl

def raw18455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18455Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18455step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw18455step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18455step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18455step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18455step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18455step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18455 raw18455Labels = mixedMoment B node5447 node5447Labels := by
  calc
    mixedMoment B raw18455 raw18455Labels = mixedMoment B raw18455step0 raw18455step0Labels := by
      have ha : raw18455step0 = (fun i j => raw18455 (permutation367 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18455step0 raw18455; decide +kernel
      have hl : raw18455step0Labels = raw18455Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18455 raw18455Labels permutation367 permutation6
    mixedMoment B raw18455step0 raw18455step0Labels = mixedMoment B raw18455step1 raw18455step1Labels := by
      have ha : raw18455step1 = -raw18455step0 := by apply Matrix.ext; change ∀ i j, raw18455step1 i j = -(raw18455step0 i j); unfold raw18455step1 raw18455step0; decide +kernel
      have hl : raw18455step1Labels = raw18455step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18455step1 raw18455step1Labels = mixedMoment B raw18455step2 raw18455step2Labels := by
      have ha : raw18455step2 = raw18455step1 := by apply Matrix.ext; unfold raw18455step2 raw18455step1; decide +kernel
      have hl : raw18455step1Labels = labelEmbedding9 ∘ raw18455step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18455step1 raw18455step1Labels raw18455step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5447 node5447Labels := by rfl

def raw18456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18456Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18456step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18456step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18456step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18456step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18456step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18456step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18456 raw18456Labels = mixedMoment B node5479 node5479Labels := by
  calc
    mixedMoment B raw18456 raw18456Labels = mixedMoment B raw18456step0 raw18456step0Labels := by
      have ha : raw18456step0 = (fun i j => raw18456 (permutation367 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18456step0 raw18456; decide +kernel
      have hl : raw18456step0Labels = raw18456Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18456 raw18456Labels permutation367 permutation7
    mixedMoment B raw18456step0 raw18456step0Labels = mixedMoment B raw18456step1 raw18456step1Labels := by
      have ha : raw18456step1 = -raw18456step0 := by apply Matrix.ext; change ∀ i j, raw18456step1 i j = -(raw18456step0 i j); unfold raw18456step1 raw18456step0; decide +kernel
      have hl : raw18456step1Labels = raw18456step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18456step1 raw18456step1Labels = mixedMoment B raw18456step2 raw18456step2Labels := by
      have ha : raw18456step2 = raw18456step1 := by apply Matrix.ext; unfold raw18456step2 raw18456step1; decide +kernel
      have hl : raw18456step1Labels = labelEmbedding10 ∘ raw18456step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18456step1 raw18456step1Labels raw18456step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5479 node5479Labels := by rfl

def raw18457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18457Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18457step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw18457step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18457step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18457step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18457step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18457step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18457 raw18457Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw18457 raw18457Labels = mixedMoment B raw18457step0 raw18457step0Labels := by
      have ha : raw18457step0 = (fun i j => raw18457 (permutation369 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18457step0 raw18457; decide +kernel
      have hl : raw18457step0Labels = raw18457Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18457 raw18457Labels permutation369 permutation6
    mixedMoment B raw18457step0 raw18457step0Labels = mixedMoment B raw18457step1 raw18457step1Labels := by
      have ha : raw18457step1 = -raw18457step0 := by apply Matrix.ext; change ∀ i j, raw18457step1 i j = -(raw18457step0 i j); unfold raw18457step1 raw18457step0; decide +kernel
      have hl : raw18457step1Labels = raw18457step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18457step1 raw18457step1Labels = mixedMoment B raw18457step2 raw18457step2Labels := by
      have ha : raw18457step2 = raw18457step1 := by apply Matrix.ext; unfold raw18457step2 raw18457step1; decide +kernel
      have hl : raw18457step1Labels = labelEmbedding9 ∘ raw18457step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18457step1 raw18457step1Labels raw18457step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw18458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw18458Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18458step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw18458step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18458step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18458step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18458step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18458step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18458 raw18458Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw18458 raw18458Labels = mixedMoment B raw18458step0 raw18458step0Labels := by
      have ha : raw18458step0 = (fun i j => raw18458 (permutation368 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18458step0 raw18458; decide +kernel
      have hl : raw18458step0Labels = raw18458Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18458 raw18458Labels permutation368 permutation6
    mixedMoment B raw18458step0 raw18458step0Labels = mixedMoment B raw18458step1 raw18458step1Labels := by
      have ha : raw18458step1 = -raw18458step0 := by apply Matrix.ext; change ∀ i j, raw18458step1 i j = -(raw18458step0 i j); unfold raw18458step1 raw18458step0; decide +kernel
      have hl : raw18458step1Labels = raw18458step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18458step1 raw18458step1Labels = mixedMoment B raw18458step2 raw18458step2Labels := by
      have ha : raw18458step2 = raw18458step1 := by apply Matrix.ext; unfold raw18458step2 raw18458step1; decide +kernel
      have hl : raw18458step1Labels = labelEmbedding9 ∘ raw18458step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18458step1 raw18458step1Labels raw18458step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw18459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw18459Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18459step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw18459step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18459step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18459step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18459step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18459step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18459 raw18459Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw18459 raw18459Labels = mixedMoment B raw18459step0 raw18459step0Labels := by
      have ha : raw18459step0 = (fun i j => raw18459 (permutation367 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18459step0 raw18459; decide +kernel
      have hl : raw18459step0Labels = raw18459Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18459 raw18459Labels permutation367 permutation6
    mixedMoment B raw18459step0 raw18459step0Labels = mixedMoment B raw18459step1 raw18459step1Labels := by
      have ha : raw18459step1 = -raw18459step0 := by apply Matrix.ext; change ∀ i j, raw18459step1 i j = -(raw18459step0 i j); unfold raw18459step1 raw18459step0; decide +kernel
      have hl : raw18459step1Labels = raw18459step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18459step1 raw18459step1Labels = mixedMoment B raw18459step2 raw18459step2Labels := by
      have ha : raw18459step2 = raw18459step1 := by apply Matrix.ext; unfold raw18459step2 raw18459step1; decide +kernel
      have hl : raw18459step1Labels = labelEmbedding9 ∘ raw18459step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18459step1 raw18459step1Labels raw18459step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw18460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18460Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18460step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw18460step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18460step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw18460step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18460step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw18460step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18460 raw18460Labels = mixedMoment B node4885 node4885Labels := by
  calc
    mixedMoment B raw18460 raw18460Labels = mixedMoment B raw18460step0 raw18460step0Labels := by
      have ha : raw18460step0 = (fun i j => raw18460 (permutation216 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18460step0 raw18460; decide +kernel
      have hl : raw18460step0Labels = raw18460Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18460 raw18460Labels permutation216 permutation5
    mixedMoment B raw18460step0 raw18460step0Labels = mixedMoment B raw18460step1 raw18460step1Labels := by
      have ha : raw18460step1 = -raw18460step0 := by apply Matrix.ext; change ∀ i j, raw18460step1 i j = -(raw18460step0 i j); unfold raw18460step1 raw18460step0; decide +kernel
      have hl : raw18460step1Labels = raw18460step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18460step1 raw18460step1Labels = mixedMoment B raw18460step2 raw18460step2Labels := by
      have ha : raw18460step2 = raw18460step1 := by apply Matrix.ext; unfold raw18460step2 raw18460step1; decide +kernel
      have hl : raw18460step1Labels = labelEmbedding8 ∘ raw18460step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18460step1 raw18460step1Labels raw18460step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4885 node4885Labels := by rfl

def raw18461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18461Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18461step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18461step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18461step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18461step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18461 raw18461Labels = mixedMoment B node5447 node5447Labels := by
  calc
    mixedMoment B raw18461 raw18461Labels = mixedMoment B raw18461step0 raw18461step0Labels := by
      have ha : raw18461step0 = (fun i j => raw18461 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18461step0 raw18461; decide +kernel
      have hl : raw18461step0Labels = raw18461Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18461 raw18461Labels permutation176 permutation3
    mixedMoment B raw18461step0 raw18461step0Labels = mixedMoment B raw18461step1 raw18461step1Labels := by
      have ha : raw18461step1 = raw18461step0 := by apply Matrix.ext; unfold raw18461step1 raw18461step0; decide +kernel
      have hl : raw18461step0Labels = labelEmbedding6 ∘ raw18461step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18461step0 raw18461step0Labels raw18461step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5447 node5447Labels := by rfl

def raw18462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18462Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18462step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18462step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18462step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18462step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18462 raw18462Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw18462 raw18462Labels = mixedMoment B raw18462step0 raw18462step0Labels := by
      have ha : raw18462step0 = (fun i j => raw18462 (permutation378 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18462step0 raw18462; decide +kernel
      have hl : raw18462step0Labels = raw18462Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18462 raw18462Labels permutation378 permutation4
    mixedMoment B raw18462step0 raw18462step0Labels = mixedMoment B raw18462step1 raw18462step1Labels := by
      have ha : raw18462step1 = raw18462step0 := by apply Matrix.ext; unfold raw18462step1 raw18462step0; decide +kernel
      have hl : raw18462step0Labels = labelEmbedding7 ∘ raw18462step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18462step0 raw18462step0Labels raw18462step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

def raw18463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw18463Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18463step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18463step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18463step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18463step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18463 raw18463Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw18463 raw18463Labels = mixedMoment B raw18463step0 raw18463step0Labels := by
      have ha : raw18463step0 = (fun i j => raw18463 (permutation374 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18463step0 raw18463; decide +kernel
      have hl : raw18463step0Labels = raw18463Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18463 raw18463Labels permutation374 permutation4
    mixedMoment B raw18463step0 raw18463step0Labels = mixedMoment B raw18463step1 raw18463step1Labels := by
      have ha : raw18463step1 = raw18463step0 := by apply Matrix.ext; unfold raw18463step1 raw18463step0; decide +kernel
      have hl : raw18463step0Labels = labelEmbedding7 ∘ raw18463step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18463step0 raw18463step0Labels raw18463step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

def raw18464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw18464Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18464step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18464step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18464step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18464step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18464 raw18464Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw18464 raw18464Labels = mixedMoment B raw18464step0 raw18464step0Labels := by
      have ha : raw18464step0 = (fun i j => raw18464 (permutation373 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18464step0 raw18464; decide +kernel
      have hl : raw18464step0Labels = raw18464Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18464 raw18464Labels permutation373 permutation4
    mixedMoment B raw18464step0 raw18464step0Labels = mixedMoment B raw18464step1 raw18464step1Labels := by
      have ha : raw18464step1 = raw18464step0 := by apply Matrix.ext; unfold raw18464step1 raw18464step0; decide +kernel
      have hl : raw18464step0Labels = labelEmbedding7 ∘ raw18464step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18464step0 raw18464step0Labels raw18464step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

def raw18465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18465Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18465step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw18465step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18465step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw18465step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18465 raw18465Labels = mixedMoment B node4830 node4830Labels := by
  calc
    mixedMoment B raw18465 raw18465Labels = mixedMoment B raw18465step0 raw18465step0Labels := by
      have ha : raw18465step0 = (fun i j => raw18465 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18465step0 raw18465; decide +kernel
      have hl : raw18465step0Labels = raw18465Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18465 raw18465Labels permutation161 permutation3
    mixedMoment B raw18465step0 raw18465step0Labels = mixedMoment B raw18465step1 raw18465step1Labels := by
      have ha : raw18465step1 = raw18465step0 := by apply Matrix.ext; unfold raw18465step1 raw18465step0; decide +kernel
      have hl : raw18465step0Labels = labelEmbedding6 ∘ raw18465step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18465step0 raw18465step0Labels raw18465step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4830 node4830Labels := by rfl

def raw18466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18466Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18466step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def raw18466step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18466step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def raw18466step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18466 raw18466Labels = mixedMoment B node5277 node5277Labels := by
  calc
    mixedMoment B raw18466 raw18466Labels = mixedMoment B raw18466step0 raw18466step0Labels := by
      have ha : raw18466step0 = (fun i j => raw18466 (permutation394 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18466step0 raw18466; decide +kernel
      have hl : raw18466step0Labels = raw18466Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18466 raw18466Labels permutation394 permutation4
    mixedMoment B raw18466step0 raw18466step0Labels = mixedMoment B raw18466step1 raw18466step1Labels := by
      have ha : raw18466step1 = raw18466step0 := by apply Matrix.ext; unfold raw18466step1 raw18466step0; decide +kernel
      have hl : raw18466step0Labels = labelEmbedding7 ∘ raw18466step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18466step0 raw18466step0Labels raw18466step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5277 node5277Labels := by rfl

def raw18467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18467Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18467step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18467step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18467step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18467step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18467 raw18467Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw18467 raw18467Labels = mixedMoment B raw18467step0 raw18467step0Labels := by
      have ha : raw18467step0 = (fun i j => raw18467 (permutation378 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18467step0 raw18467; decide +kernel
      have hl : raw18467step0Labels = raw18467Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18467 raw18467Labels permutation378 permutation4
    mixedMoment B raw18467step0 raw18467step0Labels = mixedMoment B raw18467step1 raw18467step1Labels := by
      have ha : raw18467step1 = raw18467step0 := by apply Matrix.ext; unfold raw18467step1 raw18467step0; decide +kernel
      have hl : raw18467step0Labels = labelEmbedding7 ∘ raw18467step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18467step0 raw18467step0Labels raw18467step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5251 node5251Labels := by rfl

def raw18468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw18468Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18468step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18468step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18468step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18468step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18468 raw18468Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw18468 raw18468Labels = mixedMoment B raw18468step0 raw18468step0Labels := by
      have ha : raw18468step0 = (fun i j => raw18468 (permutation374 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18468step0 raw18468; decide +kernel
      have hl : raw18468step0Labels = raw18468Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18468 raw18468Labels permutation374 permutation4
    mixedMoment B raw18468step0 raw18468step0Labels = mixedMoment B raw18468step1 raw18468step1Labels := by
      have ha : raw18468step1 = raw18468step0 := by apply Matrix.ext; unfold raw18468step1 raw18468step0; decide +kernel
      have hl : raw18468step0Labels = labelEmbedding7 ∘ raw18468step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18468step0 raw18468step0Labels raw18468step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5251 node5251Labels := by rfl

def raw18469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw18469Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18469step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18469step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18469step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18469step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18469 raw18469Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw18469 raw18469Labels = mixedMoment B raw18469step0 raw18469step0Labels := by
      have ha : raw18469step0 = (fun i j => raw18469 (permutation373 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18469step0 raw18469; decide +kernel
      have hl : raw18469step0Labels = raw18469Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18469 raw18469Labels permutation373 permutation4
    mixedMoment B raw18469step0 raw18469step0Labels = mixedMoment B raw18469step1 raw18469step1Labels := by
      have ha : raw18469step1 = raw18469step0 := by apply Matrix.ext; unfold raw18469step1 raw18469step0; decide +kernel
      have hl : raw18469step0Labels = labelEmbedding7 ∘ raw18469step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18469step0 raw18469step0Labels raw18469step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5251 node5251Labels := by rfl

def raw18470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18470Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18470step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18470step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18470step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18470step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18470 raw18470Labels = mixedMoment B node4815 node4815Labels := by
  calc
    mixedMoment B raw18470 raw18470Labels = mixedMoment B raw18470step0 raw18470step0Labels := by
      have ha : raw18470step0 = (fun i j => raw18470 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18470step0 raw18470; decide +kernel
      have hl : raw18470step0Labels = raw18470Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18470 raw18470Labels permutation155 permutation3
    mixedMoment B raw18470step0 raw18470step0Labels = mixedMoment B raw18470step1 raw18470step1Labels := by
      have ha : raw18470step1 = raw18470step0 := by apply Matrix.ext; unfold raw18470step1 raw18470step0; decide +kernel
      have hl : raw18470step0Labels = labelEmbedding6 ∘ raw18470step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18470step0 raw18470step0Labels raw18470step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4815 node4815Labels := by rfl

def raw18471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18471Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18471step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18471step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18471step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18471step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18471 raw18471Labels = mixedMoment B node5359 node5359Labels := by
  calc
    mixedMoment B raw18471 raw18471Labels = mixedMoment B raw18471step0 raw18471step0Labels := by
      have ha : raw18471step0 = (fun i j => raw18471 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18471step0 raw18471; decide +kernel
      have hl : raw18471step0Labels = raw18471Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18471 raw18471Labels permutation155 permutation3
    mixedMoment B raw18471step0 raw18471step0Labels = mixedMoment B raw18471step1 raw18471step1Labels := by
      have ha : raw18471step1 = raw18471step0 := by apply Matrix.ext; unfold raw18471step1 raw18471step0; decide +kernel
      have hl : raw18471step0Labels = labelEmbedding6 ∘ raw18471step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18471step0 raw18471step0Labels raw18471step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5359 node5359Labels := by rfl

def raw18472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18472Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18472step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18472step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18472step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18472step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18472 raw18472Labels = mixedMoment B node5422 node5422Labels := by
  calc
    mixedMoment B raw18472 raw18472Labels = mixedMoment B raw18472step0 raw18472step0Labels := by
      have ha : raw18472step0 = (fun i j => raw18472 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18472step0 raw18472; decide +kernel
      have hl : raw18472step0Labels = raw18472Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18472 raw18472Labels permutation155 permutation3
    mixedMoment B raw18472step0 raw18472step0Labels = mixedMoment B raw18472step1 raw18472step1Labels := by
      have ha : raw18472step1 = raw18472step0 := by apply Matrix.ext; unfold raw18472step1 raw18472step0; decide +kernel
      have hl : raw18472step0Labels = labelEmbedding6 ∘ raw18472step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18472step0 raw18472step0Labels raw18472step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5422 node5422Labels := by rfl

def raw18473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1]]
def raw18473Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18473step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18473step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18473step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18473step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18473step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18473step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18473 raw18473Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw18473 raw18473Labels = mixedMoment B raw18473step0 raw18473step0Labels := by
      have ha : raw18473step0 = (fun i j => raw18473 (permutation229 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18473step0 raw18473; decide +kernel
      have hl : raw18473step0Labels = raw18473Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18473 raw18473Labels permutation229 permutation5
    mixedMoment B raw18473step0 raw18473step0Labels = mixedMoment B raw18473step1 raw18473step1Labels := by
      have ha : raw18473step1 = -raw18473step0 := by apply Matrix.ext; change ∀ i j, raw18473step1 i j = -(raw18473step0 i j); unfold raw18473step1 raw18473step0; decide +kernel
      have hl : raw18473step1Labels = raw18473step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18473step1 raw18473step1Labels = mixedMoment B raw18473step2 raw18473step2Labels := by
      have ha : raw18473step2 = raw18473step1 := by apply Matrix.ext; unfold raw18473step2 raw18473step1; decide +kernel
      have hl : raw18473step1Labels = labelEmbedding8 ∘ raw18473step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18473step1 raw18473step1Labels raw18473step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw18474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1]]
def raw18474Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18474step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18474step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18474step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18474step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18474step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18474step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18474 raw18474Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw18474 raw18474Labels = mixedMoment B raw18474step0 raw18474step0Labels := by
      have ha : raw18474step0 = (fun i j => raw18474 (permutation251 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18474step0 raw18474; decide +kernel
      have hl : raw18474step0Labels = raw18474Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18474 raw18474Labels permutation251 permutation5
    mixedMoment B raw18474step0 raw18474step0Labels = mixedMoment B raw18474step1 raw18474step1Labels := by
      have ha : raw18474step1 = -raw18474step0 := by apply Matrix.ext; change ∀ i j, raw18474step1 i j = -(raw18474step0 i j); unfold raw18474step1 raw18474step0; decide +kernel
      have hl : raw18474step1Labels = raw18474step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18474step1 raw18474step1Labels = mixedMoment B raw18474step2 raw18474step2Labels := by
      have ha : raw18474step2 = raw18474step1 := by apply Matrix.ext; unfold raw18474step2 raw18474step1; decide +kernel
      have hl : raw18474step1Labels = labelEmbedding8 ∘ raw18474step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18474step1 raw18474step1Labels raw18474step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw18475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw18475Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18475step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18475step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18475step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18475step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18475 raw18475Labels = mixedMoment B node4815 node4815Labels := by
  calc
    mixedMoment B raw18475 raw18475Labels = mixedMoment B raw18475step0 raw18475step0Labels := by
      have ha : raw18475step0 = (fun i j => raw18475 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18475step0 raw18475; decide +kernel
      have hl : raw18475step0Labels = raw18475Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18475 raw18475Labels permutation153 permutation3
    mixedMoment B raw18475step0 raw18475step0Labels = mixedMoment B raw18475step1 raw18475step1Labels := by
      have ha : raw18475step1 = raw18475step0 := by apply Matrix.ext; unfold raw18475step1 raw18475step0; decide +kernel
      have hl : raw18475step0Labels = labelEmbedding6 ∘ raw18475step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18475step0 raw18475step0Labels raw18475step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4815 node4815Labels := by rfl

def raw18476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw18476Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18476step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18476step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18476step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18476step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18476 raw18476Labels = mixedMoment B node5359 node5359Labels := by
  calc
    mixedMoment B raw18476 raw18476Labels = mixedMoment B raw18476step0 raw18476step0Labels := by
      have ha : raw18476step0 = (fun i j => raw18476 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18476step0 raw18476; decide +kernel
      have hl : raw18476step0Labels = raw18476Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18476 raw18476Labels permutation153 permutation3
    mixedMoment B raw18476step0 raw18476step0Labels = mixedMoment B raw18476step1 raw18476step1Labels := by
      have ha : raw18476step1 = raw18476step0 := by apply Matrix.ext; unfold raw18476step1 raw18476step0; decide +kernel
      have hl : raw18476step0Labels = labelEmbedding6 ∘ raw18476step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18476step0 raw18476step0Labels raw18476step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5359 node5359Labels := by rfl

def raw18477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw18477Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18477step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18477step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18477step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18477step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18477 raw18477Labels = mixedMoment B node5422 node5422Labels := by
  calc
    mixedMoment B raw18477 raw18477Labels = mixedMoment B raw18477step0 raw18477step0Labels := by
      have ha : raw18477step0 = (fun i j => raw18477 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18477step0 raw18477; decide +kernel
      have hl : raw18477step0Labels = raw18477Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18477 raw18477Labels permutation153 permutation3
    mixedMoment B raw18477step0 raw18477step0Labels = mixedMoment B raw18477step1 raw18477step1Labels := by
      have ha : raw18477step1 = raw18477step0 := by apply Matrix.ext; unfold raw18477step1 raw18477step0; decide +kernel
      have hl : raw18477step0Labels = labelEmbedding6 ∘ raw18477step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18477step0 raw18477step0Labels raw18477step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5422 node5422Labels := by rfl

def raw18478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1]]
def raw18478Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18478step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18478step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18478step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18478step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18478step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18478step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18478 raw18478Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw18478 raw18478Labels = mixedMoment B raw18478step0 raw18478step0Labels := by
      have ha : raw18478step0 = (fun i j => raw18478 (permutation205 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18478step0 raw18478; decide +kernel
      have hl : raw18478step0Labels = raw18478Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18478 raw18478Labels permutation205 permutation5
    mixedMoment B raw18478step0 raw18478step0Labels = mixedMoment B raw18478step1 raw18478step1Labels := by
      have ha : raw18478step1 = -raw18478step0 := by apply Matrix.ext; change ∀ i j, raw18478step1 i j = -(raw18478step0 i j); unfold raw18478step1 raw18478step0; decide +kernel
      have hl : raw18478step1Labels = raw18478step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18478step1 raw18478step1Labels = mixedMoment B raw18478step2 raw18478step2Labels := by
      have ha : raw18478step2 = raw18478step1 := by apply Matrix.ext; unfold raw18478step2 raw18478step1; decide +kernel
      have hl : raw18478step1Labels = labelEmbedding8 ∘ raw18478step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18478step1 raw18478step1Labels raw18478step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw18479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1]]
def raw18479Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18479step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18479step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18479step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18479step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18479step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18479step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18479 raw18479Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw18479 raw18479Labels = mixedMoment B raw18479step0 raw18479step0Labels := by
      have ha : raw18479step0 = (fun i j => raw18479 (permutation249 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18479step0 raw18479; decide +kernel
      have hl : raw18479step0Labels = raw18479Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18479 raw18479Labels permutation249 permutation5
    mixedMoment B raw18479step0 raw18479step0Labels = mixedMoment B raw18479step1 raw18479step1Labels := by
      have ha : raw18479step1 = -raw18479step0 := by apply Matrix.ext; change ∀ i j, raw18479step1 i j = -(raw18479step0 i j); unfold raw18479step1 raw18479step0; decide +kernel
      have hl : raw18479step1Labels = raw18479step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18479step1 raw18479step1Labels = mixedMoment B raw18479step2 raw18479step2Labels := by
      have ha : raw18479step2 = raw18479step1 := by apply Matrix.ext; unfold raw18479step2 raw18479step1; decide +kernel
      have hl : raw18479step1Labels = labelEmbedding8 ∘ raw18479step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18479step1 raw18479step1Labels raw18479step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw18480 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18480Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18480step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18480step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18480step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18480step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18480 raw18480Labels = mixedMoment B node4815 node4815Labels := by
  calc
    mixedMoment B raw18480 raw18480Labels = mixedMoment B raw18480step0 raw18480step0Labels := by
      have ha : raw18480step0 = (fun i j => raw18480 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18480step0 raw18480; decide +kernel
      have hl : raw18480step0Labels = raw18480Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18480 raw18480Labels permutation152 permutation3
    mixedMoment B raw18480step0 raw18480step0Labels = mixedMoment B raw18480step1 raw18480step1Labels := by
      have ha : raw18480step1 = raw18480step0 := by apply Matrix.ext; unfold raw18480step1 raw18480step0; decide +kernel
      have hl : raw18480step0Labels = labelEmbedding6 ∘ raw18480step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18480step0 raw18480step0Labels raw18480step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4815 node4815Labels := by rfl

def raw18481 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18481Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18481step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18481step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18481step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18481step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18481 raw18481Labels = mixedMoment B node5359 node5359Labels := by
  calc
    mixedMoment B raw18481 raw18481Labels = mixedMoment B raw18481step0 raw18481step0Labels := by
      have ha : raw18481step0 = (fun i j => raw18481 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18481step0 raw18481; decide +kernel
      have hl : raw18481step0Labels = raw18481Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18481 raw18481Labels permutation152 permutation3
    mixedMoment B raw18481step0 raw18481step0Labels = mixedMoment B raw18481step1 raw18481step1Labels := by
      have ha : raw18481step1 = raw18481step0 := by apply Matrix.ext; unfold raw18481step1 raw18481step0; decide +kernel
      have hl : raw18481step0Labels = labelEmbedding6 ∘ raw18481step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18481step0 raw18481step0Labels raw18481step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5359 node5359Labels := by rfl

def raw18482 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18482Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18482step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18482step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18482step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw18482step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18482 raw18482Labels = mixedMoment B node5422 node5422Labels := by
  calc
    mixedMoment B raw18482 raw18482Labels = mixedMoment B raw18482step0 raw18482step0Labels := by
      have ha : raw18482step0 = (fun i j => raw18482 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18482step0 raw18482; decide +kernel
      have hl : raw18482step0Labels = raw18482Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18482 raw18482Labels permutation152 permutation3
    mixedMoment B raw18482step0 raw18482step0Labels = mixedMoment B raw18482step1 raw18482step1Labels := by
      have ha : raw18482step1 = raw18482step0 := by apply Matrix.ext; unfold raw18482step1 raw18482step0; decide +kernel
      have hl : raw18482step0Labels = labelEmbedding6 ∘ raw18482step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18482step0 raw18482step0Labels raw18482step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5422 node5422Labels := by rfl

def raw18483 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18483Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18483step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18483step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18483step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18483step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18483step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18483step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18483 raw18483Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw18483 raw18483Labels = mixedMoment B raw18483step0 raw18483step0Labels := by
      have ha : raw18483step0 = (fun i j => raw18483 (permutation203 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18483step0 raw18483; decide +kernel
      have hl : raw18483step0Labels = raw18483Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18483 raw18483Labels permutation203 permutation5
    mixedMoment B raw18483step0 raw18483step0Labels = mixedMoment B raw18483step1 raw18483step1Labels := by
      have ha : raw18483step1 = -raw18483step0 := by apply Matrix.ext; change ∀ i j, raw18483step1 i j = -(raw18483step0 i j); unfold raw18483step1 raw18483step0; decide +kernel
      have hl : raw18483step1Labels = raw18483step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18483step1 raw18483step1Labels = mixedMoment B raw18483step2 raw18483step2Labels := by
      have ha : raw18483step2 = raw18483step1 := by apply Matrix.ext; unfold raw18483step2 raw18483step1; decide +kernel
      have hl : raw18483step1Labels = labelEmbedding8 ∘ raw18483step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18483step1 raw18483step1Labels raw18483step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw18484 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw18484Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18484step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18484step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18484step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18484step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18484step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18484step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18484 raw18484Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw18484 raw18484Labels = mixedMoment B raw18484step0 raw18484step0Labels := by
      have ha : raw18484step0 = (fun i j => raw18484 (permutation227 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18484step0 raw18484; decide +kernel
      have hl : raw18484step0Labels = raw18484Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18484 raw18484Labels permutation227 permutation5
    mixedMoment B raw18484step0 raw18484step0Labels = mixedMoment B raw18484step1 raw18484step1Labels := by
      have ha : raw18484step1 = -raw18484step0 := by apply Matrix.ext; change ∀ i j, raw18484step1 i j = -(raw18484step0 i j); unfold raw18484step1 raw18484step0; decide +kernel
      have hl : raw18484step1Labels = raw18484step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18484step1 raw18484step1Labels = mixedMoment B raw18484step2 raw18484step2Labels := by
      have ha : raw18484step2 = raw18484step1 := by apply Matrix.ext; unfold raw18484step2 raw18484step1; decide +kernel
      have hl : raw18484step1Labels = labelEmbedding8 ∘ raw18484step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18484step1 raw18484step1Labels raw18484step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw18485 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18485Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18485step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18485step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18485step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18485step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18485 raw18485Labels = mixedMoment B node5440 node5440Labels := by
  calc
    mixedMoment B raw18485 raw18485Labels = mixedMoment B raw18485step0 raw18485step0Labels := by
      have hz : ∀ j, raw18485 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18485step0 = (fun i j => raw18485 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18485step0 raw18485; decide +kernel
      have hl : raw18485step0Labels = raw18485Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18485 raw18485Labels permutation346 hz
    mixedMoment B raw18485step0 raw18485step0Labels = mixedMoment B raw18485step1 raw18485step1Labels := by
      have ha : raw18485step1 = (fun i j => raw18485step0 (permutation60 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18485step1 raw18485step0; decide +kernel
      have hl : raw18485step1Labels = raw18485step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18485step0 raw18485step0Labels permutation60 permutation2
    _ = mixedMoment B node5440 node5440Labels := by rfl

def raw18486 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18486Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18486step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18486step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18486step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18486step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18486step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18486step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18486 raw18486Labels = mixedMoment B node5489 node5489Labels := by
  calc
    mixedMoment B raw18486 raw18486Labels = mixedMoment B raw18486step0 raw18486step0Labels := by
      have ha : raw18486step0 = (fun i j => raw18486 (permutation269 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18486step0 raw18486; decide +kernel
      have hl : raw18486step0Labels = raw18486Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18486 raw18486Labels permutation269 permutation7
    mixedMoment B raw18486step0 raw18486step0Labels = mixedMoment B raw18486step1 raw18486step1Labels := by
      have ha : raw18486step1 = -raw18486step0 := by apply Matrix.ext; change ∀ i j, raw18486step1 i j = -(raw18486step0 i j); unfold raw18486step1 raw18486step0; decide +kernel
      have hl : raw18486step1Labels = raw18486step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18486step1 raw18486step1Labels = mixedMoment B raw18486step2 raw18486step2Labels := by
      have ha : raw18486step2 = raw18486step1 := by apply Matrix.ext; unfold raw18486step2 raw18486step1; decide +kernel
      have hl : raw18486step1Labels = labelEmbedding10 ∘ raw18486step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18486step1 raw18486step1Labels raw18486step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5489 node5489Labels := by rfl

def raw18487 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw18487Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw18487step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18487step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18487step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18487step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18487step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18487step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18487step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18487 raw18487Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw18487 raw18487Labels = mixedMoment B raw18487step0 raw18487step0Labels := by
      have hz : ∀ j, raw18487 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18487step0 = (fun i j => raw18487 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18487step0 raw18487; decide +kernel
      have hl : raw18487step0Labels = raw18487Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18487 raw18487Labels permutation346 hz
    mixedMoment B raw18487step0 raw18487step0Labels = mixedMoment B raw18487step1 raw18487step1Labels := by
      have ha : raw18487step1 = (fun i j => raw18487step0 (permutation74 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18487step1 raw18487step0; decide +kernel
      have hl : raw18487step1Labels = raw18487step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18487step0 raw18487step0Labels permutation74 permutation6
    mixedMoment B raw18487step1 raw18487step1Labels = mixedMoment B raw18487step2 raw18487step2Labels := by
      have ha : raw18487step2 = -raw18487step1 := by apply Matrix.ext; change ∀ i j, raw18487step2 i j = -(raw18487step1 i j); unfold raw18487step2 raw18487step1; decide +kernel
      have hl : raw18487step2Labels = raw18487step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18487step2 raw18487step2Labels = mixedMoment B raw18487step3 raw18487step3Labels := by
      have ha : raw18487step3 = raw18487step2 := by apply Matrix.ext; unfold raw18487step3 raw18487step2; decide +kernel
      have hl : raw18487step2Labels = labelEmbedding9 ∘ raw18487step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18487step2 raw18487step2Labels raw18487step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw18488 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw18488Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18488step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18488step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18488step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1]]
def raw18488step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18488step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18488step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18488step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18488step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18488step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18488step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18488 raw18488Labels = mixedMoment B node5493 node5493Labels := by
  calc
    mixedMoment B raw18488 raw18488Labels = mixedMoment B raw18488step0 raw18488step0Labels := by
      have hz : ∀ j, raw18488 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw18488step0 = (fun i j => raw18488 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw18488step0 raw18488; decide +kernel
      have hl : raw18488step0Labels = raw18488Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18488 raw18488Labels permutation590 hz
    mixedMoment B raw18488step0 raw18488step0Labels = mixedMoment B raw18488step1 raw18488step1Labels := by
      have hz : ∀ j, raw18488step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18488step1 = (fun i j => raw18488step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18488step1 raw18488step0; decide +kernel
      have hl : raw18488step1Labels = raw18488step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18488step0 raw18488step0Labels permutation80 hz
    mixedMoment B raw18488step1 raw18488step1Labels = mixedMoment B raw18488step2 raw18488step2Labels := by
      have ha : raw18488step2 = (fun i j => raw18488step1 (permutation14 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18488step2 raw18488step1; decide +kernel
      have hl : raw18488step2Labels = raw18488step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18488step1 raw18488step1Labels permutation14 permutation7
    mixedMoment B raw18488step2 raw18488step2Labels = mixedMoment B raw18488step3 raw18488step3Labels := by
      have ha : raw18488step3 = -raw18488step2 := by apply Matrix.ext; change ∀ i j, raw18488step3 i j = -(raw18488step2 i j); unfold raw18488step3 raw18488step2; decide +kernel
      have hl : raw18488step3Labels = raw18488step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18488step3 raw18488step3Labels = mixedMoment B raw18488step4 raw18488step4Labels := by
      have ha : raw18488step4 = raw18488step3 := by apply Matrix.ext; unfold raw18488step4 raw18488step3; decide +kernel
      have hl : raw18488step3Labels = labelEmbedding10 ∘ raw18488step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18488step3 raw18488step3Labels raw18488step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5493 node5493Labels := by rfl

def raw18489 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18489Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18489step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18489step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18489step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw18489step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18489step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18489step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18489step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18489step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18489 raw18489Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw18489 raw18489Labels = mixedMoment B raw18489step0 raw18489step0Labels := by
      have hz : ∀ j, raw18489 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18489step0 = (fun i j => raw18489 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18489step0 raw18489; decide +kernel
      have hl : raw18489step0Labels = raw18489Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18489 raw18489Labels permutation346 hz
    mixedMoment B raw18489step0 raw18489step0Labels = mixedMoment B raw18489step1 raw18489step1Labels := by
      have ha : raw18489step1 = (fun i j => raw18489step0 (permutation41 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18489step1 raw18489step0; decide +kernel
      have hl : raw18489step1Labels = raw18489step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18489step0 raw18489step0Labels permutation41 permutation5
    mixedMoment B raw18489step1 raw18489step1Labels = mixedMoment B raw18489step2 raw18489step2Labels := by
      have ha : raw18489step2 = -raw18489step1 := by apply Matrix.ext; change ∀ i j, raw18489step2 i j = -(raw18489step1 i j); unfold raw18489step2 raw18489step1; decide +kernel
      have hl : raw18489step2Labels = raw18489step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18489step2 raw18489step2Labels = mixedMoment B raw18489step3 raw18489step3Labels := by
      have ha : raw18489step3 = raw18489step2 := by apply Matrix.ext; unfold raw18489step3 raw18489step2; decide +kernel
      have hl : raw18489step2Labels = labelEmbedding8 ∘ raw18489step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18489step2 raw18489step2Labels raw18489step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

def raw18490 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18490Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18490step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw18490step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18490step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18490step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18490step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18490step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18490 raw18490Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw18490 raw18490Labels = mixedMoment B raw18490step0 raw18490step0Labels := by
      have ha : raw18490step0 = (fun i j => raw18490 (permutation185 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18490step0 raw18490; decide +kernel
      have hl : raw18490step0Labels = raw18490Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18490 raw18490Labels permutation185 permutation5
    mixedMoment B raw18490step0 raw18490step0Labels = mixedMoment B raw18490step1 raw18490step1Labels := by
      have ha : raw18490step1 = -raw18490step0 := by apply Matrix.ext; change ∀ i j, raw18490step1 i j = -(raw18490step0 i j); unfold raw18490step1 raw18490step0; decide +kernel
      have hl : raw18490step1Labels = raw18490step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18490step1 raw18490step1Labels = mixedMoment B raw18490step2 raw18490step2Labels := by
      have ha : raw18490step2 = raw18490step1 := by apply Matrix.ext; unfold raw18490step2 raw18490step1; decide +kernel
      have hl : raw18490step1Labels = labelEmbedding8 ∘ raw18490step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18490step1 raw18490step1Labels raw18490step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5406 node5406Labels := by rfl

def raw18491 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw18491Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18491step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw18491step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18491step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18491step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18491step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18491step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18491 raw18491Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw18491 raw18491Labels = mixedMoment B raw18491step0 raw18491step0Labels := by
      have hz : ∀ j, raw18491 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18491step0 = (fun i j => raw18491 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18491step0 raw18491; decide +kernel
      have hl : raw18491step0Labels = raw18491Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18491 raw18491Labels permutation346 hz
    mixedMoment B raw18491step0 raw18491step0Labels = mixedMoment B raw18491step1 raw18491step1Labels := by
      have ha : raw18491step1 = (fun i j => raw18491step0 (permutation77 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18491step1 raw18491step0; decide +kernel
      have hl : raw18491step1Labels = raw18491step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18491step0 raw18491step0Labels permutation77 permutation4
    mixedMoment B raw18491step1 raw18491step1Labels = mixedMoment B raw18491step2 raw18491step2Labels := by
      have ha : raw18491step2 = raw18491step1 := by apply Matrix.ext; unfold raw18491step2 raw18491step1; decide +kernel
      have hl : raw18491step1Labels = labelEmbedding7 ∘ raw18491step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18491step1 raw18491step1Labels raw18491step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5435 node5435Labels := by rfl

def raw18492 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw18492Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18492step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18492step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw18492step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18492step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18492step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18492step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18492step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18492 raw18492Labels = mixedMoment B node5453 node5453Labels := by
  calc
    mixedMoment B raw18492 raw18492Labels = mixedMoment B raw18492step0 raw18492step0Labels := by
      have hz : ∀ j, raw18492 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw18492step0 = (fun i j => raw18492 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw18492step0 raw18492; decide +kernel
      have hl : raw18492step0Labels = raw18492Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18492 raw18492Labels permutation590 hz
    mixedMoment B raw18492step0 raw18492step0Labels = mixedMoment B raw18492step1 raw18492step1Labels := by
      have hz : ∀ j, raw18492step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18492step1 = (fun i j => raw18492step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18492step1 raw18492step0; decide +kernel
      have hl : raw18492step1Labels = raw18492step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18492step0 raw18492step0Labels permutation80 hz
    mixedMoment B raw18492step1 raw18492step1Labels = mixedMoment B raw18492step2 raw18492step2Labels := by
      have ha : raw18492step2 = (fun i j => raw18492step1 (permutation17 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18492step2 raw18492step1; decide +kernel
      have hl : raw18492step2Labels = raw18492step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18492step1 raw18492step1Labels permutation17 permutation4
    mixedMoment B raw18492step2 raw18492step2Labels = mixedMoment B raw18492step3 raw18492step3Labels := by
      have ha : raw18492step3 = raw18492step2 := by apply Matrix.ext; unfold raw18492step3 raw18492step2; decide +kernel
      have hl : raw18492step2Labels = labelEmbedding7 ∘ raw18492step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18492step2 raw18492step2Labels raw18492step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5453 node5453Labels := by rfl

def raw18493 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18493Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18493step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18493step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18493step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18493step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18493 raw18493Labels = mixedMoment B node4864 node4864Labels := by
  calc
    mixedMoment B raw18493 raw18493Labels = mixedMoment B raw18493step0 raw18493step0Labels := by
      have ha : raw18493step0 = (fun i j => raw18493 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18493step0 raw18493; decide +kernel
      have hl : raw18493step0Labels = raw18493Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18493 raw18493Labels permutation160 permutation3
    mixedMoment B raw18493step0 raw18493step0Labels = mixedMoment B raw18493step1 raw18493step1Labels := by
      have ha : raw18493step1 = raw18493step0 := by apply Matrix.ext; unfold raw18493step1 raw18493step0; decide +kernel
      have hl : raw18493step0Labels = labelEmbedding6 ∘ raw18493step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18493step0 raw18493step0Labels raw18493step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4864 node4864Labels := by rfl

def raw18494 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18494Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18494step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18494step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18494 raw18494Labels = mixedMoment B node5386 node5386Labels := by
  calc
    mixedMoment B raw18494 raw18494Labels = mixedMoment B raw18494step0 raw18494step0Labels := by
      have ha : raw18494step0 = (fun i j => raw18494 (permutation269 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18494step0 raw18494; decide +kernel
      have hl : raw18494step0Labels = raw18494Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18494 raw18494Labels permutation269 permutation2
    _ = mixedMoment B node5386 node5386Labels := by rfl

def raw18495 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw18495Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18495step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18495step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18495step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18495step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18495step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18495step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18495 raw18495Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw18495 raw18495Labels = mixedMoment B raw18495step0 raw18495step0Labels := by
      have ha : raw18495step0 = (fun i j => raw18495 (permutation234 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18495step0 raw18495; decide +kernel
      have hl : raw18495step0Labels = raw18495Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18495 raw18495Labels permutation234 permutation5
    mixedMoment B raw18495step0 raw18495step0Labels = mixedMoment B raw18495step1 raw18495step1Labels := by
      have ha : raw18495step1 = -raw18495step0 := by apply Matrix.ext; change ∀ i j, raw18495step1 i j = -(raw18495step0 i j); unfold raw18495step1 raw18495step0; decide +kernel
      have hl : raw18495step1Labels = raw18495step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18495step1 raw18495step1Labels = mixedMoment B raw18495step2 raw18495step2Labels := by
      have ha : raw18495step2 = raw18495step1 := by apply Matrix.ext; unfold raw18495step2 raw18495step1; decide +kernel
      have hl : raw18495step1Labels = labelEmbedding8 ∘ raw18495step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18495step1 raw18495step1Labels raw18495step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

def raw18496 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw18496Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18496step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18496step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18496step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18496step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18496step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18496step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18496 raw18496Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw18496 raw18496Labels = mixedMoment B raw18496step0 raw18496step0Labels := by
      have hz : ∀ j, raw18496 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw18496step0 = (fun i j => raw18496 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw18496step0 raw18496; decide +kernel
      have hl : raw18496step0Labels = raw18496Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18496 raw18496Labels permutation590 hz
    mixedMoment B raw18496step0 raw18496step0Labels = mixedMoment B raw18496step1 raw18496step1Labels := by
      have ha : raw18496step1 = (fun i j => raw18496step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18496step1 raw18496step0; decide +kernel
      have hl : raw18496step1Labels = raw18496step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18496step0 raw18496step0Labels permutation35 permutation3
    mixedMoment B raw18496step1 raw18496step1Labels = mixedMoment B raw18496step2 raw18496step2Labels := by
      have ha : raw18496step2 = raw18496step1 := by apply Matrix.ext; unfold raw18496step2 raw18496step1; decide +kernel
      have hl : raw18496step1Labels = labelEmbedding6 ∘ raw18496step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18496step1 raw18496step1Labels raw18496step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw18497 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18497Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18497step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18497step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18497step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18497step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18497step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18497step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18497 raw18497Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw18497 raw18497Labels = mixedMoment B raw18497step0 raw18497step0Labels := by
      have hz : ∀ j, raw18497 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18497step0 = (fun i j => raw18497 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18497step0 raw18497; decide +kernel
      have hl : raw18497step0Labels = raw18497Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18497 raw18497Labels permutation346 hz
    mixedMoment B raw18497step0 raw18497step0Labels = mixedMoment B raw18497step1 raw18497step1Labels := by
      have ha : raw18497step1 = (fun i j => raw18497step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18497step1 raw18497step0; decide +kernel
      have hl : raw18497step1Labels = raw18497step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18497step0 raw18497step0Labels permutation35 permutation3
    mixedMoment B raw18497step1 raw18497step1Labels = mixedMoment B raw18497step2 raw18497step2Labels := by
      have ha : raw18497step2 = raw18497step1 := by apply Matrix.ext; unfold raw18497step2 raw18497step1; decide +kernel
      have hl : raw18497step1Labels = labelEmbedding6 ∘ raw18497step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18497step1 raw18497step1Labels raw18497step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4866 node4866Labels := by rfl

def raw18498 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18498Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18498step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18498step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18498step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18498step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18498 raw18498Labels = mixedMoment B node5388 node5388Labels := by
  calc
    mixedMoment B raw18498 raw18498Labels = mixedMoment B raw18498step0 raw18498step0Labels := by
      have hz : ∀ j, raw18498 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18498step0 = (fun i j => raw18498 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18498step0 raw18498; decide +kernel
      have hl : raw18498step0Labels = raw18498Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18498 raw18498Labels permutation346 hz
    mixedMoment B raw18498step0 raw18498step0Labels = mixedMoment B raw18498step1 raw18498step1Labels := by
      have ha : raw18498step1 = (fun i j => raw18498step0 (permutation61 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18498step1 raw18498step0; decide +kernel
      have hl : raw18498step1Labels = raw18498step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18498step0 raw18498step0Labels permutation61 permutation2
    _ = mixedMoment B node5388 node5388Labels := by rfl

def raw18499 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18499Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18499step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18499step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18499step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18499step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18499 raw18499Labels = mixedMoment B node5401 node5401Labels := by
  calc
    mixedMoment B raw18499 raw18499Labels = mixedMoment B raw18499step0 raw18499step0Labels := by
      have ha : raw18499step0 = (fun i j => raw18499 (permutation179 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18499step0 raw18499; decide +kernel
      have hl : raw18499step0Labels = raw18499Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18499 raw18499Labels permutation179 permutation3
    mixedMoment B raw18499step0 raw18499step0Labels = mixedMoment B raw18499step1 raw18499step1Labels := by
      have ha : raw18499step1 = raw18499step0 := by apply Matrix.ext; unfold raw18499step1 raw18499step0; decide +kernel
      have hl : raw18499step0Labels = labelEmbedding6 ∘ raw18499step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18499step0 raw18499step0Labels raw18499step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5401 node5401Labels := by rfl

def raw18500 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw18500Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18500step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw18500step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18500step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw18500step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18500step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18500step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18500step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18500step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18500 raw18500Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw18500 raw18500Labels = mixedMoment B raw18500step0 raw18500step0Labels := by
      have hz : ∀ j, raw18500 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18500step0 = (fun i j => raw18500 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18500step0 raw18500; decide +kernel
      have hl : raw18500step0Labels = raw18500Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18500 raw18500Labels permutation346 hz
    mixedMoment B raw18500step0 raw18500step0Labels = mixedMoment B raw18500step1 raw18500step1Labels := by
      have ha : raw18500step1 = (fun i j => raw18500step0 (permutation45 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18500step1 raw18500step0; decide +kernel
      have hl : raw18500step1Labels = raw18500step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18500step0 raw18500step0Labels permutation45 permutation5
    mixedMoment B raw18500step1 raw18500step1Labels = mixedMoment B raw18500step2 raw18500step2Labels := by
      have ha : raw18500step2 = -raw18500step1 := by apply Matrix.ext; change ∀ i j, raw18500step2 i j = -(raw18500step1 i j); unfold raw18500step2 raw18500step1; decide +kernel
      have hl : raw18500step2Labels = raw18500step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18500step2 raw18500step2Labels = mixedMoment B raw18500step3 raw18500step3Labels := by
      have ha : raw18500step3 = raw18500step2 := by apply Matrix.ext; unfold raw18500step3 raw18500step2; decide +kernel
      have hl : raw18500step2Labels = labelEmbedding8 ∘ raw18500step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18500step2 raw18500step2Labels raw18500step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw18501 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw18501Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18501step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw18501step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18501step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1]]
def raw18501step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18501step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18501step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18501step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18501step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18501 raw18501Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw18501 raw18501Labels = mixedMoment B raw18501step0 raw18501step0Labels := by
      have hz : ∀ j, raw18501 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw18501step0 = (fun i j => raw18501 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw18501step0 raw18501; decide +kernel
      have hl : raw18501step0Labels = raw18501Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18501 raw18501Labels permutation590 hz
    mixedMoment B raw18501step0 raw18501step0Labels = mixedMoment B raw18501step1 raw18501step1Labels := by
      have hz : ∀ j, raw18501step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18501step1 = (fun i j => raw18501step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18501step1 raw18501step0; decide +kernel
      have hl : raw18501step1Labels = raw18501step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18501step0 raw18501step0Labels permutation80 hz
    mixedMoment B raw18501step1 raw18501step1Labels = mixedMoment B raw18501step2 raw18501step2Labels := by
      have ha : raw18501step2 = (fun i j => raw18501step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18501step2 raw18501step1; decide +kernel
      have hl : raw18501step2Labels = raw18501step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18501step1 raw18501step1Labels permutation9 permutation3
    mixedMoment B raw18501step2 raw18501step2Labels = mixedMoment B raw18501step3 raw18501step3Labels := by
      have ha : raw18501step3 = raw18501step2 := by apply Matrix.ext; unfold raw18501step3 raw18501step2; decide +kernel
      have hl : raw18501step2Labels = labelEmbedding6 ∘ raw18501step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18501step2 raw18501step2Labels raw18501step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5451 node5451Labels := by rfl

def raw18502 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw18502Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18502step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw18502step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18502step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18502step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18502step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18502step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18502 raw18502Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw18502 raw18502Labels = mixedMoment B raw18502step0 raw18502step0Labels := by
      have hz : ∀ j, raw18502 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18502step0 = (fun i j => raw18502 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18502step0 raw18502; decide +kernel
      have hl : raw18502step0Labels = raw18502Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18502 raw18502Labels permutation346 hz
    mixedMoment B raw18502step0 raw18502step0Labels = mixedMoment B raw18502step1 raw18502step1Labels := by
      have ha : raw18502step1 = (fun i j => raw18502step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18502step1 raw18502step0; decide +kernel
      have hl : raw18502step1Labels = raw18502step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18502step0 raw18502step0Labels permutation33 permutation3
    mixedMoment B raw18502step1 raw18502step1Labels = mixedMoment B raw18502step2 raw18502step2Labels := by
      have ha : raw18502step2 = raw18502step1 := by apply Matrix.ext; unfold raw18502step2 raw18502step1; decide +kernel
      have hl : raw18502step1Labels = labelEmbedding6 ∘ raw18502step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18502step1 raw18502step1Labels raw18502step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4866 node4866Labels := by rfl

def raw18503 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw18503Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18503step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw18503step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18503step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18503step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18503 raw18503Labels = mixedMoment B node5388 node5388Labels := by
  calc
    mixedMoment B raw18503 raw18503Labels = mixedMoment B raw18503step0 raw18503step0Labels := by
      have hz : ∀ j, raw18503 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18503step0 = (fun i j => raw18503 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18503step0 raw18503; decide +kernel
      have hl : raw18503step0Labels = raw18503Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18503 raw18503Labels permutation346 hz
    mixedMoment B raw18503step0 raw18503step0Labels = mixedMoment B raw18503step1 raw18503step1Labels := by
      have ha : raw18503step1 = (fun i j => raw18503step0 (permutation60 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18503step1 raw18503step0; decide +kernel
      have hl : raw18503step1Labels = raw18503step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18503step0 raw18503step0Labels permutation60 permutation2
    _ = mixedMoment B node5388 node5388Labels := by rfl

def raw18504 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw18504Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18504step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18504step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18504step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18504step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18504 raw18504Labels = mixedMoment B node5401 node5401Labels := by
  calc
    mixedMoment B raw18504 raw18504Labels = mixedMoment B raw18504step0 raw18504step0Labels := by
      have ha : raw18504step0 = (fun i j => raw18504 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18504step0 raw18504; decide +kernel
      have hl : raw18504step0Labels = raw18504Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18504 raw18504Labels permutation177 permutation3
    mixedMoment B raw18504step0 raw18504step0Labels = mixedMoment B raw18504step1 raw18504step1Labels := by
      have ha : raw18504step1 = raw18504step0 := by apply Matrix.ext; unfold raw18504step1 raw18504step0; decide +kernel
      have hl : raw18504step0Labels = labelEmbedding6 ∘ raw18504step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18504step0 raw18504step0Labels raw18504step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5401 node5401Labels := by rfl

def raw18505 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw18505Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18505step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1]]
def raw18505step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18505step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1]]
def raw18505step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18505step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18505step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18505step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18505step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18505 raw18505Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw18505 raw18505Labels = mixedMoment B raw18505step0 raw18505step0Labels := by
      have hz : ∀ j, raw18505 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw18505step0 = (fun i j => raw18505 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw18505step0 raw18505; decide +kernel
      have hl : raw18505step0Labels = raw18505Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18505 raw18505Labels permutation590 hz
    mixedMoment B raw18505step0 raw18505step0Labels = mixedMoment B raw18505step1 raw18505step1Labels := by
      have hz : ∀ j, raw18505step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18505step1 = (fun i j => raw18505step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18505step1 raw18505step0; decide +kernel
      have hl : raw18505step1Labels = raw18505step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18505step0 raw18505step0Labels permutation80 hz
    mixedMoment B raw18505step1 raw18505step1Labels = mixedMoment B raw18505step2 raw18505step2Labels := by
      have ha : raw18505step2 = (fun i j => raw18505step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18505step2 raw18505step1; decide +kernel
      have hl : raw18505step2Labels = raw18505step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18505step1 raw18505step1Labels permutation8 permutation3
    mixedMoment B raw18505step2 raw18505step2Labels = mixedMoment B raw18505step3 raw18505step3Labels := by
      have ha : raw18505step3 = raw18505step2 := by apply Matrix.ext; unfold raw18505step3 raw18505step2; decide +kernel
      have hl : raw18505step2Labels = labelEmbedding6 ∘ raw18505step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18505step2 raw18505step2Labels raw18505step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5451 node5451Labels := by rfl

def raw18506 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18506Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18506step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18506step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18506step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw18506step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18506step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18506step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18506step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18506step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18506 raw18506Labels = mixedMoment B node5432 node5432Labels := by
  calc
    mixedMoment B raw18506 raw18506Labels = mixedMoment B raw18506step0 raw18506step0Labels := by
      have hz : ∀ j, raw18506 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18506step0 = (fun i j => raw18506 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18506step0 raw18506; decide +kernel
      have hl : raw18506step0Labels = raw18506Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18506 raw18506Labels permutation346 hz
    mixedMoment B raw18506step0 raw18506step0Labels = mixedMoment B raw18506step1 raw18506step1Labels := by
      have ha : raw18506step1 = (fun i j => raw18506step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18506step1 raw18506step0; decide +kernel
      have hl : raw18506step1Labels = raw18506step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18506step0 raw18506step0Labels permutation151 permutation3
    mixedMoment B raw18506step1 raw18506step1Labels = mixedMoment B raw18506step2 raw18506step2Labels := by
      have ha : raw18506step2 = -raw18506step1 := by apply Matrix.ext; change ∀ i j, raw18506step2 i j = -(raw18506step1 i j); unfold raw18506step2 raw18506step1; decide +kernel
      have hl : raw18506step2Labels = raw18506step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18506step2 raw18506step2Labels = mixedMoment B raw18506step3 raw18506step3Labels := by
      have ha : raw18506step3 = raw18506step2 := by apply Matrix.ext; unfold raw18506step3 raw18506step2; decide +kernel
      have hl : raw18506step2Labels = labelEmbedding6 ∘ raw18506step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18506step2 raw18506step2Labels raw18506step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5432 node5432Labels := by rfl

def raw18507 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18507Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18507step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw18507step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18507step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18507step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18507 raw18507Labels = mixedMoment B node5472 node5472Labels := by
  calc
    mixedMoment B raw18507 raw18507Labels = mixedMoment B raw18507step0 raw18507step0Labels := by
      have ha : raw18507step0 = (fun i j => raw18507 (permutation283 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18507step0 raw18507; decide +kernel
      have hl : raw18507step0Labels = raw18507Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18507 raw18507Labels permutation283 permutation2
    mixedMoment B raw18507step0 raw18507step0Labels = mixedMoment B raw18507step1 raw18507step1Labels := by
      have ha : raw18507step1 = -raw18507step0 := by apply Matrix.ext; change ∀ i j, raw18507step1 i j = -(raw18507step0 i j); unfold raw18507step1 raw18507step0; decide +kernel
      have hl : raw18507step1Labels = raw18507step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5472 node5472Labels := by rfl

def raw18508 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18508Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18508step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18508step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18508step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18508step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18508step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18508step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18508 raw18508Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw18508 raw18508Labels = mixedMoment B raw18508step0 raw18508step0Labels := by
      have hz : ∀ j, raw18508 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18508step0 = (fun i j => raw18508 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18508step0 raw18508; decide +kernel
      have hl : raw18508step0Labels = raw18508Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18508 raw18508Labels permutation346 hz
    mixedMoment B raw18508step0 raw18508step0Labels = mixedMoment B raw18508step1 raw18508step1Labels := by
      have ha : raw18508step1 = (fun i j => raw18508step0 (permutation61 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18508step1 raw18508step0; decide +kernel
      have hl : raw18508step1Labels = raw18508step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18508step0 raw18508step0Labels permutation61 permutation2
    mixedMoment B raw18508step1 raw18508step1Labels = mixedMoment B raw18508step2 raw18508step2Labels := by
      have ha : raw18508step2 = -raw18508step1 := by apply Matrix.ext; change ∀ i j, raw18508step2 i j = -(raw18508step1 i j); unfold raw18508step2 raw18508step1; decide +kernel
      have hl : raw18508step2Labels = raw18508step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw18509 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw18509Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw18509step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18509step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18509step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18509step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18509step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18509 raw18509Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw18509 raw18509Labels = mixedMoment B raw18509step0 raw18509step0Labels := by
      have hz : ∀ j, raw18509 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18509step0 = (fun i j => raw18509 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18509step0 raw18509; decide +kernel
      have hl : raw18509step0Labels = raw18509Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18509 raw18509Labels permutation346 hz
    mixedMoment B raw18509step0 raw18509step0Labels = mixedMoment B raw18509step1 raw18509step1Labels := by
      have ha : raw18509step1 = (fun i j => raw18509step0 (permutation60 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18509step1 raw18509step0; decide +kernel
      have hl : raw18509step1Labels = raw18509step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18509step0 raw18509step0Labels permutation60 permutation2
    mixedMoment B raw18509step1 raw18509step1Labels = mixedMoment B raw18509step2 raw18509step2Labels := by
      have ha : raw18509step2 = -raw18509step1 := by apply Matrix.ext; change ∀ i j, raw18509step2 i j = -(raw18509step1 i j); unfold raw18509step2 raw18509step1; decide +kernel
      have hl : raw18509step2Labels = raw18509step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw18510 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18510Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18510step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18510step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18510step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18510step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18510step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18510step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18510 raw18510Labels = mixedMoment B node5474 node5474Labels := by
  calc
    mixedMoment B raw18510 raw18510Labels = mixedMoment B raw18510step0 raw18510step0Labels := by
      have hz : ∀ j, raw18510 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18510step0 = (fun i j => raw18510 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18510step0 raw18510; decide +kernel
      have hl : raw18510step0Labels = raw18510Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18510 raw18510Labels permutation346 hz
    mixedMoment B raw18510step0 raw18510step0Labels = mixedMoment B raw18510step1 raw18510step1Labels := by
      have ha : raw18510step1 = (fun i j => raw18510step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18510step1 raw18510step0; decide +kernel
      have hl : raw18510step1Labels = raw18510step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18510step0 raw18510step0Labels permutation56 permutation2
    mixedMoment B raw18510step1 raw18510step1Labels = mixedMoment B raw18510step2 raw18510step2Labels := by
      have ha : raw18510step2 = -raw18510step1 := by apply Matrix.ext; change ∀ i j, raw18510step2 i j = -(raw18510step1 i j); unfold raw18510step2 raw18510step1; decide +kernel
      have hl : raw18510step2Labels = raw18510step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5474 node5474Labels := by rfl

def raw18511 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -2, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18511Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![3, -2, -1], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18511step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18511step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -2, 3]]
def raw18511step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18511step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw18511step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18511step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw18511step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18511 raw18511Labels = mixedMoment B node5270 node5270Labels := by
  calc
    mixedMoment B raw18511 raw18511Labels = mixedMoment B raw18511step0 raw18511step0Labels := by
      have hz : ∀ j, raw18511 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18511step0 = (fun i j => raw18511 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18511step0 raw18511; decide +kernel
      have hl : raw18511step0Labels = raw18511Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18511 raw18511Labels permutation346 hz
    mixedMoment B raw18511step0 raw18511step0Labels = mixedMoment B raw18511step1 raw18511step1Labels := by
      have ha : raw18511step1 = (fun i j => raw18511step0 (permutation77 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18511step1 raw18511step0; decide +kernel
      have hl : raw18511step1Labels = raw18511step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18511step0 raw18511step0Labels permutation77 permutation3
    mixedMoment B raw18511step1 raw18511step1Labels = mixedMoment B raw18511step2 raw18511step2Labels := by
      have ha : raw18511step2 = -raw18511step1 := by apply Matrix.ext; change ∀ i j, raw18511step2 i j = -(raw18511step1 i j); unfold raw18511step2 raw18511step1; decide +kernel
      have hl : raw18511step2Labels = raw18511step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18511step2 raw18511step2Labels = mixedMoment B raw18511step3 raw18511step3Labels := by
      have ha : raw18511step3 = raw18511step2 := by apply Matrix.ext; unfold raw18511step3 raw18511step2; decide +kernel
      have hl : raw18511step2Labels = labelEmbedding6 ∘ raw18511step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18511step2 raw18511step2Labels raw18511step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5270 node5270Labels := by rfl

def raw18512 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18512Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18512step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw18512step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18512step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18512step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18512step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18512step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18512 raw18512Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw18512 raw18512Labels = mixedMoment B raw18512step0 raw18512step0Labels := by
      have ha : raw18512step0 = (fun i j => raw18512 (permutation336 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18512step0 raw18512; decide +kernel
      have hl : raw18512step0Labels = raw18512Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18512 raw18512Labels permutation336 permutation3
    mixedMoment B raw18512step0 raw18512step0Labels = mixedMoment B raw18512step1 raw18512step1Labels := by
      have ha : raw18512step1 = -raw18512step0 := by apply Matrix.ext; change ∀ i j, raw18512step1 i j = -(raw18512step0 i j); unfold raw18512step1 raw18512step0; decide +kernel
      have hl : raw18512step1Labels = raw18512step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18512step1 raw18512step1Labels = mixedMoment B raw18512step2 raw18512step2Labels := by
      have ha : raw18512step2 = raw18512step1 := by apply Matrix.ext; unfold raw18512step2 raw18512step1; decide +kernel
      have hl : raw18512step1Labels = labelEmbedding6 ∘ raw18512step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18512step1 raw18512step1Labels raw18512step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

def raw18513 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18513Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18513step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18513step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18513step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw18513step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18513step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw18513step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18513step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw18513step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18513 raw18513Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw18513 raw18513Labels = mixedMoment B raw18513step0 raw18513step0Labels := by
      have hz : ∀ j, raw18513 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18513step0 = (fun i j => raw18513 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18513step0 raw18513; decide +kernel
      have hl : raw18513step0Labels = raw18513Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18513 raw18513Labels permutation346 hz
    mixedMoment B raw18513step0 raw18513step0Labels = mixedMoment B raw18513step1 raw18513step1Labels := by
      have ha : raw18513step1 = (fun i j => raw18513step0 (permutation75 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18513step1 raw18513step0; decide +kernel
      have hl : raw18513step1Labels = raw18513step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18513step0 raw18513step0Labels permutation75 permutation3
    mixedMoment B raw18513step1 raw18513step1Labels = mixedMoment B raw18513step2 raw18513step2Labels := by
      have ha : raw18513step2 = -raw18513step1 := by apply Matrix.ext; change ∀ i j, raw18513step2 i j = -(raw18513step1 i j); unfold raw18513step2 raw18513step1; decide +kernel
      have hl : raw18513step2Labels = raw18513step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18513step2 raw18513step2Labels = mixedMoment B raw18513step3 raw18513step3Labels := by
      have ha : raw18513step3 = raw18513step2 := by apply Matrix.ext; unfold raw18513step3 raw18513step2; decide +kernel
      have hl : raw18513step2Labels = labelEmbedding6 ∘ raw18513step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18513step2 raw18513step2Labels raw18513step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

def raw18514 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw18514Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw18514step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18514step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw18514step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18514step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw18514step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18514step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw18514step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18514 raw18514Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw18514 raw18514Labels = mixedMoment B raw18514step0 raw18514step0Labels := by
      have hz : ∀ j, raw18514 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18514step0 = (fun i j => raw18514 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18514step0 raw18514; decide +kernel
      have hl : raw18514step0Labels = raw18514Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18514 raw18514Labels permutation346 hz
    mixedMoment B raw18514step0 raw18514step0Labels = mixedMoment B raw18514step1 raw18514step1Labels := by
      have ha : raw18514step1 = (fun i j => raw18514step0 (permutation74 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18514step1 raw18514step0; decide +kernel
      have hl : raw18514step1Labels = raw18514step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18514step0 raw18514step0Labels permutation74 permutation3
    mixedMoment B raw18514step1 raw18514step1Labels = mixedMoment B raw18514step2 raw18514step2Labels := by
      have ha : raw18514step2 = -raw18514step1 := by apply Matrix.ext; change ∀ i j, raw18514step2 i j = -(raw18514step1 i j); unfold raw18514step2 raw18514step1; decide +kernel
      have hl : raw18514step2Labels = raw18514step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18514step2 raw18514step2Labels = mixedMoment B raw18514step3 raw18514step3Labels := by
      have ha : raw18514step3 = raw18514step2 := by apply Matrix.ext; unfold raw18514step3 raw18514step2; decide +kernel
      have hl : raw18514step2Labels = labelEmbedding6 ∘ raw18514step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18514step2 raw18514step2Labels raw18514step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

def raw18515 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18515Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18515step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![3, -2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18515step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18515step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw18515step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18515step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18515step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18515step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18515step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18515 raw18515Labels = mixedMoment B node5301 node5301Labels := by
  calc
    mixedMoment B raw18515 raw18515Labels = mixedMoment B raw18515step0 raw18515step0Labels := by
      have hz : ∀ j, raw18515 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18515step0 = (fun i j => raw18515 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18515step0 raw18515; decide +kernel
      have hl : raw18515step0Labels = raw18515Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18515 raw18515Labels permutation346 hz
    mixedMoment B raw18515step0 raw18515step0Labels = mixedMoment B raw18515step1 raw18515step1Labels := by
      have ha : raw18515step1 = (fun i j => raw18515step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18515step1 raw18515step0; decide +kernel
      have hl : raw18515step1Labels = raw18515step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18515step0 raw18515step0Labels permutation56 permutation3
    mixedMoment B raw18515step1 raw18515step1Labels = mixedMoment B raw18515step2 raw18515step2Labels := by
      have ha : raw18515step2 = -raw18515step1 := by apply Matrix.ext; change ∀ i j, raw18515step2 i j = -(raw18515step1 i j); unfold raw18515step2 raw18515step1; decide +kernel
      have hl : raw18515step2Labels = raw18515step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18515step2 raw18515step2Labels = mixedMoment B raw18515step3 raw18515step3Labels := by
      have ha : raw18515step3 = raw18515step2 := by apply Matrix.ext; unfold raw18515step3 raw18515step2; decide +kernel
      have hl : raw18515step2Labels = labelEmbedding6 ∘ raw18515step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18515step2 raw18515step2Labels raw18515step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5301 node5301Labels := by rfl

def raw18516 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18516Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18516step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18516step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18516step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18516step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18516 raw18516Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw18516 raw18516Labels = mixedMoment B raw18516step0 raw18516step0Labels := by
      have ha : raw18516step0 = (fun i j => raw18516 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18516step0 raw18516; decide +kernel
      have hl : raw18516step0Labels = raw18516Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18516 raw18516Labels permutation152 permutation6
    mixedMoment B raw18516step0 raw18516step0Labels = mixedMoment B raw18516step1 raw18516step1Labels := by
      have ha : raw18516step1 = raw18516step0 := by apply Matrix.ext; unfold raw18516step1 raw18516step0; decide +kernel
      have hl : raw18516step0Labels = labelEmbedding9 ∘ raw18516step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18516step0 raw18516step0Labels raw18516step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw18517 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18517Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18517step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18517step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18517step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18517step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18517step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18517step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18517step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18517step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18517 raw18517Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw18517 raw18517Labels = mixedMoment B raw18517step0 raw18517step0Labels := by
      have hz : ∀ j, raw18517 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18517step0 = (fun i j => raw18517 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18517step0 raw18517; decide +kernel
      have hl : raw18517step0Labels = raw18517Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18517 raw18517Labels permutation346 hz
    mixedMoment B raw18517step0 raw18517step0Labels = mixedMoment B raw18517step1 raw18517step1Labels := by
      have ha : raw18517step1 = (fun i j => raw18517step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18517step1 raw18517step0; decide +kernel
      have hl : raw18517step1Labels = raw18517step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18517step0 raw18517step0Labels permutation44 permutation4
    mixedMoment B raw18517step1 raw18517step1Labels = mixedMoment B raw18517step2 raw18517step2Labels := by
      have ha : raw18517step2 = -raw18517step1 := by apply Matrix.ext; change ∀ i j, raw18517step2 i j = -(raw18517step1 i j); unfold raw18517step2 raw18517step1; decide +kernel
      have hl : raw18517step2Labels = raw18517step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18517step2 raw18517step2Labels = mixedMoment B raw18517step3 raw18517step3Labels := by
      have ha : raw18517step3 = raw18517step2 := by apply Matrix.ext; unfold raw18517step3 raw18517step2; decide +kernel
      have hl : raw18517step2Labels = labelEmbedding7 ∘ raw18517step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18517step2 raw18517step2Labels raw18517step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

def raw18518 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw18518Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18518step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18518step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18518step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18518step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18518step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18518step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18518 raw18518Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw18518 raw18518Labels = mixedMoment B raw18518step0 raw18518step0Labels := by
      have ha : raw18518step0 = (fun i j => raw18518 (permutation188 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18518step0 raw18518; decide +kernel
      have hl : raw18518step0Labels = raw18518Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18518 raw18518Labels permutation188 permutation4
    mixedMoment B raw18518step0 raw18518step0Labels = mixedMoment B raw18518step1 raw18518step1Labels := by
      have ha : raw18518step1 = -raw18518step0 := by apply Matrix.ext; change ∀ i j, raw18518step1 i j = -(raw18518step0 i j); unfold raw18518step1 raw18518step0; decide +kernel
      have hl : raw18518step1Labels = raw18518step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18518step1 raw18518step1Labels = mixedMoment B raw18518step2 raw18518step2Labels := by
      have ha : raw18518step2 = raw18518step1 := by apply Matrix.ext; unfold raw18518step2 raw18518step1; decide +kernel
      have hl : raw18518step1Labels = labelEmbedding7 ∘ raw18518step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18518step1 raw18518step1Labels raw18518step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

def raw18519 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw18519Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18519step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw18519step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18519step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18519step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18519step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18519step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18519step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18519step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18519 raw18519Labels = mixedMoment B node5448 node5448Labels := by
  calc
    mixedMoment B raw18519 raw18519Labels = mixedMoment B raw18519step0 raw18519step0Labels := by
      have hz : ∀ j, raw18519 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18519step0 = (fun i j => raw18519 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18519step0 raw18519; decide +kernel
      have hl : raw18519step0Labels = raw18519Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18519 raw18519Labels permutation346 hz
    mixedMoment B raw18519step0 raw18519step0Labels = mixedMoment B raw18519step1 raw18519step1Labels := by
      have ha : raw18519step1 = (fun i j => raw18519step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18519step1 raw18519step0; decide +kernel
      have hl : raw18519step1Labels = raw18519step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18519step0 raw18519step0Labels permutation44 permutation4
    mixedMoment B raw18519step1 raw18519step1Labels = mixedMoment B raw18519step2 raw18519step2Labels := by
      have ha : raw18519step2 = -raw18519step1 := by apply Matrix.ext; change ∀ i j, raw18519step2 i j = -(raw18519step1 i j); unfold raw18519step2 raw18519step1; decide +kernel
      have hl : raw18519step2Labels = raw18519step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18519step2 raw18519step2Labels = mixedMoment B raw18519step3 raw18519step3Labels := by
      have ha : raw18519step3 = raw18519step2 := by apply Matrix.ext; unfold raw18519step3 raw18519step2; decide +kernel
      have hl : raw18519step2Labels = labelEmbedding7 ∘ raw18519step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18519step2 raw18519step2Labels raw18519step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5448 node5448Labels := by rfl

def raw18520 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18520Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18520step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18520step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18520step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18520step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18520step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18520step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18520 raw18520Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw18520 raw18520Labels = mixedMoment B raw18520step0 raw18520step0Labels := by
      have hz : ∀ j, raw18520 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18520step0 = (fun i j => raw18520 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18520step0 raw18520; decide +kernel
      have hl : raw18520step0Labels = raw18520Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18520 raw18520Labels permutation346 hz
    mixedMoment B raw18520step0 raw18520step0Labels = mixedMoment B raw18520step1 raw18520step1Labels := by
      have ha : raw18520step1 = (fun i j => raw18520step0 (permutation35 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18520step1 raw18520step0; decide +kernel
      have hl : raw18520step1Labels = raw18520step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18520step0 raw18520step0Labels permutation35 permutation6
    mixedMoment B raw18520step1 raw18520step1Labels = mixedMoment B raw18520step2 raw18520step2Labels := by
      have ha : raw18520step2 = raw18520step1 := by apply Matrix.ext; unfold raw18520step2 raw18520step1; decide +kernel
      have hl : raw18520step1Labels = labelEmbedding9 ∘ raw18520step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18520step1 raw18520step1Labels raw18520step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw18521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw18521Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18521step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw18521step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18521step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18521step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18521step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18521step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18521step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18521step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18521 raw18521Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw18521 raw18521Labels = mixedMoment B raw18521step0 raw18521step0Labels := by
      have hz : ∀ j, raw18521 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18521step0 = (fun i j => raw18521 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18521step0 raw18521; decide +kernel
      have hl : raw18521step0Labels = raw18521Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18521 raw18521Labels permutation346 hz
    mixedMoment B raw18521step0 raw18521step0Labels = mixedMoment B raw18521step1 raw18521step1Labels := by
      have ha : raw18521step1 = (fun i j => raw18521step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18521step1 raw18521step0; decide +kernel
      have hl : raw18521step1Labels = raw18521step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18521step0 raw18521step0Labels permutation38 permutation4
    mixedMoment B raw18521step1 raw18521step1Labels = mixedMoment B raw18521step2 raw18521step2Labels := by
      have ha : raw18521step2 = -raw18521step1 := by apply Matrix.ext; change ∀ i j, raw18521step2 i j = -(raw18521step1 i j); unfold raw18521step2 raw18521step1; decide +kernel
      have hl : raw18521step2Labels = raw18521step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18521step2 raw18521step2Labels = mixedMoment B raw18521step3 raw18521step3Labels := by
      have ha : raw18521step3 = raw18521step2 := by apply Matrix.ext; unfold raw18521step3 raw18521step2; decide +kernel
      have hl : raw18521step2Labels = labelEmbedding7 ∘ raw18521step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18521step2 raw18521step2Labels raw18521step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5290 node5290Labels := by rfl

def raw18522 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw18522Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18522step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18522step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18522step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18522step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18522step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18522step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18522 raw18522Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw18522 raw18522Labels = mixedMoment B raw18522step0 raw18522step0Labels := by
      have ha : raw18522step0 = (fun i j => raw18522 (permutation182 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18522step0 raw18522; decide +kernel
      have hl : raw18522step0Labels = raw18522Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18522 raw18522Labels permutation182 permutation4
    mixedMoment B raw18522step0 raw18522step0Labels = mixedMoment B raw18522step1 raw18522step1Labels := by
      have ha : raw18522step1 = -raw18522step0 := by apply Matrix.ext; change ∀ i j, raw18522step1 i j = -(raw18522step0 i j); unfold raw18522step1 raw18522step0; decide +kernel
      have hl : raw18522step1Labels = raw18522step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18522step1 raw18522step1Labels = mixedMoment B raw18522step2 raw18522step2Labels := by
      have ha : raw18522step2 = raw18522step1 := by apply Matrix.ext; unfold raw18522step2 raw18522step1; decide +kernel
      have hl : raw18522step1Labels = labelEmbedding7 ∘ raw18522step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18522step1 raw18522step1Labels raw18522step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

def raw18523 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw18523Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18523step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw18523step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18523step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18523step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18523step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18523step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18523step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18523step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18523 raw18523Labels = mixedMoment B node5448 node5448Labels := by
  calc
    mixedMoment B raw18523 raw18523Labels = mixedMoment B raw18523step0 raw18523step0Labels := by
      have hz : ∀ j, raw18523 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18523step0 = (fun i j => raw18523 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18523step0 raw18523; decide +kernel
      have hl : raw18523step0Labels = raw18523Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18523 raw18523Labels permutation346 hz
    mixedMoment B raw18523step0 raw18523step0Labels = mixedMoment B raw18523step1 raw18523step1Labels := by
      have ha : raw18523step1 = (fun i j => raw18523step0 (permutation38 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18523step1 raw18523step0; decide +kernel
      have hl : raw18523step1Labels = raw18523step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18523step0 raw18523step0Labels permutation38 permutation4
    mixedMoment B raw18523step1 raw18523step1Labels = mixedMoment B raw18523step2 raw18523step2Labels := by
      have ha : raw18523step2 = -raw18523step1 := by apply Matrix.ext; change ∀ i j, raw18523step2 i j = -(raw18523step1 i j); unfold raw18523step2 raw18523step1; decide +kernel
      have hl : raw18523step2Labels = raw18523step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18523step2 raw18523step2Labels = mixedMoment B raw18523step3 raw18523step3Labels := by
      have ha : raw18523step3 = raw18523step2 := by apply Matrix.ext; unfold raw18523step3 raw18523step2; decide +kernel
      have hl : raw18523step2Labels = labelEmbedding7 ∘ raw18523step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18523step2 raw18523step2Labels raw18523step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5448 node5448Labels := by rfl

def raw18524 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw18524Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw18524step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18524step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18524step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18524step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18524step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18524 raw18524Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw18524 raw18524Labels = mixedMoment B raw18524step0 raw18524step0Labels := by
      have hz : ∀ j, raw18524 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18524step0 = (fun i j => raw18524 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18524step0 raw18524; decide +kernel
      have hl : raw18524step0Labels = raw18524Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18524 raw18524Labels permutation346 hz
    mixedMoment B raw18524step0 raw18524step0Labels = mixedMoment B raw18524step1 raw18524step1Labels := by
      have ha : raw18524step1 = (fun i j => raw18524step0 (permutation33 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18524step1 raw18524step0; decide +kernel
      have hl : raw18524step1Labels = raw18524step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18524step0 raw18524step0Labels permutation33 permutation6
    mixedMoment B raw18524step1 raw18524step1Labels = mixedMoment B raw18524step2 raw18524step2Labels := by
      have ha : raw18524step2 = raw18524step1 := by apply Matrix.ext; unfold raw18524step2 raw18524step1; decide +kernel
      have hl : raw18524step1Labels = labelEmbedding9 ∘ raw18524step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18524step1 raw18524step1Labels raw18524step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw18525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw18525Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18525step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 3, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw18525step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18525step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw18525step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18525step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18525step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18525step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18525step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18525 raw18525Labels = mixedMoment B node5282 node5282Labels := by
  calc
    mixedMoment B raw18525 raw18525Labels = mixedMoment B raw18525step0 raw18525step0Labels := by
      have hz : ∀ j, raw18525 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18525step0 = (fun i j => raw18525 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18525step0 raw18525; decide +kernel
      have hl : raw18525step0Labels = raw18525Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18525 raw18525Labels permutation346 hz
    mixedMoment B raw18525step0 raw18525step0Labels = mixedMoment B raw18525step1 raw18525step1Labels := by
      have ha : raw18525step1 = (fun i j => raw18525step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18525step1 raw18525step0; decide +kernel
      have hl : raw18525step1Labels = raw18525step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18525step0 raw18525step0Labels permutation40 permutation4
    mixedMoment B raw18525step1 raw18525step1Labels = mixedMoment B raw18525step2 raw18525step2Labels := by
      have ha : raw18525step2 = -raw18525step1 := by apply Matrix.ext; change ∀ i j, raw18525step2 i j = -(raw18525step1 i j); unfold raw18525step2 raw18525step1; decide +kernel
      have hl : raw18525step2Labels = raw18525step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18525step2 raw18525step2Labels = mixedMoment B raw18525step3 raw18525step3Labels := by
      have ha : raw18525step3 = raw18525step2 := by apply Matrix.ext; unfold raw18525step3 raw18525step2; decide +kernel
      have hl : raw18525step2Labels = labelEmbedding7 ∘ raw18525step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18525step2 raw18525step2Labels raw18525step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5282 node5282Labels := by rfl

def raw18526 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw18526Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18526step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw18526step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18526step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18526step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18526step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18526step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18526 raw18526Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw18526 raw18526Labels = mixedMoment B raw18526step0 raw18526step0Labels := by
      have ha : raw18526step0 = (fun i j => raw18526 (permutation184 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18526step0 raw18526; decide +kernel
      have hl : raw18526step0Labels = raw18526Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18526 raw18526Labels permutation184 permutation4
    mixedMoment B raw18526step0 raw18526step0Labels = mixedMoment B raw18526step1 raw18526step1Labels := by
      have ha : raw18526step1 = -raw18526step0 := by apply Matrix.ext; change ∀ i j, raw18526step1 i j = -(raw18526step0 i j); unfold raw18526step1 raw18526step0; decide +kernel
      have hl : raw18526step1Labels = raw18526step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18526step1 raw18526step1Labels = mixedMoment B raw18526step2 raw18526step2Labels := by
      have ha : raw18526step2 = raw18526step1 := by apply Matrix.ext; unfold raw18526step2 raw18526step1; decide +kernel
      have hl : raw18526step1Labels = labelEmbedding7 ∘ raw18526step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18526step1 raw18526step1Labels raw18526step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5429 node5429Labels := by rfl

def raw18527 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw18527Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18527step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw18527step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18527step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw18527step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18527step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18527step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18527step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18527step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18527 raw18527Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw18527 raw18527Labels = mixedMoment B raw18527step0 raw18527step0Labels := by
      have hz : ∀ j, raw18527 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18527step0 = (fun i j => raw18527 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18527step0 raw18527; decide +kernel
      have hl : raw18527step0Labels = raw18527Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18527 raw18527Labels permutation346 hz
    mixedMoment B raw18527step0 raw18527step0Labels = mixedMoment B raw18527step1 raw18527step1Labels := by
      have ha : raw18527step1 = (fun i j => raw18527step0 (permutation40 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18527step1 raw18527step0; decide +kernel
      have hl : raw18527step1Labels = raw18527step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18527step0 raw18527step0Labels permutation40 permutation4
    mixedMoment B raw18527step1 raw18527step1Labels = mixedMoment B raw18527step2 raw18527step2Labels := by
      have ha : raw18527step2 = -raw18527step1 := by apply Matrix.ext; change ∀ i j, raw18527step2 i j = -(raw18527step1 i j); unfold raw18527step2 raw18527step1; decide +kernel
      have hl : raw18527step2Labels = raw18527step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18527step2 raw18527step2Labels = mixedMoment B raw18527step3 raw18527step3Labels := by
      have ha : raw18527step3 = raw18527step2 := by apply Matrix.ext; unfold raw18527step3 raw18527step2; decide +kernel
      have hl : raw18527step2Labels = labelEmbedding7 ∘ raw18527step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18527step2 raw18527step2Labels raw18527step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

def raw18528 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw18528Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18528step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![2, -1, -1], ![-1, 0, 1], ![-2, 1, 1], ![1, -2, 1]]
def raw18528step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18528step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw18528step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18528step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18528step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18528step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw18528step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18528 raw18528Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw18528 raw18528Labels = mixedMoment B raw18528step0 raw18528step0Labels := by
      have hz : ∀ j, raw18528 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18528step0 = (fun i j => raw18528 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18528step0 raw18528; decide +kernel
      have hl : raw18528step0Labels = raw18528Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18528 raw18528Labels permutation346 hz
    mixedMoment B raw18528step0 raw18528step0Labels = mixedMoment B raw18528step1 raw18528step1Labels := by
      have ha : raw18528step1 = (fun i j => raw18528step0 (permutation46 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18528step1 raw18528step0; decide +kernel
      have hl : raw18528step1Labels = raw18528step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18528step0 raw18528step0Labels permutation46 permutation4
    mixedMoment B raw18528step1 raw18528step1Labels = mixedMoment B raw18528step2 raw18528step2Labels := by
      have ha : raw18528step2 = -raw18528step1 := by apply Matrix.ext; change ∀ i j, raw18528step2 i j = -(raw18528step1 i j); unfold raw18528step2 raw18528step1; decide +kernel
      have hl : raw18528step2Labels = raw18528step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18528step2 raw18528step2Labels = mixedMoment B raw18528step3 raw18528step3Labels := by
      have ha : raw18528step3 = raw18528step2 := by apply Matrix.ext; unfold raw18528step3 raw18528step2; decide +kernel
      have hl : raw18528step2Labels = labelEmbedding7 ∘ raw18528step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18528step2 raw18528step2Labels raw18528step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

def raw18529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18529Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18529step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18529step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18529step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18529step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18529step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18529step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18529 raw18529Labels = mixedMoment B node5162 node5162Labels := by
  calc
    mixedMoment B raw18529 raw18529Labels = mixedMoment B raw18529step0 raw18529step0Labels := by
      have ha : raw18529step0 = (fun i j => raw18529 (permutation289 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18529step0 raw18529; decide +kernel
      have hl : raw18529step0Labels = raw18529Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18529 raw18529Labels permutation289 permutation5
    mixedMoment B raw18529step0 raw18529step0Labels = mixedMoment B raw18529step1 raw18529step1Labels := by
      have ha : raw18529step1 = -raw18529step0 := by apply Matrix.ext; change ∀ i j, raw18529step1 i j = -(raw18529step0 i j); unfold raw18529step1 raw18529step0; decide +kernel
      have hl : raw18529step1Labels = raw18529step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18529step1 raw18529step1Labels = mixedMoment B raw18529step2 raw18529step2Labels := by
      have ha : raw18529step2 = raw18529step1 := by apply Matrix.ext; unfold raw18529step2 raw18529step1; decide +kernel
      have hl : raw18529step1Labels = labelEmbedding8 ∘ raw18529step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18529step1 raw18529step1Labels raw18529step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5162 node5162Labels := by rfl

def raw18530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18530Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18530step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![2, -1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18530step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18530step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18530step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18530step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18530step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18530 raw18530Labels = mixedMoment B node5462 node5462Labels := by
  calc
    mixedMoment B raw18530 raw18530Labels = mixedMoment B raw18530step0 raw18530step0Labels := by
      have ha : raw18530step0 = (fun i j => raw18530 (permutation289 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18530step0 raw18530; decide +kernel
      have hl : raw18530step0Labels = raw18530Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18530 raw18530Labels permutation289 permutation5
    mixedMoment B raw18530step0 raw18530step0Labels = mixedMoment B raw18530step1 raw18530step1Labels := by
      have ha : raw18530step1 = -raw18530step0 := by apply Matrix.ext; change ∀ i j, raw18530step1 i j = -(raw18530step0 i j); unfold raw18530step1 raw18530step0; decide +kernel
      have hl : raw18530step1Labels = raw18530step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18530step1 raw18530step1Labels = mixedMoment B raw18530step2 raw18530step2Labels := by
      have ha : raw18530step2 = raw18530step1 := by apply Matrix.ext; unfold raw18530step2 raw18530step1; decide +kernel
      have hl : raw18530step1Labels = labelEmbedding8 ∘ raw18530step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18530step1 raw18530step1Labels raw18530step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5462 node5462Labels := by rfl

def raw18531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18531Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18531step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw18531step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18531step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw18531step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18531step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18531step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18531step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18531step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18531 raw18531Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw18531 raw18531Labels = mixedMoment B raw18531step0 raw18531step0Labels := by
      have hz : ∀ j, raw18531 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18531step0 = (fun i j => raw18531 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18531step0 raw18531; decide +kernel
      have hl : raw18531step0Labels = raw18531Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18531 raw18531Labels permutation434 hz
    mixedMoment B raw18531step0 raw18531step0Labels = mixedMoment B raw18531step1 raw18531step1Labels := by
      have ha : raw18531step1 = (fun i j => raw18531step0 (permutation65 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18531step1 raw18531step0; decide +kernel
      have hl : raw18531step1Labels = raw18531step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18531step0 raw18531step0Labels permutation65 permutation4
    mixedMoment B raw18531step1 raw18531step1Labels = mixedMoment B raw18531step2 raw18531step2Labels := by
      have ha : raw18531step2 = -raw18531step1 := by apply Matrix.ext; change ∀ i j, raw18531step2 i j = -(raw18531step1 i j); unfold raw18531step2 raw18531step1; decide +kernel
      have hl : raw18531step2Labels = raw18531step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18531step2 raw18531step2Labels = mixedMoment B raw18531step3 raw18531step3Labels := by
      have ha : raw18531step3 = raw18531step2 := by apply Matrix.ext; unfold raw18531step3 raw18531step2; decide +kernel
      have hl : raw18531step2Labels = labelEmbedding7 ∘ raw18531step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18531step2 raw18531step2Labels raw18531step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5485 node5485Labels := by rfl

def raw18532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw18532Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18532step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw18532step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18532step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw18532step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18532step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18532step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18532step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18532step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18532 raw18532Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw18532 raw18532Labels = mixedMoment B raw18532step0 raw18532step0Labels := by
      have hz : ∀ j, raw18532 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18532step0 = (fun i j => raw18532 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18532step0 raw18532; decide +kernel
      have hl : raw18532step0Labels = raw18532Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18532 raw18532Labels permutation520 hz
    mixedMoment B raw18532step0 raw18532step0Labels = mixedMoment B raw18532step1 raw18532step1Labels := by
      have ha : raw18532step1 = (fun i j => raw18532step0 (permutation65 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18532step1 raw18532step0; decide +kernel
      have hl : raw18532step1Labels = raw18532step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18532step0 raw18532step0Labels permutation65 permutation4
    mixedMoment B raw18532step1 raw18532step1Labels = mixedMoment B raw18532step2 raw18532step2Labels := by
      have ha : raw18532step2 = -raw18532step1 := by apply Matrix.ext; change ∀ i j, raw18532step2 i j = -(raw18532step1 i j); unfold raw18532step2 raw18532step1; decide +kernel
      have hl : raw18532step2Labels = raw18532step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18532step2 raw18532step2Labels = mixedMoment B raw18532step3 raw18532step3Labels := by
      have ha : raw18532step3 = raw18532step2 := by apply Matrix.ext; unfold raw18532step3 raw18532step2; decide +kernel
      have hl : raw18532step2Labels = labelEmbedding7 ∘ raw18532step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18532step2 raw18532step2Labels raw18532step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5485 node5485Labels := by rfl

def raw18533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw18533Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18533step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw18533step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18533step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw18533step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18533step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18533step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18533step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18533step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18533 raw18533Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw18533 raw18533Labels = mixedMoment B raw18533step0 raw18533step0Labels := by
      have hz : ∀ j, raw18533 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw18533step0 = (fun i j => raw18533 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw18533step0 raw18533; decide +kernel
      have hl : raw18533step0Labels = raw18533Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18533 raw18533Labels permutation590 hz
    mixedMoment B raw18533step0 raw18533step0Labels = mixedMoment B raw18533step1 raw18533step1Labels := by
      have ha : raw18533step1 = (fun i j => raw18533step0 (permutation65 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18533step1 raw18533step0; decide +kernel
      have hl : raw18533step1Labels = raw18533step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18533step0 raw18533step0Labels permutation65 permutation4
    mixedMoment B raw18533step1 raw18533step1Labels = mixedMoment B raw18533step2 raw18533step2Labels := by
      have ha : raw18533step2 = -raw18533step1 := by apply Matrix.ext; change ∀ i j, raw18533step2 i j = -(raw18533step1 i j); unfold raw18533step2 raw18533step1; decide +kernel
      have hl : raw18533step2Labels = raw18533step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18533step2 raw18533step2Labels = mixedMoment B raw18533step3 raw18533step3Labels := by
      have ha : raw18533step3 = raw18533step2 := by apply Matrix.ext; unfold raw18533step3 raw18533step2; decide +kernel
      have hl : raw18533step2Labels = labelEmbedding7 ∘ raw18533step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18533step2 raw18533step2Labels raw18533step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5485 node5485Labels := by rfl

def raw18534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18534Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18534 raw18534Labels = mixedMoment B node5283 node5283Labels := by
  calc
    _ = mixedMoment B node5283 node5283Labels := by rfl

def raw18535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18535Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18535step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18535step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18535step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18535step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18535step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18535step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18535 raw18535Labels = mixedMoment B node5227 node5227Labels := by
  calc
    mixedMoment B raw18535 raw18535Labels = mixedMoment B raw18535step0 raw18535step0Labels := by
      have ha : raw18535step0 = (fun i j => raw18535 (permutation265 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18535step0 raw18535; decide +kernel
      have hl : raw18535step0Labels = raw18535Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18535 raw18535Labels permutation265 permutation5
    mixedMoment B raw18535step0 raw18535step0Labels = mixedMoment B raw18535step1 raw18535step1Labels := by
      have ha : raw18535step1 = -raw18535step0 := by apply Matrix.ext; change ∀ i j, raw18535step1 i j = -(raw18535step0 i j); unfold raw18535step1 raw18535step0; decide +kernel
      have hl : raw18535step1Labels = raw18535step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18535step1 raw18535step1Labels = mixedMoment B raw18535step2 raw18535step2Labels := by
      have ha : raw18535step2 = raw18535step1 := by apply Matrix.ext; unfold raw18535step2 raw18535step1; decide +kernel
      have hl : raw18535step1Labels = labelEmbedding8 ∘ raw18535step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18535step1 raw18535step1Labels raw18535step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5227 node5227Labels := by rfl

def raw18536 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18536Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18536step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw18536step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18536step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18536step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18536 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18536 raw18536Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw18536 raw18536Labels = mixedMoment B raw18536step0 raw18536step0Labels := by
      have hz : ∀ j, raw18536 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18536step0 = (fun i j => raw18536 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18536step0 raw18536; decide +kernel
      have hl : raw18536step0Labels = raw18536Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18536 raw18536Labels permutation434 hz
    mixedMoment B raw18536step0 raw18536step0Labels = mixedMoment B raw18536step1 raw18536step1Labels := by
      have ha : raw18536step1 = (fun i j => raw18536step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18536step1 raw18536step0; decide +kernel
      have hl : raw18536step1Labels = raw18536step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18536step0 raw18536step0Labels permutation35 permutation2
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw18537 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw18537Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18537step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw18537step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18537step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18537step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18537 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18537 raw18537Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw18537 raw18537Labels = mixedMoment B raw18537step0 raw18537step0Labels := by
      have hz : ∀ j, raw18537 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18537step0 = (fun i j => raw18537 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18537step0 raw18537; decide +kernel
      have hl : raw18537step0Labels = raw18537Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18537 raw18537Labels permutation520 hz
    mixedMoment B raw18537step0 raw18537step0Labels = mixedMoment B raw18537step1 raw18537step1Labels := by
      have ha : raw18537step1 = (fun i j => raw18537step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18537step1 raw18537step0; decide +kernel
      have hl : raw18537step1Labels = raw18537step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18537step0 raw18537step0Labels permutation35 permutation2
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw18538 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw18538Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18538step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw18538step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18538step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18538step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18538 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18538 raw18538Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw18538 raw18538Labels = mixedMoment B raw18538step0 raw18538step0Labels := by
      have hz : ∀ j, raw18538 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw18538step0 = (fun i j => raw18538 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw18538step0 raw18538; decide +kernel
      have hl : raw18538step0Labels = raw18538Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18538 raw18538Labels permutation590 hz
    mixedMoment B raw18538step0 raw18538step0Labels = mixedMoment B raw18538step1 raw18538step1Labels := by
      have ha : raw18538step1 = (fun i j => raw18538step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18538step1 raw18538step0; decide +kernel
      have hl : raw18538step1Labels = raw18538step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18538step0 raw18538step0Labels permutation35 permutation2
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw18539 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18539Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18539step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw18539step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18539step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18539step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18539step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18539step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18539 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18539 raw18539Labels = mixedMoment B node5123 node5123Labels := by
  calc
    mixedMoment B raw18539 raw18539Labels = mixedMoment B raw18539step0 raw18539step0Labels := by
      have ha : raw18539step0 = (fun i j => raw18539 (permutation292 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18539step0 raw18539; decide +kernel
      have hl : raw18539step0Labels = raw18539Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18539 raw18539Labels permutation292 permutation5
    mixedMoment B raw18539step0 raw18539step0Labels = mixedMoment B raw18539step1 raw18539step1Labels := by
      have ha : raw18539step1 = -raw18539step0 := by apply Matrix.ext; change ∀ i j, raw18539step1 i j = -(raw18539step0 i j); unfold raw18539step1 raw18539step0; decide +kernel
      have hl : raw18539step1Labels = raw18539step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18539step1 raw18539step1Labels = mixedMoment B raw18539step2 raw18539step2Labels := by
      have ha : raw18539step2 = raw18539step1 := by apply Matrix.ext; unfold raw18539step2 raw18539step1; decide +kernel
      have hl : raw18539step1Labels = labelEmbedding8 ∘ raw18539step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18539step1 raw18539step1Labels raw18539step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5123 node5123Labels := by rfl

def raw18540 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18540Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18540step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw18540step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18540step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw18540step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18540 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18540 raw18540Labels = mixedMoment B node5391 node5391Labels := by
  calc
    mixedMoment B raw18540 raw18540Labels = mixedMoment B raw18540step0 raw18540step0Labels := by
      have ha : raw18540step0 = (fun i j => raw18540 (permutation499 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18540step0 raw18540; decide +kernel
      have hl : raw18540step0Labels = raw18540Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18540 raw18540Labels permutation499 permutation5
    mixedMoment B raw18540step0 raw18540step0Labels = mixedMoment B raw18540step1 raw18540step1Labels := by
      have ha : raw18540step1 = raw18540step0 := by apply Matrix.ext; unfold raw18540step1 raw18540step0; decide +kernel
      have hl : raw18540step0Labels = labelEmbedding8 ∘ raw18540step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18540step0 raw18540step0Labels raw18540step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5391 node5391Labels := by rfl

def raw18541 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0]]
def raw18541Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18541step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw18541step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18541step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18541step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18541step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18541step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18541step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18541step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18541 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18541 raw18541Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw18541 raw18541Labels = mixedMoment B raw18541step0 raw18541step0Labels := by
      have hz : ∀ j, raw18541 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18541step0 = (fun i j => raw18541 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18541step0 raw18541; decide +kernel
      have hl : raw18541step0Labels = raw18541Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18541 raw18541Labels permutation520 hz
    mixedMoment B raw18541step0 raw18541step0Labels = mixedMoment B raw18541step1 raw18541step1Labels := by
      have ha : raw18541step1 = (fun i j => raw18541step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18541step1 raw18541step0; decide +kernel
      have hl : raw18541step1Labels = raw18541step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18541step0 raw18541step0Labels permutation127 permutation3
    mixedMoment B raw18541step1 raw18541step1Labels = mixedMoment B raw18541step2 raw18541step2Labels := by
      have ha : raw18541step2 = -raw18541step1 := by apply Matrix.ext; change ∀ i j, raw18541step2 i j = -(raw18541step1 i j); unfold raw18541step2 raw18541step1; decide +kernel
      have hl : raw18541step2Labels = raw18541step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18541step2 raw18541step2Labels = mixedMoment B raw18541step3 raw18541step3Labels := by
      have ha : raw18541step3 = raw18541step2 := by apply Matrix.ext; unfold raw18541step3 raw18541step2; decide +kernel
      have hl : raw18541step2Labels = labelEmbedding6 ∘ raw18541step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18541step2 raw18541step2Labels raw18541step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw18542 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0]]
def raw18542Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18542step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw18542step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18542step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18542step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18542step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18542step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18542step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18542step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18542 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18542 raw18542Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw18542 raw18542Labels = mixedMoment B raw18542step0 raw18542step0Labels := by
      have hz : ∀ j, raw18542 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw18542step0 = (fun i j => raw18542 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw18542step0 raw18542; decide +kernel
      have hl : raw18542step0Labels = raw18542Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18542 raw18542Labels permutation590 hz
    mixedMoment B raw18542step0 raw18542step0Labels = mixedMoment B raw18542step1 raw18542step1Labels := by
      have ha : raw18542step1 = (fun i j => raw18542step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18542step1 raw18542step0; decide +kernel
      have hl : raw18542step1Labels = raw18542step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18542step0 raw18542step0Labels permutation127 permutation3
    mixedMoment B raw18542step1 raw18542step1Labels = mixedMoment B raw18542step2 raw18542step2Labels := by
      have ha : raw18542step2 = -raw18542step1 := by apply Matrix.ext; change ∀ i j, raw18542step2 i j = -(raw18542step1 i j); unfold raw18542step2 raw18542step1; decide +kernel
      have hl : raw18542step2Labels = raw18542step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18542step2 raw18542step2Labels = mixedMoment B raw18542step3 raw18542step3Labels := by
      have ha : raw18542step3 = raw18542step2 := by apply Matrix.ext; unfold raw18542step3 raw18542step2; decide +kernel
      have hl : raw18542step2Labels = labelEmbedding6 ∘ raw18542step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18542step2 raw18542step2Labels raw18542step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw18543 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw18543Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18543step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw18543step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18543step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18543step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18543step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18543step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18543 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18543 raw18543Labels = mixedMoment B node5123 node5123Labels := by
  calc
    mixedMoment B raw18543 raw18543Labels = mixedMoment B raw18543step0 raw18543step0Labels := by
      have ha : raw18543step0 = (fun i j => raw18543 (permutation290 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18543step0 raw18543; decide +kernel
      have hl : raw18543step0Labels = raw18543Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18543 raw18543Labels permutation290 permutation5
    mixedMoment B raw18543step0 raw18543step0Labels = mixedMoment B raw18543step1 raw18543step1Labels := by
      have ha : raw18543step1 = -raw18543step0 := by apply Matrix.ext; change ∀ i j, raw18543step1 i j = -(raw18543step0 i j); unfold raw18543step1 raw18543step0; decide +kernel
      have hl : raw18543step1Labels = raw18543step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18543step1 raw18543step1Labels = mixedMoment B raw18543step2 raw18543step2Labels := by
      have ha : raw18543step2 = raw18543step1 := by apply Matrix.ext; unfold raw18543step2 raw18543step1; decide +kernel
      have hl : raw18543step1Labels = labelEmbedding8 ∘ raw18543step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18543step1 raw18543step1Labels raw18543step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5123 node5123Labels := by rfl

def raw18544 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw18544Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18544step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw18544step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18544step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw18544step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18544 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18544 raw18544Labels = mixedMoment B node5391 node5391Labels := by
  calc
    mixedMoment B raw18544 raw18544Labels = mixedMoment B raw18544step0 raw18544step0Labels := by
      have ha : raw18544step0 = (fun i j => raw18544 (permutation563 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18544step0 raw18544; decide +kernel
      have hl : raw18544step0Labels = raw18544Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18544 raw18544Labels permutation563 permutation5
    mixedMoment B raw18544step0 raw18544step0Labels = mixedMoment B raw18544step1 raw18544step1Labels := by
      have ha : raw18544step1 = raw18544step0 := by apply Matrix.ext; unfold raw18544step1 raw18544step0; decide +kernel
      have hl : raw18544step0Labels = labelEmbedding8 ∘ raw18544step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18544step0 raw18544step0Labels raw18544step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5391 node5391Labels := by rfl

def raw18545 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0]]
def raw18545Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18545step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0]]
def raw18545step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18545step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18545step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18545step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18545step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18545step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18545step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18545 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18545 raw18545Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw18545 raw18545Labels = mixedMoment B raw18545step0 raw18545step0Labels := by
      have hz : ∀ j, raw18545 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18545step0 = (fun i j => raw18545 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18545step0 raw18545; decide +kernel
      have hl : raw18545step0Labels = raw18545Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18545 raw18545Labels permutation434 hz
    mixedMoment B raw18545step0 raw18545step0Labels = mixedMoment B raw18545step1 raw18545step1Labels := by
      have ha : raw18545step1 = (fun i j => raw18545step0 (permutation127 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18545step1 raw18545step0; decide +kernel
      have hl : raw18545step1Labels = raw18545step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18545step0 raw18545step0Labels permutation127 permutation3
    mixedMoment B raw18545step1 raw18545step1Labels = mixedMoment B raw18545step2 raw18545step2Labels := by
      have ha : raw18545step2 = -raw18545step1 := by apply Matrix.ext; change ∀ i j, raw18545step2 i j = -(raw18545step1 i j); unfold raw18545step2 raw18545step1; decide +kernel
      have hl : raw18545step2Labels = raw18545step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18545step2 raw18545step2Labels = mixedMoment B raw18545step3 raw18545step3Labels := by
      have ha : raw18545step3 = raw18545step2 := by apply Matrix.ext; unfold raw18545step3 raw18545step2; decide +kernel
      have hl : raw18545step2Labels = labelEmbedding6 ∘ raw18545step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18545step2 raw18545step2Labels raw18545step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw18546 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0]]
def raw18546Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18546step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw18546step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18546step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18546step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18546step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18546step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18546step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18546step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18546 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18546 raw18546Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw18546 raw18546Labels = mixedMoment B raw18546step0 raw18546step0Labels := by
      have hz : ∀ j, raw18546 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw18546step0 = (fun i j => raw18546 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw18546step0 raw18546; decide +kernel
      have hl : raw18546step0Labels = raw18546Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18546 raw18546Labels permutation590 hz
    mixedMoment B raw18546step0 raw18546step0Labels = mixedMoment B raw18546step1 raw18546step1Labels := by
      have ha : raw18546step1 = (fun i j => raw18546step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18546step1 raw18546step0; decide +kernel
      have hl : raw18546step1Labels = raw18546step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18546step0 raw18546step0Labels permutation151 permutation3
    mixedMoment B raw18546step1 raw18546step1Labels = mixedMoment B raw18546step2 raw18546step2Labels := by
      have ha : raw18546step2 = -raw18546step1 := by apply Matrix.ext; change ∀ i j, raw18546step2 i j = -(raw18546step1 i j); unfold raw18546step2 raw18546step1; decide +kernel
      have hl : raw18546step2Labels = raw18546step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18546step2 raw18546step2Labels = mixedMoment B raw18546step3 raw18546step3Labels := by
      have ha : raw18546step3 = raw18546step2 := by apply Matrix.ext; unfold raw18546step3 raw18546step2; decide +kernel
      have hl : raw18546step2Labels = labelEmbedding6 ∘ raw18546step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18546step2 raw18546step2Labels raw18546step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw18547 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18547Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18547step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw18547step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18547step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18547step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18547step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18547step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18547 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18547 raw18547Labels = mixedMoment B node5123 node5123Labels := by
  calc
    mixedMoment B raw18547 raw18547Labels = mixedMoment B raw18547step0 raw18547step0Labels := by
      have ha : raw18547step0 = (fun i j => raw18547 (permutation289 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18547step0 raw18547; decide +kernel
      have hl : raw18547step0Labels = raw18547Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18547 raw18547Labels permutation289 permutation5
    mixedMoment B raw18547step0 raw18547step0Labels = mixedMoment B raw18547step1 raw18547step1Labels := by
      have ha : raw18547step1 = -raw18547step0 := by apply Matrix.ext; change ∀ i j, raw18547step1 i j = -(raw18547step0 i j); unfold raw18547step1 raw18547step0; decide +kernel
      have hl : raw18547step1Labels = raw18547step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18547step1 raw18547step1Labels = mixedMoment B raw18547step2 raw18547step2Labels := by
      have ha : raw18547step2 = raw18547step1 := by apply Matrix.ext; unfold raw18547step2 raw18547step1; decide +kernel
      have hl : raw18547step1Labels = labelEmbedding8 ∘ raw18547step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18547step1 raw18547step1Labels raw18547step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5123 node5123Labels := by rfl

def raw18548 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18548Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18548step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw18548step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18548step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw18548step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18548 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18548 raw18548Labels = mixedMoment B node5391 node5391Labels := by
  calc
    mixedMoment B raw18548 raw18548Labels = mixedMoment B raw18548step0 raw18548step0Labels := by
      have ha : raw18548step0 = (fun i j => raw18548 (permutation659 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18548step0 raw18548; decide +kernel
      have hl : raw18548step0Labels = raw18548Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18548 raw18548Labels permutation659 permutation5
    mixedMoment B raw18548step0 raw18548step0Labels = mixedMoment B raw18548step1 raw18548step1Labels := by
      have ha : raw18548step1 = raw18548step0 := by apply Matrix.ext; unfold raw18548step1 raw18548step0; decide +kernel
      have hl : raw18548step0Labels = labelEmbedding8 ∘ raw18548step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18548step0 raw18548step0Labels raw18548step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5391 node5391Labels := by rfl

def raw18549 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw18549Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18549step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw18549step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18549step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18549step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18549step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18549step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18549step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18549step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18549 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18549 raw18549Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw18549 raw18549Labels = mixedMoment B raw18549step0 raw18549step0Labels := by
      have hz : ∀ j, raw18549 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18549step0 = (fun i j => raw18549 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18549step0 raw18549; decide +kernel
      have hl : raw18549step0Labels = raw18549Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18549 raw18549Labels permutation434 hz
    mixedMoment B raw18549step0 raw18549step0Labels = mixedMoment B raw18549step1 raw18549step1Labels := by
      have ha : raw18549step1 = (fun i j => raw18549step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18549step1 raw18549step0; decide +kernel
      have hl : raw18549step1Labels = raw18549step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18549step0 raw18549step0Labels permutation151 permutation3
    mixedMoment B raw18549step1 raw18549step1Labels = mixedMoment B raw18549step2 raw18549step2Labels := by
      have ha : raw18549step2 = -raw18549step1 := by apply Matrix.ext; change ∀ i j, raw18549step2 i j = -(raw18549step1 i j); unfold raw18549step2 raw18549step1; decide +kernel
      have hl : raw18549step2Labels = raw18549step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18549step2 raw18549step2Labels = mixedMoment B raw18549step3 raw18549step3Labels := by
      have ha : raw18549step3 = raw18549step2 := by apply Matrix.ext; unfold raw18549step3 raw18549step2; decide +kernel
      have hl : raw18549step2Labels = labelEmbedding6 ∘ raw18549step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18549step2 raw18549step2Labels raw18549step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw18550 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0]]
def raw18550Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18550step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw18550step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18550step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18550step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18550step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18550step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18550step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18550step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18550 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18550 raw18550Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw18550 raw18550Labels = mixedMoment B raw18550step0 raw18550step0Labels := by
      have hz : ∀ j, raw18550 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18550step0 = (fun i j => raw18550 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18550step0 raw18550; decide +kernel
      have hl : raw18550step0Labels = raw18550Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18550 raw18550Labels permutation520 hz
    mixedMoment B raw18550step0 raw18550step0Labels = mixedMoment B raw18550step1 raw18550step1Labels := by
      have ha : raw18550step1 = (fun i j => raw18550step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18550step1 raw18550step0; decide +kernel
      have hl : raw18550step1Labels = raw18550step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18550step0 raw18550step0Labels permutation151 permutation3
    mixedMoment B raw18550step1 raw18550step1Labels = mixedMoment B raw18550step2 raw18550step2Labels := by
      have ha : raw18550step2 = -raw18550step1 := by apply Matrix.ext; change ∀ i j, raw18550step2 i j = -(raw18550step1 i j); unfold raw18550step2 raw18550step1; decide +kernel
      have hl : raw18550step2Labels = raw18550step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18550step2 raw18550step2Labels = mixedMoment B raw18550step3 raw18550step3Labels := by
      have ha : raw18550step3 = raw18550step2 := by apply Matrix.ext; unfold raw18550step3 raw18550step2; decide +kernel
      have hl : raw18550step2Labels = labelEmbedding6 ∘ raw18550step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18550step2 raw18550step2Labels raw18550step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw18551 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 3, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18551Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18551step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18551step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18551 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18551 raw18551Labels = mixedMoment B node3563 node3563Labels := by
  calc
    mixedMoment B raw18551 raw18551Labels = mixedMoment B raw18551step0 raw18551step0Labels := by
      have ha : raw18551step0 = (fun i j => raw18551 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18551step0 raw18551; decide +kernel
      have hl : raw18551step0Labels = raw18551Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18551 raw18551Labels permutation265 permutation3
    _ = mixedMoment B node3563 node3563Labels := by rfl

def raw18552 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18552Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18552step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw18552step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18552step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2]]
def raw18552step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18552 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18552 raw18552Labels = mixedMoment B node4007 node4007Labels := by
  calc
    mixedMoment B raw18552 raw18552Labels = mixedMoment B raw18552step0 raw18552step0Labels := by
      have ha : raw18552step0 = (fun i j => raw18552 (permutation216 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18552step0 raw18552; decide +kernel
      have hl : raw18552step0Labels = raw18552Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18552 raw18552Labels permutation216 permutation6
    mixedMoment B raw18552step0 raw18552step0Labels = mixedMoment B raw18552step1 raw18552step1Labels := by
      have ha : raw18552step1 = -raw18552step0 := by apply Matrix.ext; change ∀ i j, raw18552step1 i j = -(raw18552step0 i j); unfold raw18552step1 raw18552step0; decide +kernel
      have hl : raw18552step1Labels = raw18552step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4007 node4007Labels := by rfl

def raw18553 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18553Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18553step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw18553step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18553step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw18553step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18553step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18553step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18553 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18553 raw18553Labels = mixedMoment B node4010 node4010Labels := by
  calc
    mixedMoment B raw18553 raw18553Labels = mixedMoment B raw18553step0 raw18553step0Labels := by
      have hz : ∀ j, raw18553 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18553step0 = (fun i j => raw18553 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18553step0 raw18553; decide +kernel
      have hl : raw18553step0Labels = raw18553Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18553 raw18553Labels permutation434 hz
    mixedMoment B raw18553step0 raw18553step0Labels = mixedMoment B raw18553step1 raw18553step1Labels := by
      have ha : raw18553step1 = (fun i j => raw18553step0 (permutation49 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18553step1 raw18553step0; decide +kernel
      have hl : raw18553step1Labels = raw18553step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18553step0 raw18553step0Labels permutation49 permutation6
    mixedMoment B raw18553step1 raw18553step1Labels = mixedMoment B raw18553step2 raw18553step2Labels := by
      have ha : raw18553step2 = -raw18553step1 := by apply Matrix.ext; change ∀ i j, raw18553step2 i j = -(raw18553step1 i j); unfold raw18553step2 raw18553step1; decide +kernel
      have hl : raw18553step2Labels = raw18553step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4010 node4010Labels := by rfl

def raw18554 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw18554Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18554step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw18554step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18554step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw18554step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18554step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18554step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18554 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18554 raw18554Labels = mixedMoment B node4010 node4010Labels := by
  calc
    mixedMoment B raw18554 raw18554Labels = mixedMoment B raw18554step0 raw18554step0Labels := by
      have hz : ∀ j, raw18554 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18554step0 = (fun i j => raw18554 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18554step0 raw18554; decide +kernel
      have hl : raw18554step0Labels = raw18554Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18554 raw18554Labels permutation520 hz
    mixedMoment B raw18554step0 raw18554step0Labels = mixedMoment B raw18554step1 raw18554step1Labels := by
      have ha : raw18554step1 = (fun i j => raw18554step0 (permutation49 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18554step1 raw18554step0; decide +kernel
      have hl : raw18554step1Labels = raw18554step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18554step0 raw18554step0Labels permutation49 permutation6
    mixedMoment B raw18554step1 raw18554step1Labels = mixedMoment B raw18554step2 raw18554step2Labels := by
      have ha : raw18554step2 = -raw18554step1 := by apply Matrix.ext; change ∀ i j, raw18554step2 i j = -(raw18554step1 i j); unfold raw18554step2 raw18554step1; decide +kernel
      have hl : raw18554step2Labels = raw18554step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4010 node4010Labels := by rfl

def raw18555 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw18555Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18555step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0]]
def raw18555step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18555step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw18555step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw18555step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18555step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18555 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18555 raw18555Labels = mixedMoment B node4010 node4010Labels := by
  calc
    mixedMoment B raw18555 raw18555Labels = mixedMoment B raw18555step0 raw18555step0Labels := by
      have hz : ∀ j, raw18555 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw18555step0 = (fun i j => raw18555 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw18555step0 raw18555; decide +kernel
      have hl : raw18555step0Labels = raw18555Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18555 raw18555Labels permutation590 hz
    mixedMoment B raw18555step0 raw18555step0Labels = mixedMoment B raw18555step1 raw18555step1Labels := by
      have ha : raw18555step1 = (fun i j => raw18555step0 (permutation49 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18555step1 raw18555step0; decide +kernel
      have hl : raw18555step1Labels = raw18555step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18555step0 raw18555step0Labels permutation49 permutation6
    mixedMoment B raw18555step1 raw18555step1Labels = mixedMoment B raw18555step2 raw18555step2Labels := by
      have ha : raw18555step2 = -raw18555step1 := by apply Matrix.ext; change ∀ i j, raw18555step2 i j = -(raw18555step1 i j); unfold raw18555step2 raw18555step1; decide +kernel
      have hl : raw18555step2Labels = raw18555step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4010 node4010Labels := by rfl

def raw18556 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18556Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18556step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18556step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18556 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18556 raw18556Labels = mixedMoment B node3076 node3076Labels := by
  calc
    mixedMoment B raw18556 raw18556Labels = mixedMoment B raw18556step0 raw18556step0Labels := by
      have ha : raw18556step0 = (fun i j => raw18556 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18556step0 raw18556; decide +kernel
      have hl : raw18556step0Labels = raw18556Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18556 raw18556Labels permutation152 permutation3
    _ = mixedMoment B node3076 node3076Labels := by rfl

def raw18557 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18557Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18557step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw18557step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18557 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18557 raw18557Labels = mixedMoment B node3390 node3390Labels := by
  calc
    mixedMoment B raw18557 raw18557Labels = mixedMoment B raw18557step0 raw18557step0Labels := by
      have ha : raw18557step0 = (fun i j => raw18557 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18557step0 raw18557; decide +kernel
      have hl : raw18557step0Labels = raw18557Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18557 raw18557Labels permutation265 permutation3
    _ = mixedMoment B node3390 node3390Labels := by rfl

def raw18558 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw18558Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18558step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw18558step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18558step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18558step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18558 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18558 raw18558Labels = mixedMoment B node4029 node4029Labels := by
  calc
    mixedMoment B raw18558 raw18558Labels = mixedMoment B raw18558step0 raw18558step0Labels := by
      have hz : ∀ j, raw18558 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18558step0 = (fun i j => raw18558 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18558step0 raw18558; decide +kernel
      have hl : raw18558step0Labels = raw18558Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18558 raw18558Labels permutation434 hz
    mixedMoment B raw18558step0 raw18558step0Labels = mixedMoment B raw18558step1 raw18558step1Labels := by
      have ha : raw18558step1 = (fun i j => raw18558step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18558step1 raw18558step0; decide +kernel
      have hl : raw18558step1Labels = raw18558step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18558step0 raw18558step0Labels permutation32 permutation3
    _ = mixedMoment B node4029 node4029Labels := by rfl

def raw18559 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw18559Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18559step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw18559step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw18559step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw18559step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18559 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18559 raw18559Labels = mixedMoment B node4029 node4029Labels := by
  calc
    mixedMoment B raw18559 raw18559Labels = mixedMoment B raw18559step0 raw18559step0Labels := by
      have hz : ∀ j, raw18559 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18559step0 = (fun i j => raw18559 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18559step0 raw18559; decide +kernel
      have hl : raw18559step0Labels = raw18559Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18559 raw18559Labels permutation520 hz
    mixedMoment B raw18559step0 raw18559step0Labels = mixedMoment B raw18559step1 raw18559step1Labels := by
      have ha : raw18559step1 = (fun i j => raw18559step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18559step1 raw18559step0; decide +kernel
      have hl : raw18559step1Labels = raw18559step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18559step0 raw18559step0Labels permutation32 permutation3
    _ = mixedMoment B node4029 node4029Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
