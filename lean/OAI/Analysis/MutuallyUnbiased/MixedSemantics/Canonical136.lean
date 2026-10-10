import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw17408 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17408Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17408step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17408step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17408step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17408step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17408step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17408 raw17408Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw17408 raw17408Labels = mixedMoment B raw17408step0 raw17408step0Labels := by
      have hz : ∀ j, raw17408 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17408step0 = (fun i j => raw17408 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17408step0 raw17408; decide +kernel
      have hl : raw17408step0Labels = raw17408Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17408 raw17408Labels permutation346 hz
    mixedMoment B raw17408step0 raw17408step0Labels = mixedMoment B raw17408step1 raw17408step1Labels := by
      have ha : raw17408step1 = (fun i j => raw17408step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17408step1 raw17408step0; decide +kernel
      have hl : raw17408step1Labels = raw17408step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17408step0 raw17408step0Labels permutation151 permutation6
    mixedMoment B raw17408step1 raw17408step1Labels = mixedMoment B raw17408step2 raw17408step2Labels := by
      have ha : raw17408step2 = -raw17408step1 := by apply Matrix.ext; change ∀ i j, raw17408step2 i j = -(raw17408step1 i j); unfold raw17408step2 raw17408step1; decide +kernel
      have hl : raw17408step2Labels = raw17408step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3876 node3876Labels := by rfl

def raw17409 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw17409Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17409step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17409step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17409 raw17409Labels = mixedMoment B node2728 node2728Labels := by
  calc
    mixedMoment B raw17409 raw17409Labels = mixedMoment B raw17409step0 raw17409step0Labels := by
      have ha : raw17409step0 = (fun i j => raw17409 (permutation538 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17409step0 raw17409; decide +kernel
      have hl : raw17409step0Labels = raw17409Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17409 raw17409Labels permutation538 permutation3
    _ = mixedMoment B node2728 node2728Labels := by rfl

def raw17410 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17410Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17410step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17410step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17410step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17410step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17410 raw17410Labels = mixedMoment B node3807 node3807Labels := by
  calc
    mixedMoment B raw17410 raw17410Labels = mixedMoment B raw17410step0 raw17410step0Labels := by
      have hz : ∀ j, raw17410 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17410step0 = (fun i j => raw17410 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17410step0 raw17410; decide +kernel
      have hl : raw17410step0Labels = raw17410Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17410 raw17410Labels permutation434 hz
    mixedMoment B raw17410step0 raw17410step0Labels = mixedMoment B raw17410step1 raw17410step1Labels := by
      have ha : raw17410step1 = (fun i j => raw17410step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17410step1 raw17410step0; decide +kernel
      have hl : raw17410step1Labels = raw17410step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17410step0 raw17410step0Labels permutation32 permutation6
    _ = mixedMoment B node3807 node3807Labels := by rfl

def raw17411 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17411Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17411step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17411step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17411step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 0, 1], ![0, -2, 2]]
def raw17411step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17411step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17411step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17411step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17411step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17411 raw17411Labels = mixedMoment B node3861 node3861Labels := by
  calc
    mixedMoment B raw17411 raw17411Labels = mixedMoment B raw17411step0 raw17411step0Labels := by
      have hz : ∀ j, raw17411 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17411step0 = (fun i j => raw17411 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17411step0 raw17411; decide +kernel
      have hl : raw17411step0Labels = raw17411Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17411 raw17411Labels permutation434 hz
    mixedMoment B raw17411step0 raw17411step0Labels = mixedMoment B raw17411step1 raw17411step1Labels := by
      have hz : ∀ j, raw17411step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17411step1 = (fun i j => raw17411step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17411step1 raw17411step0; decide +kernel
      have hl : raw17411step1Labels = raw17411step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17411step0 raw17411step0Labels permutation80 hz
    mixedMoment B raw17411step1 raw17411step1Labels = mixedMoment B raw17411step2 raw17411step2Labels := by
      have ha : raw17411step2 = (fun i j => raw17411step1 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17411step2 raw17411step1; decide +kernel
      have hl : raw17411step2Labels = raw17411step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17411step1 raw17411step1Labels permutation31 permutation6
    mixedMoment B raw17411step2 raw17411step2Labels = mixedMoment B raw17411step3 raw17411step3Labels := by
      have ha : raw17411step3 = -raw17411step2 := by apply Matrix.ext; change ∀ i j, raw17411step3 i j = -(raw17411step2 i j); unfold raw17411step3 raw17411step2; decide +kernel
      have hl : raw17411step3Labels = raw17411step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3861 node3861Labels := by rfl

def raw17412 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17412Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17412step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17412step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17412step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17412step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17412 raw17412Labels = mixedMoment B node3838 node3838Labels := by
  calc
    mixedMoment B raw17412 raw17412Labels = mixedMoment B raw17412step0 raw17412step0Labels := by
      have ha : raw17412step0 = (fun i j => raw17412 (permutation682 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17412step0 raw17412; decide +kernel
      have hl : raw17412step0Labels = raw17412Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17412 raw17412Labels permutation682 permutation6
    mixedMoment B raw17412step0 raw17412step0Labels = mixedMoment B raw17412step1 raw17412step1Labels := by
      have ha : raw17412step1 = -raw17412step0 := by apply Matrix.ext; change ∀ i j, raw17412step1 i j = -(raw17412step0 i j); unfold raw17412step1 raw17412step0; decide +kernel
      have hl : raw17412step1Labels = raw17412step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3838 node3838Labels := by rfl

def raw17413 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw17413Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw17413step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17413step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw17413step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17413step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17413step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17413 raw17413Labels = mixedMoment B node3564 node3564Labels := by
  calc
    mixedMoment B raw17413 raw17413Labels = mixedMoment B raw17413step0 raw17413step0Labels := by
      have hz : ∀ j, raw17413 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17413step0 = (fun i j => raw17413 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17413step0 raw17413; decide +kernel
      have hl : raw17413step0Labels = raw17413Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17413 raw17413Labels permutation434 hz
    mixedMoment B raw17413step0 raw17413step0Labels = mixedMoment B raw17413step1 raw17413step1Labels := by
      have ha : raw17413step1 = (fun i j => raw17413step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17413step1 raw17413step0; decide +kernel
      have hl : raw17413step1Labels = raw17413step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17413step0 raw17413step0Labels permutation151 permutation6
    mixedMoment B raw17413step1 raw17413step1Labels = mixedMoment B raw17413step2 raw17413step2Labels := by
      have ha : raw17413step2 = -raw17413step1 := by apply Matrix.ext; change ∀ i j, raw17413step2 i j = -(raw17413step1 i j); unfold raw17413step2 raw17413step1; decide +kernel
      have hl : raw17413step2Labels = raw17413step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3564 node3564Labels := by rfl

def raw17414 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw17414Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17414step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw17414step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17414step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17414step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17414step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17414step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17414 raw17414Labels = mixedMoment B node3565 node3565Labels := by
  calc
    mixedMoment B raw17414 raw17414Labels = mixedMoment B raw17414step0 raw17414step0Labels := by
      have hz : ∀ j, raw17414 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17414step0 = (fun i j => raw17414 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17414step0 raw17414; decide +kernel
      have hl : raw17414step0Labels = raw17414Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17414 raw17414Labels permutation434 hz
    mixedMoment B raw17414step0 raw17414step0Labels = mixedMoment B raw17414step1 raw17414step1Labels := by
      have ha : raw17414step1 = (fun i j => raw17414step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17414step1 raw17414step0; decide +kernel
      have hl : raw17414step1Labels = raw17414step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17414step0 raw17414step0Labels permutation151 permutation6
    mixedMoment B raw17414step1 raw17414step1Labels = mixedMoment B raw17414step2 raw17414step2Labels := by
      have ha : raw17414step2 = -raw17414step1 := by apply Matrix.ext; change ∀ i j, raw17414step2 i j = -(raw17414step1 i j); unfold raw17414step2 raw17414step1; decide +kernel
      have hl : raw17414step2Labels = raw17414step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3565 node3565Labels := by rfl

def raw17415 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw17415Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17415step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw17415step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17415step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-2, 1, 1], ![1, -3, 2]]
def raw17415step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17415step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17415step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17415step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17415step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17415 raw17415Labels = mixedMoment B node3583 node3583Labels := by
  calc
    mixedMoment B raw17415 raw17415Labels = mixedMoment B raw17415step0 raw17415step0Labels := by
      have hz : ∀ j, raw17415 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17415step0 = (fun i j => raw17415 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17415step0 raw17415; decide +kernel
      have hl : raw17415step0Labels = raw17415Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17415 raw17415Labels permutation434 hz
    mixedMoment B raw17415step0 raw17415step0Labels = mixedMoment B raw17415step1 raw17415step1Labels := by
      have hz : ∀ j, raw17415step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17415step1 = (fun i j => raw17415step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17415step1 raw17415step0; decide +kernel
      have hl : raw17415step1Labels = raw17415step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17415step0 raw17415step0Labels permutation80 hz
    mixedMoment B raw17415step1 raw17415step1Labels = mixedMoment B raw17415step2 raw17415step2Labels := by
      have ha : raw17415step2 = (fun i j => raw17415step1 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17415step2 raw17415step1; decide +kernel
      have hl : raw17415step2Labels = raw17415step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17415step1 raw17415step1Labels permutation31 permutation6
    mixedMoment B raw17415step2 raw17415step2Labels = mixedMoment B raw17415step3 raw17415step3Labels := by
      have ha : raw17415step3 = -raw17415step2 := by apply Matrix.ext; change ∀ i j, raw17415step3 i j = -(raw17415step2 i j); unfold raw17415step3 raw17415step2; decide +kernel
      have hl : raw17415step3Labels = raw17415step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3583 node3583Labels := by rfl

def raw17416 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw17416Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17416step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17416step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17416step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17416step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17416 raw17416Labels = mixedMoment B node3558 node3558Labels := by
  calc
    mixedMoment B raw17416 raw17416Labels = mixedMoment B raw17416step0 raw17416step0Labels := by
      have ha : raw17416step0 = (fun i j => raw17416 (permutation682 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17416step0 raw17416; decide +kernel
      have hl : raw17416step0Labels = raw17416Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17416 raw17416Labels permutation682 permutation6
    mixedMoment B raw17416step0 raw17416step0Labels = mixedMoment B raw17416step1 raw17416step1Labels := by
      have ha : raw17416step1 = -raw17416step0 := by apply Matrix.ext; change ∀ i j, raw17416step1 i j = -(raw17416step0 i j); unfold raw17416step1 raw17416step0; decide +kernel
      have hl : raw17416step1Labels = raw17416step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3558 node3558Labels := by rfl

def raw17417 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-3, 2, 1], ![1, -3, 2]]
def raw17417Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-3, 2, 1], ![1, -3, 2]]
def raw17417step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17417step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw17417step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17417 raw17417Labels = mixedMoment B node2735 node2735Labels := by
  calc
    mixedMoment B raw17417 raw17417Labels = mixedMoment B raw17417step0 raw17417step0Labels := by
      have hz : ∀ j, raw17417 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17417step0 = (fun i j => raw17417 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17417step0 raw17417; decide +kernel
      have hl : raw17417step0Labels = raw17417Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17417 raw17417Labels permutation434 hz
    mixedMoment B raw17417step0 raw17417step0Labels = mixedMoment B raw17417step1 raw17417step1Labels := by
      have ha : raw17417step1 = (fun i j => raw17417step0 (permutation110 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17417step1 raw17417step0; decide +kernel
      have hl : raw17417step1Labels = raw17417step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17417step0 raw17417step0Labels permutation110 permutation3
    _ = mixedMoment B node2735 node2735Labels := by rfl

def raw17418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17418Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17418step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17418step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17418step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17418step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17418step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17418 raw17418Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw17418 raw17418Labels = mixedMoment B raw17418step0 raw17418step0Labels := by
      have hz : ∀ j, raw17418 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw17418step0 = (fun i j => raw17418 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw17418step0 raw17418; decide +kernel
      have hl : raw17418step0Labels = raw17418Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17418 raw17418Labels permutation265 hz
    mixedMoment B raw17418step0 raw17418step0Labels = mixedMoment B raw17418step1 raw17418step1Labels := by
      have ha : raw17418step1 = (fun i j => raw17418step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17418step1 raw17418step0; decide +kernel
      have hl : raw17418step1Labels = raw17418step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17418step0 raw17418step0Labels permutation38 permutation3
    mixedMoment B raw17418step1 raw17418step1Labels = mixedMoment B raw17418step2 raw17418step2Labels := by
      have ha : raw17418step2 = raw17418step1 := by apply Matrix.ext; unfold raw17418step2 raw17418step1; decide +kernel
      have hl : raw17418step1Labels = labelEmbedding6 ∘ raw17418step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17418step1 raw17418step1Labels raw17418step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw17419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17419Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17419step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17419 raw17419Labels = mixedMoment B node5483 node5483Labels := by
  calc
    mixedMoment B raw17419 raw17419Labels = mixedMoment B raw17419step0 raw17419step0Labels := by
      have hz : ∀ j, raw17419 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw17419step0 = (fun i j => raw17419 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw17419step0 raw17419; decide +kernel
      have hl : raw17419step0Labels = raw17419Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17419 raw17419Labels permutation265 hz
    _ = mixedMoment B node5483 node5483Labels := by rfl

def raw17420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17420Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17420step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17420step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17420step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17420step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17420step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17420 raw17420Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw17420 raw17420Labels = mixedMoment B raw17420step0 raw17420step0Labels := by
      have hz : ∀ j, raw17420 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw17420step0 = (fun i j => raw17420 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw17420step0 raw17420; decide +kernel
      have hl : raw17420step0Labels = raw17420Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17420 raw17420Labels permutation265 hz
    mixedMoment B raw17420step0 raw17420step0Labels = mixedMoment B raw17420step1 raw17420step1Labels := by
      have ha : raw17420step1 = (fun i j => raw17420step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17420step1 raw17420step0; decide +kernel
      have hl : raw17420step1Labels = raw17420step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17420step0 raw17420step0Labels permutation38 permutation3
    mixedMoment B raw17420step1 raw17420step1Labels = mixedMoment B raw17420step2 raw17420step2Labels := by
      have ha : raw17420step2 = raw17420step1 := by apply Matrix.ext; unfold raw17420step2 raw17420step1; decide +kernel
      have hl : raw17420step1Labels = labelEmbedding6 ∘ raw17420step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17420step1 raw17420step1Labels raw17420step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw17421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw17421Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17421step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw17421step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17421step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw17421step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17421 raw17421Labels = mixedMoment B node5491 node5491Labels := by
  calc
    mixedMoment B raw17421 raw17421Labels = mixedMoment B raw17421step0 raw17421step0Labels := by
      have hz : ∀ j, raw17421 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17421step0 = (fun i j => raw17421 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17421step0 raw17421; decide +kernel
      have hl : raw17421step0Labels = raw17421Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17421 raw17421Labels permutation520 hz
    mixedMoment B raw17421step0 raw17421step0Labels = mixedMoment B raw17421step1 raw17421step1Labels := by
      have hz : ∀ j, raw17421step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw17421step1 = (fun i j => raw17421step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw17421step1 raw17421step0; decide +kernel
      have hl : raw17421step1Labels = raw17421step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17421step0 raw17421step0Labels permutation56 hz
    _ = mixedMoment B node5491 node5491Labels := by rfl

def raw17422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17422Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17422step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17422step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17422step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17422step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17422 raw17422Labels = mixedMoment B node5059 node5059Labels := by
  calc
    mixedMoment B raw17422 raw17422Labels = mixedMoment B raw17422step0 raw17422step0Labels := by
      have ha : raw17422step0 = (fun i j => raw17422 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17422step0 raw17422; decide +kernel
      have hl : raw17422step0Labels = raw17422Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17422 raw17422Labels permutation160 permutation3
    mixedMoment B raw17422step0 raw17422step0Labels = mixedMoment B raw17422step1 raw17422step1Labels := by
      have ha : raw17422step1 = raw17422step0 := by apply Matrix.ext; unfold raw17422step1 raw17422step0; decide +kernel
      have hl : raw17422step0Labels = labelEmbedding6 ∘ raw17422step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17422step0 raw17422step0Labels raw17422step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5059 node5059Labels := by rfl

def raw17423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17423Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17423step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17423step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17423step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17423step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17423 raw17423Labels = mixedMoment B node5346 node5346Labels := by
  calc
    mixedMoment B raw17423 raw17423Labels = mixedMoment B raw17423step0 raw17423step0Labels := by
      have ha : raw17423step0 = (fun i j => raw17423 (permutation273 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17423step0 raw17423; decide +kernel
      have hl : raw17423step0Labels = raw17423Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17423 raw17423Labels permutation273 permutation3
    mixedMoment B raw17423step0 raw17423step0Labels = mixedMoment B raw17423step1 raw17423step1Labels := by
      have ha : raw17423step1 = raw17423step0 := by apply Matrix.ext; unfold raw17423step1 raw17423step0; decide +kernel
      have hl : raw17423step0Labels = labelEmbedding6 ∘ raw17423step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17423step0 raw17423step0Labels raw17423step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5346 node5346Labels := by rfl

def raw17424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17424Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17424step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17424step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17424step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17424step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17424 raw17424Labels = mixedMoment B node5467 node5467Labels := by
  calc
    mixedMoment B raw17424 raw17424Labels = mixedMoment B raw17424step0 raw17424step0Labels := by
      have ha : raw17424step0 = (fun i j => raw17424 (permutation202 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17424step0 raw17424; decide +kernel
      have hl : raw17424step0Labels = raw17424Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17424 raw17424Labels permutation202 permutation3
    mixedMoment B raw17424step0 raw17424step0Labels = mixedMoment B raw17424step1 raw17424step1Labels := by
      have ha : raw17424step1 = raw17424step0 := by apply Matrix.ext; unfold raw17424step1 raw17424step0; decide +kernel
      have hl : raw17424step0Labels = labelEmbedding6 ∘ raw17424step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17424step0 raw17424step0Labels raw17424step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5467 node5467Labels := by rfl

def raw17425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw17425Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw17425step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17425step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17425step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17425step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17425step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17425step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17425step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17425 raw17425Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw17425 raw17425Labels = mixedMoment B raw17425step0 raw17425step0Labels := by
      have hz : ∀ j, raw17425 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17425step0 = (fun i j => raw17425 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17425step0 raw17425; decide +kernel
      have hl : raw17425step0Labels = raw17425Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17425 raw17425Labels permutation520 hz
    mixedMoment B raw17425step0 raw17425step0Labels = mixedMoment B raw17425step1 raw17425step1Labels := by
      have ha : raw17425step1 = (fun i j => raw17425step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17425step1 raw17425step0; decide +kernel
      have hl : raw17425step1Labels = raw17425step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17425step0 raw17425step0Labels permutation145 permutation3
    mixedMoment B raw17425step1 raw17425step1Labels = mixedMoment B raw17425step2 raw17425step2Labels := by
      have ha : raw17425step2 = -raw17425step1 := by apply Matrix.ext; change ∀ i j, raw17425step2 i j = -(raw17425step1 i j); unfold raw17425step2 raw17425step1; decide +kernel
      have hl : raw17425step2Labels = raw17425step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17425step2 raw17425step2Labels = mixedMoment B raw17425step3 raw17425step3Labels := by
      have ha : raw17425step3 = raw17425step2 := by apply Matrix.ext; unfold raw17425step3 raw17425step2; decide +kernel
      have hl : raw17425step2Labels = labelEmbedding6 ∘ raw17425step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17425step2 raw17425step2Labels raw17425step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw17426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17426Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17426step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17426step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17426step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17426step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17426 raw17426Labels = mixedMoment B node5073 node5073Labels := by
  calc
    mixedMoment B raw17426 raw17426Labels = mixedMoment B raw17426step0 raw17426step0Labels := by
      have ha : raw17426step0 = (fun i j => raw17426 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17426step0 raw17426; decide +kernel
      have hl : raw17426step0Labels = raw17426Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17426 raw17426Labels permutation152 permutation3
    mixedMoment B raw17426step0 raw17426step0Labels = mixedMoment B raw17426step1 raw17426step1Labels := by
      have ha : raw17426step1 = raw17426step0 := by apply Matrix.ext; unfold raw17426step1 raw17426step0; decide +kernel
      have hl : raw17426step0Labels = labelEmbedding6 ∘ raw17426step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17426step0 raw17426step0Labels raw17426step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5073 node5073Labels := by rfl

def raw17427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17427Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17427step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17427step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17427step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17427step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17427 raw17427Labels = mixedMoment B node5352 node5352Labels := by
  calc
    mixedMoment B raw17427 raw17427Labels = mixedMoment B raw17427step0 raw17427step0Labels := by
      have ha : raw17427step0 = (fun i j => raw17427 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17427step0 raw17427; decide +kernel
      have hl : raw17427step0Labels = raw17427Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17427 raw17427Labels permutation265 permutation3
    mixedMoment B raw17427step0 raw17427step0Labels = mixedMoment B raw17427step1 raw17427step1Labels := by
      have ha : raw17427step1 = raw17427step0 := by apply Matrix.ext; unfold raw17427step1 raw17427step0; decide +kernel
      have hl : raw17427step0Labels = labelEmbedding6 ∘ raw17427step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17427step0 raw17427step0Labels raw17427step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5352 node5352Labels := by rfl

def raw17428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17428Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17428step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17428step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17428 raw17428Labels = mixedMoment B node5476 node5476Labels := by
  calc
    mixedMoment B raw17428 raw17428Labels = mixedMoment B raw17428step0 raw17428step0Labels := by
      have ha : raw17428step0 = (fun i j => raw17428 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17428step0 raw17428; decide +kernel
      have hl : raw17428step0Labels = raw17428Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17428 raw17428Labels permutation178 permutation2
    _ = mixedMoment B node5476 node5476Labels := by rfl

def raw17429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw17429Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17429step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17429step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17429step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17429step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17429step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17429step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17429 raw17429Labels = mixedMoment B node5483 node5483Labels := by
  calc
    mixedMoment B raw17429 raw17429Labels = mixedMoment B raw17429step0 raw17429step0Labels := by
      have hz : ∀ j, raw17429 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17429step0 = (fun i j => raw17429 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17429step0 raw17429; decide +kernel
      have hl : raw17429step0Labels = raw17429Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17429 raw17429Labels permutation520 hz
    mixedMoment B raw17429step0 raw17429step0Labels = mixedMoment B raw17429step1 raw17429step1Labels := by
      have ha : raw17429step1 = (fun i j => raw17429step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17429step1 raw17429step0; decide +kernel
      have hl : raw17429step1Labels = raw17429step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17429step0 raw17429step0Labels permutation151 permutation2
    mixedMoment B raw17429step1 raw17429step1Labels = mixedMoment B raw17429step2 raw17429step2Labels := by
      have ha : raw17429step2 = -raw17429step1 := by apply Matrix.ext; change ∀ i j, raw17429step2 i j = -(raw17429step1 i j); unfold raw17429step2 raw17429step1; decide +kernel
      have hl : raw17429step2Labels = raw17429step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5483 node5483Labels := by rfl

def raw17430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17430Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17430step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17430step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17430step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17430step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17430 raw17430Labels = mixedMoment B node5050 node5050Labels := by
  calc
    mixedMoment B raw17430 raw17430Labels = mixedMoment B raw17430step0 raw17430step0Labels := by
      have ha : raw17430step0 = (fun i j => raw17430 (permutation159 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17430step0 raw17430; decide +kernel
      have hl : raw17430step0Labels = raw17430Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17430 raw17430Labels permutation159 permutation3
    mixedMoment B raw17430step0 raw17430step0Labels = mixedMoment B raw17430step1 raw17430step1Labels := by
      have ha : raw17430step1 = raw17430step0 := by apply Matrix.ext; unfold raw17430step1 raw17430step0; decide +kernel
      have hl : raw17430step0Labels = labelEmbedding6 ∘ raw17430step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17430step0 raw17430step0Labels raw17430step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5050 node5050Labels := by rfl

def raw17431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17431Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17431step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17431step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17431step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17431step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17431 raw17431Labels = mixedMoment B node5341 node5341Labels := by
  calc
    mixedMoment B raw17431 raw17431Labels = mixedMoment B raw17431step0 raw17431step0Labels := by
      have ha : raw17431step0 = (fun i j => raw17431 (permutation272 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17431step0 raw17431; decide +kernel
      have hl : raw17431step0Labels = raw17431Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17431 raw17431Labels permutation272 permutation3
    mixedMoment B raw17431step0 raw17431step0Labels = mixedMoment B raw17431step1 raw17431step1Labels := by
      have ha : raw17431step1 = raw17431step0 := by apply Matrix.ext; unfold raw17431step1 raw17431step0; decide +kernel
      have hl : raw17431step0Labels = labelEmbedding6 ∘ raw17431step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17431step0 raw17431step0Labels raw17431step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5341 node5341Labels := by rfl

def raw17432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17432Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17432step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17432step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17432step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17432step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17432step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17432step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17432 raw17432Labels = mixedMoment B node5352 node5352Labels := by
  calc
    mixedMoment B raw17432 raw17432Labels = mixedMoment B raw17432step0 raw17432step0Labels := by
      have ha : raw17432step0 = (fun i j => raw17432 (permutation589 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17432step0 raw17432; decide +kernel
      have hl : raw17432step0Labels = raw17432Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17432 raw17432Labels permutation589 permutation3
    mixedMoment B raw17432step0 raw17432step0Labels = mixedMoment B raw17432step1 raw17432step1Labels := by
      have ha : raw17432step1 = -raw17432step0 := by apply Matrix.ext; change ∀ i j, raw17432step1 i j = -(raw17432step0 i j); unfold raw17432step1 raw17432step0; decide +kernel
      have hl : raw17432step1Labels = raw17432step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17432step1 raw17432step1Labels = mixedMoment B raw17432step2 raw17432step2Labels := by
      have ha : raw17432step2 = raw17432step1 := by apply Matrix.ext; unfold raw17432step2 raw17432step1; decide +kernel
      have hl : raw17432step1Labels = labelEmbedding6 ∘ raw17432step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17432step1 raw17432step1Labels raw17432step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5352 node5352Labels := by rfl

def raw17433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17433Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17433step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17433step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17433step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17433step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17433step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17433step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17433 raw17433Labels = mixedMoment B node5346 node5346Labels := by
  calc
    mixedMoment B raw17433 raw17433Labels = mixedMoment B raw17433step0 raw17433step0Labels := by
      have ha : raw17433step0 = (fun i j => raw17433 (permutation582 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17433step0 raw17433; decide +kernel
      have hl : raw17433step0Labels = raw17433Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17433 raw17433Labels permutation582 permutation3
    mixedMoment B raw17433step0 raw17433step0Labels = mixedMoment B raw17433step1 raw17433step1Labels := by
      have ha : raw17433step1 = -raw17433step0 := by apply Matrix.ext; change ∀ i j, raw17433step1 i j = -(raw17433step0 i j); unfold raw17433step1 raw17433step0; decide +kernel
      have hl : raw17433step1Labels = raw17433step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17433step1 raw17433step1Labels = mixedMoment B raw17433step2 raw17433step2Labels := by
      have ha : raw17433step2 = raw17433step1 := by apply Matrix.ext; unfold raw17433step2 raw17433step1; decide +kernel
      have hl : raw17433step1Labels = labelEmbedding6 ∘ raw17433step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17433step1 raw17433step1Labels raw17433step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5346 node5346Labels := by rfl

def raw17434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17434Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17434step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw17434step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17434step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw17434step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17434 raw17434Labels = mixedMoment B node5047 node5047Labels := by
  calc
    mixedMoment B raw17434 raw17434Labels = mixedMoment B raw17434step0 raw17434step0Labels := by
      have ha : raw17434step0 = (fun i j => raw17434 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17434step0 raw17434; decide +kernel
      have hl : raw17434step0Labels = raw17434Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17434 raw17434Labels permutation158 permutation3
    mixedMoment B raw17434step0 raw17434step0Labels = mixedMoment B raw17434step1 raw17434step1Labels := by
      have ha : raw17434step1 = raw17434step0 := by apply Matrix.ext; unfold raw17434step1 raw17434step0; decide +kernel
      have hl : raw17434step0Labels = labelEmbedding6 ∘ raw17434step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17434step0 raw17434step0Labels raw17434step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5047 node5047Labels := by rfl

def raw17435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17435Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17435step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw17435step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17435step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17435step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17435step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17435step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17435 raw17435Labels = mixedMoment B node5050 node5050Labels := by
  calc
    mixedMoment B raw17435 raw17435Labels = mixedMoment B raw17435step0 raw17435step0Labels := by
      have ha : raw17435step0 = (fun i j => raw17435 (permutation681 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17435step0 raw17435; decide +kernel
      have hl : raw17435step0Labels = raw17435Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17435 raw17435Labels permutation681 permutation3
    mixedMoment B raw17435step0 raw17435step0Labels = mixedMoment B raw17435step1 raw17435step1Labels := by
      have ha : raw17435step1 = -raw17435step0 := by apply Matrix.ext; change ∀ i j, raw17435step1 i j = -(raw17435step0 i j); unfold raw17435step1 raw17435step0; decide +kernel
      have hl : raw17435step1Labels = raw17435step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17435step1 raw17435step1Labels = mixedMoment B raw17435step2 raw17435step2Labels := by
      have ha : raw17435step2 = raw17435step1 := by apply Matrix.ext; unfold raw17435step2 raw17435step1; decide +kernel
      have hl : raw17435step1Labels = labelEmbedding6 ∘ raw17435step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17435step1 raw17435step1Labels raw17435step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5050 node5050Labels := by rfl

def raw17436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17436Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17436step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17436step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17436step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17436step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17436step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17436step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17436 raw17436Labels = mixedMoment B node5073 node5073Labels := by
  calc
    mixedMoment B raw17436 raw17436Labels = mixedMoment B raw17436step0 raw17436step0Labels := by
      have ha : raw17436step0 = (fun i j => raw17436 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17436step0 raw17436; decide +kernel
      have hl : raw17436step0Labels = raw17436Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17436 raw17436Labels permutation688 permutation3
    mixedMoment B raw17436step0 raw17436step0Labels = mixedMoment B raw17436step1 raw17436step1Labels := by
      have ha : raw17436step1 = -raw17436step0 := by apply Matrix.ext; change ∀ i j, raw17436step1 i j = -(raw17436step0 i j); unfold raw17436step1 raw17436step0; decide +kernel
      have hl : raw17436step1Labels = raw17436step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17436step1 raw17436step1Labels = mixedMoment B raw17436step2 raw17436step2Labels := by
      have ha : raw17436step2 = raw17436step1 := by apply Matrix.ext; unfold raw17436step2 raw17436step1; decide +kernel
      have hl : raw17436step1Labels = labelEmbedding6 ∘ raw17436step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17436step1 raw17436step1Labels raw17436step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5073 node5073Labels := by rfl

def raw17437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17437Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17437step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17437step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17437step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17437step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17437step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17437step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17437 raw17437Labels = mixedMoment B node5059 node5059Labels := by
  calc
    mixedMoment B raw17437 raw17437Labels = mixedMoment B raw17437step0 raw17437step0Labels := by
      have ha : raw17437step0 = (fun i j => raw17437 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17437step0 raw17437; decide +kernel
      have hl : raw17437step0Labels = raw17437Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17437 raw17437Labels permutation680 permutation3
    mixedMoment B raw17437step0 raw17437step0Labels = mixedMoment B raw17437step1 raw17437step1Labels := by
      have ha : raw17437step1 = -raw17437step0 := by apply Matrix.ext; change ∀ i j, raw17437step1 i j = -(raw17437step0 i j); unfold raw17437step1 raw17437step0; decide +kernel
      have hl : raw17437step1Labels = raw17437step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17437step1 raw17437step1Labels = mixedMoment B raw17437step2 raw17437step2Labels := by
      have ha : raw17437step2 = raw17437step1 := by apply Matrix.ext; unfold raw17437step2 raw17437step1; decide +kernel
      have hl : raw17437step1Labels = labelEmbedding6 ∘ raw17437step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17437step1 raw17437step1Labels raw17437step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5059 node5059Labels := by rfl

def raw17438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw17438Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17438step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw17438step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17438step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17438step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17438step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17438step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17438step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17438step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17438 raw17438Labels = mixedMoment B node5259 node5259Labels := by
  calc
    mixedMoment B raw17438 raw17438Labels = mixedMoment B raw17438step0 raw17438step0Labels := by
      have hz : ∀ j, raw17438 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17438step0 = (fun i j => raw17438 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17438step0 raw17438; decide +kernel
      have hl : raw17438step0Labels = raw17438Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17438 raw17438Labels permutation520 hz
    mixedMoment B raw17438step0 raw17438step0Labels = mixedMoment B raw17438step1 raw17438step1Labels := by
      have ha : raw17438step1 = (fun i j => raw17438step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17438step1 raw17438step0; decide +kernel
      have hl : raw17438step1Labels = raw17438step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17438step0 raw17438step0Labels permutation145 permutation3
    mixedMoment B raw17438step1 raw17438step1Labels = mixedMoment B raw17438step2 raw17438step2Labels := by
      have ha : raw17438step2 = -raw17438step1 := by apply Matrix.ext; change ∀ i j, raw17438step2 i j = -(raw17438step1 i j); unfold raw17438step2 raw17438step1; decide +kernel
      have hl : raw17438step2Labels = raw17438step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17438step2 raw17438step2Labels = mixedMoment B raw17438step3 raw17438step3Labels := by
      have ha : raw17438step3 = raw17438step2 := by apply Matrix.ext; unfold raw17438step3 raw17438step2; decide +kernel
      have hl : raw17438step2Labels = labelEmbedding6 ∘ raw17438step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17438step2 raw17438step2Labels raw17438step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5259 node5259Labels := by rfl

def raw17439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17439Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17439step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17439step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17439 raw17439Labels = mixedMoment B node3838 node3838Labels := by
  calc
    mixedMoment B raw17439 raw17439Labels = mixedMoment B raw17439step0 raw17439step0Labels := by
      have ha : raw17439step0 = (fun i j => raw17439 (permutation271 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17439step0 raw17439; decide +kernel
      have hl : raw17439step0Labels = raw17439Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17439 raw17439Labels permutation271 permutation3
    _ = mixedMoment B node3838 node3838Labels := by rfl

def raw17440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17440Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17440step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw17440step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17440step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17440step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17440 raw17440Labels = mixedMoment B node3980 node3980Labels := by
  calc
    mixedMoment B raw17440 raw17440Labels = mixedMoment B raw17440step0 raw17440step0Labels := by
      have ha : raw17440step0 = (fun i j => raw17440 (permutation684 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17440step0 raw17440; decide +kernel
      have hl : raw17440step0Labels = raw17440Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17440 raw17440Labels permutation684 permutation3
    mixedMoment B raw17440step0 raw17440step0Labels = mixedMoment B raw17440step1 raw17440step1Labels := by
      have ha : raw17440step1 = -raw17440step0 := by apply Matrix.ext; change ∀ i j, raw17440step1 i j = -(raw17440step0 i j); unfold raw17440step1 raw17440step0; decide +kernel
      have hl : raw17440step1Labels = raw17440step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3980 node3980Labels := by rfl

def raw17441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17441Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17441step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17441step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17441step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17441step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17441 raw17441Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw17441 raw17441Labels = mixedMoment B raw17441step0 raw17441step0Labels := by
      have ha : raw17441step0 = (fun i j => raw17441 (permutation677 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17441step0 raw17441; decide +kernel
      have hl : raw17441step0Labels = raw17441Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17441 raw17441Labels permutation677 permutation3
    mixedMoment B raw17441step0 raw17441step0Labels = mixedMoment B raw17441step1 raw17441step1Labels := by
      have ha : raw17441step1 = -raw17441step0 := by apply Matrix.ext; change ∀ i j, raw17441step1 i j = -(raw17441step0 i j); unfold raw17441step1 raw17441step0; decide +kernel
      have hl : raw17441step1Labels = raw17441step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3974 node3974Labels := by rfl

def raw17442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw17442Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw17442step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17442step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw17442step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17442step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17442step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17442 raw17442Labels = mixedMoment B node4013 node4013Labels := by
  calc
    mixedMoment B raw17442 raw17442Labels = mixedMoment B raw17442step0 raw17442step0Labels := by
      have hz : ∀ j, raw17442 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17442step0 = (fun i j => raw17442 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17442step0 raw17442; decide +kernel
      have hl : raw17442step0Labels = raw17442Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17442 raw17442Labels permutation520 hz
    mixedMoment B raw17442step0 raw17442step0Labels = mixedMoment B raw17442step1 raw17442step1Labels := by
      have ha : raw17442step1 = (fun i j => raw17442step0 (permutation144 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17442step1 raw17442step0; decide +kernel
      have hl : raw17442step1Labels = raw17442step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17442step0 raw17442step0Labels permutation144 permutation3
    mixedMoment B raw17442step1 raw17442step1Labels = mixedMoment B raw17442step2 raw17442step2Labels := by
      have ha : raw17442step2 = -raw17442step1 := by apply Matrix.ext; change ∀ i j, raw17442step2 i j = -(raw17442step1 i j); unfold raw17442step2 raw17442step1; decide +kernel
      have hl : raw17442step2Labels = raw17442step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4013 node4013Labels := by rfl

def raw17443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17443Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17443step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17443step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17443 raw17443Labels = mixedMoment B node4053 node4053Labels := by
  calc
    mixedMoment B raw17443 raw17443Labels = mixedMoment B raw17443step0 raw17443step0Labels := by
      have ha : raw17443step0 = (fun i j => raw17443 (permutation272 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17443step0 raw17443; decide +kernel
      have hl : raw17443step0Labels = raw17443Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17443 raw17443Labels permutation272 permutation3
    _ = mixedMoment B node4053 node4053Labels := by rfl

def raw17444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17444Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17444step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17444step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17444step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17444step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17444 raw17444Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw17444 raw17444Labels = mixedMoment B raw17444step0 raw17444step0Labels := by
      have hz : ∀ j, raw17444 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw17444step0 = (fun i j => raw17444 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw17444step0 raw17444; decide +kernel
      have hl : raw17444step0Labels = raw17444Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17444 raw17444Labels permutation265 hz
    mixedMoment B raw17444step0 raw17444step0Labels = mixedMoment B raw17444step1 raw17444step1Labels := by
      have ha : raw17444step1 = (fun i j => raw17444step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17444step1 raw17444step0; decide +kernel
      have hl : raw17444step1Labels = raw17444step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17444step0 raw17444step0Labels permutation38 permutation3
    _ = mixedMoment B node2723 node2723Labels := by rfl

def raw17445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17445Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17445step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17445step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17445step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17445step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17445step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17445 raw17445Labels = mixedMoment B node3981 node3981Labels := by
  calc
    mixedMoment B raw17445 raw17445Labels = mixedMoment B raw17445step0 raw17445step0Labels := by
      have hz : ∀ j, raw17445 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw17445step0 = (fun i j => raw17445 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw17445step0 raw17445; decide +kernel
      have hl : raw17445step0Labels = raw17445Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17445 raw17445Labels permutation265 hz
    mixedMoment B raw17445step0 raw17445step0Labels = mixedMoment B raw17445step1 raw17445step1Labels := by
      have ha : raw17445step1 = (fun i j => raw17445step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17445step1 raw17445step0; decide +kernel
      have hl : raw17445step1Labels = raw17445step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17445step0 raw17445step0Labels permutation151 permutation3
    mixedMoment B raw17445step1 raw17445step1Labels = mixedMoment B raw17445step2 raw17445step2Labels := by
      have ha : raw17445step2 = -raw17445step1 := by apply Matrix.ext; change ∀ i j, raw17445step2 i j = -(raw17445step1 i j); unfold raw17445step2 raw17445step1; decide +kernel
      have hl : raw17445step2Labels = raw17445step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3981 node3981Labels := by rfl

def raw17446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17446Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17446step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17446step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17446step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17446 raw17446Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw17446 raw17446Labels = mixedMoment B raw17446step0 raw17446step0Labels := by
      have hz : ∀ j, raw17446 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw17446step0 = (fun i j => raw17446 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw17446step0 raw17446; decide +kernel
      have hl : raw17446step0Labels = raw17446Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17446 raw17446Labels permutation265 hz
    mixedMoment B raw17446step0 raw17446step0Labels = mixedMoment B raw17446step1 raw17446step1Labels := by
      have ha : raw17446step1 = (fun i j => raw17446step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17446step1 raw17446step0; decide +kernel
      have hl : raw17446step1Labels = raw17446step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17446step0 raw17446step0Labels permutation38 permutation3
    _ = mixedMoment B node3958 node3958Labels := by rfl

def raw17447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw17447Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17447step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw17447step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17447step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw17447step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17447step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw17447step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17447 raw17447Labels = mixedMoment B node4014 node4014Labels := by
  calc
    mixedMoment B raw17447 raw17447Labels = mixedMoment B raw17447step0 raw17447step0Labels := by
      have hz : ∀ j, raw17447 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17447step0 = (fun i j => raw17447 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17447step0 raw17447; decide +kernel
      have hl : raw17447step0Labels = raw17447Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17447 raw17447Labels permutation520 hz
    mixedMoment B raw17447step0 raw17447step0Labels = mixedMoment B raw17447step1 raw17447step1Labels := by
      have hz : ∀ j, raw17447step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw17447step1 = (fun i j => raw17447step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw17447step1 raw17447step0; decide +kernel
      have hl : raw17447step1Labels = raw17447step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17447step0 raw17447step0Labels permutation56 hz
    mixedMoment B raw17447step1 raw17447step1Labels = mixedMoment B raw17447step2 raw17447step2Labels := by
      have ha : raw17447step2 = (fun i j => raw17447step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17447step2 raw17447step1; decide +kernel
      have hl : raw17447step2Labels = raw17447step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17447step1 raw17447step1Labels permutation10 permutation3
    _ = mixedMoment B node4014 node4014Labels := by rfl

def raw17448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17448Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17448step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17448step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17448step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17448step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17448 raw17448Labels = mixedMoment B node4013 node4013Labels := by
  calc
    mixedMoment B raw17448 raw17448Labels = mixedMoment B raw17448step0 raw17448step0Labels := by
      have hz : ∀ j, raw17448 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw17448step0 = (fun i j => raw17448 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw17448step0 raw17448; decide +kernel
      have hl : raw17448step0Labels = raw17448Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17448 raw17448Labels permutation265 hz
    mixedMoment B raw17448step0 raw17448step0Labels = mixedMoment B raw17448step1 raw17448step1Labels := by
      have ha : raw17448step1 = (fun i j => raw17448step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17448step1 raw17448step0; decide +kernel
      have hl : raw17448step1Labels = raw17448step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17448step0 raw17448step0Labels permutation39 permutation3
    _ = mixedMoment B node4013 node4013Labels := by rfl

def raw17449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17449Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17449step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17449step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17449 raw17449Labels = mixedMoment B node2462 node2462Labels := by
  calc
    mixedMoment B raw17449 raw17449Labels = mixedMoment B raw17449step0 raw17449step0Labels := by
      have ha : raw17449step0 = (fun i j => raw17449 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17449step0 raw17449; decide +kernel
      have hl : raw17449step0Labels = raw17449Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17449 raw17449Labels permutation160 permutation3
    _ = mixedMoment B node2462 node2462Labels := by rfl

def raw17450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17450Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17450step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17450step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17450 raw17450Labels = mixedMoment B node3683 node3683Labels := by
  calc
    mixedMoment B raw17450 raw17450Labels = mixedMoment B raw17450step0 raw17450step0Labels := by
      have ha : raw17450step0 = (fun i j => raw17450 (permutation273 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17450step0 raw17450; decide +kernel
      have hl : raw17450step0Labels = raw17450Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17450 raw17450Labels permutation273 permutation3
    _ = mixedMoment B node3683 node3683Labels := by rfl

def raw17451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17451Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17451step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17451step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17451 raw17451Labels = mixedMoment B node3942 node3942Labels := by
  calc
    mixedMoment B raw17451 raw17451Labels = mixedMoment B raw17451step0 raw17451step0Labels := by
      have ha : raw17451step0 = (fun i j => raw17451 (permutation202 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17451step0 raw17451; decide +kernel
      have hl : raw17451step0Labels = raw17451Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17451 raw17451Labels permutation202 permutation3
    _ = mixedMoment B node3942 node3942Labels := by rfl

def raw17452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw17452Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17452step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw17452step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17452step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17452step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17452step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17452step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17452 raw17452Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw17452 raw17452Labels = mixedMoment B raw17452step0 raw17452step0Labels := by
      have hz : ∀ j, raw17452 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17452step0 = (fun i j => raw17452 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17452step0 raw17452; decide +kernel
      have hl : raw17452step0Labels = raw17452Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17452 raw17452Labels permutation520 hz
    mixedMoment B raw17452step0 raw17452step0Labels = mixedMoment B raw17452step1 raw17452step1Labels := by
      have ha : raw17452step1 = (fun i j => raw17452step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17452step1 raw17452step0; decide +kernel
      have hl : raw17452step1Labels = raw17452step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17452step0 raw17452step0Labels permutation145 permutation3
    mixedMoment B raw17452step1 raw17452step1Labels = mixedMoment B raw17452step2 raw17452step2Labels := by
      have ha : raw17452step2 = -raw17452step1 := by apply Matrix.ext; change ∀ i j, raw17452step2 i j = -(raw17452step1 i j); unfold raw17452step2 raw17452step1; decide +kernel
      have hl : raw17452step2Labels = raw17452step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3958 node3958Labels := by rfl

def raw17453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17453Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17453step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17453step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17453 raw17453Labels = mixedMoment B node3974 node3974Labels := by
  calc
    mixedMoment B raw17453 raw17453Labels = mixedMoment B raw17453step0 raw17453step0Labels := by
      have ha : raw17453step0 = (fun i j => raw17453 (permutation163 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17453step0 raw17453; decide +kernel
      have hl : raw17453step0Labels = raw17453Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17453 raw17453Labels permutation163 permutation3
    _ = mixedMoment B node3974 node3974Labels := by rfl

def raw17454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17454Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17454step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17454step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17454 raw17454Labels = mixedMoment B node2480 node2480Labels := by
  calc
    mixedMoment B raw17454 raw17454Labels = mixedMoment B raw17454step0 raw17454step0Labels := by
      have ha : raw17454step0 = (fun i j => raw17454 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17454step0 raw17454; decide +kernel
      have hl : raw17454step0Labels = raw17454Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17454 raw17454Labels permutation152 permutation3
    _ = mixedMoment B node2480 node2480Labels := by rfl

def raw17455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17455Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17455step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17455step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17455 raw17455Labels = mixedMoment B node3690 node3690Labels := by
  calc
    mixedMoment B raw17455 raw17455Labels = mixedMoment B raw17455step0 raw17455step0Labels := by
      have ha : raw17455step0 = (fun i j => raw17455 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17455step0 raw17455; decide +kernel
      have hl : raw17455step0Labels = raw17455Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17455 raw17455Labels permutation265 permutation3
    _ = mixedMoment B node3690 node3690Labels := by rfl

def raw17456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17456Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17456step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17456step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17456 raw17456Labels = mixedMoment B node3965 node3965Labels := by
  calc
    mixedMoment B raw17456 raw17456Labels = mixedMoment B raw17456step0 raw17456step0Labels := by
      have ha : raw17456step0 = (fun i j => raw17456 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17456step0 raw17456; decide +kernel
      have hl : raw17456step0Labels = raw17456Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17456 raw17456Labels permutation152 permutation3
    _ = mixedMoment B node3965 node3965Labels := by rfl

def raw17457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw17457Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17457step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17457step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17457step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17457step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17457 raw17457Labels = mixedMoment B node3981 node3981Labels := by
  calc
    mixedMoment B raw17457 raw17457Labels = mixedMoment B raw17457step0 raw17457step0Labels := by
      have hz : ∀ j, raw17457 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17457step0 = (fun i j => raw17457 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17457step0 raw17457; decide +kernel
      have hl : raw17457step0Labels = raw17457Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17457 raw17457Labels permutation520 hz
    mixedMoment B raw17457step0 raw17457step0Labels = mixedMoment B raw17457step1 raw17457step1Labels := by
      have ha : raw17457step1 = (fun i j => raw17457step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17457step1 raw17457step0; decide +kernel
      have hl : raw17457step1Labels = raw17457step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17457step0 raw17457step0Labels permutation32 permutation3
    _ = mixedMoment B node3981 node3981Labels := by rfl

def raw17458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17458Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17458step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17458step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17458 raw17458Labels = mixedMoment B node3980 node3980Labels := by
  calc
    mixedMoment B raw17458 raw17458Labels = mixedMoment B raw17458step0 raw17458step0Labels := by
      have ha : raw17458step0 = (fun i j => raw17458 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17458step0 raw17458; decide +kernel
      have hl : raw17458step0Labels = raw17458Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17458 raw17458Labels permutation153 permutation3
    _ = mixedMoment B node3980 node3980Labels := by rfl

def raw17459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17459Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17459step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17459step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17459 raw17459Labels = mixedMoment B node2452 node2452Labels := by
  calc
    mixedMoment B raw17459 raw17459Labels = mixedMoment B raw17459step0 raw17459step0Labels := by
      have ha : raw17459step0 = (fun i j => raw17459 (permutation159 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17459step0 raw17459; decide +kernel
      have hl : raw17459step0Labels = raw17459Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17459 raw17459Labels permutation159 permutation3
    _ = mixedMoment B node2452 node2452Labels := by rfl

def raw17460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17460Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17460step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17460step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17460 raw17460Labels = mixedMoment B node3678 node3678Labels := by
  calc
    mixedMoment B raw17460 raw17460Labels = mixedMoment B raw17460step0 raw17460step0Labels := by
      have ha : raw17460step0 = (fun i j => raw17460 (permutation272 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17460step0 raw17460; decide +kernel
      have hl : raw17460step0Labels = raw17460Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17460 raw17460Labels permutation272 permutation3
    _ = mixedMoment B node3678 node3678Labels := by rfl

def raw17461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17461Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17461step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17461step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17461step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17461step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17461 raw17461Labels = mixedMoment B node3690 node3690Labels := by
  calc
    mixedMoment B raw17461 raw17461Labels = mixedMoment B raw17461step0 raw17461step0Labels := by
      have ha : raw17461step0 = (fun i j => raw17461 (permutation589 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17461step0 raw17461; decide +kernel
      have hl : raw17461step0Labels = raw17461Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17461 raw17461Labels permutation589 permutation3
    mixedMoment B raw17461step0 raw17461step0Labels = mixedMoment B raw17461step1 raw17461step1Labels := by
      have ha : raw17461step1 = -raw17461step0 := by apply Matrix.ext; change ∀ i j, raw17461step1 i j = -(raw17461step0 i j); unfold raw17461step1 raw17461step0; decide +kernel
      have hl : raw17461step1Labels = raw17461step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3690 node3690Labels := by rfl

def raw17462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![2, -2, 0], ![2, -1, -1]]
def raw17462Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17462step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17462step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17462step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17462step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17462 raw17462Labels = mixedMoment B node3683 node3683Labels := by
  calc
    mixedMoment B raw17462 raw17462Labels = mixedMoment B raw17462step0 raw17462step0Labels := by
      have ha : raw17462step0 = (fun i j => raw17462 (permutation582 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17462step0 raw17462; decide +kernel
      have hl : raw17462step0Labels = raw17462Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17462 raw17462Labels permutation582 permutation3
    mixedMoment B raw17462step0 raw17462step0Labels = mixedMoment B raw17462step1 raw17462step1Labels := by
      have ha : raw17462step1 = -raw17462step0 := by apply Matrix.ext; change ∀ i j, raw17462step1 i j = -(raw17462step0 i j); unfold raw17462step1 raw17462step0; decide +kernel
      have hl : raw17462step1Labels = raw17462step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3683 node3683Labels := by rfl

def raw17463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![1, 0, -1]]
def raw17463Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17463step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17463step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17463step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17463step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17463 raw17463Labels = mixedMoment B node3838 node3838Labels := by
  calc
    mixedMoment B raw17463 raw17463Labels = mixedMoment B raw17463step0 raw17463step0Labels := by
      have ha : raw17463step0 = (fun i j => raw17463 (permutation584 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17463step0 raw17463; decide +kernel
      have hl : raw17463step0Labels = raw17463Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17463 raw17463Labels permutation584 permutation3
    mixedMoment B raw17463step0 raw17463step0Labels = mixedMoment B raw17463step1 raw17463step1Labels := by
      have ha : raw17463step1 = -raw17463step0 := by apply Matrix.ext; change ∀ i j, raw17463step1 i j = -(raw17463step0 i j); unfold raw17463step1 raw17463step0; decide +kernel
      have hl : raw17463step1Labels = raw17463step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3838 node3838Labels := by rfl

def raw17464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17464Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17464step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw17464step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17464 raw17464Labels = mixedMoment B node2449 node2449Labels := by
  calc
    mixedMoment B raw17464 raw17464Labels = mixedMoment B raw17464step0 raw17464step0Labels := by
      have ha : raw17464step0 = (fun i j => raw17464 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17464step0 raw17464; decide +kernel
      have hl : raw17464step0Labels = raw17464Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17464 raw17464Labels permutation158 permutation3
    _ = mixedMoment B node2449 node2449Labels := by rfl

def raw17465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17465Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17465step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw17465step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17465step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw17465step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17465 raw17465Labels = mixedMoment B node2452 node2452Labels := by
  calc
    mixedMoment B raw17465 raw17465Labels = mixedMoment B raw17465step0 raw17465step0Labels := by
      have ha : raw17465step0 = (fun i j => raw17465 (permutation681 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17465step0 raw17465; decide +kernel
      have hl : raw17465step0Labels = raw17465Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17465 raw17465Labels permutation681 permutation3
    mixedMoment B raw17465step0 raw17465step0Labels = mixedMoment B raw17465step1 raw17465step1Labels := by
      have ha : raw17465step1 = -raw17465step0 := by apply Matrix.ext; change ∀ i j, raw17465step1 i j = -(raw17465step0 i j); unfold raw17465step1 raw17465step0; decide +kernel
      have hl : raw17465step1Labels = raw17465step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2452 node2452Labels := by rfl

def raw17466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17466Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17466step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17466step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17466step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17466step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17466 raw17466Labels = mixedMoment B node2480 node2480Labels := by
  calc
    mixedMoment B raw17466 raw17466Labels = mixedMoment B raw17466step0 raw17466step0Labels := by
      have ha : raw17466step0 = (fun i j => raw17466 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17466step0 raw17466; decide +kernel
      have hl : raw17466step0Labels = raw17466Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17466 raw17466Labels permutation688 permutation3
    mixedMoment B raw17466step0 raw17466step0Labels = mixedMoment B raw17466step1 raw17466step1Labels := by
      have ha : raw17466step1 = -raw17466step0 := by apply Matrix.ext; change ∀ i j, raw17466step1 i j = -(raw17466step0 i j); unfold raw17466step1 raw17466step0; decide +kernel
      have hl : raw17466step1Labels = raw17466step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2480 node2480Labels := by rfl

def raw17467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 2, -1], ![1, -1, 0], ![3, -2, -1]]
def raw17467Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17467step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17467step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17467step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17467step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17467 raw17467Labels = mixedMoment B node2462 node2462Labels := by
  calc
    mixedMoment B raw17467 raw17467Labels = mixedMoment B raw17467step0 raw17467step0Labels := by
      have ha : raw17467step0 = (fun i j => raw17467 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17467step0 raw17467; decide +kernel
      have hl : raw17467step0Labels = raw17467Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17467 raw17467Labels permutation680 permutation3
    mixedMoment B raw17467step0 raw17467step0Labels = mixedMoment B raw17467step1 raw17467step1Labels := by
      have ha : raw17467step1 = -raw17467step0 := by apply Matrix.ext; change ∀ i j, raw17467step1 i j = -(raw17467step0 i j); unfold raw17467step1 raw17467step0; decide +kernel
      have hl : raw17467step1Labels = raw17467step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2462 node2462Labels := by rfl

def raw17468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![3, -2, -1]]
def raw17468Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17468step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![3, -2, -1]]
def raw17468step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17468step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17468step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17468step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17468step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17468 raw17468Labels = mixedMoment B node2723 node2723Labels := by
  calc
    mixedMoment B raw17468 raw17468Labels = mixedMoment B raw17468step0 raw17468step0Labels := by
      have hz : ∀ j, raw17468 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17468step0 = (fun i j => raw17468 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17468step0 raw17468; decide +kernel
      have hl : raw17468step0Labels = raw17468Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17468 raw17468Labels permutation520 hz
    mixedMoment B raw17468step0 raw17468step0Labels = mixedMoment B raw17468step1 raw17468step1Labels := by
      have ha : raw17468step1 = (fun i j => raw17468step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17468step1 raw17468step0; decide +kernel
      have hl : raw17468step1Labels = raw17468step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17468step0 raw17468step0Labels permutation145 permutation3
    mixedMoment B raw17468step1 raw17468step1Labels = mixedMoment B raw17468step2 raw17468step2Labels := by
      have ha : raw17468step2 = -raw17468step1 := by apply Matrix.ext; change ∀ i j, raw17468step2 i j = -(raw17468step1 i j); unfold raw17468step2 raw17468step1; decide +kernel
      have hl : raw17468step2Labels = raw17468step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2723 node2723Labels := by rfl

def raw17469 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17469Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17469step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw17469step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17469step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17469step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17469 raw17469Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw17469 raw17469Labels = mixedMoment B raw17469step0 raw17469step0Labels := by
      have ha : raw17469step0 = (fun i j => raw17469 (permutation188 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17469step0 raw17469; decide +kernel
      have hl : raw17469step0Labels = raw17469Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17469 raw17469Labels permutation188 permutation2
    mixedMoment B raw17469step0 raw17469step0Labels = mixedMoment B raw17469step1 raw17469step1Labels := by
      have ha : raw17469step1 = -raw17469step0 := by apply Matrix.ext; change ∀ i j, raw17469step1 i j = -(raw17469step0 i j); unfold raw17469step1 raw17469step0; decide +kernel
      have hl : raw17469step1Labels = raw17469step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5430 node5430Labels := by rfl

def raw17470 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17470Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17470step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17470step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17470step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17470step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17470step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17470 raw17470Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw17470 raw17470Labels = mixedMoment B raw17470step0 raw17470step0Labels := by
      have hz : ∀ j, raw17470 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17470step0 = (fun i j => raw17470 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17470step0 raw17470; decide +kernel
      have hl : raw17470step0Labels = raw17470Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17470 raw17470Labels permutation346 hz
    mixedMoment B raw17470step0 raw17470step0Labels = mixedMoment B raw17470step1 raw17470step1Labels := by
      have ha : raw17470step1 = (fun i j => raw17470step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17470step1 raw17470step0; decide +kernel
      have hl : raw17470step1Labels = raw17470step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17470step0 raw17470step0Labels permutation32 permutation7
    mixedMoment B raw17470step1 raw17470step1Labels = mixedMoment B raw17470step2 raw17470step2Labels := by
      have ha : raw17470step2 = raw17470step1 := by apply Matrix.ext; unfold raw17470step2 raw17470step1; decide +kernel
      have hl : raw17470step1Labels = labelEmbedding10 ∘ raw17470step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17470step1 raw17470step1Labels raw17470step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw17471 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17471Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17471step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw17471step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17471step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17471step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17471 raw17471Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw17471 raw17471Labels = mixedMoment B raw17471step0 raw17471step0Labels := by
      have ha : raw17471step0 = (fun i j => raw17471 (permutation179 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17471step0 raw17471; decide +kernel
      have hl : raw17471step0Labels = raw17471Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17471 raw17471Labels permutation179 permutation2
    mixedMoment B raw17471step0 raw17471step0Labels = mixedMoment B raw17471step1 raw17471step1Labels := by
      have ha : raw17471step1 = -raw17471step0 := by apply Matrix.ext; change ∀ i j, raw17471step1 i j = -(raw17471step0 i j); unfold raw17471step1 raw17471step0; decide +kernel
      have hl : raw17471step1Labels = raw17471step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw17472 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17472Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17472step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17472step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17472step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17472step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17472 raw17472Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw17472 raw17472Labels = mixedMoment B raw17472step0 raw17472step0Labels := by
      have ha : raw17472step0 = (fun i j => raw17472 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17472step0 raw17472; decide +kernel
      have hl : raw17472step0Labels = raw17472Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17472 raw17472Labels permutation152 permutation7
    mixedMoment B raw17472step0 raw17472step0Labels = mixedMoment B raw17472step1 raw17472step1Labels := by
      have ha : raw17472step1 = raw17472step0 := by apply Matrix.ext; unfold raw17472step1 raw17472step0; decide +kernel
      have hl : raw17472step0Labels = labelEmbedding10 ∘ raw17472step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17472step0 raw17472step0Labels raw17472step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw17473 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw17473Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17473step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17473step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17473 raw17473Labels = mixedMoment B node5423 node5423Labels := by
  calc
    mixedMoment B raw17473 raw17473Labels = mixedMoment B raw17473step0 raw17473step0Labels := by
      have ha : raw17473step0 = (fun i j => raw17473 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17473step0 raw17473; decide +kernel
      have hl : raw17473step0Labels = raw17473Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17473 raw17473Labels permutation662 permutation2
    _ = mixedMoment B node5423 node5423Labels := by rfl

def raw17474 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17474Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17474step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17474step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17474step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17474step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17474 raw17474Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw17474 raw17474Labels = mixedMoment B raw17474step0 raw17474step0Labels := by
      have ha : raw17474step0 = (fun i j => raw17474 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17474step0 raw17474; decide +kernel
      have hl : raw17474step0Labels = raw17474Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17474 raw17474Labels permutation158 permutation6
    mixedMoment B raw17474step0 raw17474step0Labels = mixedMoment B raw17474step1 raw17474step1Labels := by
      have ha : raw17474step1 = raw17474step0 := by apply Matrix.ext; unfold raw17474step1 raw17474step0; decide +kernel
      have hl : raw17474step0Labels = labelEmbedding9 ∘ raw17474step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17474step0 raw17474step0Labels raw17474step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw17475 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17475Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17475step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17475step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17475step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17475step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17475step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17475step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17475step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17475step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17475 raw17475Labels = mixedMoment B node5483 node5483Labels := by
  calc
    mixedMoment B raw17475 raw17475Labels = mixedMoment B raw17475step0 raw17475step0Labels := by
      have hz : ∀ j, raw17475 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17475step0 = (fun i j => raw17475 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17475step0 raw17475; decide +kernel
      have hl : raw17475step0Labels = raw17475Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17475 raw17475Labels permutation346 hz
    mixedMoment B raw17475step0 raw17475step0Labels = mixedMoment B raw17475step1 raw17475step1Labels := by
      have ha : raw17475step1 = (fun i j => raw17475step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17475step1 raw17475step0; decide +kernel
      have hl : raw17475step1Labels = raw17475step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17475step0 raw17475step0Labels permutation151 permutation6
    mixedMoment B raw17475step1 raw17475step1Labels = mixedMoment B raw17475step2 raw17475step2Labels := by
      have ha : raw17475step2 = -raw17475step1 := by apply Matrix.ext; change ∀ i j, raw17475step2 i j = -(raw17475step1 i j); unfold raw17475step2 raw17475step1; decide +kernel
      have hl : raw17475step2Labels = raw17475step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17475step2 raw17475step2Labels = mixedMoment B raw17475step3 raw17475step3Labels := by
      have ha : raw17475step3 = raw17475step2 := by apply Matrix.ext; unfold raw17475step3 raw17475step2; decide +kernel
      have hl : raw17475step2Labels = labelEmbedding9 ∘ raw17475step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17475step2 raw17475step2Labels raw17475step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5483 node5483Labels := by rfl

def raw17476 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17476Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17476step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17476step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17476step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17476step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17476 raw17476Labels = mixedMoment B node5445 node5445Labels := by
  calc
    mixedMoment B raw17476 raw17476Labels = mixedMoment B raw17476step0 raw17476step0Labels := by
      have ha : raw17476step0 = (fun i j => raw17476 (permutation514 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17476step0 raw17476; decide +kernel
      have hl : raw17476step0Labels = raw17476Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17476 raw17476Labels permutation514 permutation3
    mixedMoment B raw17476step0 raw17476step0Labels = mixedMoment B raw17476step1 raw17476step1Labels := by
      have ha : raw17476step1 = raw17476step0 := by apply Matrix.ext; unfold raw17476step1 raw17476step0; decide +kernel
      have hl : raw17476step0Labels = labelEmbedding6 ∘ raw17476step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17476step0 raw17476step0Labels raw17476step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5445 node5445Labels := by rfl

def raw17477 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17477Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17477step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17477step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17477step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17477step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17477 raw17477Labels = mixedMoment B node5477 node5477Labels := by
  calc
    mixedMoment B raw17477 raw17477Labels = mixedMoment B raw17477step0 raw17477step0Labels := by
      have ha : raw17477step0 = (fun i j => raw17477 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17477step0 raw17477; decide +kernel
      have hl : raw17477step0Labels = raw17477Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17477 raw17477Labels permutation152 permutation7
    mixedMoment B raw17477step0 raw17477step0Labels = mixedMoment B raw17477step1 raw17477step1Labels := by
      have ha : raw17477step1 = raw17477step0 := by apply Matrix.ext; unfold raw17477step1 raw17477step0; decide +kernel
      have hl : raw17477step0Labels = labelEmbedding10 ∘ raw17477step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17477step0 raw17477step0Labels raw17477step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5477 node5477Labels := by rfl

def raw17478 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw17478Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17478step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17478step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17478step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17478step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17478step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17478step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17478 raw17478Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw17478 raw17478Labels = mixedMoment B raw17478step0 raw17478step0Labels := by
      have ha : raw17478step0 = (fun i j => raw17478 (permutation688 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17478step0 raw17478; decide +kernel
      have hl : raw17478step0Labels = raw17478Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17478 raw17478Labels permutation688 permutation7
    mixedMoment B raw17478step0 raw17478step0Labels = mixedMoment B raw17478step1 raw17478step1Labels := by
      have ha : raw17478step1 = -raw17478step0 := by apply Matrix.ext; change ∀ i j, raw17478step1 i j = -(raw17478step0 i j); unfold raw17478step1 raw17478step0; decide +kernel
      have hl : raw17478step1Labels = raw17478step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17478step1 raw17478step1Labels = mixedMoment B raw17478step2 raw17478step2Labels := by
      have ha : raw17478step2 = raw17478step1 := by apply Matrix.ext; unfold raw17478step2 raw17478step1; decide +kernel
      have hl : raw17478step1Labels = labelEmbedding10 ∘ raw17478step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17478step1 raw17478step1Labels raw17478step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw17479 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17479Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17479step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw17479step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17479step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17479step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17479step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17479step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17479 raw17479Labels = mixedMoment B node5397 node5397Labels := by
  calc
    mixedMoment B raw17479 raw17479Labels = mixedMoment B raw17479step0 raw17479step0Labels := by
      have ha : raw17479step0 = (fun i j => raw17479 (permutation161 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17479step0 raw17479; decide +kernel
      have hl : raw17479step0Labels = raw17479Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17479 raw17479Labels permutation161 permutation4
    mixedMoment B raw17479step0 raw17479step0Labels = mixedMoment B raw17479step1 raw17479step1Labels := by
      have ha : raw17479step1 = -raw17479step0 := by apply Matrix.ext; change ∀ i j, raw17479step1 i j = -(raw17479step0 i j); unfold raw17479step1 raw17479step0; decide +kernel
      have hl : raw17479step1Labels = raw17479step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17479step1 raw17479step1Labels = mixedMoment B raw17479step2 raw17479step2Labels := by
      have ha : raw17479step2 = raw17479step1 := by apply Matrix.ext; unfold raw17479step2 raw17479step1; decide +kernel
      have hl : raw17479step1Labels = labelEmbedding7 ∘ raw17479step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17479step1 raw17479step1Labels raw17479step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5397 node5397Labels := by rfl

def raw17480 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17480Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17480step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17480step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17480step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17480step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17480 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17480 raw17480Labels = mixedMoment B node5421 node5421Labels := by
  calc
    mixedMoment B raw17480 raw17480Labels = mixedMoment B raw17480step0 raw17480step0Labels := by
      have ha : raw17480step0 = (fun i j => raw17480 (permutation410 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17480step0 raw17480; decide +kernel
      have hl : raw17480step0Labels = raw17480Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17480 raw17480Labels permutation410 permutation5
    mixedMoment B raw17480step0 raw17480step0Labels = mixedMoment B raw17480step1 raw17480step1Labels := by
      have ha : raw17480step1 = raw17480step0 := by apply Matrix.ext; unfold raw17480step1 raw17480step0; decide +kernel
      have hl : raw17480step0Labels = labelEmbedding8 ∘ raw17480step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17480step0 raw17480step0Labels raw17480step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5421 node5421Labels := by rfl

def raw17481 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17481Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17481step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17481step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17481step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17481step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17481 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17481 raw17481Labels = mixedMoment B node5420 node5420Labels := by
  calc
    mixedMoment B raw17481 raw17481Labels = mixedMoment B raw17481step0 raw17481step0Labels := by
      have ha : raw17481step0 = (fun i j => raw17481 (permutation409 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17481step0 raw17481; decide +kernel
      have hl : raw17481step0Labels = raw17481Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17481 raw17481Labels permutation409 permutation5
    mixedMoment B raw17481step0 raw17481step0Labels = mixedMoment B raw17481step1 raw17481step1Labels := by
      have ha : raw17481step1 = raw17481step0 := by apply Matrix.ext; unfold raw17481step1 raw17481step0; decide +kernel
      have hl : raw17481step0Labels = labelEmbedding8 ∘ raw17481step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17481step0 raw17481step0Labels raw17481step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5420 node5420Labels := by rfl

def raw17482 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17482Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17482step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw17482step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17482step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17482step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17482step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17482step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17482 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17482 raw17482Labels = mixedMoment B node5445 node5445Labels := by
  calc
    mixedMoment B raw17482 raw17482Labels = mixedMoment B raw17482step0 raw17482step0Labels := by
      have ha : raw17482step0 = (fun i j => raw17482 (permutation351 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17482step0 raw17482; decide +kernel
      have hl : raw17482step0Labels = raw17482Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17482 raw17482Labels permutation351 permutation3
    mixedMoment B raw17482step0 raw17482step0Labels = mixedMoment B raw17482step1 raw17482step1Labels := by
      have ha : raw17482step1 = -raw17482step0 := by apply Matrix.ext; change ∀ i j, raw17482step1 i j = -(raw17482step0 i j); unfold raw17482step1 raw17482step0; decide +kernel
      have hl : raw17482step1Labels = raw17482step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17482step1 raw17482step1Labels = mixedMoment B raw17482step2 raw17482step2Labels := by
      have ha : raw17482step2 = raw17482step1 := by apply Matrix.ext; unfold raw17482step2 raw17482step1; decide +kernel
      have hl : raw17482step1Labels = labelEmbedding6 ∘ raw17482step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17482step1 raw17482step1Labels raw17482step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5445 node5445Labels := by rfl

def raw17483 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw17483Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17483step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17483step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17483 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17483 raw17483Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw17483 raw17483Labels = mixedMoment B raw17483step0 raw17483step0Labels := by
      have ha : raw17483step0 = (fun i j => raw17483 (permutation661 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17483step0 raw17483; decide +kernel
      have hl : raw17483step0Labels = raw17483Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17483 raw17483Labels permutation661 permutation2
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw17484 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17484Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17484step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17484step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17484step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17484step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17484step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17484step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17484 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17484 raw17484Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw17484 raw17484Labels = mixedMoment B raw17484step0 raw17484step0Labels := by
      have hz : ∀ j, raw17484 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17484step0 = (fun i j => raw17484 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17484step0 raw17484; decide +kernel
      have hl : raw17484step0Labels = raw17484Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17484 raw17484Labels permutation434 hz
    mixedMoment B raw17484step0 raw17484step0Labels = mixedMoment B raw17484step1 raw17484step1Labels := by
      have ha : raw17484step1 = (fun i j => raw17484step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17484step1 raw17484step0; decide +kernel
      have hl : raw17484step1Labels = raw17484step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17484step0 raw17484step0Labels permutation32 permutation6
    mixedMoment B raw17484step1 raw17484step1Labels = mixedMoment B raw17484step2 raw17484step2Labels := by
      have ha : raw17484step2 = raw17484step1 := by apply Matrix.ext; unfold raw17484step2 raw17484step1; decide +kernel
      have hl : raw17484step1Labels = labelEmbedding9 ∘ raw17484step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17484step1 raw17484step1Labels raw17484step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5410 node5410Labels := by rfl

def raw17485 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17485Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17485step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-2, 1, 1]]
def raw17485step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17485step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17485step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17485step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17485step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17485 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17485 raw17485Labels = mixedMoment B node5395 node5395Labels := by
  calc
    mixedMoment B raw17485 raw17485Labels = mixedMoment B raw17485step0 raw17485step0Labels := by
      have ha : raw17485step0 = (fun i j => raw17485 (permutation159 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17485step0 raw17485; decide +kernel
      have hl : raw17485step0Labels = raw17485Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17485 raw17485Labels permutation159 permutation4
    mixedMoment B raw17485step0 raw17485step0Labels = mixedMoment B raw17485step1 raw17485step1Labels := by
      have ha : raw17485step1 = -raw17485step0 := by apply Matrix.ext; change ∀ i j, raw17485step1 i j = -(raw17485step0 i j); unfold raw17485step1 raw17485step0; decide +kernel
      have hl : raw17485step1Labels = raw17485step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17485step1 raw17485step1Labels = mixedMoment B raw17485step2 raw17485step2Labels := by
      have ha : raw17485step2 = raw17485step1 := by apply Matrix.ext; unfold raw17485step2 raw17485step1; decide +kernel
      have hl : raw17485step1Labels = labelEmbedding7 ∘ raw17485step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17485step1 raw17485step1Labels raw17485step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5395 node5395Labels := by rfl

def raw17486 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17486Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17486step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17486step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17486step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17486step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17486 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17486 raw17486Labels = mixedMoment B node5468 node5468Labels := by
  calc
    mixedMoment B raw17486 raw17486Labels = mixedMoment B raw17486step0 raw17486step0Labels := by
      have ha : raw17486step0 = (fun i j => raw17486 (permutation583 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17486step0 raw17486; decide +kernel
      have hl : raw17486step0Labels = raw17486Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17486 raw17486Labels permutation583 permutation4
    mixedMoment B raw17486step0 raw17486step0Labels = mixedMoment B raw17486step1 raw17486step1Labels := by
      have ha : raw17486step1 = raw17486step0 := by apply Matrix.ext; unfold raw17486step1 raw17486step0; decide +kernel
      have hl : raw17486step0Labels = labelEmbedding7 ∘ raw17486step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17486step0 raw17486step0Labels raw17486step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5468 node5468Labels := by rfl

def raw17487 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17487Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17487step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17487step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17487step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17487step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17487step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17487step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17487step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17487step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17487 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17487 raw17487Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw17487 raw17487Labels = mixedMoment B raw17487step0 raw17487step0Labels := by
      have hz : ∀ j, raw17487 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17487step0 = (fun i j => raw17487 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17487step0 raw17487; decide +kernel
      have hl : raw17487step0Labels = raw17487Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17487 raw17487Labels permutation346 hz
    mixedMoment B raw17487step0 raw17487step0Labels = mixedMoment B raw17487step1 raw17487step1Labels := by
      have ha : raw17487step1 = (fun i j => raw17487step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17487step1 raw17487step0; decide +kernel
      have hl : raw17487step1Labels = raw17487step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17487step0 raw17487step0Labels permutation151 permutation6
    mixedMoment B raw17487step1 raw17487step1Labels = mixedMoment B raw17487step2 raw17487step2Labels := by
      have ha : raw17487step2 = -raw17487step1 := by apply Matrix.ext; change ∀ i j, raw17487step2 i j = -(raw17487step1 i j); unfold raw17487step2 raw17487step1; decide +kernel
      have hl : raw17487step2Labels = raw17487step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17487step2 raw17487step2Labels = mixedMoment B raw17487step3 raw17487step3Labels := by
      have ha : raw17487step3 = raw17487step2 := by apply Matrix.ext; unfold raw17487step3 raw17487step2; decide +kernel
      have hl : raw17487step2Labels = labelEmbedding9 ∘ raw17487step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17487step2 raw17487step2Labels raw17487step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw17488 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17488Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17488step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17488step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17488step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17488step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17488step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17488step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17488 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17488 raw17488Labels = mixedMoment B node5421 node5421Labels := by
  calc
    mixedMoment B raw17488 raw17488Labels = mixedMoment B raw17488step0 raw17488step0Labels := by
      have ha : raw17488step0 = (fun i j => raw17488 (permutation455 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17488step0 raw17488; decide +kernel
      have hl : raw17488step0Labels = raw17488Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17488 raw17488Labels permutation455 permutation5
    mixedMoment B raw17488step0 raw17488step0Labels = mixedMoment B raw17488step1 raw17488step1Labels := by
      have ha : raw17488step1 = -raw17488step0 := by apply Matrix.ext; change ∀ i j, raw17488step1 i j = -(raw17488step0 i j); unfold raw17488step1 raw17488step0; decide +kernel
      have hl : raw17488step1Labels = raw17488step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17488step1 raw17488step1Labels = mixedMoment B raw17488step2 raw17488step2Labels := by
      have ha : raw17488step2 = raw17488step1 := by apply Matrix.ext; unfold raw17488step2 raw17488step1; decide +kernel
      have hl : raw17488step1Labels = labelEmbedding8 ∘ raw17488step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17488step1 raw17488step1Labels raw17488step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5421 node5421Labels := by rfl

def raw17489 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw17489Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17489step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17489step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17489 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17489 raw17489Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw17489 raw17489Labels = mixedMoment B raw17489step0 raw17489step0Labels := by
      have ha : raw17489step0 = (fun i j => raw17489 (permutation654 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17489step0 raw17489; decide +kernel
      have hl : raw17489step0Labels = raw17489Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17489 raw17489Labels permutation654 permutation2
    _ = mixedMoment B node5430 node5430Labels := by rfl

def raw17490 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17490Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17490step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17490step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17490step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw17490step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17490 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17490 raw17490Labels = mixedMoment B node5394 node5394Labels := by
  calc
    mixedMoment B raw17490 raw17490Labels = mixedMoment B raw17490step0 raw17490step0Labels := by
      have ha : raw17490step0 = (fun i j => raw17490 (permutation682 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17490step0 raw17490; decide +kernel
      have hl : raw17490step0Labels = raw17490Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17490 raw17490Labels permutation682 permutation4
    mixedMoment B raw17490step0 raw17490step0Labels = mixedMoment B raw17490step1 raw17490step1Labels := by
      have ha : raw17490step1 = raw17490step0 := by apply Matrix.ext; unfold raw17490step1 raw17490step0; decide +kernel
      have hl : raw17490step0Labels = labelEmbedding7 ∘ raw17490step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17490step0 raw17490step0Labels raw17490step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5394 node5394Labels := by rfl

def raw17491 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17491Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17491step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17491step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17491step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw17491step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17491 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17491 raw17491Labels = mixedMoment B node5395 node5395Labels := by
  calc
    mixedMoment B raw17491 raw17491Labels = mixedMoment B raw17491step0 raw17491step0Labels := by
      have ha : raw17491step0 = (fun i j => raw17491 (permutation681 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17491step0 raw17491; decide +kernel
      have hl : raw17491step0Labels = raw17491Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17491 raw17491Labels permutation681 permutation4
    mixedMoment B raw17491step0 raw17491step0Labels = mixedMoment B raw17491step1 raw17491step1Labels := by
      have ha : raw17491step1 = raw17491step0 := by apply Matrix.ext; unfold raw17491step1 raw17491step0; decide +kernel
      have hl : raw17491step0Labels = labelEmbedding7 ∘ raw17491step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17491step0 raw17491step0Labels raw17491step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5395 node5395Labels := by rfl

def raw17492 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17492Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17492step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17492step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17492step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17492step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17492step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17492step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17492step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17492step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17492 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17492 raw17492Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw17492 raw17492Labels = mixedMoment B raw17492step0 raw17492step0Labels := by
      have hz : ∀ j, raw17492 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17492step0 = (fun i j => raw17492 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17492step0 raw17492; decide +kernel
      have hl : raw17492step0Labels = raw17492Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17492 raw17492Labels permutation346 hz
    mixedMoment B raw17492step0 raw17492step0Labels = mixedMoment B raw17492step1 raw17492step1Labels := by
      have ha : raw17492step1 = (fun i j => raw17492step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17492step1 raw17492step0; decide +kernel
      have hl : raw17492step1Labels = raw17492step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17492step0 raw17492step0Labels permutation151 permutation6
    mixedMoment B raw17492step1 raw17492step1Labels = mixedMoment B raw17492step2 raw17492step2Labels := by
      have ha : raw17492step2 = -raw17492step1 := by apply Matrix.ext; change ∀ i j, raw17492step2 i j = -(raw17492step1 i j); unfold raw17492step2 raw17492step1; decide +kernel
      have hl : raw17492step2Labels = raw17492step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17492step2 raw17492step2Labels = mixedMoment B raw17492step3 raw17492step3Labels := by
      have ha : raw17492step3 = raw17492step2 := by apply Matrix.ext; unfold raw17492step3 raw17492step2; decide +kernel
      have hl : raw17492step2Labels = labelEmbedding9 ∘ raw17492step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17492step2 raw17492step2Labels raw17492step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5410 node5410Labels := by rfl

def raw17493 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17493Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17493step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17493step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17493step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17493step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17493 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17493 raw17493Labels = mixedMoment B node5397 node5397Labels := by
  calc
    mixedMoment B raw17493 raw17493Labels = mixedMoment B raw17493step0 raw17493step0Labels := by
      have ha : raw17493step0 = (fun i j => raw17493 (permutation679 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17493step0 raw17493; decide +kernel
      have hl : raw17493step0Labels = raw17493Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17493 raw17493Labels permutation679 permutation4
    mixedMoment B raw17493step0 raw17493step0Labels = mixedMoment B raw17493step1 raw17493step1Labels := by
      have ha : raw17493step1 = raw17493step0 := by apply Matrix.ext; unfold raw17493step1 raw17493step0; decide +kernel
      have hl : raw17493step0Labels = labelEmbedding7 ∘ raw17493step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17493step0 raw17493step0Labels raw17493step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5397 node5397Labels := by rfl

def raw17494 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17494Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17494step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw17494step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17494step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17494step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17494 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17494 raw17494Labels = mixedMoment B node3972 node3972Labels := by
  calc
    mixedMoment B raw17494 raw17494Labels = mixedMoment B raw17494step0 raw17494step0Labels := by
      have ha : raw17494step0 = (fun i j => raw17494 (permutation682 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17494step0 raw17494; decide +kernel
      have hl : raw17494step0Labels = raw17494Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17494 raw17494Labels permutation682 permutation6
    mixedMoment B raw17494step0 raw17494step0Labels = mixedMoment B raw17494step1 raw17494step1Labels := by
      have ha : raw17494step1 = -raw17494step0 := by apply Matrix.ext; change ∀ i j, raw17494step1 i j = -(raw17494step0 i j); unfold raw17494step1 raw17494step0; decide +kernel
      have hl : raw17494step1Labels = raw17494step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3972 node3972Labels := by rfl

def raw17495 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17495Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17495step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17495step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17495step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw17495step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17495step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17495step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17495 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17495 raw17495Labels = mixedMoment B node3982 node3982Labels := by
  calc
    mixedMoment B raw17495 raw17495Labels = mixedMoment B raw17495step0 raw17495step0Labels := by
      have hz : ∀ j, raw17495 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17495step0 = (fun i j => raw17495 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17495step0 raw17495; decide +kernel
      have hl : raw17495step0Labels = raw17495Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17495 raw17495Labels permutation346 hz
    mixedMoment B raw17495step0 raw17495step0Labels = mixedMoment B raw17495step1 raw17495step1Labels := by
      have ha : raw17495step1 = (fun i j => raw17495step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17495step1 raw17495step0; decide +kernel
      have hl : raw17495step1Labels = raw17495step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17495step0 raw17495step0Labels permutation151 permutation6
    mixedMoment B raw17495step1 raw17495step1Labels = mixedMoment B raw17495step2 raw17495step2Labels := by
      have ha : raw17495step2 = -raw17495step1 := by apply Matrix.ext; change ∀ i j, raw17495step2 i j = -(raw17495step1 i j); unfold raw17495step2 raw17495step1; decide +kernel
      have hl : raw17495step2Labels = raw17495step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3982 node3982Labels := by rfl

def raw17496 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17496Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17496step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17496step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17496 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17496 raw17496Labels = mixedMoment B node3872 node3872Labels := by
  calc
    mixedMoment B raw17496 raw17496Labels = mixedMoment B raw17496step0 raw17496step0Labels := by
      have ha : raw17496step0 = (fun i j => raw17496 (permutation511 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17496step0 raw17496; decide +kernel
      have hl : raw17496step0Labels = raw17496Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17496 raw17496Labels permutation511 permutation3
    _ = mixedMoment B node3872 node3872Labels := by rfl

def raw17497 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17497Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17497step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw17497step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17497step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17497step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17497 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17497 raw17497Labels = mixedMoment B node3990 node3990Labels := by
  calc
    mixedMoment B raw17497 raw17497Labels = mixedMoment B raw17497step0 raw17497step0Labels := by
      have ha : raw17497step0 = (fun i j => raw17497 (permutation682 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17497step0 raw17497; decide +kernel
      have hl : raw17497step0Labels = raw17497Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17497 raw17497Labels permutation682 permutation6
    mixedMoment B raw17497step0 raw17497step0Labels = mixedMoment B raw17497step1 raw17497step1Labels := by
      have ha : raw17497step1 = -raw17497step0 := by apply Matrix.ext; change ∀ i j, raw17497step1 i j = -(raw17497step0 i j); unfold raw17497step1 raw17497step0; decide +kernel
      have hl : raw17497step1Labels = raw17497step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3990 node3990Labels := by rfl

def raw17498 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw17498Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17498step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17498step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17498 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17498 raw17498Labels = mixedMoment B node4032 node4032Labels := by
  calc
    mixedMoment B raw17498 raw17498Labels = mixedMoment B raw17498step0 raw17498step0Labels := by
      have ha : raw17498step0 = (fun i j => raw17498 (permutation654 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17498step0 raw17498; decide +kernel
      have hl : raw17498step0Labels = raw17498Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17498 raw17498Labels permutation654 permutation3
    _ = mixedMoment B node4032 node4032Labels := by rfl

def raw17499 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17499Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17499step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17499step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17499 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17499 raw17499Labels = mixedMoment B node3838 node3838Labels := by
  calc
    mixedMoment B raw17499 raw17499Labels = mixedMoment B raw17499step0 raw17499step0Labels := by
      have ha : raw17499step0 = (fun i j => raw17499 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17499step0 raw17499; decide +kernel
      have hl : raw17499step0Labels = raw17499Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17499 raw17499Labels permutation158 permutation6
    _ = mixedMoment B node3838 node3838Labels := by rfl

def raw17500 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17500Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17500step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17500step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17500step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17500step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17500step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17500step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17500 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17500 raw17500Labels = mixedMoment B node3981 node3981Labels := by
  calc
    mixedMoment B raw17500 raw17500Labels = mixedMoment B raw17500step0 raw17500step0Labels := by
      have hz : ∀ j, raw17500 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17500step0 = (fun i j => raw17500 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17500step0 raw17500; decide +kernel
      have hl : raw17500step0Labels = raw17500Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17500 raw17500Labels permutation346 hz
    mixedMoment B raw17500step0 raw17500step0Labels = mixedMoment B raw17500step1 raw17500step1Labels := by
      have ha : raw17500step1 = (fun i j => raw17500step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17500step1 raw17500step0; decide +kernel
      have hl : raw17500step1Labels = raw17500step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17500step0 raw17500step0Labels permutation151 permutation6
    mixedMoment B raw17500step1 raw17500step1Labels = mixedMoment B raw17500step2 raw17500step2Labels := by
      have ha : raw17500step2 = -raw17500step1 := by apply Matrix.ext; change ∀ i j, raw17500step2 i j = -(raw17500step1 i j); unfold raw17500step2 raw17500step1; decide +kernel
      have hl : raw17500step2Labels = raw17500step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3981 node3981Labels := by rfl

def raw17501 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17501Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17501step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17501step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17501 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17501 raw17501Labels = mixedMoment B node3880 node3880Labels := by
  calc
    mixedMoment B raw17501 raw17501Labels = mixedMoment B raw17501step0 raw17501step0Labels := by
      have ha : raw17501step0 = (fun i j => raw17501 (permutation514 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17501step0 raw17501; decide +kernel
      have hl : raw17501step0Labels = raw17501Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17501 raw17501Labels permutation514 permutation3
    _ = mixedMoment B node3880 node3880Labels := by rfl

def raw17502 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17502Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17502step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17502step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17502 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17502 raw17502Labels = mixedMoment B node3989 node3989Labels := by
  calc
    mixedMoment B raw17502 raw17502Labels = mixedMoment B raw17502step0 raw17502step0Labels := by
      have ha : raw17502step0 = (fun i j => raw17502 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17502step0 raw17502; decide +kernel
      have hl : raw17502step0Labels = raw17502Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17502 raw17502Labels permutation158 permutation6
    _ = mixedMoment B node3989 node3989Labels := by rfl

def raw17503 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw17503Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17503step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17503step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17503 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17503 raw17503Labels = mixedMoment B node3990 node3990Labels := by
  calc
    mixedMoment B raw17503 raw17503Labels = mixedMoment B raw17503step0 raw17503step0Labels := by
      have ha : raw17503step0 = (fun i j => raw17503 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17503step0 raw17503; decide +kernel
      have hl : raw17503step0Labels = raw17503Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17503 raw17503Labels permutation158 permutation6
    _ = mixedMoment B node3990 node3990Labels := by rfl

def raw17504 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17504Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17504step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw17504step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17504 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17504 raw17504Labels = mixedMoment B node3796 node3796Labels := by
  calc
    mixedMoment B raw17504 raw17504Labels = mixedMoment B raw17504step0 raw17504step0Labels := by
      have ha : raw17504step0 = (fun i j => raw17504 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17504step0 raw17504; decide +kernel
      have hl : raw17504step0Labels = raw17504Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17504 raw17504Labels permutation158 permutation6
    _ = mixedMoment B node3796 node3796Labels := by rfl

def raw17505 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17505Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17505step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw17505step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17505step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17505step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17505 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17505 raw17505Labels = mixedMoment B node3873 node3873Labels := by
  calc
    mixedMoment B raw17505 raw17505Labels = mixedMoment B raw17505step0 raw17505step0Labels := by
      have ha : raw17505step0 = (fun i j => raw17505 (permutation360 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17505step0 raw17505; decide +kernel
      have hl : raw17505step0Labels = raw17505Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17505 raw17505Labels permutation360 permutation3
    mixedMoment B raw17505step0 raw17505step0Labels = mixedMoment B raw17505step1 raw17505step1Labels := by
      have ha : raw17505step1 = -raw17505step0 := by apply Matrix.ext; change ∀ i j, raw17505step1 i j = -(raw17505step0 i j); unfold raw17505step1 raw17505step0; decide +kernel
      have hl : raw17505step1Labels = raw17505step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3873 node3873Labels := by rfl

def raw17506 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-2, 2, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17506Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17506step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17506step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17506 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17506 raw17506Labels = mixedMoment B node3870 node3870Labels := by
  calc
    mixedMoment B raw17506 raw17506Labels = mixedMoment B raw17506step0 raw17506step0Labels := by
      have ha : raw17506step0 = (fun i j => raw17506 (permutation510 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17506step0 raw17506; decide +kernel
      have hl : raw17506step0Labels = raw17506Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17506 raw17506Labels permutation510 permutation3
    _ = mixedMoment B node3870 node3870Labels := by rfl

def raw17507 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw17507Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17507step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw17507step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17507step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17507step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17507 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17507 raw17507Labels = mixedMoment B node3880 node3880Labels := by
  calc
    mixedMoment B raw17507 raw17507Labels = mixedMoment B raw17507step0 raw17507step0Labels := by
      have ha : raw17507step0 = (fun i j => raw17507 (permutation351 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17507step0 raw17507; decide +kernel
      have hl : raw17507step0Labels = raw17507Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17507 raw17507Labels permutation351 permutation3
    mixedMoment B raw17507step0 raw17507step0Labels = mixedMoment B raw17507step1 raw17507step1Labels := by
      have ha : raw17507step1 = -raw17507step0 := by apply Matrix.ext; change ∀ i j, raw17507step1 i j = -(raw17507step0 i j); unfold raw17507step1 raw17507step0; decide +kernel
      have hl : raw17507step1Labels = raw17507step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3880 node3880Labels := by rfl

def raw17508 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw17508Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17508step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw17508step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17508step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17508step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17508 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17508 raw17508Labels = mixedMoment B node3872 node3872Labels := by
  calc
    mixedMoment B raw17508 raw17508Labels = mixedMoment B raw17508step0 raw17508step0Labels := by
      have ha : raw17508step0 = (fun i j => raw17508 (permutation356 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17508step0 raw17508; decide +kernel
      have hl : raw17508step0Labels = raw17508Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17508 raw17508Labels permutation356 permutation3
    mixedMoment B raw17508step0 raw17508step0Labels = mixedMoment B raw17508step1 raw17508step1Labels := by
      have ha : raw17508step1 = -raw17508step0 := by apply Matrix.ext; change ∀ i j, raw17508step1 i j = -(raw17508step0 i j); unfold raw17508step1 raw17508step0; decide +kernel
      have hl : raw17508step1Labels = raw17508step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3872 node3872Labels := by rfl

def raw17509 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17509Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17509step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17509step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17509step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17509step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17509 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17509 raw17509Labels = mixedMoment B node3808 node3808Labels := by
  calc
    mixedMoment B raw17509 raw17509Labels = mixedMoment B raw17509step0 raw17509step0Labels := by
      have hz : ∀ j, raw17509 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17509step0 = (fun i j => raw17509 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17509step0 raw17509; decide +kernel
      have hl : raw17509step0Labels = raw17509Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17509 raw17509Labels permutation434 hz
    mixedMoment B raw17509step0 raw17509step0Labels = mixedMoment B raw17509step1 raw17509step1Labels := by
      have ha : raw17509step1 = (fun i j => raw17509step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17509step1 raw17509step0; decide +kernel
      have hl : raw17509step1Labels = raw17509step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17509step0 raw17509step0Labels permutation32 permutation6
    _ = mixedMoment B node3808 node3808Labels := by rfl

def raw17510 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17510Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17510step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![-1, -1, 2]]
def raw17510step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17510step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2]]
def raw17510step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17510step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17510step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17510 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17510 raw17510Labels = mixedMoment B node3986 node3986Labels := by
  calc
    mixedMoment B raw17510 raw17510Labels = mixedMoment B raw17510step0 raw17510step0Labels := by
      have hz : ∀ j, raw17510 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17510step0 = (fun i j => raw17510 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17510step0 raw17510; decide +kernel
      have hl : raw17510step0Labels = raw17510Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17510 raw17510Labels permutation434 hz
    mixedMoment B raw17510step0 raw17510step0Labels = mixedMoment B raw17510step1 raw17510step1Labels := by
      have hz : ∀ j, raw17510step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17510step1 = (fun i j => raw17510step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17510step1 raw17510step0; decide +kernel
      have hl : raw17510step1Labels = raw17510step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17510step0 raw17510step0Labels permutation80 hz
    mixedMoment B raw17510step1 raw17510step1Labels = mixedMoment B raw17510step2 raw17510step2Labels := by
      have ha : raw17510step2 = (fun i j => raw17510step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17510step2 raw17510step1; decide +kernel
      have hl : raw17510step2Labels = raw17510step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17510step1 raw17510step1Labels permutation8 permutation6
    _ = mixedMoment B node3986 node3986Labels := by rfl

def raw17511 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw17511Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17511step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 0, 2]]
def raw17511step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17511step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17511step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17511 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17511 raw17511Labels = mixedMoment B node3982 node3982Labels := by
  calc
    mixedMoment B raw17511 raw17511Labels = mixedMoment B raw17511step0 raw17511step0Labels := by
      have hz : ∀ j, raw17511 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17511step0 = (fun i j => raw17511 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17511step0 raw17511; decide +kernel
      have hl : raw17511step0Labels = raw17511Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17511 raw17511Labels permutation434 hz
    mixedMoment B raw17511step0 raw17511step0Labels = mixedMoment B raw17511step1 raw17511step1Labels := by
      have ha : raw17511step1 = (fun i j => raw17511step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17511step1 raw17511step0; decide +kernel
      have hl : raw17511step1Labels = raw17511step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17511step0 raw17511step0Labels permutation32 permutation6
    _ = mixedMoment B node3982 node3982Labels := by rfl

def raw17512 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17512Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17512step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17512step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17512 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17512 raw17512Labels = mixedMoment B node3794 node3794Labels := by
  calc
    mixedMoment B raw17512 raw17512Labels = mixedMoment B raw17512step0 raw17512step0Labels := by
      have ha : raw17512step0 = (fun i j => raw17512 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17512step0 raw17512; decide +kernel
      have hl : raw17512step0Labels = raw17512Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17512 raw17512Labels permutation158 permutation6
    _ = mixedMoment B node3794 node3794Labels := by rfl

def raw17513 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17513Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17513step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17513step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17513 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17513 raw17513Labels = mixedMoment B node3950 node3950Labels := by
  calc
    mixedMoment B raw17513 raw17513Labels = mixedMoment B raw17513step0 raw17513step0Labels := by
      have ha : raw17513step0 = (fun i j => raw17513 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17513step0 raw17513; decide +kernel
      have hl : raw17513step0Labels = raw17513Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17513 raw17513Labels permutation158 permutation6
    _ = mixedMoment B node3950 node3950Labels := by rfl

def raw17514 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17514Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17514step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17514step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17514step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17514step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17514step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17514step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17514 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17514 raw17514Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw17514 raw17514Labels = mixedMoment B raw17514step0 raw17514step0Labels := by
      have hz : ∀ j, raw17514 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17514step0 = (fun i j => raw17514 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17514step0 raw17514; decide +kernel
      have hl : raw17514step0Labels = raw17514Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17514 raw17514Labels permutation346 hz
    mixedMoment B raw17514step0 raw17514step0Labels = mixedMoment B raw17514step1 raw17514step1Labels := by
      have ha : raw17514step1 = (fun i j => raw17514step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17514step1 raw17514step0; decide +kernel
      have hl : raw17514step1Labels = raw17514step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17514step0 raw17514step0Labels permutation151 permutation6
    mixedMoment B raw17514step1 raw17514step1Labels = mixedMoment B raw17514step2 raw17514step2Labels := by
      have ha : raw17514step2 = -raw17514step1 := by apply Matrix.ext; change ∀ i j, raw17514step2 i j = -(raw17514step1 i j); unfold raw17514step2 raw17514step1; decide +kernel
      have hl : raw17514step2Labels = raw17514step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3958 node3958Labels := by rfl

def raw17515 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 2, 0], ![1, -2, 1], ![-1, -1, 2]]
def raw17515Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17515step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17515step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17515 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17515 raw17515Labels = mixedMoment B node3873 node3873Labels := by
  calc
    mixedMoment B raw17515 raw17515Labels = mixedMoment B raw17515step0 raw17515step0Labels := by
      have ha : raw17515step0 = (fun i j => raw17515 (permutation508 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17515step0 raw17515; decide +kernel
      have hl : raw17515step0Labels = raw17515Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17515 raw17515Labels permutation508 permutation3
    _ = mixedMoment B node3873 node3873Labels := by rfl

def raw17516 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![1, -2, 1], ![-2, 0, 2]]
def raw17516Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17516step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17516step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17516 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17516 raw17516Labels = mixedMoment B node3972 node3972Labels := by
  calc
    mixedMoment B raw17516 raw17516Labels = mixedMoment B raw17516step0 raw17516step0Labels := by
      have ha : raw17516step0 = (fun i j => raw17516 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17516step0 raw17516; decide +kernel
      have hl : raw17516step0Labels = raw17516Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17516 raw17516Labels permutation158 permutation6
    _ = mixedMoment B node3972 node3972Labels := by rfl

def raw17517 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17517Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17517step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw17517step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17517 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17517 raw17517Labels = mixedMoment B node3793 node3793Labels := by
  calc
    mixedMoment B raw17517 raw17517Labels = mixedMoment B raw17517step0 raw17517step0Labels := by
      have ha : raw17517step0 = (fun i j => raw17517 (permutation158 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17517step0 raw17517; decide +kernel
      have hl : raw17517step0Labels = raw17517Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17517 raw17517Labels permutation158 permutation6
    _ = mixedMoment B node3793 node3793Labels := by rfl

def raw17518 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17518Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17518step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17518step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17518step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17518step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17518 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17518 raw17518Labels = mixedMoment B node3794 node3794Labels := by
  calc
    mixedMoment B raw17518 raw17518Labels = mixedMoment B raw17518step0 raw17518step0Labels := by
      have ha : raw17518step0 = (fun i j => raw17518 (permutation682 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17518step0 raw17518; decide +kernel
      have hl : raw17518step0Labels = raw17518Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17518 raw17518Labels permutation682 permutation6
    mixedMoment B raw17518step0 raw17518step0Labels = mixedMoment B raw17518step1 raw17518step1Labels := by
      have ha : raw17518step1 = -raw17518step0 := by apply Matrix.ext; change ∀ i j, raw17518step1 i j = -(raw17518step0 i j); unfold raw17518step1 raw17518step0; decide +kernel
      have hl : raw17518step1Labels = raw17518step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3794 node3794Labels := by rfl

def raw17519 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17519Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17519step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17519step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17519step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17519step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17519step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17519step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17519 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17519 raw17519Labels = mixedMoment B node3808 node3808Labels := by
  calc
    mixedMoment B raw17519 raw17519Labels = mixedMoment B raw17519step0 raw17519step0Labels := by
      have hz : ∀ j, raw17519 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw17519step0 = (fun i j => raw17519 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw17519step0 raw17519; decide +kernel
      have hl : raw17519step0Labels = raw17519Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17519 raw17519Labels permutation346 hz
    mixedMoment B raw17519step0 raw17519step0Labels = mixedMoment B raw17519step1 raw17519step1Labels := by
      have ha : raw17519step1 = (fun i j => raw17519step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17519step1 raw17519step0; decide +kernel
      have hl : raw17519step1Labels = raw17519step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17519step0 raw17519step0Labels permutation151 permutation6
    mixedMoment B raw17519step1 raw17519step1Labels = mixedMoment B raw17519step2 raw17519step2Labels := by
      have ha : raw17519step2 = -raw17519step1 := by apply Matrix.ext; change ∀ i j, raw17519step2 i j = -(raw17519step1 i j); unfold raw17519step2 raw17519step1; decide +kernel
      have hl : raw17519step2Labels = raw17519step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3808 node3808Labels := by rfl

def raw17520 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 2, 0], ![0, -1, 1], ![0, -2, 2]]
def raw17520Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17520step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw17520step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17520step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw17520step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17520 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17520 raw17520Labels = mixedMoment B node3796 node3796Labels := by
  calc
    mixedMoment B raw17520 raw17520Labels = mixedMoment B raw17520step0 raw17520step0Labels := by
      have ha : raw17520step0 = (fun i j => raw17520 (permutation682 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17520step0 raw17520; decide +kernel
      have hl : raw17520step0Labels = raw17520Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17520 raw17520Labels permutation682 permutation6
    mixedMoment B raw17520step0 raw17520step0Labels = mixedMoment B raw17520step1 raw17520step1Labels := by
      have ha : raw17520step1 = -raw17520step0 := by apply Matrix.ext; change ∀ i j, raw17520step1 i j = -(raw17520step0 i j); unfold raw17520step1 raw17520step0; decide +kernel
      have hl : raw17520step1Labels = raw17520step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3796 node3796Labels := by rfl

def raw17521 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17521Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17521step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17521step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17521step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17521step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17521 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17521 raw17521Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw17521 raw17521Labels = mixedMoment B raw17521step0 raw17521step0Labels := by
      have ha : raw17521step0 = (fun i j => raw17521 (permutation681 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17521step0 raw17521; decide +kernel
      have hl : raw17521step0Labels = raw17521Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17521 raw17521Labels permutation681 permutation2
    mixedMoment B raw17521step0 raw17521step0Labels = mixedMoment B raw17521step1 raw17521step1Labels := by
      have ha : raw17521step1 = -raw17521step0 := by apply Matrix.ext; change ∀ i j, raw17521step1 i j = -(raw17521step0 i j); unfold raw17521step1 raw17521step0; decide +kernel
      have hl : raw17521step1Labels = raw17521step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw17522 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17522Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17522step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw17522step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17522step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17522step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17522 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17522 raw17522Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw17522 raw17522Labels = mixedMoment B raw17522step0 raw17522step0Labels := by
      have ha : raw17522step0 = (fun i j => raw17522 (permutation687 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17522step0 raw17522; decide +kernel
      have hl : raw17522step0Labels = raw17522Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17522 raw17522Labels permutation687 permutation2
    mixedMoment B raw17522step0 raw17522step0Labels = mixedMoment B raw17522step1 raw17522step1Labels := by
      have ha : raw17522step1 = -raw17522step0 := by apply Matrix.ext; change ∀ i j, raw17522step1 i j = -(raw17522step0 i j); unfold raw17522step1 raw17522step0; decide +kernel
      have hl : raw17522step1Labels = raw17522step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5431 node5431Labels := by rfl

def raw17523 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17523Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17523step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw17523step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17523step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw17523step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17523 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17523 raw17523Labels = mixedMoment B node5427 node5427Labels := by
  calc
    mixedMoment B raw17523 raw17523Labels = mixedMoment B raw17523step0 raw17523step0Labels := by
      have ha : raw17523step0 = (fun i j => raw17523 (permutation677 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17523step0 raw17523; decide +kernel
      have hl : raw17523step0Labels = raw17523Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17523 raw17523Labels permutation677 permutation2
    mixedMoment B raw17523step0 raw17523step0Labels = mixedMoment B raw17523step1 raw17523step1Labels := by
      have ha : raw17523step1 = -raw17523step0 := by apply Matrix.ext; change ∀ i j, raw17523step1 i j = -(raw17523step0 i j); unfold raw17523step1 raw17523step0; decide +kernel
      have hl : raw17523step1Labels = raw17523step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5427 node5427Labels := by rfl

def raw17524 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw17524Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17524step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw17524step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17524step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17524step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17524step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17524step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17524 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17524 raw17524Labels = mixedMoment B node5440 node5440Labels := by
  calc
    mixedMoment B raw17524 raw17524Labels = mixedMoment B raw17524step0 raw17524step0Labels := by
      have hz : ∀ j, raw17524 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17524step0 = (fun i j => raw17524 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17524step0 raw17524; decide +kernel
      have hl : raw17524step0Labels = raw17524Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17524 raw17524Labels permutation520 hz
    mixedMoment B raw17524step0 raw17524step0Labels = mixedMoment B raw17524step1 raw17524step1Labels := by
      have ha : raw17524step1 = (fun i j => raw17524step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17524step1 raw17524step0; decide +kernel
      have hl : raw17524step1Labels = raw17524step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17524step0 raw17524step0Labels permutation144 permutation7
    mixedMoment B raw17524step1 raw17524step1Labels = mixedMoment B raw17524step2 raw17524step2Labels := by
      have ha : raw17524step2 = raw17524step1 := by apply Matrix.ext; unfold raw17524step2 raw17524step1; decide +kernel
      have hl : raw17524step1Labels = labelEmbedding10 ∘ raw17524step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17524step1 raw17524step1Labels raw17524step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5440 node5440Labels := by rfl

def raw17525 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17525Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17525step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17525step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17525step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17525step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17525 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17525 raw17525Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw17525 raw17525Labels = mixedMoment B raw17525step0 raw17525step0Labels := by
      have ha : raw17525step0 = (fun i j => raw17525 (permutation641 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17525step0 raw17525; decide +kernel
      have hl : raw17525step0Labels = raw17525Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17525 raw17525Labels permutation641 permutation6
    mixedMoment B raw17525step0 raw17525step0Labels = mixedMoment B raw17525step1 raw17525step1Labels := by
      have ha : raw17525step1 = raw17525step0 := by apply Matrix.ext; unfold raw17525step1 raw17525step0; decide +kernel
      have hl : raw17525step0Labels = labelEmbedding9 ∘ raw17525step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17525step0 raw17525step0Labels raw17525step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw17526 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17526Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17526step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17526step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17526step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17526step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17526 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17526 raw17526Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw17526 raw17526Labels = mixedMoment B raw17526step0 raw17526step0Labels := by
      have ha : raw17526step0 = (fun i j => raw17526 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17526step0 raw17526; decide +kernel
      have hl : raw17526step0Labels = raw17526Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17526 raw17526Labels permutation176 permutation3
    mixedMoment B raw17526step0 raw17526step0Labels = mixedMoment B raw17526step1 raw17526step1Labels := by
      have ha : raw17526step1 = raw17526step0 := by apply Matrix.ext; unfold raw17526step1 raw17526step0; decide +kernel
      have hl : raw17526step0Labels = labelEmbedding6 ∘ raw17526step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17526step0 raw17526step0Labels raw17526step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5251 node5251Labels := by rfl

def raw17527 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17527Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17527step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw17527step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17527step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17527step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17527 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17527 raw17527Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw17527 raw17527Labels = mixedMoment B raw17527step0 raw17527step0Labels := by
      have ha : raw17527step0 = (fun i j => raw17527 (permutation676 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17527step0 raw17527; decide +kernel
      have hl : raw17527step0Labels = raw17527Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17527 raw17527Labels permutation676 permutation2
    mixedMoment B raw17527step0 raw17527step0Labels = mixedMoment B raw17527step1 raw17527step1Labels := by
      have ha : raw17527step1 = -raw17527step0 := by apply Matrix.ext; change ∀ i j, raw17527step1 i j = -(raw17527step0 i j); unfold raw17527step1 raw17527step0; decide +kernel
      have hl : raw17527step1Labels = raw17527step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5429 node5429Labels := by rfl

def raw17528 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17528Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17528step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17528step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17528step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17528step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17528 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17528 raw17528Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw17528 raw17528Labels = mixedMoment B raw17528step0 raw17528step0Labels := by
      have ha : raw17528step0 = (fun i j => raw17528 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17528step0 raw17528; decide +kernel
      have hl : raw17528step0Labels = raw17528Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17528 raw17528Labels permutation680 permutation2
    mixedMoment B raw17528step0 raw17528step0Labels = mixedMoment B raw17528step1 raw17528step1Labels := by
      have ha : raw17528step1 = -raw17528step0 := by apply Matrix.ext; change ∀ i j, raw17528step1 i j = -(raw17528step0 i j); unfold raw17528step1 raw17528step0; decide +kernel
      have hl : raw17528step1Labels = raw17528step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw17529 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw17529Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17529step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw17529step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17529step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17529step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17529step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17529step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17529 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17529 raw17529Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw17529 raw17529Labels = mixedMoment B raw17529step0 raw17529step0Labels := by
      have hz : ∀ j, raw17529 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17529step0 = (fun i j => raw17529 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17529step0 raw17529; decide +kernel
      have hl : raw17529step0Labels = raw17529Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17529 raw17529Labels permutation520 hz
    mixedMoment B raw17529step0 raw17529step0Labels = mixedMoment B raw17529step1 raw17529step1Labels := by
      have ha : raw17529step1 = (fun i j => raw17529step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17529step1 raw17529step0; decide +kernel
      have hl : raw17529step1Labels = raw17529step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17529step0 raw17529step0Labels permutation143 permutation7
    mixedMoment B raw17529step1 raw17529step1Labels = mixedMoment B raw17529step2 raw17529step2Labels := by
      have ha : raw17529step2 = raw17529step1 := by apply Matrix.ext; unfold raw17529step2 raw17529step1; decide +kernel
      have hl : raw17529step1Labels = labelEmbedding10 ∘ raw17529step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17529step1 raw17529step1Labels raw17529step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw17530 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17530Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17530step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17530step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17530step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17530step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17530 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17530 raw17530Labels = mixedMoment B node5481 node5481Labels := by
  calc
    mixedMoment B raw17530 raw17530Labels = mixedMoment B raw17530step0 raw17530step0Labels := by
      have ha : raw17530step0 = (fun i j => raw17530 (permutation641 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17530step0 raw17530; decide +kernel
      have hl : raw17530step0Labels = raw17530Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17530 raw17530Labels permutation641 permutation6
    mixedMoment B raw17530step0 raw17530step0Labels = mixedMoment B raw17530step1 raw17530step1Labels := by
      have ha : raw17530step1 = raw17530step0 := by apply Matrix.ext; unfold raw17530step1 raw17530step0; decide +kernel
      have hl : raw17530step0Labels = labelEmbedding9 ∘ raw17530step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17530step0 raw17530step0Labels raw17530step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5481 node5481Labels := by rfl

def raw17531 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17531Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17531step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17531step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17531step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw17531step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17531 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17531 raw17531Labels = mixedMoment B node5149 node5149Labels := by
  calc
    mixedMoment B raw17531 raw17531Labels = mixedMoment B raw17531step0 raw17531step0Labels := by
      have ha : raw17531step0 = (fun i j => raw17531 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17531step0 raw17531; decide +kernel
      have hl : raw17531step0Labels = raw17531Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17531 raw17531Labels permutation158 permutation3
    mixedMoment B raw17531step0 raw17531step0Labels = mixedMoment B raw17531step1 raw17531step1Labels := by
      have ha : raw17531step1 = raw17531step0 := by apply Matrix.ext; unfold raw17531step1 raw17531step0; decide +kernel
      have hl : raw17531step0Labels = labelEmbedding6 ∘ raw17531step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17531step0 raw17531step0Labels raw17531step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5149 node5149Labels := by rfl

def raw17532 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17532Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17532step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17532step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17532step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17532step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17532 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17532 raw17532Labels = mixedMoment B node5393 node5393Labels := by
  calc
    mixedMoment B raw17532 raw17532Labels = mixedMoment B raw17532step0 raw17532step0Labels := by
      have ha : raw17532step0 = (fun i j => raw17532 (permutation645 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17532step0 raw17532; decide +kernel
      have hl : raw17532step0Labels = raw17532Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17532 raw17532Labels permutation645 permutation2
    mixedMoment B raw17532step0 raw17532step0Labels = mixedMoment B raw17532step1 raw17532step1Labels := by
      have ha : raw17532step1 = -raw17532step0 := by apply Matrix.ext; change ∀ i j, raw17532step1 i j = -(raw17532step0 i j); unfold raw17532step1 raw17532step0; decide +kernel
      have hl : raw17532step1Labels = raw17532step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5393 node5393Labels := by rfl

def raw17533 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw17533Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17533step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17533step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17533step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17533step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17533 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17533 raw17533Labels = mixedMoment B node5396 node5396Labels := by
  calc
    mixedMoment B raw17533 raw17533Labels = mixedMoment B raw17533step0 raw17533step0Labels := by
      have ha : raw17533step0 = (fun i j => raw17533 (permutation644 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17533step0 raw17533; decide +kernel
      have hl : raw17533step0Labels = raw17533Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17533 raw17533Labels permutation644 permutation2
    mixedMoment B raw17533step0 raw17533step0Labels = mixedMoment B raw17533step1 raw17533step1Labels := by
      have ha : raw17533step1 = -raw17533step0 := by apply Matrix.ext; change ∀ i j, raw17533step1 i j = -(raw17533step0 i j); unfold raw17533step1 raw17533step0; decide +kernel
      have hl : raw17533step1Labels = raw17533step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5396 node5396Labels := by rfl

def raw17534 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw17534Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17534step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw17534step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17534step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17534step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17534step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17534step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17534 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17534 raw17534Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw17534 raw17534Labels = mixedMoment B raw17534step0 raw17534step0Labels := by
      have hz : ∀ j, raw17534 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw17534step0 = (fun i j => raw17534 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw17534step0 raw17534; decide +kernel
      have hl : raw17534step0Labels = raw17534Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17534 raw17534Labels permutation520 hz
    mixedMoment B raw17534step0 raw17534step0Labels = mixedMoment B raw17534step1 raw17534step1Labels := by
      have ha : raw17534step1 = (fun i j => raw17534step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17534step1 raw17534step0; decide +kernel
      have hl : raw17534step1Labels = raw17534step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17534step0 raw17534step0Labels permutation145 permutation2
    mixedMoment B raw17534step1 raw17534step1Labels = mixedMoment B raw17534step2 raw17534step2Labels := by
      have ha : raw17534step2 = -raw17534step1 := by apply Matrix.ext; change ∀ i j, raw17534step2 i j = -(raw17534step1 i j); unfold raw17534step2 raw17534step1; decide +kernel
      have hl : raw17534step2Labels = raw17534step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5410 node5410Labels := by rfl

def raw17535 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17535Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17535step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17535step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17535 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17535 raw17535Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw17535 raw17535Labels = mixedMoment B raw17535step0 raw17535step0Labels := by
      have ha : raw17535step0 = (fun i j => raw17535 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17535step0 raw17535; decide +kernel
      have hl : raw17535step0Labels = raw17535Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17535 raw17535Labels permutation160 permutation2
    _ = mixedMoment B node5478 node5478Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
