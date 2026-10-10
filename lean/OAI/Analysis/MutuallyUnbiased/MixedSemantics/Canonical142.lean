import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw18176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18176Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18176step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18176step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18176step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-2, 0, 2]]
def raw18176step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18176step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw18176step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18176step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw18176step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18176 raw18176Labels = mixedMoment B node3811 node3811Labels := by
  calc
    mixedMoment B raw18176 raw18176Labels = mixedMoment B raw18176step0 raw18176step0Labels := by
      have hz : ∀ j, raw18176 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18176step0 = (fun i j => raw18176 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18176step0 raw18176; decide +kernel
      have hl : raw18176step0Labels = raw18176Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18176 raw18176Labels permutation346 hz
    mixedMoment B raw18176step0 raw18176step0Labels = mixedMoment B raw18176step1 raw18176step1Labels := by
      have ha : raw18176step1 = (fun i j => raw18176step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18176step1 raw18176step0; decide +kernel
      have hl : raw18176step1Labels = raw18176step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18176step0 raw18176step0Labels permutation40 permutation7
    mixedMoment B raw18176step1 raw18176step1Labels = mixedMoment B raw18176step2 raw18176step2Labels := by
      have ha : raw18176step2 = -raw18176step1 := by apply Matrix.ext; change ∀ i j, raw18176step2 i j = -(raw18176step1 i j); unfold raw18176step2 raw18176step1; decide +kernel
      have hl : raw18176step2Labels = raw18176step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18176step2 raw18176step2Labels = mixedMoment B raw18176step3 raw18176step3Labels := by
      have ha : raw18176step3 = raw18176step2 := by apply Matrix.ext; unfold raw18176step3 raw18176step2; decide +kernel
      have hl : raw18176step2Labels = labelEmbedding1 ∘ raw18176step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18176step2 raw18176step2Labels raw18176step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3811 node3811Labels := by rfl

def raw18177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18177Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18177step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18177step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw18177step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18177step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw18177step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18177 raw18177Labels = mixedMoment B node3854 node3854Labels := by
  calc
    mixedMoment B raw18177 raw18177Labels = mixedMoment B raw18177step0 raw18177step0Labels := by
      have hz : ∀ j, raw18177 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18177step0 = (fun i j => raw18177 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18177step0 raw18177; decide +kernel
      have hl : raw18177step0Labels = raw18177Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18177 raw18177Labels permutation346 hz
    mixedMoment B raw18177step0 raw18177step0Labels = mixedMoment B raw18177step1 raw18177step1Labels := by
      have ha : raw18177step1 = (fun i j => raw18177step0 (permutation117 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18177step1 raw18177step0; decide +kernel
      have hl : raw18177step1Labels = raw18177step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18177step0 raw18177step0Labels permutation117 permutation5
    mixedMoment B raw18177step1 raw18177step1Labels = mixedMoment B raw18177step2 raw18177step2Labels := by
      have ha : raw18177step2 = raw18177step1 := by apply Matrix.ext; unfold raw18177step2 raw18177step1; decide +kernel
      have hl : raw18177step1Labels = labelEmbedding1 ∘ raw18177step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18177step1 raw18177step1Labels raw18177step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3854 node3854Labels := by rfl

def raw18178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18178Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18178step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18178step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18178step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -2, 3]]
def raw18178step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18178step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw18178step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18178step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw18178step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18178 raw18178Labels = mixedMoment B node2681 node2681Labels := by
  calc
    mixedMoment B raw18178 raw18178Labels = mixedMoment B raw18178step0 raw18178step0Labels := by
      have hz : ∀ j, raw18178 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18178step0 = (fun i j => raw18178 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18178step0 raw18178; decide +kernel
      have hl : raw18178step0Labels = raw18178Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18178 raw18178Labels permutation346 hz
    mixedMoment B raw18178step0 raw18178step0Labels = mixedMoment B raw18178step1 raw18178step1Labels := by
      have ha : raw18178step1 = (fun i j => raw18178step0 (permutation56 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18178step1 raw18178step0; decide +kernel
      have hl : raw18178step1Labels = raw18178step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18178step0 raw18178step0Labels permutation56 permutation5
    mixedMoment B raw18178step1 raw18178step1Labels = mixedMoment B raw18178step2 raw18178step2Labels := by
      have ha : raw18178step2 = -raw18178step1 := by apply Matrix.ext; change ∀ i j, raw18178step2 i j = -(raw18178step1 i j); unfold raw18178step2 raw18178step1; decide +kernel
      have hl : raw18178step2Labels = raw18178step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18178step2 raw18178step2Labels = mixedMoment B raw18178step3 raw18178step3Labels := by
      have ha : raw18178step3 = raw18178step2 := by apply Matrix.ext; unfold raw18178step3 raw18178step2; decide +kernel
      have hl : raw18178step2Labels = labelEmbedding1 ∘ raw18178step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18178step2 raw18178step2Labels raw18178step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2681 node2681Labels := by rfl

def raw18179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18179Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18179step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18179step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18179step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18179step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18179 raw18179Labels = mixedMoment B node3557 node3557Labels := by
  calc
    mixedMoment B raw18179 raw18179Labels = mixedMoment B raw18179step0 raw18179step0Labels := by
      have ha : raw18179step0 = (fun i j => raw18179 (permutation620 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18179step0 raw18179; decide +kernel
      have hl : raw18179step0Labels = raw18179Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18179 raw18179Labels permutation620 permutation7
    mixedMoment B raw18179step0 raw18179step0Labels = mixedMoment B raw18179step1 raw18179step1Labels := by
      have ha : raw18179step1 = raw18179step0 := by apply Matrix.ext; unfold raw18179step1 raw18179step0; decide +kernel
      have hl : raw18179step0Labels = labelEmbedding1 ∘ raw18179step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18179step0 raw18179step0Labels raw18179step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3557 node3557Labels := by rfl

def raw18180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18180Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18180step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18180step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18180step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18180step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18180step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18180 raw18180Labels = mixedMoment B node3564 node3564Labels := by
  calc
    mixedMoment B raw18180 raw18180Labels = mixedMoment B raw18180step0 raw18180step0Labels := by
      have hz : ∀ j, raw18180 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18180step0 = (fun i j => raw18180 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18180step0 raw18180; decide +kernel
      have hl : raw18180step0Labels = raw18180Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18180 raw18180Labels permutation346 hz
    mixedMoment B raw18180step0 raw18180step0Labels = mixedMoment B raw18180step1 raw18180step1Labels := by
      have ha : raw18180step1 = (fun i j => raw18180step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18180step1 raw18180step0; decide +kernel
      have hl : raw18180step1Labels = raw18180step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18180step0 raw18180step0Labels permutation139 permutation7
    mixedMoment B raw18180step1 raw18180step1Labels = mixedMoment B raw18180step2 raw18180step2Labels := by
      have ha : raw18180step2 = raw18180step1 := by apply Matrix.ext; unfold raw18180step2 raw18180step1; decide +kernel
      have hl : raw18180step1Labels = labelEmbedding1 ∘ raw18180step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18180step1 raw18180step1Labels raw18180step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3564 node3564Labels := by rfl

def raw18181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![3, -1, -2]]
def raw18181Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18181step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw18181step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18181step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![3, -1, -2]]
def raw18181step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18181step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18181step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18181step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18181step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18181 raw18181Labels = mixedMoment B node3582 node3582Labels := by
  calc
    mixedMoment B raw18181 raw18181Labels = mixedMoment B raw18181step0 raw18181step0Labels := by
      have hz : ∀ j, raw18181 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18181step0 = (fun i j => raw18181 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18181step0 raw18181; decide +kernel
      have hl : raw18181step0Labels = raw18181Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18181 raw18181Labels permutation520 hz
    mixedMoment B raw18181step0 raw18181step0Labels = mixedMoment B raw18181step1 raw18181step1Labels := by
      have hz : ∀ j, raw18181step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18181step1 = (fun i j => raw18181step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18181step1 raw18181step0; decide +kernel
      have hl : raw18181step1Labels = raw18181step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18181step0 raw18181step0Labels permutation80 hz
    mixedMoment B raw18181step1 raw18181step1Labels = mixedMoment B raw18181step2 raw18181step2Labels := by
      have ha : raw18181step2 = (fun i j => raw18181step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18181step2 raw18181step1; decide +kernel
      have hl : raw18181step2Labels = raw18181step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18181step1 raw18181step1Labels permutation29 permutation7
    mixedMoment B raw18181step2 raw18181step2Labels = mixedMoment B raw18181step3 raw18181step3Labels := by
      have ha : raw18181step3 = raw18181step2 := by apply Matrix.ext; unfold raw18181step3 raw18181step2; decide +kernel
      have hl : raw18181step2Labels = labelEmbedding1 ∘ raw18181step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18181step2 raw18181step2Labels raw18181step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3582 node3582Labels := by rfl

def raw18182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18182Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18182step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18182step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18182step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18182 raw18182Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw18182 raw18182Labels = mixedMoment B raw18182step0 raw18182step0Labels := by
      have hz : ∀ j, raw18182 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18182step0 = (fun i j => raw18182 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18182step0 raw18182; decide +kernel
      have hl : raw18182step0Labels = raw18182Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18182 raw18182Labels permutation346 hz
    mixedMoment B raw18182step0 raw18182step0Labels = mixedMoment B raw18182step1 raw18182step1Labels := by
      have ha : raw18182step1 = (fun i j => raw18182step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18182step1 raw18182step0; decide +kernel
      have hl : raw18182step1Labels = raw18182step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18182step0 raw18182step0Labels permutation56 permutation2
    _ = mixedMoment B node5435 node5435Labels := by rfl

def raw18183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18183Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18183step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18183step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18183step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18183step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18183step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18183step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18183 raw18183Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw18183 raw18183Labels = mixedMoment B raw18183step0 raw18183step0Labels := by
      have ha : raw18183step0 = (fun i j => raw18183 (permutation685 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18183step0 raw18183; decide +kernel
      have hl : raw18183step0Labels = raw18183Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18183 raw18183Labels permutation685 permutation3
    mixedMoment B raw18183step0 raw18183step0Labels = mixedMoment B raw18183step1 raw18183step1Labels := by
      have ha : raw18183step1 = -raw18183step0 := by apply Matrix.ext; change ∀ i j, raw18183step1 i j = -(raw18183step0 i j); unfold raw18183step1 raw18183step0; decide +kernel
      have hl : raw18183step1Labels = raw18183step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18183step1 raw18183step1Labels = mixedMoment B raw18183step2 raw18183step2Labels := by
      have ha : raw18183step2 = raw18183step1 := by apply Matrix.ext; unfold raw18183step2 raw18183step1; decide +kernel
      have hl : raw18183step1Labels = labelEmbedding6 ∘ raw18183step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18183step1 raw18183step1Labels raw18183step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

def raw18184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18184Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18184step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18184step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw18184step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18184step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18184step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18184step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18184step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18184 raw18184Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw18184 raw18184Labels = mixedMoment B raw18184step0 raw18184step0Labels := by
      have hz : ∀ j, raw18184 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18184step0 = (fun i j => raw18184 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18184step0 raw18184; decide +kernel
      have hl : raw18184step0Labels = raw18184Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18184 raw18184Labels permutation346 hz
    mixedMoment B raw18184step0 raw18184step0Labels = mixedMoment B raw18184step1 raw18184step1Labels := by
      have ha : raw18184step1 = (fun i j => raw18184step0 (permutation148 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18184step1 raw18184step0; decide +kernel
      have hl : raw18184step1Labels = raw18184step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18184step0 raw18184step0Labels permutation148 permutation3
    mixedMoment B raw18184step1 raw18184step1Labels = mixedMoment B raw18184step2 raw18184step2Labels := by
      have ha : raw18184step2 = -raw18184step1 := by apply Matrix.ext; change ∀ i j, raw18184step2 i j = -(raw18184step1 i j); unfold raw18184step2 raw18184step1; decide +kernel
      have hl : raw18184step2Labels = raw18184step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18184step2 raw18184step2Labels = mixedMoment B raw18184step3 raw18184step3Labels := by
      have ha : raw18184step3 = raw18184step2 := by apply Matrix.ext; unfold raw18184step3 raw18184step2; decide +kernel
      have hl : raw18184step2Labels = labelEmbedding6 ∘ raw18184step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18184step2 raw18184step2Labels raw18184step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw18185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18185Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18185step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18185step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18185step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18185step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18185step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18185 raw18185Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw18185 raw18185Labels = mixedMoment B raw18185step0 raw18185step0Labels := by
      have hz : ∀ j, raw18185 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18185step0 = (fun i j => raw18185 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18185step0 raw18185; decide +kernel
      have hl : raw18185step0Labels = raw18185Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18185 raw18185Labels permutation346 hz
    mixedMoment B raw18185step0 raw18185step0Labels = mixedMoment B raw18185step1 raw18185step1Labels := by
      have ha : raw18185step1 = (fun i j => raw18185step0 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18185step1 raw18185step0; decide +kernel
      have hl : raw18185step1Labels = raw18185step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18185step0 raw18185step0Labels permutation137 permutation5
    mixedMoment B raw18185step1 raw18185step1Labels = mixedMoment B raw18185step2 raw18185step2Labels := by
      have ha : raw18185step2 = raw18185step1 := by apply Matrix.ext; unfold raw18185step2 raw18185step1; decide +kernel
      have hl : raw18185step1Labels = labelEmbedding8 ∘ raw18185step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18185step1 raw18185step1Labels raw18185step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw18186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18186Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18186step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18186step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1]]
def raw18186step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18186step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18186step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18186step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18186step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18186 raw18186Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw18186 raw18186Labels = mixedMoment B raw18186step0 raw18186step0Labels := by
      have hz : ∀ j, raw18186 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18186step0 = (fun i j => raw18186 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18186step0 raw18186; decide +kernel
      have hl : raw18186step0Labels = raw18186Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18186 raw18186Labels permutation346 hz
    mixedMoment B raw18186step0 raw18186step0Labels = mixedMoment B raw18186step1 raw18186step1Labels := by
      have ha : raw18186step1 = (fun i j => raw18186step0 (permutation75 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18186step1 raw18186step0; decide +kernel
      have hl : raw18186step1Labels = raw18186step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18186step0 raw18186step0Labels permutation75 permutation6
    mixedMoment B raw18186step1 raw18186step1Labels = mixedMoment B raw18186step2 raw18186step2Labels := by
      have ha : raw18186step2 = -raw18186step1 := by apply Matrix.ext; change ∀ i j, raw18186step2 i j = -(raw18186step1 i j); unfold raw18186step2 raw18186step1; decide +kernel
      have hl : raw18186step2Labels = raw18186step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18186step2 raw18186step2Labels = mixedMoment B raw18186step3 raw18186step3Labels := by
      have ha : raw18186step3 = raw18186step2 := by apply Matrix.ext; unfold raw18186step3 raw18186step2; decide +kernel
      have hl : raw18186step2Labels = labelEmbedding9 ∘ raw18186step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18186step2 raw18186step2Labels raw18186step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw18187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18187Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18187step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18187step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18187step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw18187step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18187step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18187step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18187step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18187step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18187 raw18187Labels = mixedMoment B node4810 node4810Labels := by
  calc
    mixedMoment B raw18187 raw18187Labels = mixedMoment B raw18187step0 raw18187step0Labels := by
      have hz : ∀ j, raw18187 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18187step0 = (fun i j => raw18187 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18187step0 raw18187; decide +kernel
      have hl : raw18187step0Labels = raw18187Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18187 raw18187Labels permutation346 hz
    mixedMoment B raw18187step0 raw18187step0Labels = mixedMoment B raw18187step1 raw18187step1Labels := by
      have ha : raw18187step1 = (fun i j => raw18187step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18187step1 raw18187step0; decide +kernel
      have hl : raw18187step1Labels = raw18187step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18187step0 raw18187step0Labels permutation40 permutation5
    mixedMoment B raw18187step1 raw18187step1Labels = mixedMoment B raw18187step2 raw18187step2Labels := by
      have ha : raw18187step2 = -raw18187step1 := by apply Matrix.ext; change ∀ i j, raw18187step2 i j = -(raw18187step1 i j); unfold raw18187step2 raw18187step1; decide +kernel
      have hl : raw18187step2Labels = raw18187step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18187step2 raw18187step2Labels = mixedMoment B raw18187step3 raw18187step3Labels := by
      have ha : raw18187step3 = raw18187step2 := by apply Matrix.ext; unfold raw18187step3 raw18187step2; decide +kernel
      have hl : raw18187step2Labels = labelEmbedding8 ∘ raw18187step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18187step2 raw18187step2Labels raw18187step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4810 node4810Labels := by rfl

def raw18188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18188Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18188step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw18188step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18188step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw18188step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18188 raw18188Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw18188 raw18188Labels = mixedMoment B raw18188step0 raw18188step0Labels := by
      have ha : raw18188step0 = (fun i j => raw18188 (permutation622 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18188step0 raw18188; decide +kernel
      have hl : raw18188step0Labels = raw18188Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18188 raw18188Labels permutation622 permutation5
    mixedMoment B raw18188step0 raw18188step0Labels = mixedMoment B raw18188step1 raw18188step1Labels := by
      have ha : raw18188step1 = raw18188step0 := by apply Matrix.ext; unfold raw18188step1 raw18188step0; decide +kernel
      have hl : raw18188step0Labels = labelEmbedding8 ∘ raw18188step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18188step0 raw18188step0Labels raw18188step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

def raw18189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18189Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18189step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18189step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw18189step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18189step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18189step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18189step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18189step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18189 raw18189Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw18189 raw18189Labels = mixedMoment B raw18189step0 raw18189step0Labels := by
      have hz : ∀ j, raw18189 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18189step0 = (fun i j => raw18189 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18189step0 raw18189; decide +kernel
      have hl : raw18189step0Labels = raw18189Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18189 raw18189Labels permutation346 hz
    mixedMoment B raw18189step0 raw18189step0Labels = mixedMoment B raw18189step1 raw18189step1Labels := by
      have ha : raw18189step1 = (fun i j => raw18189step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18189step1 raw18189step0; decide +kernel
      have hl : raw18189step1Labels = raw18189step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18189step0 raw18189step0Labels permutation40 permutation5
    mixedMoment B raw18189step1 raw18189step1Labels = mixedMoment B raw18189step2 raw18189step2Labels := by
      have ha : raw18189step2 = -raw18189step1 := by apply Matrix.ext; change ∀ i j, raw18189step2 i j = -(raw18189step1 i j); unfold raw18189step2 raw18189step1; decide +kernel
      have hl : raw18189step2Labels = raw18189step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18189step2 raw18189step2Labels = mixedMoment B raw18189step3 raw18189step3Labels := by
      have ha : raw18189step3 = raw18189step2 := by apply Matrix.ext; unfold raw18189step3 raw18189step2; decide +kernel
      have hl : raw18189step2Labels = labelEmbedding8 ∘ raw18189step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18189step2 raw18189step2Labels raw18189step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

def raw18190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18190Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18190step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18190step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18190step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18190step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18190step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18190 raw18190Labels = mixedMoment B node5387 node5387Labels := by
  calc
    mixedMoment B raw18190 raw18190Labels = mixedMoment B raw18190step0 raw18190step0Labels := by
      have hz : ∀ j, raw18190 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18190step0 = (fun i j => raw18190 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18190step0 raw18190; decide +kernel
      have hl : raw18190step0Labels = raw18190Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18190 raw18190Labels permutation346 hz
    mixedMoment B raw18190step0 raw18190step0Labels = mixedMoment B raw18190step1 raw18190step1Labels := by
      have ha : raw18190step1 = (fun i j => raw18190step0 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18190step1 raw18190step0; decide +kernel
      have hl : raw18190step1Labels = raw18190step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18190step0 raw18190step0Labels permutation137 permutation5
    mixedMoment B raw18190step1 raw18190step1Labels = mixedMoment B raw18190step2 raw18190step2Labels := by
      have ha : raw18190step2 = raw18190step1 := by apply Matrix.ext; unfold raw18190step2 raw18190step1; decide +kernel
      have hl : raw18190step1Labels = labelEmbedding8 ∘ raw18190step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18190step1 raw18190step1Labels raw18190step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5387 node5387Labels := by rfl

def raw18191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18191Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18191step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18191step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18191step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw18191step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18191step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18191 raw18191Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw18191 raw18191Labels = mixedMoment B raw18191step0 raw18191step0Labels := by
      have hz : ∀ j, raw18191 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18191step0 = (fun i j => raw18191 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18191step0 raw18191; decide +kernel
      have hl : raw18191step0Labels = raw18191Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18191 raw18191Labels permutation346 hz
    mixedMoment B raw18191step0 raw18191step0Labels = mixedMoment B raw18191step1 raw18191step1Labels := by
      have ha : raw18191step1 = (fun i j => raw18191step0 (permutation79 i) (permutation4 j)) := by apply Matrix.ext; unfold raw18191step1 raw18191step0; decide +kernel
      have hl : raw18191step1Labels = raw18191step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18191step0 raw18191step0Labels permutation79 permutation4
    mixedMoment B raw18191step1 raw18191step1Labels = mixedMoment B raw18191step2 raw18191step2Labels := by
      have ha : raw18191step2 = raw18191step1 := by apply Matrix.ext; unfold raw18191step2 raw18191step1; decide +kernel
      have hl : raw18191step1Labels = labelEmbedding7 ∘ raw18191step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18191step1 raw18191step1Labels raw18191step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5435 node5435Labels := by rfl

def raw18192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18192Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18192step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw18192step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18192step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18192step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18192step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18192step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18192 raw18192Labels = mixedMoment B node4798 node4798Labels := by
  calc
    mixedMoment B raw18192 raw18192Labels = mixedMoment B raw18192step0 raw18192step0Labels := by
      have ha : raw18192step0 = (fun i j => raw18192 (permutation212 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18192step0 raw18192; decide +kernel
      have hl : raw18192step0Labels = raw18192Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18192 raw18192Labels permutation212 permutation5
    mixedMoment B raw18192step0 raw18192step0Labels = mixedMoment B raw18192step1 raw18192step1Labels := by
      have ha : raw18192step1 = -raw18192step0 := by apply Matrix.ext; change ∀ i j, raw18192step1 i j = -(raw18192step0 i j); unfold raw18192step1 raw18192step0; decide +kernel
      have hl : raw18192step1Labels = raw18192step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18192step1 raw18192step1Labels = mixedMoment B raw18192step2 raw18192step2Labels := by
      have ha : raw18192step2 = raw18192step1 := by apply Matrix.ext; unfold raw18192step2 raw18192step1; decide +kernel
      have hl : raw18192step1Labels = labelEmbedding8 ∘ raw18192step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18192step1 raw18192step1Labels raw18192step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4798 node4798Labels := by rfl

def raw18193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18193Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18193step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw18193step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18193step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw18193step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18193 raw18193Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw18193 raw18193Labels = mixedMoment B raw18193step0 raw18193step0Labels := by
      have ha : raw18193step0 = (fun i j => raw18193 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18193step0 raw18193; decide +kernel
      have hl : raw18193step0Labels = raw18193Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18193 raw18193Labels permutation160 permutation3
    mixedMoment B raw18193step0 raw18193step0Labels = mixedMoment B raw18193step1 raw18193step1Labels := by
      have ha : raw18193step1 = raw18193step0 := by apply Matrix.ext; unfold raw18193step1 raw18193step0; decide +kernel
      have hl : raw18193step0Labels = labelEmbedding6 ∘ raw18193step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18193step0 raw18193step0Labels raw18193step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

def raw18194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18194Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18194step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw18194step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18194step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18194step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18194step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18194step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18194 raw18194Labels = mixedMoment B node5349 node5349Labels := by
  calc
    mixedMoment B raw18194 raw18194Labels = mixedMoment B raw18194step0 raw18194step0Labels := by
      have ha : raw18194step0 = (fun i j => raw18194 (permutation212 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18194step0 raw18194; decide +kernel
      have hl : raw18194step0Labels = raw18194Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18194 raw18194Labels permutation212 permutation5
    mixedMoment B raw18194step0 raw18194step0Labels = mixedMoment B raw18194step1 raw18194step1Labels := by
      have ha : raw18194step1 = -raw18194step0 := by apply Matrix.ext; change ∀ i j, raw18194step1 i j = -(raw18194step0 i j); unfold raw18194step1 raw18194step0; decide +kernel
      have hl : raw18194step1Labels = raw18194step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18194step1 raw18194step1Labels = mixedMoment B raw18194step2 raw18194step2Labels := by
      have ha : raw18194step2 = raw18194step1 := by apply Matrix.ext; unfold raw18194step2 raw18194step1; decide +kernel
      have hl : raw18194step1Labels = labelEmbedding8 ∘ raw18194step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18194step1 raw18194step1Labels raw18194step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5349 node5349Labels := by rfl

def raw18195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18195Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18195step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18195step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18195step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18195step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18195 raw18195Labels = mixedMoment B node5400 node5400Labels := by
  calc
    mixedMoment B raw18195 raw18195Labels = mixedMoment B raw18195step0 raw18195step0Labels := by
      have ha : raw18195step0 = (fun i j => raw18195 (permutation632 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18195step0 raw18195; decide +kernel
      have hl : raw18195step0Labels = raw18195Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18195 raw18195Labels permutation632 permutation5
    mixedMoment B raw18195step0 raw18195step0Labels = mixedMoment B raw18195step1 raw18195step1Labels := by
      have ha : raw18195step1 = raw18195step0 := by apply Matrix.ext; unfold raw18195step1 raw18195step0; decide +kernel
      have hl : raw18195step0Labels = labelEmbedding8 ∘ raw18195step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18195step0 raw18195step0Labels raw18195step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5400 node5400Labels := by rfl

def raw18196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18196Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18196step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw18196step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18196step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18196step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18196step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw18196step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18196 raw18196Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw18196 raw18196Labels = mixedMoment B raw18196step0 raw18196step0Labels := by
      have ha : raw18196step0 = (fun i j => raw18196 (permutation212 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18196step0 raw18196; decide +kernel
      have hl : raw18196step0Labels = raw18196Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18196 raw18196Labels permutation212 permutation5
    mixedMoment B raw18196step0 raw18196step0Labels = mixedMoment B raw18196step1 raw18196step1Labels := by
      have ha : raw18196step1 = -raw18196step0 := by apply Matrix.ext; change ∀ i j, raw18196step1 i j = -(raw18196step0 i j); unfold raw18196step1 raw18196step0; decide +kernel
      have hl : raw18196step1Labels = raw18196step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18196step1 raw18196step1Labels = mixedMoment B raw18196step2 raw18196step2Labels := by
      have ha : raw18196step2 = raw18196step1 := by apply Matrix.ext; unfold raw18196step2 raw18196step1; decide +kernel
      have hl : raw18196step1Labels = labelEmbedding8 ∘ raw18196step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18196step1 raw18196step1Labels raw18196step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

def raw18197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18197Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18197step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18197step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18197step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18197step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18197step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18197step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18197 raw18197Labels = mixedMoment B node4865 node4865Labels := by
  calc
    mixedMoment B raw18197 raw18197Labels = mixedMoment B raw18197step0 raw18197step0Labels := by
      have hz : ∀ j, raw18197 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18197step0 = (fun i j => raw18197 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18197step0 raw18197; decide +kernel
      have hl : raw18197step0Labels = raw18197Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18197 raw18197Labels permutation346 hz
    mixedMoment B raw18197step0 raw18197step0Labels = mixedMoment B raw18197step1 raw18197step1Labels := by
      have ha : raw18197step1 = (fun i j => raw18197step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18197step1 raw18197step0; decide +kernel
      have hl : raw18197step1Labels = raw18197step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18197step0 raw18197step0Labels permutation32 permutation3
    mixedMoment B raw18197step1 raw18197step1Labels = mixedMoment B raw18197step2 raw18197step2Labels := by
      have ha : raw18197step2 = raw18197step1 := by apply Matrix.ext; unfold raw18197step2 raw18197step1; decide +kernel
      have hl : raw18197step1Labels = labelEmbedding6 ∘ raw18197step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18197step1 raw18197step1Labels raw18197step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4865 node4865Labels := by rfl

def raw18198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18198Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18198step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18198step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18198step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18198step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18198step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18198 raw18198Labels = mixedMoment B node5387 node5387Labels := by
  calc
    mixedMoment B raw18198 raw18198Labels = mixedMoment B raw18198step0 raw18198step0Labels := by
      have hz : ∀ j, raw18198 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18198step0 = (fun i j => raw18198 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18198step0 raw18198; decide +kernel
      have hl : raw18198step0Labels = raw18198Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18198 raw18198Labels permutation346 hz
    mixedMoment B raw18198step0 raw18198step0Labels = mixedMoment B raw18198step1 raw18198step1Labels := by
      have ha : raw18198step1 = (fun i j => raw18198step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18198step1 raw18198step0; decide +kernel
      have hl : raw18198step1Labels = raw18198step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18198step0 raw18198step0Labels permutation32 permutation3
    mixedMoment B raw18198step1 raw18198step1Labels = mixedMoment B raw18198step2 raw18198step2Labels := by
      have ha : raw18198step2 = raw18198step1 := by apply Matrix.ext; unfold raw18198step2 raw18198step1; decide +kernel
      have hl : raw18198step1Labels = labelEmbedding6 ∘ raw18198step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18198step1 raw18198step1Labels raw18198step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5387 node5387Labels := by rfl

def raw18199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18199Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18199step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18199step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18199step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18199step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18199 raw18199Labels = mixedMoment B node5400 node5400Labels := by
  calc
    mixedMoment B raw18199 raw18199Labels = mixedMoment B raw18199step0 raw18199step0Labels := by
      have ha : raw18199step0 = (fun i j => raw18199 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18199step0 raw18199; decide +kernel
      have hl : raw18199step0Labels = raw18199Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18199 raw18199Labels permutation176 permutation3
    mixedMoment B raw18199step0 raw18199step0Labels = mixedMoment B raw18199step1 raw18199step1Labels := by
      have ha : raw18199step1 = raw18199step0 := by apply Matrix.ext; unfold raw18199step1 raw18199step0; decide +kernel
      have hl : raw18199step0Labels = labelEmbedding6 ∘ raw18199step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18199step0 raw18199step0Labels raw18199step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5400 node5400Labels := by rfl

def raw18200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18200Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18200step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18200step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw18200step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18200step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18200step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18200step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18200step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18200 raw18200Labels = mixedMoment B node5432 node5432Labels := by
  calc
    mixedMoment B raw18200 raw18200Labels = mixedMoment B raw18200step0 raw18200step0Labels := by
      have hz : ∀ j, raw18200 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18200step0 = (fun i j => raw18200 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18200step0 raw18200; decide +kernel
      have hl : raw18200step0Labels = raw18200Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18200 raw18200Labels permutation346 hz
    mixedMoment B raw18200step0 raw18200step0Labels = mixedMoment B raw18200step1 raw18200step1Labels := by
      have ha : raw18200step1 = (fun i j => raw18200step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18200step1 raw18200step0; decide +kernel
      have hl : raw18200step1Labels = raw18200step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18200step0 raw18200step0Labels permutation145 permutation3
    mixedMoment B raw18200step1 raw18200step1Labels = mixedMoment B raw18200step2 raw18200step2Labels := by
      have ha : raw18200step2 = -raw18200step1 := by apply Matrix.ext; change ∀ i j, raw18200step2 i j = -(raw18200step1 i j); unfold raw18200step2 raw18200step1; decide +kernel
      have hl : raw18200step2Labels = raw18200step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18200step2 raw18200step2Labels = mixedMoment B raw18200step3 raw18200step3Labels := by
      have ha : raw18200step3 = raw18200step2 := by apply Matrix.ext; unfold raw18200step3 raw18200step2; decide +kernel
      have hl : raw18200step2Labels = labelEmbedding6 ∘ raw18200step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18200step2 raw18200step2Labels raw18200step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5432 node5432Labels := by rfl

def raw18201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18201Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18201step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18201step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18201step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18201step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18201step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18201 raw18201Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw18201 raw18201Labels = mixedMoment B raw18201step0 raw18201step0Labels := by
      have hz : ∀ j, raw18201 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18201step0 = (fun i j => raw18201 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18201step0 raw18201; decide +kernel
      have hl : raw18201step0Labels = raw18201Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18201 raw18201Labels permutation346 hz
    mixedMoment B raw18201step0 raw18201step0Labels = mixedMoment B raw18201step1 raw18201step1Labels := by
      have ha : raw18201step1 = (fun i j => raw18201step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18201step1 raw18201step0; decide +kernel
      have hl : raw18201step1Labels = raw18201step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18201step0 raw18201step0Labels permutation32 permutation3
    mixedMoment B raw18201step1 raw18201step1Labels = mixedMoment B raw18201step2 raw18201step2Labels := by
      have ha : raw18201step2 = raw18201step1 := by apply Matrix.ext; unfold raw18201step2 raw18201step1; decide +kernel
      have hl : raw18201step1Labels = labelEmbedding6 ∘ raw18201step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18201step1 raw18201step1Labels raw18201step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw18202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw18202Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18202step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw18202step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18202step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw18202step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18202step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw18202step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18202step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw18202step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18202 raw18202Labels = mixedMoment B node4828 node4828Labels := by
  calc
    mixedMoment B raw18202 raw18202Labels = mixedMoment B raw18202step0 raw18202step0Labels := by
      have hz : ∀ j, raw18202 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18202step0 = (fun i j => raw18202 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18202step0 raw18202; decide +kernel
      have hl : raw18202step0Labels = raw18202Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18202 raw18202Labels permutation346 hz
    mixedMoment B raw18202step0 raw18202step0Labels = mixedMoment B raw18202step1 raw18202step1Labels := by
      have ha : raw18202step1 = (fun i j => raw18202step0 (permutation38 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18202step1 raw18202step0; decide +kernel
      have hl : raw18202step1Labels = raw18202step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18202step0 raw18202step0Labels permutation38 permutation5
    mixedMoment B raw18202step1 raw18202step1Labels = mixedMoment B raw18202step2 raw18202step2Labels := by
      have ha : raw18202step2 = -raw18202step1 := by apply Matrix.ext; change ∀ i j, raw18202step2 i j = -(raw18202step1 i j); unfold raw18202step2 raw18202step1; decide +kernel
      have hl : raw18202step2Labels = raw18202step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18202step2 raw18202step2Labels = mixedMoment B raw18202step3 raw18202step3Labels := by
      have ha : raw18202step3 = raw18202step2 := by apply Matrix.ext; unfold raw18202step3 raw18202step2; decide +kernel
      have hl : raw18202step2Labels = labelEmbedding8 ∘ raw18202step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18202step2 raw18202step2Labels raw18202step3Labels labelEmbedding8 hl
    _ = mixedMoment B node4828 node4828Labels := by rfl

def raw18203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw18203Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw18203step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18203step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw18203step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18203step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18203step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18203step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18203step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18203 raw18203Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw18203 raw18203Labels = mixedMoment B raw18203step0 raw18203step0Labels := by
      have hz : ∀ j, raw18203 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18203step0 = (fun i j => raw18203 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18203step0 raw18203; decide +kernel
      have hl : raw18203step0Labels = raw18203Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18203 raw18203Labels permutation346 hz
    mixedMoment B raw18203step0 raw18203step0Labels = mixedMoment B raw18203step1 raw18203step1Labels := by
      have ha : raw18203step1 = (fun i j => raw18203step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18203step1 raw18203step0; decide +kernel
      have hl : raw18203step1Labels = raw18203step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18203step0 raw18203step0Labels permutation151 permutation3
    mixedMoment B raw18203step1 raw18203step1Labels = mixedMoment B raw18203step2 raw18203step2Labels := by
      have ha : raw18203step2 = -raw18203step1 := by apply Matrix.ext; change ∀ i j, raw18203step2 i j = -(raw18203step1 i j); unfold raw18203step2 raw18203step1; decide +kernel
      have hl : raw18203step2Labels = raw18203step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18203step2 raw18203step2Labels = mixedMoment B raw18203step3 raw18203step3Labels := by
      have ha : raw18203step3 = raw18203step2 := by apply Matrix.ext; unfold raw18203step3 raw18203step2; decide +kernel
      have hl : raw18203step2Labels = labelEmbedding6 ∘ raw18203step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18203step2 raw18203step2Labels raw18203step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

def raw18204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw18204Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18204step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw18204step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18204step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18204step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18204step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18204step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18204 raw18204Labels = mixedMoment B node5349 node5349Labels := by
  calc
    mixedMoment B raw18204 raw18204Labels = mixedMoment B raw18204step0 raw18204step0Labels := by
      have ha : raw18204step0 = (fun i j => raw18204 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18204step0 raw18204; decide +kernel
      have hl : raw18204step0Labels = raw18204Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18204 raw18204Labels permutation686 permutation3
    mixedMoment B raw18204step0 raw18204step0Labels = mixedMoment B raw18204step1 raw18204step1Labels := by
      have ha : raw18204step1 = -raw18204step0 := by apply Matrix.ext; change ∀ i j, raw18204step1 i j = -(raw18204step0 i j); unfold raw18204step1 raw18204step0; decide +kernel
      have hl : raw18204step1Labels = raw18204step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18204step1 raw18204step1Labels = mixedMoment B raw18204step2 raw18204step2Labels := by
      have ha : raw18204step2 = raw18204step1 := by apply Matrix.ext; unfold raw18204step2 raw18204step1; decide +kernel
      have hl : raw18204step1Labels = labelEmbedding6 ∘ raw18204step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18204step1 raw18204step1Labels raw18204step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5349 node5349Labels := by rfl

def raw18205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw18205Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw18205step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18205step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw18205step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18205step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw18205step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18205step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw18205step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18205 raw18205Labels = mixedMoment B node5364 node5364Labels := by
  calc
    mixedMoment B raw18205 raw18205Labels = mixedMoment B raw18205step0 raw18205step0Labels := by
      have hz : ∀ j, raw18205 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18205step0 = (fun i j => raw18205 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18205step0 raw18205; decide +kernel
      have hl : raw18205step0Labels = raw18205Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18205 raw18205Labels permutation346 hz
    mixedMoment B raw18205step0 raw18205step0Labels = mixedMoment B raw18205step1 raw18205step1Labels := by
      have ha : raw18205step1 = (fun i j => raw18205step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18205step1 raw18205step0; decide +kernel
      have hl : raw18205step1Labels = raw18205step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18205step0 raw18205step0Labels permutation149 permutation3
    mixedMoment B raw18205step1 raw18205step1Labels = mixedMoment B raw18205step2 raw18205step2Labels := by
      have ha : raw18205step2 = -raw18205step1 := by apply Matrix.ext; change ∀ i j, raw18205step2 i j = -(raw18205step1 i j); unfold raw18205step2 raw18205step1; decide +kernel
      have hl : raw18205step2Labels = raw18205step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18205step2 raw18205step2Labels = mixedMoment B raw18205step3 raw18205step3Labels := by
      have ha : raw18205step3 = raw18205step2 := by apply Matrix.ext; unfold raw18205step3 raw18205step2; decide +kernel
      have hl : raw18205step2Labels = labelEmbedding6 ∘ raw18205step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18205step2 raw18205step2Labels raw18205step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5364 node5364Labels := by rfl

def raw18206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw18206Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18206step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw18206step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18206step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw18206step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18206step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18206step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18206step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw18206step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18206 raw18206Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw18206 raw18206Labels = mixedMoment B raw18206step0 raw18206step0Labels := by
      have hz : ∀ j, raw18206 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18206step0 = (fun i j => raw18206 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18206step0 raw18206; decide +kernel
      have hl : raw18206step0Labels = raw18206Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18206 raw18206Labels permutation346 hz
    mixedMoment B raw18206step0 raw18206step0Labels = mixedMoment B raw18206step1 raw18206step1Labels := by
      have ha : raw18206step1 = (fun i j => raw18206step0 (permutation39 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18206step1 raw18206step0; decide +kernel
      have hl : raw18206step1Labels = raw18206step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18206step0 raw18206step0Labels permutation39 permutation5
    mixedMoment B raw18206step1 raw18206step1Labels = mixedMoment B raw18206step2 raw18206step2Labels := by
      have ha : raw18206step2 = -raw18206step1 := by apply Matrix.ext; change ∀ i j, raw18206step2 i j = -(raw18206step1 i j); unfold raw18206step2 raw18206step1; decide +kernel
      have hl : raw18206step2Labels = raw18206step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18206step2 raw18206step2Labels = mixedMoment B raw18206step3 raw18206step3Labels := by
      have ha : raw18206step3 = raw18206step2 := by apply Matrix.ext; unfold raw18206step3 raw18206step2; decide +kernel
      have hl : raw18206step2Labels = labelEmbedding8 ∘ raw18206step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18206step2 raw18206step2Labels raw18206step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw18207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw18207Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18207step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw18207step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18207step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-3, 0, 3]]
def raw18207step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18207step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw18207step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18207step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw18207step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18207 raw18207Labels = mixedMoment B node4800 node4800Labels := by
  calc
    mixedMoment B raw18207 raw18207Labels = mixedMoment B raw18207step0 raw18207step0Labels := by
      have hz : ∀ j, raw18207 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18207step0 = (fun i j => raw18207 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18207step0 raw18207; decide +kernel
      have hl : raw18207step0Labels = raw18207Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18207 raw18207Labels permutation346 hz
    mixedMoment B raw18207step0 raw18207step0Labels = mixedMoment B raw18207step1 raw18207step1Labels := by
      have ha : raw18207step1 = (fun i j => raw18207step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18207step1 raw18207step0; decide +kernel
      have hl : raw18207step1Labels = raw18207step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18207step0 raw18207step0Labels permutation151 permutation3
    mixedMoment B raw18207step1 raw18207step1Labels = mixedMoment B raw18207step2 raw18207step2Labels := by
      have ha : raw18207step2 = -raw18207step1 := by apply Matrix.ext; change ∀ i j, raw18207step2 i j = -(raw18207step1 i j); unfold raw18207step2 raw18207step1; decide +kernel
      have hl : raw18207step2Labels = raw18207step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18207step2 raw18207step2Labels = mixedMoment B raw18207step3 raw18207step3Labels := by
      have ha : raw18207step3 = raw18207step2 := by apply Matrix.ext; unfold raw18207step3 raw18207step2; decide +kernel
      have hl : raw18207step2Labels = labelEmbedding6 ∘ raw18207step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18207step2 raw18207step2Labels raw18207step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4800 node4800Labels := by rfl

def raw18208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw18208Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw18208step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18208step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw18208step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18208step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18208step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18208step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18208step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18208 raw18208Labels = mixedMoment B node4810 node4810Labels := by
  calc
    mixedMoment B raw18208 raw18208Labels = mixedMoment B raw18208step0 raw18208step0Labels := by
      have hz : ∀ j, raw18208 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18208step0 = (fun i j => raw18208 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18208step0 raw18208; decide +kernel
      have hl : raw18208step0Labels = raw18208Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18208 raw18208Labels permutation346 hz
    mixedMoment B raw18208step0 raw18208step0Labels = mixedMoment B raw18208step1 raw18208step1Labels := by
      have ha : raw18208step1 = (fun i j => raw18208step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18208step1 raw18208step0; decide +kernel
      have hl : raw18208step1Labels = raw18208step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18208step0 raw18208step0Labels permutation151 permutation3
    mixedMoment B raw18208step1 raw18208step1Labels = mixedMoment B raw18208step2 raw18208step2Labels := by
      have ha : raw18208step2 = -raw18208step1 := by apply Matrix.ext; change ∀ i j, raw18208step2 i j = -(raw18208step1 i j); unfold raw18208step2 raw18208step1; decide +kernel
      have hl : raw18208step2Labels = raw18208step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18208step2 raw18208step2Labels = mixedMoment B raw18208step3 raw18208step3Labels := by
      have ha : raw18208step3 = raw18208step2 := by apply Matrix.ext; unfold raw18208step3 raw18208step2; decide +kernel
      have hl : raw18208step2Labels = labelEmbedding6 ∘ raw18208step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18208step2 raw18208step2Labels raw18208step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4810 node4810Labels := by rfl

def raw18209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw18209Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18209step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw18209step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18209step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18209step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18209step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw18209step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18209 raw18209Labels = mixedMoment B node4798 node4798Labels := by
  calc
    mixedMoment B raw18209 raw18209Labels = mixedMoment B raw18209step0 raw18209step0Labels := by
      have ha : raw18209step0 = (fun i j => raw18209 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18209step0 raw18209; decide +kernel
      have hl : raw18209step0Labels = raw18209Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18209 raw18209Labels permutation686 permutation3
    mixedMoment B raw18209step0 raw18209step0Labels = mixedMoment B raw18209step1 raw18209step1Labels := by
      have ha : raw18209step1 = -raw18209step0 := by apply Matrix.ext; change ∀ i j, raw18209step1 i j = -(raw18209step0 i j); unfold raw18209step1 raw18209step0; decide +kernel
      have hl : raw18209step1Labels = raw18209step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18209step1 raw18209step1Labels = mixedMoment B raw18209step2 raw18209step2Labels := by
      have ha : raw18209step2 = raw18209step1 := by apply Matrix.ext; unfold raw18209step2 raw18209step1; decide +kernel
      have hl : raw18209step1Labels = labelEmbedding6 ∘ raw18209step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18209step1 raw18209step1Labels raw18209step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4798 node4798Labels := by rfl

def raw18210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw18210Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw18210step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18210step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 2, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw18210step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18210step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw18210step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18210step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw18210step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18210 raw18210Labels = mixedMoment B node4828 node4828Labels := by
  calc
    mixedMoment B raw18210 raw18210Labels = mixedMoment B raw18210step0 raw18210step0Labels := by
      have hz : ∀ j, raw18210 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18210step0 = (fun i j => raw18210 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18210step0 raw18210; decide +kernel
      have hl : raw18210step0Labels = raw18210Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18210 raw18210Labels permutation346 hz
    mixedMoment B raw18210step0 raw18210step0Labels = mixedMoment B raw18210step1 raw18210step1Labels := by
      have ha : raw18210step1 = (fun i j => raw18210step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18210step1 raw18210step0; decide +kernel
      have hl : raw18210step1Labels = raw18210step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18210step0 raw18210step0Labels permutation149 permutation3
    mixedMoment B raw18210step1 raw18210step1Labels = mixedMoment B raw18210step2 raw18210step2Labels := by
      have ha : raw18210step2 = -raw18210step1 := by apply Matrix.ext; change ∀ i j, raw18210step2 i j = -(raw18210step1 i j); unfold raw18210step2 raw18210step1; decide +kernel
      have hl : raw18210step2Labels = raw18210step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18210step2 raw18210step2Labels = mixedMoment B raw18210step3 raw18210step3Labels := by
      have ha : raw18210step3 = raw18210step2 := by apply Matrix.ext; unfold raw18210step3 raw18210step2; decide +kernel
      have hl : raw18210step2Labels = labelEmbedding6 ∘ raw18210step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18210step2 raw18210step2Labels raw18210step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4828 node4828Labels := by rfl

def raw18211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw18211Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18211step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw18211step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18211step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18211step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18211step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18211step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18211 raw18211Labels = mixedMoment B node4865 node4865Labels := by
  calc
    mixedMoment B raw18211 raw18211Labels = mixedMoment B raw18211step0 raw18211step0Labels := by
      have hz : ∀ j, raw18211 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18211step0 = (fun i j => raw18211 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18211step0 raw18211; decide +kernel
      have hl : raw18211step0Labels = raw18211Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18211 raw18211Labels permutation346 hz
    mixedMoment B raw18211step0 raw18211step0Labels = mixedMoment B raw18211step1 raw18211step1Labels := by
      have ha : raw18211step1 = (fun i j => raw18211step0 (permutation137 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18211step1 raw18211step0; decide +kernel
      have hl : raw18211step1Labels = raw18211step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18211step0 raw18211step0Labels permutation137 permutation5
    mixedMoment B raw18211step1 raw18211step1Labels = mixedMoment B raw18211step2 raw18211step2Labels := by
      have ha : raw18211step2 = raw18211step1 := by apply Matrix.ext; unfold raw18211step2 raw18211step1; decide +kernel
      have hl : raw18211step1Labels = labelEmbedding8 ∘ raw18211step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18211step1 raw18211step1Labels raw18211step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4865 node4865Labels := by rfl

def raw18212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18212Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18212step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18212step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18212step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18212step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18212 raw18212Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw18212 raw18212Labels = mixedMoment B raw18212step0 raw18212step0Labels := by
      have ha : raw18212step0 = (fun i j => raw18212 (permutation681 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18212step0 raw18212; decide +kernel
      have hl : raw18212step0Labels = raw18212Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18212 raw18212Labels permutation681 permutation2
    mixedMoment B raw18212step0 raw18212step0Labels = mixedMoment B raw18212step1 raw18212step1Labels := by
      have ha : raw18212step1 = -raw18212step0 := by apply Matrix.ext; change ∀ i j, raw18212step1 i j = -(raw18212step0 i j); unfold raw18212step1 raw18212step0; decide +kernel
      have hl : raw18212step1Labels = raw18212step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw18213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18213Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18213step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, -1, 2]]
def raw18213step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18213step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18213step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18213 raw18213Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw18213 raw18213Labels = mixedMoment B raw18213step0 raw18213step0Labels := by
      have ha : raw18213step0 = (fun i j => raw18213 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18213step0 raw18213; decide +kernel
      have hl : raw18213step0Labels = raw18213Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18213 raw18213Labels permutation688 permutation2
    mixedMoment B raw18213step0 raw18213step0Labels = mixedMoment B raw18213step1 raw18213step1Labels := by
      have ha : raw18213step1 = -raw18213step0 := by apply Matrix.ext; change ∀ i j, raw18213step1 i j = -(raw18213step0 i j); unfold raw18213step1 raw18213step0; decide +kernel
      have hl : raw18213step1Labels = raw18213step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5430 node5430Labels := by rfl

def raw18214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18214Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18214step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18214step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18214step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18214step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18214 raw18214Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw18214 raw18214Labels = mixedMoment B raw18214step0 raw18214step0Labels := by
      have ha : raw18214step0 = (fun i j => raw18214 (permutation644 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18214step0 raw18214; decide +kernel
      have hl : raw18214step0Labels = raw18214Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18214 raw18214Labels permutation644 permutation7
    mixedMoment B raw18214step0 raw18214step0Labels = mixedMoment B raw18214step1 raw18214step1Labels := by
      have ha : raw18214step1 = raw18214step0 := by apply Matrix.ext; unfold raw18214step1 raw18214step0; decide +kernel
      have hl : raw18214step0Labels = labelEmbedding10 ∘ raw18214step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18214step0 raw18214step0Labels raw18214step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw18215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw18215Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18215step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw18215step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18215step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18215step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18215step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18215step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18215 raw18215Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw18215 raw18215Labels = mixedMoment B raw18215step0 raw18215step0Labels := by
      have hz : ∀ j, raw18215 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18215step0 = (fun i j => raw18215 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18215step0 raw18215; decide +kernel
      have hl : raw18215step0Labels = raw18215Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18215 raw18215Labels permutation520 hz
    mixedMoment B raw18215step0 raw18215step0Labels = mixedMoment B raw18215step1 raw18215step1Labels := by
      have ha : raw18215step1 = (fun i j => raw18215step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18215step1 raw18215step0; decide +kernel
      have hl : raw18215step1Labels = raw18215step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18215step0 raw18215step0Labels permutation143 permutation7
    mixedMoment B raw18215step1 raw18215step1Labels = mixedMoment B raw18215step2 raw18215step2Labels := by
      have ha : raw18215step2 = raw18215step1 := by apply Matrix.ext; unfold raw18215step2 raw18215step1; decide +kernel
      have hl : raw18215step1Labels = labelEmbedding10 ∘ raw18215step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18215step1 raw18215step1Labels raw18215step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw18216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18216Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18216step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18216step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18216step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18216step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18216 raw18216Labels = mixedMoment B node5477 node5477Labels := by
  calc
    mixedMoment B raw18216 raw18216Labels = mixedMoment B raw18216step0 raw18216step0Labels := by
      have ha : raw18216step0 = (fun i j => raw18216 (permutation634 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18216step0 raw18216; decide +kernel
      have hl : raw18216step0Labels = raw18216Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18216 raw18216Labels permutation634 permutation6
    mixedMoment B raw18216step0 raw18216step0Labels = mixedMoment B raw18216step1 raw18216step1Labels := by
      have ha : raw18216step1 = raw18216step0 := by apply Matrix.ext; unfold raw18216step1 raw18216step0; decide +kernel
      have hl : raw18216step0Labels = labelEmbedding9 ∘ raw18216step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18216step0 raw18216step0Labels raw18216step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5477 node5477Labels := by rfl

def raw18217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18217Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18217step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18217step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw18217step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18217step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18217step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18217 raw18217Labels = mixedMoment B node5432 node5432Labels := by
  calc
    mixedMoment B raw18217 raw18217Labels = mixedMoment B raw18217step0 raw18217step0Labels := by
      have hz : ∀ j, raw18217 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw18217step0 = (fun i j => raw18217 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw18217step0 raw18217; decide +kernel
      have hl : raw18217step0Labels = raw18217Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18217 raw18217Labels permutation265 hz
    mixedMoment B raw18217step0 raw18217step0Labels = mixedMoment B raw18217step1 raw18217step1Labels := by
      have ha : raw18217step1 = (fun i j => raw18217step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18217step1 raw18217step0; decide +kernel
      have hl : raw18217step1Labels = raw18217step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18217step0 raw18217step0Labels permutation151 permutation2
    mixedMoment B raw18217step1 raw18217step1Labels = mixedMoment B raw18217step2 raw18217step2Labels := by
      have ha : raw18217step2 = -raw18217step1 := by apply Matrix.ext; change ∀ i j, raw18217step2 i j = -(raw18217step1 i j); unfold raw18217step2 raw18217step1; decide +kernel
      have hl : raw18217step2Labels = raw18217step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5432 node5432Labels := by rfl

def raw18218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18218Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18218step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18218step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18218step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18218step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18218 raw18218Labels = mixedMoment B node5409 node5409Labels := by
  calc
    mixedMoment B raw18218 raw18218Labels = mixedMoment B raw18218step0 raw18218step0Labels := by
      have hz : ∀ j, raw18218 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw18218step0 = (fun i j => raw18218 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw18218step0 raw18218; decide +kernel
      have hl : raw18218step0Labels = raw18218Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18218 raw18218Labels permutation265 hz
    mixedMoment B raw18218step0 raw18218step0Labels = mixedMoment B raw18218step1 raw18218step1Labels := by
      have ha : raw18218step1 = (fun i j => raw18218step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18218step1 raw18218step0; decide +kernel
      have hl : raw18218step1Labels = raw18218step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18218step0 raw18218step0Labels permutation38 permutation2
    _ = mixedMoment B node5409 node5409Labels := by rfl

def raw18219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw18219Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18219step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw18219step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18219step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw18219step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18219step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18219step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18219step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18219step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18219 raw18219Labels = mixedMoment B node5441 node5441Labels := by
  calc
    mixedMoment B raw18219 raw18219Labels = mixedMoment B raw18219step0 raw18219step0Labels := by
      have hz : ∀ j, raw18219 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18219step0 = (fun i j => raw18219 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18219step0 raw18219; decide +kernel
      have hl : raw18219step0Labels = raw18219Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18219 raw18219Labels permutation520 hz
    mixedMoment B raw18219step0 raw18219step0Labels = mixedMoment B raw18219step1 raw18219step1Labels := by
      have hz : ∀ j, raw18219step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw18219step1 = (fun i j => raw18219step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw18219step1 raw18219step0; decide +kernel
      have hl : raw18219step1Labels = raw18219step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18219step0 raw18219step0Labels permutation56 hz
    mixedMoment B raw18219step1 raw18219step1Labels = mixedMoment B raw18219step2 raw18219step2Labels := by
      have ha : raw18219step2 = (fun i j => raw18219step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18219step2 raw18219step1; decide +kernel
      have hl : raw18219step2Labels = raw18219step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18219step1 raw18219step1Labels permutation29 permutation7
    mixedMoment B raw18219step2 raw18219step2Labels = mixedMoment B raw18219step3 raw18219step3Labels := by
      have ha : raw18219step3 = raw18219step2 := by apply Matrix.ext; unfold raw18219step3 raw18219step2; decide +kernel
      have hl : raw18219step2Labels = labelEmbedding10 ∘ raw18219step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18219step2 raw18219step2Labels raw18219step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5441 node5441Labels := by rfl

def raw18220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18220Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18220step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw18220step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18220 raw18220Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw18220 raw18220Labels = mixedMoment B raw18220step0 raw18220step0Labels := by
      have ha : raw18220step0 = (fun i j => raw18220 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18220step0 raw18220; decide +kernel
      have hl : raw18220step0Labels = raw18220Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18220 raw18220Labels permutation160 permutation2
    _ = mixedMoment B node5134 node5134Labels := by rfl

def raw18221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18221Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18221step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw18221step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18221 raw18221Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw18221 raw18221Labels = mixedMoment B raw18221step0 raw18221step0Labels := by
      have ha : raw18221step0 = (fun i j => raw18221 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18221step0 raw18221; decide +kernel
      have hl : raw18221step0Labels = raw18221Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18221 raw18221Labels permutation160 permutation2
    _ = mixedMoment B node5378 node5378Labels := by rfl

def raw18222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18222Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18222step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw18222step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18222 raw18222Labels = mixedMoment B node5394 node5394Labels := by
  calc
    mixedMoment B raw18222 raw18222Labels = mixedMoment B raw18222step0 raw18222step0Labels := by
      have ha : raw18222step0 = (fun i j => raw18222 (permutation202 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18222step0 raw18222; decide +kernel
      have hl : raw18222step0Labels = raw18222Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18222 raw18222Labels permutation202 permutation2
    _ = mixedMoment B node5394 node5394Labels := by rfl

def raw18223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw18223Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw18223step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18223step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw18223step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18223step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18223step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18223 raw18223Labels = mixedMoment B node5409 node5409Labels := by
  calc
    mixedMoment B raw18223 raw18223Labels = mixedMoment B raw18223step0 raw18223step0Labels := by
      have hz : ∀ j, raw18223 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18223step0 = (fun i j => raw18223 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18223step0 raw18223; decide +kernel
      have hl : raw18223step0Labels = raw18223Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18223 raw18223Labels permutation520 hz
    mixedMoment B raw18223step0 raw18223step0Labels = mixedMoment B raw18223step1 raw18223step1Labels := by
      have ha : raw18223step1 = (fun i j => raw18223step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18223step1 raw18223step0; decide +kernel
      have hl : raw18223step1Labels = raw18223step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18223step0 raw18223step0Labels permutation145 permutation2
    mixedMoment B raw18223step1 raw18223step1Labels = mixedMoment B raw18223step2 raw18223step2Labels := by
      have ha : raw18223step2 = -raw18223step1 := by apply Matrix.ext; change ∀ i j, raw18223step2 i j = -(raw18223step1 i j); unfold raw18223step2 raw18223step1; decide +kernel
      have hl : raw18223step2Labels = raw18223step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5409 node5409Labels := by rfl

def raw18224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18224Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18224step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18224step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18224step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18224step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18224step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18224step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18224 raw18224Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw18224 raw18224Labels = mixedMoment B raw18224step0 raw18224step0Labels := by
      have ha : raw18224step0 = (fun i j => raw18224 (permutation202 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18224step0 raw18224; decide +kernel
      have hl : raw18224step0Labels = raw18224Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18224 raw18224Labels permutation202 permutation7
    mixedMoment B raw18224step0 raw18224step0Labels = mixedMoment B raw18224step1 raw18224step1Labels := by
      have ha : raw18224step1 = -raw18224step0 := by apply Matrix.ext; change ∀ i j, raw18224step1 i j = -(raw18224step0 i j); unfold raw18224step1 raw18224step0; decide +kernel
      have hl : raw18224step1Labels = raw18224step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18224step1 raw18224step1Labels = mixedMoment B raw18224step2 raw18224step2Labels := by
      have ha : raw18224step2 = raw18224step1 := by apply Matrix.ext; unfold raw18224step2 raw18224step1; decide +kernel
      have hl : raw18224step1Labels = labelEmbedding10 ∘ raw18224step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18224step1 raw18224step1Labels raw18224step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw18225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18225Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18225step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18225step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18225step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18225step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18225 raw18225Labels = mixedMoment B node5381 node5381Labels := by
  calc
    mixedMoment B raw18225 raw18225Labels = mixedMoment B raw18225step0 raw18225step0Labels := by
      have ha : raw18225step0 = (fun i j => raw18225 (permutation267 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18225step0 raw18225; decide +kernel
      have hl : raw18225step0Labels = raw18225Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18225 raw18225Labels permutation267 permutation3
    mixedMoment B raw18225step0 raw18225step0Labels = mixedMoment B raw18225step1 raw18225step1Labels := by
      have ha : raw18225step1 = raw18225step0 := by apply Matrix.ext; unfold raw18225step1 raw18225step0; decide +kernel
      have hl : raw18225step0Labels = labelEmbedding6 ∘ raw18225step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18225step0 raw18225step0Labels raw18225step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5381 node5381Labels := by rfl

def raw18226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18226Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18226 raw18226Labels = mixedMoment B node5420 node5420Labels := by
  calc
    _ = mixedMoment B node5420 node5420Labels := by rfl

def raw18227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw18227Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18227step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18227 raw18227Labels = mixedMoment B node5432 node5432Labels := by
  calc
    mixedMoment B raw18227 raw18227Labels = mixedMoment B raw18227step0 raw18227step0Labels := by
      have hz : ∀ j, raw18227 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18227step0 = (fun i j => raw18227 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18227step0 raw18227; decide +kernel
      have hl : raw18227step0Labels = raw18227Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18227 raw18227Labels permutation520 hz
    _ = mixedMoment B node5432 node5432Labels := by rfl

def raw18228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18228Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18228step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18228step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18228 raw18228Labels = mixedMoment B node5129 node5129Labels := by
  calc
    mixedMoment B raw18228 raw18228Labels = mixedMoment B raw18228step0 raw18228step0Labels := by
      have ha : raw18228step0 = (fun i j => raw18228 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18228step0 raw18228; decide +kernel
      have hl : raw18228step0Labels = raw18228Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18228 raw18228Labels permutation158 permutation2
    _ = mixedMoment B node5129 node5129Labels := by rfl

def raw18229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18229Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18229step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18229step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18229 raw18229Labels = mixedMoment B node5376 node5376Labels := by
  calc
    mixedMoment B raw18229 raw18229Labels = mixedMoment B raw18229step0 raw18229step0Labels := by
      have ha : raw18229step0 = (fun i j => raw18229 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18229step0 raw18229; decide +kernel
      have hl : raw18229step0Labels = raw18229Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18229 raw18229Labels permutation158 permutation2
    _ = mixedMoment B node5376 node5376Labels := by rfl

def raw18230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18230Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18230step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw18230step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18230step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18230step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18230step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18230step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18230 raw18230Labels = mixedMoment B node5381 node5381Labels := by
  calc
    mixedMoment B raw18230 raw18230Labels = mixedMoment B raw18230step0 raw18230step0Labels := by
      have ha : raw18230step0 = (fun i j => raw18230 (permutation587 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18230step0 raw18230; decide +kernel
      have hl : raw18230step0Labels = raw18230Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18230 raw18230Labels permutation587 permutation3
    mixedMoment B raw18230step0 raw18230step0Labels = mixedMoment B raw18230step1 raw18230step1Labels := by
      have ha : raw18230step1 = -raw18230step0 := by apply Matrix.ext; change ∀ i j, raw18230step1 i j = -(raw18230step0 i j); unfold raw18230step1 raw18230step0; decide +kernel
      have hl : raw18230step1Labels = raw18230step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18230step1 raw18230step1Labels = mixedMoment B raw18230step2 raw18230step2Labels := by
      have ha : raw18230step2 = raw18230step1 := by apply Matrix.ext; unfold raw18230step2 raw18230step1; decide +kernel
      have hl : raw18230step1Labels = labelEmbedding6 ∘ raw18230step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18230step1 raw18230step1Labels raw18230step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5381 node5381Labels := by rfl

def raw18231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18231Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18231step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw18231step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18231step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw18231step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18231 raw18231Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw18231 raw18231Labels = mixedMoment B raw18231step0 raw18231step0Labels := by
      have ha : raw18231step0 = (fun i j => raw18231 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18231step0 raw18231; decide +kernel
      have hl : raw18231step0Labels = raw18231Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18231 raw18231Labels permutation680 permutation2
    mixedMoment B raw18231step0 raw18231step0Labels = mixedMoment B raw18231step1 raw18231step1Labels := by
      have ha : raw18231step1 = -raw18231step0 := by apply Matrix.ext; change ∀ i j, raw18231step1 i j = -(raw18231step0 i j); unfold raw18231step1 raw18231step0; decide +kernel
      have hl : raw18231step1Labels = raw18231step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5378 node5378Labels := by rfl

def raw18232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18232Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18232step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw18232step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18232 raw18232Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw18232 raw18232Labels = mixedMoment B raw18232step0 raw18232step0Labels := by
      have ha : raw18232step0 = (fun i j => raw18232 (permutation159 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18232step0 raw18232; decide +kernel
      have hl : raw18232step0Labels = raw18232Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18232 raw18232Labels permutation159 permutation2
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw18233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18233Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18233step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw18233step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18233 raw18233Labels = mixedMoment B node5127 node5127Labels := by
  calc
    mixedMoment B raw18233 raw18233Labels = mixedMoment B raw18233step0 raw18233step0Labels := by
      have ha : raw18233step0 = (fun i j => raw18233 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18233step0 raw18233; decide +kernel
      have hl : raw18233step0Labels = raw18233Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18233 raw18233Labels permutation158 permutation2
    _ = mixedMoment B node5127 node5127Labels := by rfl

def raw18234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18234Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18234step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw18234step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18234step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw18234step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18234 raw18234Labels = mixedMoment B node5129 node5129Labels := by
  calc
    mixedMoment B raw18234 raw18234Labels = mixedMoment B raw18234step0 raw18234step0Labels := by
      have ha : raw18234step0 = (fun i j => raw18234 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18234step0 raw18234; decide +kernel
      have hl : raw18234step0Labels = raw18234Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18234 raw18234Labels permutation682 permutation2
    mixedMoment B raw18234step0 raw18234step0Labels = mixedMoment B raw18234step1 raw18234step1Labels := by
      have ha : raw18234step1 = -raw18234step0 := by apply Matrix.ext; change ∀ i j, raw18234step1 i j = -(raw18234step0 i j); unfold raw18234step1 raw18234step0; decide +kernel
      have hl : raw18234step1Labels = raw18234step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5129 node5129Labels := by rfl

def raw18235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18235Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18235step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-2, 0, 2]]
def raw18235step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18235step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18235step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18235 raw18235Labels = mixedMoment B node5144 node5144Labels := by
  calc
    mixedMoment B raw18235 raw18235Labels = mixedMoment B raw18235step0 raw18235step0Labels := by
      have ha : raw18235step0 = (fun i j => raw18235 (permutation688 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18235step0 raw18235; decide +kernel
      have hl : raw18235step0Labels = raw18235Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18235 raw18235Labels permutation688 permutation2
    mixedMoment B raw18235step0 raw18235step0Labels = mixedMoment B raw18235step1 raw18235step1Labels := by
      have ha : raw18235step1 = -raw18235step0 := by apply Matrix.ext; change ∀ i j, raw18235step1 i j = -(raw18235step0 i j); unfold raw18235step1 raw18235step0; decide +kernel
      have hl : raw18235step1Labels = raw18235step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5144 node5144Labels := by rfl

def raw18236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18236Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18236step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw18236step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18236step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw18236step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18236 raw18236Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw18236 raw18236Labels = mixedMoment B raw18236step0 raw18236step0Labels := by
      have ha : raw18236step0 = (fun i j => raw18236 (permutation680 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18236step0 raw18236; decide +kernel
      have hl : raw18236step0Labels = raw18236Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18236 raw18236Labels permutation680 permutation2
    mixedMoment B raw18236step0 raw18236step0Labels = mixedMoment B raw18236step1 raw18236step1Labels := by
      have ha : raw18236step1 = -raw18236step0 := by apply Matrix.ext; change ∀ i j, raw18236step1 i j = -(raw18236step0 i j); unfold raw18236step1 raw18236step0; decide +kernel
      have hl : raw18236step1Labels = raw18236step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5134 node5134Labels := by rfl

def raw18237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![3, -1, -2]]
def raw18237Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![3, -1, -2]]
def raw18237step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18237step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw18237step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18237step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18237step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18237 raw18237Labels = mixedMoment B node5258 node5258Labels := by
  calc
    mixedMoment B raw18237 raw18237Labels = mixedMoment B raw18237step0 raw18237step0Labels := by
      have hz : ∀ j, raw18237 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18237step0 = (fun i j => raw18237 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18237step0 raw18237; decide +kernel
      have hl : raw18237step0Labels = raw18237Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18237 raw18237Labels permutation520 hz
    mixedMoment B raw18237step0 raw18237step0Labels = mixedMoment B raw18237step1 raw18237step1Labels := by
      have ha : raw18237step1 = (fun i j => raw18237step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18237step1 raw18237step0; decide +kernel
      have hl : raw18237step1Labels = raw18237step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18237step0 raw18237step0Labels permutation145 permutation2
    mixedMoment B raw18237step1 raw18237step1Labels = mixedMoment B raw18237step2 raw18237step2Labels := by
      have ha : raw18237step2 = -raw18237step1 := by apply Matrix.ext; change ∀ i j, raw18237step2 i j = -(raw18237step1 i j); unfold raw18237step2 raw18237step1; decide +kernel
      have hl : raw18237step2Labels = raw18237step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5258 node5258Labels := by rfl

def raw18238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18238Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18238step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw18238step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18238step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw18238step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18238 raw18238Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw18238 raw18238Labels = mixedMoment B raw18238step0 raw18238step0Labels := by
      have ha : raw18238step0 = (fun i j => raw18238 (permutation644 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18238step0 raw18238; decide +kernel
      have hl : raw18238step0Labels = raw18238Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18238 raw18238Labels permutation644 permutation7
    mixedMoment B raw18238step0 raw18238step0Labels = mixedMoment B raw18238step1 raw18238step1Labels := by
      have ha : raw18238step1 = raw18238step0 := by apply Matrix.ext; unfold raw18238step1 raw18238step0; decide +kernel
      have hl : raw18238step0Labels = labelEmbedding1 ∘ raw18238step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18238step0 raw18238step0Labels raw18238step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3840 node3840Labels := by rfl

def raw18239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18239Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18239step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18239step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18239step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18239step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18239 raw18239Labels = mixedMoment B node3871 node3871Labels := by
  calc
    mixedMoment B raw18239 raw18239Labels = mixedMoment B raw18239step0 raw18239step0Labels := by
      have ha : raw18239step0 = (fun i j => raw18239 (permutation644 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18239step0 raw18239; decide +kernel
      have hl : raw18239step0Labels = raw18239Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18239 raw18239Labels permutation644 permutation7
    mixedMoment B raw18239step0 raw18239step0Labels = mixedMoment B raw18239step1 raw18239step1Labels := by
      have ha : raw18239step1 = raw18239step0 := by apply Matrix.ext; unfold raw18239step1 raw18239step0; decide +kernel
      have hl : raw18239step0Labels = labelEmbedding1 ∘ raw18239step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18239step0 raw18239step0Labels raw18239step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3871 node3871Labels := by rfl

def raw18240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18240Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18240step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18240step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18240step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18240step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18240 raw18240Labels = mixedMoment B node3838 node3838Labels := by
  calc
    mixedMoment B raw18240 raw18240Labels = mixedMoment B raw18240step0 raw18240step0Labels := by
      have ha : raw18240step0 = (fun i j => raw18240 (permutation644 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18240step0 raw18240; decide +kernel
      have hl : raw18240step0Labels = raw18240Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18240 raw18240Labels permutation644 permutation7
    mixedMoment B raw18240step0 raw18240step0Labels = mixedMoment B raw18240step1 raw18240step1Labels := by
      have ha : raw18240step1 = raw18240step0 := by apply Matrix.ext; unfold raw18240step1 raw18240step0; decide +kernel
      have hl : raw18240step0Labels = labelEmbedding1 ∘ raw18240step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18240step0 raw18240step0Labels raw18240step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3838 node3838Labels := by rfl

def raw18241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw18241Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18241step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw18241step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18241step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18241step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18241step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18241step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18241 raw18241Labels = mixedMoment B node3852 node3852Labels := by
  calc
    mixedMoment B raw18241 raw18241Labels = mixedMoment B raw18241step0 raw18241step0Labels := by
      have hz : ∀ j, raw18241 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18241step0 = (fun i j => raw18241 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18241step0 raw18241; decide +kernel
      have hl : raw18241step0Labels = raw18241Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18241 raw18241Labels permutation520 hz
    mixedMoment B raw18241step0 raw18241step0Labels = mixedMoment B raw18241step1 raw18241step1Labels := by
      have ha : raw18241step1 = (fun i j => raw18241step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18241step1 raw18241step0; decide +kernel
      have hl : raw18241step1Labels = raw18241step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18241step0 raw18241step0Labels permutation143 permutation7
    mixedMoment B raw18241step1 raw18241step1Labels = mixedMoment B raw18241step2 raw18241step2Labels := by
      have ha : raw18241step2 = raw18241step1 := by apply Matrix.ext; unfold raw18241step2 raw18241step1; decide +kernel
      have hl : raw18241step1Labels = labelEmbedding1 ∘ raw18241step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18241step1 raw18241step1Labels raw18241step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3852 node3852Labels := by rfl

def raw18242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18242Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18242step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18242step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18242step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw18242step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18242 raw18242Labels = mixedMoment B node3989 node3989Labels := by
  calc
    mixedMoment B raw18242 raw18242Labels = mixedMoment B raw18242step0 raw18242step0Labels := by
      have ha : raw18242step0 = (fun i j => raw18242 (permutation644 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18242step0 raw18242; decide +kernel
      have hl : raw18242step0Labels = raw18242Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18242 raw18242Labels permutation644 permutation7
    mixedMoment B raw18242step0 raw18242step0Labels = mixedMoment B raw18242step1 raw18242step1Labels := by
      have ha : raw18242step1 = raw18242step0 := by apply Matrix.ext; unfold raw18242step1 raw18242step0; decide +kernel
      have hl : raw18242step0Labels = labelEmbedding1 ∘ raw18242step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18242step0 raw18242step0Labels raw18242step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3989 node3989Labels := by rfl

def raw18243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18243Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18243step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18243step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw18243step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18243step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18243step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18243step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18243step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18243 raw18243Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw18243 raw18243Labels = mixedMoment B raw18243step0 raw18243step0Labels := by
      have hz : ∀ j, raw18243 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw18243step0 = (fun i j => raw18243 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw18243step0 raw18243; decide +kernel
      have hl : raw18243step0Labels = raw18243Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18243 raw18243Labels permutation265 hz
    mixedMoment B raw18243step0 raw18243step0Labels = mixedMoment B raw18243step1 raw18243step1Labels := by
      have ha : raw18243step1 = (fun i j => raw18243step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18243step1 raw18243step0; decide +kernel
      have hl : raw18243step1Labels = raw18243step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18243step0 raw18243step0Labels permutation40 permutation7
    mixedMoment B raw18243step1 raw18243step1Labels = mixedMoment B raw18243step2 raw18243step2Labels := by
      have ha : raw18243step2 = -raw18243step1 := by apply Matrix.ext; change ∀ i j, raw18243step2 i j = -(raw18243step1 i j); unfold raw18243step2 raw18243step1; decide +kernel
      have hl : raw18243step2Labels = raw18243step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18243step2 raw18243step2Labels = mixedMoment B raw18243step3 raw18243step3Labels := by
      have ha : raw18243step3 = raw18243step2 := by apply Matrix.ext; unfold raw18243step3 raw18243step2; decide +kernel
      have hl : raw18243step2Labels = labelEmbedding1 ∘ raw18243step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18243step2 raw18243step2Labels raw18243step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3850 node3850Labels := by rfl

def raw18244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18244Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18244step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18244step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw18244step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18244step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18244step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18244step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18244step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18244 raw18244Labels = mixedMoment B node3807 node3807Labels := by
  calc
    mixedMoment B raw18244 raw18244Labels = mixedMoment B raw18244step0 raw18244step0Labels := by
      have hz : ∀ j, raw18244 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw18244step0 = (fun i j => raw18244 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw18244step0 raw18244; decide +kernel
      have hl : raw18244step0Labels = raw18244Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18244 raw18244Labels permutation265 hz
    mixedMoment B raw18244step0 raw18244step0Labels = mixedMoment B raw18244step1 raw18244step1Labels := by
      have ha : raw18244step1 = (fun i j => raw18244step0 (permutation40 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18244step1 raw18244step0; decide +kernel
      have hl : raw18244step1Labels = raw18244step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18244step0 raw18244step0Labels permutation40 permutation7
    mixedMoment B raw18244step1 raw18244step1Labels = mixedMoment B raw18244step2 raw18244step2Labels := by
      have ha : raw18244step2 = -raw18244step1 := by apply Matrix.ext; change ∀ i j, raw18244step2 i j = -(raw18244step1 i j); unfold raw18244step2 raw18244step1; decide +kernel
      have hl : raw18244step2Labels = raw18244step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18244step2 raw18244step2Labels = mixedMoment B raw18244step3 raw18244step3Labels := by
      have ha : raw18244step3 = raw18244step2 := by apply Matrix.ext; unfold raw18244step3 raw18244step2; decide +kernel
      have hl : raw18244step2Labels = labelEmbedding1 ∘ raw18244step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18244step2 raw18244step2Labels raw18244step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3807 node3807Labels := by rfl

def raw18245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw18245Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw18245step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18245step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw18245step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18245step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18245step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18245step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18245step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18245 raw18245Labels = mixedMoment B node3860 node3860Labels := by
  calc
    mixedMoment B raw18245 raw18245Labels = mixedMoment B raw18245step0 raw18245step0Labels := by
      have hz : ∀ j, raw18245 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18245step0 = (fun i j => raw18245 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18245step0 raw18245; decide +kernel
      have hl : raw18245step0Labels = raw18245Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18245 raw18245Labels permutation520 hz
    mixedMoment B raw18245step0 raw18245step0Labels = mixedMoment B raw18245step1 raw18245step1Labels := by
      have hz : ∀ j, raw18245step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw18245step1 = (fun i j => raw18245step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw18245step1 raw18245step0; decide +kernel
      have hl : raw18245step1Labels = raw18245step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18245step0 raw18245step0Labels permutation56 hz
    mixedMoment B raw18245step1 raw18245step1Labels = mixedMoment B raw18245step2 raw18245step2Labels := by
      have ha : raw18245step2 = (fun i j => raw18245step1 (permutation29 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18245step2 raw18245step1; decide +kernel
      have hl : raw18245step2Labels = raw18245step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18245step1 raw18245step1Labels permutation29 permutation7
    mixedMoment B raw18245step2 raw18245step2Labels = mixedMoment B raw18245step3 raw18245step3Labels := by
      have ha : raw18245step3 = raw18245step2 := by apply Matrix.ext; unfold raw18245step3 raw18245step2; decide +kernel
      have hl : raw18245step2Labels = labelEmbedding1 ∘ raw18245step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18245step2 raw18245step2Labels raw18245step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3860 node3860Labels := by rfl

def raw18246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18246Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18246step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw18246step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18246step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18246step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18246step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18246step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18246 raw18246Labels = mixedMoment B node3514 node3514Labels := by
  calc
    mixedMoment B raw18246 raw18246Labels = mixedMoment B raw18246step0 raw18246step0Labels := by
      have ha : raw18246step0 = (fun i j => raw18246 (permutation202 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18246step0 raw18246; decide +kernel
      have hl : raw18246step0Labels = raw18246Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18246 raw18246Labels permutation202 permutation7
    mixedMoment B raw18246step0 raw18246step0Labels = mixedMoment B raw18246step1 raw18246step1Labels := by
      have ha : raw18246step1 = -raw18246step0 := by apply Matrix.ext; change ∀ i j, raw18246step1 i j = -(raw18246step0 i j); unfold raw18246step1 raw18246step0; decide +kernel
      have hl : raw18246step1Labels = raw18246step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18246step1 raw18246step1Labels = mixedMoment B raw18246step2 raw18246step2Labels := by
      have ha : raw18246step2 = raw18246step1 := by apply Matrix.ext; unfold raw18246step2 raw18246step1; decide +kernel
      have hl : raw18246step1Labels = labelEmbedding1 ∘ raw18246step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18246step1 raw18246step1Labels raw18246step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3514 node3514Labels := by rfl

def raw18247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18247Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18247step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw18247step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18247step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw18247step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18247 raw18247Labels = mixedMoment B node3795 node3795Labels := by
  calc
    mixedMoment B raw18247 raw18247Labels = mixedMoment B raw18247step0 raw18247step0Labels := by
      have ha : raw18247step0 = (fun i j => raw18247 (permutation644 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18247step0 raw18247; decide +kernel
      have hl : raw18247step0Labels = raw18247Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18247 raw18247Labels permutation644 permutation7
    mixedMoment B raw18247step0 raw18247step0Labels = mixedMoment B raw18247step1 raw18247step1Labels := by
      have ha : raw18247step1 = raw18247step0 := by apply Matrix.ext; unfold raw18247step1 raw18247step0; decide +kernel
      have hl : raw18247step0Labels = labelEmbedding1 ∘ raw18247step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18247step0 raw18247step0Labels raw18247step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3795 node3795Labels := by rfl

def raw18248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18248Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18248step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18248step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18248step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18248step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18248 raw18248Labels = mixedMoment B node3793 node3793Labels := by
  calc
    mixedMoment B raw18248 raw18248Labels = mixedMoment B raw18248step0 raw18248step0Labels := by
      have ha : raw18248step0 = (fun i j => raw18248 (permutation644 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18248step0 raw18248; decide +kernel
      have hl : raw18248step0Labels = raw18248Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18248 raw18248Labels permutation644 permutation7
    mixedMoment B raw18248step0 raw18248step0Labels = mixedMoment B raw18248step1 raw18248step1Labels := by
      have ha : raw18248step1 = raw18248step0 := by apply Matrix.ext; unfold raw18248step1 raw18248step0; decide +kernel
      have hl : raw18248step0Labels = labelEmbedding1 ∘ raw18248step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18248step0 raw18248step0Labels raw18248step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3793 node3793Labels := by rfl

def raw18249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2]]
def raw18249Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18249step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw18249step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18249step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18249step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18249step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18249step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18249 raw18249Labels = mixedMoment B node3807 node3807Labels := by
  calc
    mixedMoment B raw18249 raw18249Labels = mixedMoment B raw18249step0 raw18249step0Labels := by
      have hz : ∀ j, raw18249 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18249step0 = (fun i j => raw18249 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18249step0 raw18249; decide +kernel
      have hl : raw18249step0Labels = raw18249Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18249 raw18249Labels permutation520 hz
    mixedMoment B raw18249step0 raw18249step0Labels = mixedMoment B raw18249step1 raw18249step1Labels := by
      have ha : raw18249step1 = (fun i j => raw18249step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18249step1 raw18249step0; decide +kernel
      have hl : raw18249step1Labels = raw18249step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18249step0 raw18249step0Labels permutation143 permutation7
    mixedMoment B raw18249step1 raw18249step1Labels = mixedMoment B raw18249step2 raw18249step2Labels := by
      have ha : raw18249step2 = raw18249step1 := by apply Matrix.ext; unfold raw18249step2 raw18249step1; decide +kernel
      have hl : raw18249step1Labels = labelEmbedding1 ∘ raw18249step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18249step1 raw18249step1Labels raw18249step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3807 node3807Labels := by rfl

def raw18250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw18250Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18250step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18250step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18250step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18250step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18250step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18250step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18250 raw18250Labels = mixedMoment B node3838 node3838Labels := by
  calc
    mixedMoment B raw18250 raw18250Labels = mixedMoment B raw18250step0 raw18250step0Labels := by
      have ha : raw18250step0 = (fun i j => raw18250 (permutation202 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18250step0 raw18250; decide +kernel
      have hl : raw18250step0Labels = raw18250Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18250 raw18250Labels permutation202 permutation7
    mixedMoment B raw18250step0 raw18250step0Labels = mixedMoment B raw18250step1 raw18250step1Labels := by
      have ha : raw18250step1 = -raw18250step0 := by apply Matrix.ext; change ∀ i j, raw18250step1 i j = -(raw18250step0 i j); unfold raw18250step1 raw18250step0; decide +kernel
      have hl : raw18250step1Labels = raw18250step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18250step1 raw18250step1Labels = mixedMoment B raw18250step2 raw18250step2Labels := by
      have ha : raw18250step2 = raw18250step1 := by apply Matrix.ext; unfold raw18250step2 raw18250step1; decide +kernel
      have hl : raw18250step1Labels = labelEmbedding1 ∘ raw18250step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18250step1 raw18250step1Labels raw18250step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3838 node3838Labels := by rfl

def raw18251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18251Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18251step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw18251step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18251step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18251step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18251step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18251step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18251 raw18251Labels = mixedMoment B node3834 node3834Labels := by
  calc
    mixedMoment B raw18251 raw18251Labels = mixedMoment B raw18251step0 raw18251step0Labels := by
      have ha : raw18251step0 = (fun i j => raw18251 (permutation294 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18251step0 raw18251; decide +kernel
      have hl : raw18251step0Labels = raw18251Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18251 raw18251Labels permutation294 permutation5
    mixedMoment B raw18251step0 raw18251step0Labels = mixedMoment B raw18251step1 raw18251step1Labels := by
      have ha : raw18251step1 = -raw18251step0 := by apply Matrix.ext; change ∀ i j, raw18251step1 i j = -(raw18251step0 i j); unfold raw18251step1 raw18251step0; decide +kernel
      have hl : raw18251step1Labels = raw18251step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18251step1 raw18251step1Labels = mixedMoment B raw18251step2 raw18251step2Labels := by
      have ha : raw18251step2 = raw18251step1 := by apply Matrix.ext; unfold raw18251step2 raw18251step1; decide +kernel
      have hl : raw18251step1Labels = labelEmbedding1 ∘ raw18251step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18251step1 raw18251step1Labels raw18251step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3834 node3834Labels := by rfl

def raw18252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw18252Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18252step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18252step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18252step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18252step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18252 raw18252Labels = mixedMoment B node3870 node3870Labels := by
  calc
    mixedMoment B raw18252 raw18252Labels = mixedMoment B raw18252step0 raw18252step0Labels := by
      have ha : raw18252step0 = (fun i j => raw18252 (permutation644 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18252step0 raw18252; decide +kernel
      have hl : raw18252step0Labels = raw18252Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18252 raw18252Labels permutation644 permutation7
    mixedMoment B raw18252step0 raw18252step0Labels = mixedMoment B raw18252step1 raw18252step1Labels := by
      have ha : raw18252step1 = raw18252step0 := by apply Matrix.ext; unfold raw18252step1 raw18252step0; decide +kernel
      have hl : raw18252step0Labels = labelEmbedding1 ∘ raw18252step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18252step0 raw18252step0Labels raw18252step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3870 node3870Labels := by rfl

def raw18253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![2, 0, -2]]
def raw18253Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18253step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18253step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18253step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18253step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw18253step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18253 raw18253Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw18253 raw18253Labels = mixedMoment B raw18253step0 raw18253step0Labels := by
      have hz : ∀ j, raw18253 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18253step0 = (fun i j => raw18253 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18253step0 raw18253; decide +kernel
      have hl : raw18253step0Labels = raw18253Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18253 raw18253Labels permutation520 hz
    mixedMoment B raw18253step0 raw18253step0Labels = mixedMoment B raw18253step1 raw18253step1Labels := by
      have ha : raw18253step1 = (fun i j => raw18253step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18253step1 raw18253step0; decide +kernel
      have hl : raw18253step1Labels = raw18253step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18253step0 raw18253step0Labels permutation143 permutation7
    mixedMoment B raw18253step1 raw18253step1Labels = mixedMoment B raw18253step2 raw18253step2Labels := by
      have ha : raw18253step2 = raw18253step1 := by apply Matrix.ext; unfold raw18253step2 raw18253step1; decide +kernel
      have hl : raw18253step1Labels = labelEmbedding1 ∘ raw18253step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18253step1 raw18253step1Labels raw18253step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3850 node3850Labels := by rfl

def raw18254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18254Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18254step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw18254step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18254step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw18254step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18254step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw18254step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18254 raw18254Labels = mixedMoment B node3516 node3516Labels := by
  calc
    mixedMoment B raw18254 raw18254Labels = mixedMoment B raw18254step0 raw18254step0Labels := by
      have ha : raw18254step0 = (fun i j => raw18254 (permutation202 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18254step0 raw18254; decide +kernel
      have hl : raw18254step0Labels = raw18254Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18254 raw18254Labels permutation202 permutation7
    mixedMoment B raw18254step0 raw18254step0Labels = mixedMoment B raw18254step1 raw18254step1Labels := by
      have ha : raw18254step1 = -raw18254step0 := by apply Matrix.ext; change ∀ i j, raw18254step1 i j = -(raw18254step0 i j); unfold raw18254step1 raw18254step0; decide +kernel
      have hl : raw18254step1Labels = raw18254step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18254step1 raw18254step1Labels = mixedMoment B raw18254step2 raw18254step2Labels := by
      have ha : raw18254step2 = raw18254step1 := by apply Matrix.ext; unfold raw18254step2 raw18254step1; decide +kernel
      have hl : raw18254step1Labels = labelEmbedding1 ∘ raw18254step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18254step1 raw18254step1Labels raw18254step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3516 node3516Labels := by rfl

def raw18255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18255Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18255step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw18255step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18255step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw18255step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18255 raw18255Labels = mixedMoment B node3833 node3833Labels := by
  calc
    mixedMoment B raw18255 raw18255Labels = mixedMoment B raw18255step0 raw18255step0Labels := by
      have ha : raw18255step0 = (fun i j => raw18255 (permutation564 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18255step0 raw18255; decide +kernel
      have hl : raw18255step0Labels = raw18255Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18255 raw18255Labels permutation564 permutation5
    mixedMoment B raw18255step0 raw18255step0Labels = mixedMoment B raw18255step1 raw18255step1Labels := by
      have ha : raw18255step1 = raw18255step0 := by apply Matrix.ext; unfold raw18255step1 raw18255step0; decide +kernel
      have hl : raw18255step0Labels = labelEmbedding1 ∘ raw18255step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18255step0 raw18255step0Labels raw18255step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3833 node3833Labels := by rfl

def raw18256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18256Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18256step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18256step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18256step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw18256step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18256 raw18256Labels = mixedMoment B node3834 node3834Labels := by
  calc
    mixedMoment B raw18256 raw18256Labels = mixedMoment B raw18256step0 raw18256step0Labels := by
      have ha : raw18256step0 = (fun i j => raw18256 (permutation563 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18256step0 raw18256; decide +kernel
      have hl : raw18256step0Labels = raw18256Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18256 raw18256Labels permutation563 permutation5
    mixedMoment B raw18256step0 raw18256step0Labels = mixedMoment B raw18256step1 raw18256step1Labels := by
      have ha : raw18256step1 = raw18256step0 := by apply Matrix.ext; unfold raw18256step1 raw18256step0; decide +kernel
      have hl : raw18256step0Labels = labelEmbedding1 ∘ raw18256step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18256step0 raw18256step0Labels raw18256step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3834 node3834Labels := by rfl

def raw18257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 0, 1], ![2, -2, 0], ![2, 0, -2]]
def raw18257Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18257step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 0, 2]]
def raw18257step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18257step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw18257step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18257step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw18257step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18257 raw18257Labels = mixedMoment B node3795 node3795Labels := by
  calc
    mixedMoment B raw18257 raw18257Labels = mixedMoment B raw18257step0 raw18257step0Labels := by
      have ha : raw18257step0 = (fun i j => raw18257 (permutation202 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18257step0 raw18257; decide +kernel
      have hl : raw18257step0Labels = raw18257Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18257 raw18257Labels permutation202 permutation7
    mixedMoment B raw18257step0 raw18257step0Labels = mixedMoment B raw18257step1 raw18257step1Labels := by
      have ha : raw18257step1 = -raw18257step0 := by apply Matrix.ext; change ∀ i j, raw18257step1 i j = -(raw18257step0 i j); unfold raw18257step1 raw18257step0; decide +kernel
      have hl : raw18257step1Labels = raw18257step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18257step1 raw18257step1Labels = mixedMoment B raw18257step2 raw18257step2Labels := by
      have ha : raw18257step2 = raw18257step1 := by apply Matrix.ext; unfold raw18257step2 raw18257step1; decide +kernel
      have hl : raw18257step1Labels = labelEmbedding1 ∘ raw18257step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18257step1 raw18257step1Labels raw18257step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3795 node3795Labels := by rfl

def raw18258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![1, 1, -2]]
def raw18258Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18258step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw18258step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18258step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw18258step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18258step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw18258step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18258 raw18258Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw18258 raw18258Labels = mixedMoment B raw18258step0 raw18258step0Labels := by
      have ha : raw18258step0 = (fun i j => raw18258 (permutation202 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18258step0 raw18258; decide +kernel
      have hl : raw18258step0Labels = raw18258Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18258 raw18258Labels permutation202 permutation7
    mixedMoment B raw18258step0 raw18258step0Labels = mixedMoment B raw18258step1 raw18258step1Labels := by
      have ha : raw18258step1 = -raw18258step0 := by apply Matrix.ext; change ∀ i j, raw18258step1 i j = -(raw18258step0 i j); unfold raw18258step1 raw18258step0; decide +kernel
      have hl : raw18258step1Labels = raw18258step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18258step1 raw18258step1Labels = mixedMoment B raw18258step2 raw18258step2Labels := by
      have ha : raw18258step2 = raw18258step1 := by apply Matrix.ext; unfold raw18258step2 raw18258step1; decide +kernel
      have hl : raw18258step1Labels = labelEmbedding1 ∘ raw18258step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18258step1 raw18258step1Labels raw18258step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3840 node3840Labels := by rfl

def raw18259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18259Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18259step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw18259step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18259step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw18259step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18259 raw18259Labels = mixedMoment B node3513 node3513Labels := by
  calc
    mixedMoment B raw18259 raw18259Labels = mixedMoment B raw18259step0 raw18259step0Labels := by
      have ha : raw18259step0 = (fun i j => raw18259 (permutation644 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18259step0 raw18259; decide +kernel
      have hl : raw18259step0Labels = raw18259Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18259 raw18259Labels permutation644 permutation7
    mixedMoment B raw18259step0 raw18259step0Labels = mixedMoment B raw18259step1 raw18259step1Labels := by
      have ha : raw18259step1 = raw18259step0 := by apply Matrix.ext; unfold raw18259step1 raw18259step0; decide +kernel
      have hl : raw18259step0Labels = labelEmbedding1 ∘ raw18259step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18259step0 raw18259step0Labels raw18259step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3513 node3513Labels := by rfl

def raw18260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18260Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18260step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw18260step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18260step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw18260step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18260 raw18260Labels = mixedMoment B node3516 node3516Labels := by
  calc
    mixedMoment B raw18260 raw18260Labels = mixedMoment B raw18260step0 raw18260step0Labels := by
      have ha : raw18260step0 = (fun i j => raw18260 (permutation644 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18260step0 raw18260; decide +kernel
      have hl : raw18260step0Labels = raw18260Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18260 raw18260Labels permutation644 permutation7
    mixedMoment B raw18260step0 raw18260step0Labels = mixedMoment B raw18260step1 raw18260step1Labels := by
      have ha : raw18260step1 = raw18260step0 := by apply Matrix.ext; unfold raw18260step1 raw18260step0; decide +kernel
      have hl : raw18260step0Labels = labelEmbedding1 ∘ raw18260step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18260step0 raw18260step0Labels raw18260step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3516 node3516Labels := by rfl

def raw18261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18261Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18261step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18261step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18261step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18261step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18261 raw18261Labels = mixedMoment B node3557 node3557Labels := by
  calc
    mixedMoment B raw18261 raw18261Labels = mixedMoment B raw18261step0 raw18261step0Labels := by
      have ha : raw18261step0 = (fun i j => raw18261 (permutation644 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18261step0 raw18261; decide +kernel
      have hl : raw18261step0Labels = raw18261Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18261 raw18261Labels permutation644 permutation7
    mixedMoment B raw18261step0 raw18261step0Labels = mixedMoment B raw18261step1 raw18261step1Labels := by
      have ha : raw18261step1 = raw18261step0 := by apply Matrix.ext; unfold raw18261step1 raw18261step0; decide +kernel
      have hl : raw18261step0Labels = labelEmbedding1 ∘ raw18261step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18261step0 raw18261step0Labels raw18261step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3557 node3557Labels := by rfl

def raw18262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![-1, 0, 1], ![1, -1, 0], ![3, -1, -2]]
def raw18262Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18262step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18262step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18262step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw18262step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18262 raw18262Labels = mixedMoment B node3514 node3514Labels := by
  calc
    mixedMoment B raw18262 raw18262Labels = mixedMoment B raw18262step0 raw18262step0Labels := by
      have ha : raw18262step0 = (fun i j => raw18262 (permutation644 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18262step0 raw18262; decide +kernel
      have hl : raw18262step0Labels = raw18262Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18262 raw18262Labels permutation644 permutation7
    mixedMoment B raw18262step0 raw18262step0Labels = mixedMoment B raw18262step1 raw18262step1Labels := by
      have ha : raw18262step1 = raw18262step0 := by apply Matrix.ext; unfold raw18262step1 raw18262step0; decide +kernel
      have hl : raw18262step0Labels = labelEmbedding1 ∘ raw18262step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18262step0 raw18262step0Labels raw18262step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3514 node3514Labels := by rfl

def raw18263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![0, 0, 0], ![3, -1, -2]]
def raw18263Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![3, -1, -2]]
def raw18263step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw18263step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18263step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw18263step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18263step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical18263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18263 raw18263Labels = mixedMoment B node3533 node3533Labels := by
  calc
    mixedMoment B raw18263 raw18263Labels = mixedMoment B raw18263step0 raw18263step0Labels := by
      have hz : ∀ j, raw18263 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18263step0 = (fun i j => raw18263 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18263step0 raw18263; decide +kernel
      have hl : raw18263step0Labels = raw18263Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18263 raw18263Labels permutation520 hz
    mixedMoment B raw18263step0 raw18263step0Labels = mixedMoment B raw18263step1 raw18263step1Labels := by
      have ha : raw18263step1 = (fun i j => raw18263step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18263step1 raw18263step0; decide +kernel
      have hl : raw18263step1Labels = raw18263step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18263step0 raw18263step0Labels permutation143 permutation7
    mixedMoment B raw18263step1 raw18263step1Labels = mixedMoment B raw18263step2 raw18263step2Labels := by
      have ha : raw18263step2 = raw18263step1 := by apply Matrix.ext; unfold raw18263step2 raw18263step1; decide +kernel
      have hl : raw18263step1Labels = labelEmbedding1 ∘ raw18263step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18263step1 raw18263step1Labels raw18263step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3533 node3533Labels := by rfl

def raw18264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18264Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18264step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18264step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18264step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18264step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18264step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18264step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18264 raw18264Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw18264 raw18264Labels = mixedMoment B raw18264step0 raw18264step0Labels := by
      have ha : raw18264step0 = (fun i j => raw18264 (permutation681 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18264step0 raw18264; decide +kernel
      have hl : raw18264step0Labels = raw18264Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18264 raw18264Labels permutation681 permutation3
    mixedMoment B raw18264step0 raw18264step0Labels = mixedMoment B raw18264step1 raw18264step1Labels := by
      have ha : raw18264step1 = -raw18264step0 := by apply Matrix.ext; change ∀ i j, raw18264step1 i j = -(raw18264step0 i j); unfold raw18264step1 raw18264step0; decide +kernel
      have hl : raw18264step1Labels = raw18264step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18264step1 raw18264step1Labels = mixedMoment B raw18264step2 raw18264step2Labels := by
      have ha : raw18264step2 = raw18264step1 := by apply Matrix.ext; unfold raw18264step2 raw18264step1; decide +kernel
      have hl : raw18264step1Labels = labelEmbedding6 ∘ raw18264step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18264step1 raw18264step1Labels raw18264step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw18265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18265Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18265step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw18265step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18265step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18265step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18265step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18265step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18265 raw18265Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw18265 raw18265Labels = mixedMoment B raw18265step0 raw18265step0Labels := by
      have ha : raw18265step0 = (fun i j => raw18265 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18265step0 raw18265; decide +kernel
      have hl : raw18265step0Labels = raw18265Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18265 raw18265Labels permutation686 permutation3
    mixedMoment B raw18265step0 raw18265step0Labels = mixedMoment B raw18265step1 raw18265step1Labels := by
      have ha : raw18265step1 = -raw18265step0 := by apply Matrix.ext; change ∀ i j, raw18265step1 i j = -(raw18265step0 i j); unfold raw18265step1 raw18265step0; decide +kernel
      have hl : raw18265step1Labels = raw18265step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18265step1 raw18265step1Labels = mixedMoment B raw18265step2 raw18265step2Labels := by
      have ha : raw18265step2 = raw18265step1 := by apply Matrix.ext; unfold raw18265step2 raw18265step1; decide +kernel
      have hl : raw18265step1Labels = labelEmbedding6 ∘ raw18265step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18265step1 raw18265step1Labels raw18265step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw18266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18266Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18266step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18266step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18266step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18266step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18266 raw18266Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw18266 raw18266Labels = mixedMoment B raw18266step0 raw18266step0Labels := by
      have ha : raw18266step0 = (fun i j => raw18266 (permutation643 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18266step0 raw18266; decide +kernel
      have hl : raw18266step0Labels = raw18266Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18266 raw18266Labels permutation643 permutation5
    mixedMoment B raw18266step0 raw18266step0Labels = mixedMoment B raw18266step1 raw18266step1Labels := by
      have ha : raw18266step1 = raw18266step0 := by apply Matrix.ext; unfold raw18266step1 raw18266step0; decide +kernel
      have hl : raw18266step0Labels = labelEmbedding8 ∘ raw18266step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18266step0 raw18266step0Labels raw18266step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw18267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18267Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18267step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18267step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18267step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18267step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18267 raw18267Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw18267 raw18267Labels = mixedMoment B raw18267step0 raw18267step0Labels := by
      have ha : raw18267step0 = (fun i j => raw18267 (permutation632 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18267step0 raw18267; decide +kernel
      have hl : raw18267step0Labels = raw18267Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18267 raw18267Labels permutation632 permutation5
    mixedMoment B raw18267step0 raw18267step0Labels = mixedMoment B raw18267step1 raw18267step1Labels := by
      have ha : raw18267step1 = raw18267step0 := by apply Matrix.ext; unfold raw18267step1 raw18267step0; decide +kernel
      have hl : raw18267step0Labels = labelEmbedding8 ∘ raw18267step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18267step0 raw18267step0Labels raw18267step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw18268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18268Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18268step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw18268step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18268 raw18268Labels = mixedMoment B node5500 node5500Labels := by
  calc
    mixedMoment B raw18268 raw18268Labels = mixedMoment B raw18268step0 raw18268step0Labels := by
      have ha : raw18268step0 = (fun i j => raw18268 (permutation266 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18268step0 raw18268; decide +kernel
      have hl : raw18268step0Labels = raw18268Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18268 raw18268Labels permutation266 permutation2
    _ = mixedMoment B node5500 node5500Labels := by rfl

def raw18269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18269Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18269step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw18269step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18269step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18269step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18269step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18269step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18269 raw18269Labels = mixedMoment B node4801 node4801Labels := by
  calc
    mixedMoment B raw18269 raw18269Labels = mixedMoment B raw18269step0 raw18269step0Labels := by
      have ha : raw18269step0 = (fun i j => raw18269 (permutation212 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18269step0 raw18269; decide +kernel
      have hl : raw18269step0Labels = raw18269Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18269 raw18269Labels permutation212 permutation5
    mixedMoment B raw18269step0 raw18269step0Labels = mixedMoment B raw18269step1 raw18269step1Labels := by
      have ha : raw18269step1 = -raw18269step0 := by apply Matrix.ext; change ∀ i j, raw18269step1 i j = -(raw18269step0 i j); unfold raw18269step1 raw18269step0; decide +kernel
      have hl : raw18269step1Labels = raw18269step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18269step1 raw18269step1Labels = mixedMoment B raw18269step2 raw18269step2Labels := by
      have ha : raw18269step2 = raw18269step1 := by apply Matrix.ext; unfold raw18269step2 raw18269step1; decide +kernel
      have hl : raw18269step1Labels = labelEmbedding8 ∘ raw18269step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18269step1 raw18269step1Labels raw18269step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4801 node4801Labels := by rfl

def raw18270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18270Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18270step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18270step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18270step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18270step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18270 raw18270Labels = mixedMoment B node5423 node5423Labels := by
  calc
    mixedMoment B raw18270 raw18270Labels = mixedMoment B raw18270step0 raw18270step0Labels := by
      have ha : raw18270step0 = (fun i j => raw18270 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18270step0 raw18270; decide +kernel
      have hl : raw18270step0Labels = raw18270Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18270 raw18270Labels permutation182 permutation3
    mixedMoment B raw18270step0 raw18270step0Labels = mixedMoment B raw18270step1 raw18270step1Labels := by
      have ha : raw18270step1 = raw18270step0 := by apply Matrix.ext; unfold raw18270step1 raw18270step0; decide +kernel
      have hl : raw18270step0Labels = labelEmbedding6 ∘ raw18270step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18270step0 raw18270step0Labels raw18270step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5423 node5423Labels := by rfl

def raw18271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18271Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18271step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw18271step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18271step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18271step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18271step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18271step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18271 raw18271Labels = mixedMoment B node5351 node5351Labels := by
  calc
    mixedMoment B raw18271 raw18271Labels = mixedMoment B raw18271step0 raw18271step0Labels := by
      have ha : raw18271step0 = (fun i j => raw18271 (permutation212 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18271step0 raw18271; decide +kernel
      have hl : raw18271step0Labels = raw18271Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18271 raw18271Labels permutation212 permutation5
    mixedMoment B raw18271step0 raw18271step0Labels = mixedMoment B raw18271step1 raw18271step1Labels := by
      have ha : raw18271step1 = -raw18271step0 := by apply Matrix.ext; change ∀ i j, raw18271step1 i j = -(raw18271step0 i j); unfold raw18271step1 raw18271step0; decide +kernel
      have hl : raw18271step1Labels = raw18271step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18271step1 raw18271step1Labels = mixedMoment B raw18271step2 raw18271step2Labels := by
      have ha : raw18271step2 = raw18271step1 := by apply Matrix.ext; unfold raw18271step2 raw18271step1; decide +kernel
      have hl : raw18271step1Labels = labelEmbedding8 ∘ raw18271step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18271step1 raw18271step1Labels raw18271step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5351 node5351Labels := by rfl

def raw18272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18272Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18272step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18272step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18272step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18272step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18272 raw18272Labels = mixedMoment B node5415 node5415Labels := by
  calc
    mixedMoment B raw18272 raw18272Labels = mixedMoment B raw18272step0 raw18272step0Labels := by
      have ha : raw18272step0 = (fun i j => raw18272 (permutation609 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18272step0 raw18272; decide +kernel
      have hl : raw18272step0Labels = raw18272Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18272 raw18272Labels permutation609 permutation5
    mixedMoment B raw18272step0 raw18272step0Labels = mixedMoment B raw18272step1 raw18272step1Labels := by
      have ha : raw18272step1 = raw18272step0 := by apply Matrix.ext; unfold raw18272step1 raw18272step0; decide +kernel
      have hl : raw18272step0Labels = labelEmbedding8 ∘ raw18272step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18272step0 raw18272step0Labels raw18272step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5415 node5415Labels := by rfl

def raw18273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18273Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18273step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw18273step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18273step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18273step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18273step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18273step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18273 raw18273Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw18273 raw18273Labels = mixedMoment B raw18273step0 raw18273step0Labels := by
      have ha : raw18273step0 = (fun i j => raw18273 (permutation212 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18273step0 raw18273; decide +kernel
      have hl : raw18273step0Labels = raw18273Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18273 raw18273Labels permutation212 permutation5
    mixedMoment B raw18273step0 raw18273step0Labels = mixedMoment B raw18273step1 raw18273step1Labels := by
      have ha : raw18273step1 = -raw18273step0 := by apply Matrix.ext; change ∀ i j, raw18273step1 i j = -(raw18273step0 i j); unfold raw18273step1 raw18273step0; decide +kernel
      have hl : raw18273step1Labels = raw18273step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18273step1 raw18273step1Labels = mixedMoment B raw18273step2 raw18273step2Labels := by
      have ha : raw18273step2 = raw18273step1 := by apply Matrix.ext; unfold raw18273step2 raw18273step1; decide +kernel
      have hl : raw18273step1Labels = labelEmbedding8 ∘ raw18273step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18273step1 raw18273step1Labels raw18273step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw18274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18274Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18274step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw18274step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18274step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw18274step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18274step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw18274step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18274 raw18274Labels = mixedMoment B node4782 node4782Labels := by
  calc
    mixedMoment B raw18274 raw18274Labels = mixedMoment B raw18274step0 raw18274step0Labels := by
      have ha : raw18274step0 = (fun i j => raw18274 (permutation202 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18274step0 raw18274; decide +kernel
      have hl : raw18274step0Labels = raw18274Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18274 raw18274Labels permutation202 permutation5
    mixedMoment B raw18274step0 raw18274step0Labels = mixedMoment B raw18274step1 raw18274step1Labels := by
      have ha : raw18274step1 = -raw18274step0 := by apply Matrix.ext; change ∀ i j, raw18274step1 i j = -(raw18274step0 i j); unfold raw18274step1 raw18274step0; decide +kernel
      have hl : raw18274step1Labels = raw18274step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18274step1 raw18274step1Labels = mixedMoment B raw18274step2 raw18274step2Labels := by
      have ha : raw18274step2 = raw18274step1 := by apply Matrix.ext; unfold raw18274step2 raw18274step1; decide +kernel
      have hl : raw18274step1Labels = labelEmbedding8 ∘ raw18274step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18274step1 raw18274step1Labels raw18274step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4782 node4782Labels := by rfl

def raw18275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18275Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18275step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw18275step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18275step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw18275step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18275 raw18275Labels = mixedMoment B node5344 node5344Labels := by
  calc
    mixedMoment B raw18275 raw18275Labels = mixedMoment B raw18275step0 raw18275step0Labels := by
      have ha : raw18275step0 = (fun i j => raw18275 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18275step0 raw18275; decide +kernel
      have hl : raw18275step0Labels = raw18275Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18275 raw18275Labels permutation160 permutation3
    mixedMoment B raw18275step0 raw18275step0Labels = mixedMoment B raw18275step1 raw18275step1Labels := by
      have ha : raw18275step1 = raw18275step0 := by apply Matrix.ext; unfold raw18275step1 raw18275step0; decide +kernel
      have hl : raw18275step0Labels = labelEmbedding6 ∘ raw18275step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18275step0 raw18275step0Labels raw18275step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5344 node5344Labels := by rfl

def raw18276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18276Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18276step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw18276step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18276step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw18276step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18276 raw18276Labels = mixedMoment B node5341 node5341Labels := by
  calc
    mixedMoment B raw18276 raw18276Labels = mixedMoment B raw18276step0 raw18276step0Labels := by
      have ha : raw18276step0 = (fun i j => raw18276 (permutation644 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18276step0 raw18276; decide +kernel
      have hl : raw18276step0Labels = raw18276Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18276 raw18276Labels permutation644 permutation5
    mixedMoment B raw18276step0 raw18276step0Labels = mixedMoment B raw18276step1 raw18276step1Labels := by
      have ha : raw18276step1 = raw18276step0 := by apply Matrix.ext; unfold raw18276step1 raw18276step0; decide +kernel
      have hl : raw18276step0Labels = labelEmbedding8 ∘ raw18276step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18276step0 raw18276step0Labels raw18276step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5341 node5341Labels := by rfl

def raw18277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18277Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18277step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18277step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18277step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18277step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18277 raw18277Labels = mixedMoment B node5351 node5351Labels := by
  calc
    mixedMoment B raw18277 raw18277Labels = mixedMoment B raw18277step0 raw18277step0Labels := by
      have ha : raw18277step0 = (fun i j => raw18277 (permutation632 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18277step0 raw18277; decide +kernel
      have hl : raw18277step0Labels = raw18277Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18277 raw18277Labels permutation632 permutation5
    mixedMoment B raw18277step0 raw18277step0Labels = mixedMoment B raw18277step1 raw18277step1Labels := by
      have ha : raw18277step1 = raw18277step0 := by apply Matrix.ext; unfold raw18277step1 raw18277step0; decide +kernel
      have hl : raw18277step0Labels = labelEmbedding8 ∘ raw18277step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18277step0 raw18277step0Labels raw18277step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5351 node5351Labels := by rfl

def raw18278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18278Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18278step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw18278step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18278step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18278step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18278step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18278step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18278 raw18278Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw18278 raw18278Labels = mixedMoment B raw18278step0 raw18278step0Labels := by
      have ha : raw18278step0 = (fun i j => raw18278 (permutation203 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18278step0 raw18278; decide +kernel
      have hl : raw18278step0Labels = raw18278Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18278 raw18278Labels permutation203 permutation5
    mixedMoment B raw18278step0 raw18278step0Labels = mixedMoment B raw18278step1 raw18278step1Labels := by
      have ha : raw18278step1 = -raw18278step0 := by apply Matrix.ext; change ∀ i j, raw18278step1 i j = -(raw18278step0 i j); unfold raw18278step1 raw18278step0; decide +kernel
      have hl : raw18278step1Labels = raw18278step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18278step1 raw18278step1Labels = mixedMoment B raw18278step2 raw18278step2Labels := by
      have ha : raw18278step2 = raw18278step1 := by apply Matrix.ext; unfold raw18278step2 raw18278step1; decide +kernel
      have hl : raw18278step1Labels = labelEmbedding8 ∘ raw18278step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18278step1 raw18278step1Labels raw18278step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw18279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18279Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18279step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18279step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18279step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18279step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18279 raw18279Labels = mixedMoment B node4801 node4801Labels := by
  calc
    mixedMoment B raw18279 raw18279Labels = mixedMoment B raw18279step0 raw18279step0Labels := by
      have ha : raw18279step0 = (fun i j => raw18279 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18279step0 raw18279; decide +kernel
      have hl : raw18279step0Labels = raw18279Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18279 raw18279Labels permutation152 permutation3
    mixedMoment B raw18279step0 raw18279step0Labels = mixedMoment B raw18279step1 raw18279step1Labels := by
      have ha : raw18279step1 = raw18279step0 := by apply Matrix.ext; unfold raw18279step1 raw18279step0; decide +kernel
      have hl : raw18279step0Labels = labelEmbedding6 ∘ raw18279step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18279step0 raw18279step0Labels raw18279step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4801 node4801Labels := by rfl

def raw18280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18280Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18280step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18280step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18280step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18280step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18280 raw18280Labels = mixedMoment B node5351 node5351Labels := by
  calc
    mixedMoment B raw18280 raw18280Labels = mixedMoment B raw18280step0 raw18280step0Labels := by
      have ha : raw18280step0 = (fun i j => raw18280 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18280step0 raw18280; decide +kernel
      have hl : raw18280step0Labels = raw18280Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18280 raw18280Labels permutation152 permutation3
    mixedMoment B raw18280step0 raw18280step0Labels = mixedMoment B raw18280step1 raw18280step1Labels := by
      have ha : raw18280step1 = raw18280step0 := by apply Matrix.ext; unfold raw18280step1 raw18280step0; decide +kernel
      have hl : raw18280step0Labels = labelEmbedding6 ∘ raw18280step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18280step0 raw18280step0Labels raw18280step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5351 node5351Labels := by rfl

def raw18281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw18281Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18281step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18281step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18281step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18281step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18281 raw18281Labels = mixedMoment B node5415 node5415Labels := by
  calc
    mixedMoment B raw18281 raw18281Labels = mixedMoment B raw18281step0 raw18281step0Labels := by
      have ha : raw18281step0 = (fun i j => raw18281 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18281step0 raw18281; decide +kernel
      have hl : raw18281step0Labels = raw18281Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18281 raw18281Labels permutation152 permutation3
    mixedMoment B raw18281step0 raw18281step0Labels = mixedMoment B raw18281step1 raw18281step1Labels := by
      have ha : raw18281step1 = raw18281step0 := by apply Matrix.ext; unfold raw18281step1 raw18281step0; decide +kernel
      have hl : raw18281step0Labels = labelEmbedding6 ∘ raw18281step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18281step0 raw18281step0Labels raw18281step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5415 node5415Labels := by rfl

def raw18282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw18282Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18282step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18282step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18282step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw18282step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18282 raw18282Labels = mixedMoment B node5423 node5423Labels := by
  calc
    mixedMoment B raw18282 raw18282Labels = mixedMoment B raw18282step0 raw18282step0Labels := by
      have ha : raw18282step0 = (fun i j => raw18282 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18282step0 raw18282; decide +kernel
      have hl : raw18282step0Labels = raw18282Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18282 raw18282Labels permutation164 permutation3
    mixedMoment B raw18282step0 raw18282step0Labels = mixedMoment B raw18282step1 raw18282step1Labels := by
      have ha : raw18282step1 = raw18282step0 := by apply Matrix.ext; unfold raw18282step1 raw18282step0; decide +kernel
      have hl : raw18282step0Labels = labelEmbedding6 ∘ raw18282step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18282step0 raw18282step0Labels raw18282step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5423 node5423Labels := by rfl

def raw18283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw18283Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18283step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18283step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18283step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw18283step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18283 raw18283Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw18283 raw18283Labels = mixedMoment B raw18283step0 raw18283step0Labels := by
      have ha : raw18283step0 = (fun i j => raw18283 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18283step0 raw18283; decide +kernel
      have hl : raw18283step0Labels = raw18283Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18283 raw18283Labels permutation152 permutation3
    mixedMoment B raw18283step0 raw18283step0Labels = mixedMoment B raw18283step1 raw18283step1Labels := by
      have ha : raw18283step1 = raw18283step0 := by apply Matrix.ext; unfold raw18283step1 raw18283step0; decide +kernel
      have hl : raw18283step0Labels = labelEmbedding6 ∘ raw18283step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18283step0 raw18283step0Labels raw18283step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw18284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw18284Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18284step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw18284step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18284step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw18284step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18284 raw18284Labels = mixedMoment B node4782 node4782Labels := by
  calc
    mixedMoment B raw18284 raw18284Labels = mixedMoment B raw18284step0 raw18284step0Labels := by
      have ha : raw18284step0 = (fun i j => raw18284 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18284step0 raw18284; decide +kernel
      have hl : raw18284step0Labels = raw18284Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18284 raw18284Labels permutation158 permutation3
    mixedMoment B raw18284step0 raw18284step0Labels = mixedMoment B raw18284step1 raw18284step1Labels := by
      have ha : raw18284step1 = raw18284step0 := by apply Matrix.ext; unfold raw18284step1 raw18284step0; decide +kernel
      have hl : raw18284step0Labels = labelEmbedding6 ∘ raw18284step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18284step0 raw18284step0Labels raw18284step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4782 node4782Labels := by rfl

def raw18285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw18285Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18285step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw18285step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18285step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw18285step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18285 raw18285Labels = mixedMoment B node5341 node5341Labels := by
  calc
    mixedMoment B raw18285 raw18285Labels = mixedMoment B raw18285step0 raw18285step0Labels := by
      have ha : raw18285step0 = (fun i j => raw18285 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18285step0 raw18285; decide +kernel
      have hl : raw18285step0Labels = raw18285Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18285 raw18285Labels permutation158 permutation3
    mixedMoment B raw18285step0 raw18285step0Labels = mixedMoment B raw18285step1 raw18285step1Labels := by
      have ha : raw18285step1 = raw18285step0 := by apply Matrix.ext; unfold raw18285step1 raw18285step0; decide +kernel
      have hl : raw18285step0Labels = labelEmbedding6 ∘ raw18285step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18285step0 raw18285step0Labels raw18285step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5341 node5341Labels := by rfl

def raw18286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw18286Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18286step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw18286step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18286step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18286step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18286step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18286step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18286 raw18286Labels = mixedMoment B node5351 node5351Labels := by
  calc
    mixedMoment B raw18286 raw18286Labels = mixedMoment B raw18286step0 raw18286step0Labels := by
      have ha : raw18286step0 = (fun i j => raw18286 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18286step0 raw18286; decide +kernel
      have hl : raw18286step0Labels = raw18286Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18286 raw18286Labels permutation686 permutation3
    mixedMoment B raw18286step0 raw18286step0Labels = mixedMoment B raw18286step1 raw18286step1Labels := by
      have ha : raw18286step1 = -raw18286step0 := by apply Matrix.ext; change ∀ i j, raw18286step1 i j = -(raw18286step0 i j); unfold raw18286step1 raw18286step0; decide +kernel
      have hl : raw18286step1Labels = raw18286step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18286step1 raw18286step1Labels = mixedMoment B raw18286step2 raw18286step2Labels := by
      have ha : raw18286step2 = raw18286step1 := by apply Matrix.ext; unfold raw18286step2 raw18286step1; decide +kernel
      have hl : raw18286step1Labels = labelEmbedding6 ∘ raw18286step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18286step1 raw18286step1Labels raw18286step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5351 node5351Labels := by rfl

def raw18287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -2, 0]]
def raw18287Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18287step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw18287step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18287step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw18287step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18287step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw18287step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18287 raw18287Labels = mixedMoment B node5344 node5344Labels := by
  calc
    mixedMoment B raw18287 raw18287Labels = mixedMoment B raw18287step0 raw18287step0Labels := by
      have ha : raw18287step0 = (fun i j => raw18287 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18287step0 raw18287; decide +kernel
      have hl : raw18287step0Labels = raw18287Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18287 raw18287Labels permutation680 permutation3
    mixedMoment B raw18287step0 raw18287step0Labels = mixedMoment B raw18287step1 raw18287step1Labels := by
      have ha : raw18287step1 = -raw18287step0 := by apply Matrix.ext; change ∀ i j, raw18287step1 i j = -(raw18287step0 i j); unfold raw18287step1 raw18287step0; decide +kernel
      have hl : raw18287step1Labels = raw18287step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18287step1 raw18287step1Labels = mixedMoment B raw18287step2 raw18287step2Labels := by
      have ha : raw18287step2 = raw18287step1 := by apply Matrix.ext; unfold raw18287step2 raw18287step1; decide +kernel
      have hl : raw18287step1Labels = labelEmbedding6 ∘ raw18287step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18287step1 raw18287step1Labels raw18287step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5344 node5344Labels := by rfl

def raw18288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw18288Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18288step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18288step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18288step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw18288step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18288 raw18288Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw18288 raw18288Labels = mixedMoment B raw18288step0 raw18288step0Labels := by
      have ha : raw18288step0 = (fun i j => raw18288 (permutation159 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18288step0 raw18288; decide +kernel
      have hl : raw18288step0Labels = raw18288Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18288 raw18288Labels permutation159 permutation3
    mixedMoment B raw18288step0 raw18288step0Labels = mixedMoment B raw18288step1 raw18288step1Labels := by
      have ha : raw18288step1 = raw18288step0 := by apply Matrix.ext; unfold raw18288step1 raw18288step0; decide +kernel
      have hl : raw18288step0Labels = labelEmbedding6 ∘ raw18288step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18288step0 raw18288step0Labels raw18288step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw18289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw18289Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18289step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw18289step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18289step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw18289step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18289 raw18289Labels = mixedMoment B node4778 node4778Labels := by
  calc
    mixedMoment B raw18289 raw18289Labels = mixedMoment B raw18289step0 raw18289step0Labels := by
      have ha : raw18289step0 = (fun i j => raw18289 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18289step0 raw18289; decide +kernel
      have hl : raw18289step0Labels = raw18289Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18289 raw18289Labels permutation158 permutation3
    mixedMoment B raw18289step0 raw18289step0Labels = mixedMoment B raw18289step1 raw18289step1Labels := by
      have ha : raw18289step1 = raw18289step0 := by apply Matrix.ext; unfold raw18289step1 raw18289step0; decide +kernel
      have hl : raw18289step0Labels = labelEmbedding6 ∘ raw18289step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18289step0 raw18289step0Labels raw18289step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4778 node4778Labels := by rfl

def raw18290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw18290Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18290step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw18290step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18290step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw18290step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18290step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw18290step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18290 raw18290Labels = mixedMoment B node4782 node4782Labels := by
  calc
    mixedMoment B raw18290 raw18290Labels = mixedMoment B raw18290step0 raw18290step0Labels := by
      have ha : raw18290step0 = (fun i j => raw18290 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18290step0 raw18290; decide +kernel
      have hl : raw18290step0Labels = raw18290Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18290 raw18290Labels permutation682 permutation3
    mixedMoment B raw18290step0 raw18290step0Labels = mixedMoment B raw18290step1 raw18290step1Labels := by
      have ha : raw18290step1 = -raw18290step0 := by apply Matrix.ext; change ∀ i j, raw18290step1 i j = -(raw18290step0 i j); unfold raw18290step1 raw18290step0; decide +kernel
      have hl : raw18290step1Labels = raw18290step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18290step1 raw18290step1Labels = mixedMoment B raw18290step2 raw18290step2Labels := by
      have ha : raw18290step2 = raw18290step1 := by apply Matrix.ext; unfold raw18290step2 raw18290step1; decide +kernel
      have hl : raw18290step1Labels = labelEmbedding6 ∘ raw18290step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18290step1 raw18290step1Labels raw18290step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4782 node4782Labels := by rfl

def raw18291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw18291Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18291step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw18291step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18291step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18291step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw18291step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18291step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18291 raw18291Labels = mixedMoment B node4801 node4801Labels := by
  calc
    mixedMoment B raw18291 raw18291Labels = mixedMoment B raw18291step0 raw18291step0Labels := by
      have ha : raw18291step0 = (fun i j => raw18291 (permutation686 i) (permutation3 j)) := by apply Matrix.ext; unfold raw18291step0 raw18291; decide +kernel
      have hl : raw18291step0Labels = raw18291Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18291 raw18291Labels permutation686 permutation3
    mixedMoment B raw18291step0 raw18291step0Labels = mixedMoment B raw18291step1 raw18291step1Labels := by
      have ha : raw18291step1 = -raw18291step0 := by apply Matrix.ext; change ∀ i j, raw18291step1 i j = -(raw18291step0 i j); unfold raw18291step1 raw18291step0; decide +kernel
      have hl : raw18291step1Labels = raw18291step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw18291step1 raw18291step1Labels = mixedMoment B raw18291step2 raw18291step2Labels := by
      have ha : raw18291step2 = raw18291step1 := by apply Matrix.ext; unfold raw18291step2 raw18291step1; decide +kernel
      have hl : raw18291step1Labels = labelEmbedding6 ∘ raw18291step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18291step1 raw18291step1Labels raw18291step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4801 node4801Labels := by rfl

def raw18292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 2, -1], ![1, 0, -1], ![3, -3, 0]]
def raw18292Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18292step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw18292step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18292step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw18292step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18292 raw18292Labels = mixedMoment B node4782 node4782Labels := by
  calc
    mixedMoment B raw18292 raw18292Labels = mixedMoment B raw18292step0 raw18292step0Labels := by
      have ha : raw18292step0 = (fun i j => raw18292 (permutation644 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18292step0 raw18292; decide +kernel
      have hl : raw18292step0Labels = raw18292Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18292 raw18292Labels permutation644 permutation5
    mixedMoment B raw18292step0 raw18292step0Labels = mixedMoment B raw18292step1 raw18292step1Labels := by
      have ha : raw18292step1 = raw18292step0 := by apply Matrix.ext; unfold raw18292step1 raw18292step0; decide +kernel
      have hl : raw18292step0Labels = labelEmbedding8 ∘ raw18292step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18292step0 raw18292step0Labels raw18292step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4782 node4782Labels := by rfl

def raw18293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw18293Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18293step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18293step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw18293step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18293step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18293 raw18293Labels = mixedMoment B node4801 node4801Labels := by
  calc
    mixedMoment B raw18293 raw18293Labels = mixedMoment B raw18293step0 raw18293step0Labels := by
      have ha : raw18293step0 = (fun i j => raw18293 (permutation632 i) (permutation5 j)) := by apply Matrix.ext; unfold raw18293step0 raw18293; decide +kernel
      have hl : raw18293step0Labels = raw18293Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18293 raw18293Labels permutation632 permutation5
    mixedMoment B raw18293step0 raw18293step0Labels = mixedMoment B raw18293step1 raw18293step1Labels := by
      have ha : raw18293step1 = raw18293step0 := by apply Matrix.ext; unfold raw18293step1 raw18293step0; decide +kernel
      have hl : raw18293step0Labels = labelEmbedding8 ∘ raw18293step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18293step0 raw18293step0Labels raw18293step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4801 node4801Labels := by rfl

def raw18294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18294Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18294step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18294step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-2, 2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18294step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18294step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0]]
def raw18294step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18294step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw18294step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18294 raw18294Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw18294 raw18294Labels = mixedMoment B raw18294step0 raw18294step0Labels := by
      have hz : ∀ j, raw18294 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18294step0 = (fun i j => raw18294 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18294step0 raw18294; decide +kernel
      have hl : raw18294step0Labels = raw18294Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18294 raw18294Labels permutation434 hz
    mixedMoment B raw18294step0 raw18294step0Labels = mixedMoment B raw18294step1 raw18294step1Labels := by
      have hz : ∀ j, raw18294step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18294step1 = (fun i j => raw18294step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18294step1 raw18294step0; decide +kernel
      have hl : raw18294step1Labels = raw18294step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18294step0 raw18294step0Labels permutation80 hz
    mixedMoment B raw18294step1 raw18294step1Labels = mixedMoment B raw18294step2 raw18294step2Labels := by
      have ha : raw18294step2 = (fun i j => raw18294step1 (permutation30 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18294step2 raw18294step1; decide +kernel
      have hl : raw18294step2Labels = raw18294step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18294step1 raw18294step1Labels permutation30 permutation2
    mixedMoment B raw18294step2 raw18294step2Labels = mixedMoment B raw18294step3 raw18294step3Labels := by
      have ha : raw18294step3 = -raw18294step2 := by apply Matrix.ext; change ∀ i j, raw18294step3 i j = -(raw18294step2 i j); unfold raw18294step3 raw18294step2; decide +kernel
      have hl : raw18294step3Labels = raw18294step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw18295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18295Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18295step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18295step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18295step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw18295step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18295step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18295step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18295 raw18295Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw18295 raw18295Labels = mixedMoment B raw18295step0 raw18295step0Labels := by
      have hz : ∀ j, raw18295 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18295step0 = (fun i j => raw18295 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18295step0 raw18295; decide +kernel
      have hl : raw18295step0Labels = raw18295Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18295 raw18295Labels permutation434 hz
    mixedMoment B raw18295step0 raw18295step0Labels = mixedMoment B raw18295step1 raw18295step1Labels := by
      have ha : raw18295step1 = (fun i j => raw18295step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18295step1 raw18295step0; decide +kernel
      have hl : raw18295step1Labels = raw18295step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18295step0 raw18295step0Labels permutation149 permutation2
    mixedMoment B raw18295step1 raw18295step1Labels = mixedMoment B raw18295step2 raw18295step2Labels := by
      have ha : raw18295step2 = -raw18295step1 := by apply Matrix.ext; change ∀ i j, raw18295step2 i j = -(raw18295step1 i j); unfold raw18295step2 raw18295step1; decide +kernel
      have hl : raw18295step2Labels = raw18295step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw18296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18296Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18296step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18296step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18296step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw18296step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18296step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18296step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18296 raw18296Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw18296 raw18296Labels = mixedMoment B raw18296step0 raw18296step0Labels := by
      have hz : ∀ j, raw18296 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18296step0 = (fun i j => raw18296 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18296step0 raw18296; decide +kernel
      have hl : raw18296step0Labels = raw18296Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18296 raw18296Labels permutation346 hz
    mixedMoment B raw18296step0 raw18296step0Labels = mixedMoment B raw18296step1 raw18296step1Labels := by
      have ha : raw18296step1 = (fun i j => raw18296step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18296step1 raw18296step0; decide +kernel
      have hl : raw18296step1Labels = raw18296step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18296step0 raw18296step0Labels permutation149 permutation2
    mixedMoment B raw18296step1 raw18296step1Labels = mixedMoment B raw18296step2 raw18296step2Labels := by
      have ha : raw18296step2 = -raw18296step1 := by apply Matrix.ext; change ∀ i j, raw18296step2 i j = -(raw18296step1 i j); unfold raw18296step2 raw18296step1; decide +kernel
      have hl : raw18296step2Labels = raw18296step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw18297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw18297Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw18297step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18297step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw18297step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18297step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![2, 0, -2]]
def raw18297step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18297step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw18297step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw18297step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![2, -1, -1]]
def raw18297step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18297 raw18297Labels = mixedMoment B node5455 node5455Labels := by
  calc
    mixedMoment B raw18297 raw18297Labels = mixedMoment B raw18297step0 raw18297step0Labels := by
      have hz : ∀ j, raw18297 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18297step0 = (fun i j => raw18297 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18297step0 raw18297; decide +kernel
      have hl : raw18297step0Labels = raw18297Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18297 raw18297Labels permutation520 hz
    mixedMoment B raw18297step0 raw18297step0Labels = mixedMoment B raw18297step1 raw18297step1Labels := by
      have hz : ∀ j, raw18297step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw18297step1 = (fun i j => raw18297step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw18297step1 raw18297step0; decide +kernel
      have hl : raw18297step1Labels = raw18297step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18297step0 raw18297step0Labels permutation104 hz
    mixedMoment B raw18297step1 raw18297step1Labels = mixedMoment B raw18297step2 raw18297step2Labels := by
      have hz : ∀ j, raw18297step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw18297step2 = (fun i j => raw18297step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw18297step2 raw18297step1; decide +kernel
      have hl : raw18297step2Labels = raw18297step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18297step1 raw18297step1Labels permutation20 hz
    mixedMoment B raw18297step2 raw18297step2Labels = mixedMoment B raw18297step3 raw18297step3Labels := by
      have ha : raw18297step3 = (fun i j => raw18297step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw18297step3 raw18297step2; decide +kernel
      have hl : raw18297step3Labels = raw18297step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18297step2 raw18297step2Labels permutation7 permutation7
    mixedMoment B raw18297step3 raw18297step3Labels = mixedMoment B raw18297step4 raw18297step4Labels := by
      have ha : raw18297step4 = raw18297step3 := by apply Matrix.ext; unfold raw18297step4 raw18297step3; decide +kernel
      have hl : raw18297step3Labels = labelEmbedding10 ∘ raw18297step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18297step3 raw18297step3Labels raw18297step4Labels labelEmbedding10 hl
    _ = mixedMoment B node5455 node5455Labels := by rfl

def raw18298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18298Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18298step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18298step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-1, -1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18298step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18298step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw18298step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw18298step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1]]
def raw18298step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18298 raw18298Labels = mixedMoment B node5491 node5491Labels := by
  calc
    mixedMoment B raw18298 raw18298Labels = mixedMoment B raw18298step0 raw18298step0Labels := by
      have hz : ∀ j, raw18298 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18298step0 = (fun i j => raw18298 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18298step0 raw18298; decide +kernel
      have hl : raw18298step0Labels = raw18298Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18298 raw18298Labels permutation434 hz
    mixedMoment B raw18298step0 raw18298step0Labels = mixedMoment B raw18298step1 raw18298step1Labels := by
      have hz : ∀ j, raw18298step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw18298step1 = (fun i j => raw18298step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw18298step1 raw18298step0; decide +kernel
      have hl : raw18298step1Labels = raw18298step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18298step0 raw18298step0Labels permutation80 hz
    mixedMoment B raw18298step1 raw18298step1Labels = mixedMoment B raw18298step2 raw18298step2Labels := by
      have ha : raw18298step2 = (fun i j => raw18298step1 (permutation29 i) (permutation6 j)) := by apply Matrix.ext; unfold raw18298step2 raw18298step1; decide +kernel
      have hl : raw18298step2Labels = raw18298step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18298step1 raw18298step1Labels permutation29 permutation6
    mixedMoment B raw18298step2 raw18298step2Labels = mixedMoment B raw18298step3 raw18298step3Labels := by
      have ha : raw18298step3 = raw18298step2 := by apply Matrix.ext; unfold raw18298step3 raw18298step2; decide +kernel
      have hl : raw18298step2Labels = labelEmbedding9 ∘ raw18298step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw18298step2 raw18298step2Labels raw18298step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5491 node5491Labels := by rfl

def raw18299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18299Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18299step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18299 raw18299Labels = mixedMoment B node5387 node5387Labels := by
  calc
    mixedMoment B raw18299 raw18299Labels = mixedMoment B raw18299step0 raw18299step0Labels := by
      have hz : ∀ j, raw18299 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18299step0 = (fun i j => raw18299 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18299step0 raw18299; decide +kernel
      have hl : raw18299step0Labels = raw18299Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18299 raw18299Labels permutation434 hz
    _ = mixedMoment B node5387 node5387Labels := by rfl

def raw18300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18300Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18300step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18300step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18300 raw18300Labels = mixedMoment B node5415 node5415Labels := by
  calc
    mixedMoment B raw18300 raw18300Labels = mixedMoment B raw18300step0 raw18300step0Labels := by
      have ha : raw18300step0 = (fun i j => raw18300 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw18300step0 raw18300; decide +kernel
      have hl : raw18300step0Labels = raw18300Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw18300 raw18300Labels permutation158 permutation2
    _ = mixedMoment B node5415 node5415Labels := by rfl

def raw18301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![2, 0, -2]]
def raw18301Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw18301step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18301step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18301step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18301 raw18301Labels = mixedMoment B node5441 node5441Labels := by
  calc
    mixedMoment B raw18301 raw18301Labels = mixedMoment B raw18301step0 raw18301step0Labels := by
      have hz : ∀ j, raw18301 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw18301step0 = (fun i j => raw18301 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw18301step0 raw18301; decide +kernel
      have hl : raw18301step0Labels = raw18301Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18301 raw18301Labels permutation520 hz
    mixedMoment B raw18301step0 raw18301step0Labels = mixedMoment B raw18301step1 raw18301step1Labels := by
      have hz : ∀ j, raw18301step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw18301step1 = (fun i j => raw18301step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw18301step1 raw18301step0; decide +kernel
      have hl : raw18301step1Labels = raw18301step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18301step0 raw18301step0Labels permutation104 hz
    _ = mixedMoment B node5441 node5441Labels := by rfl

def raw18302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18302Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw18302step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18302 raw18302Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw18302 raw18302Labels = mixedMoment B raw18302step0 raw18302step0Labels := by
      have hz : ∀ j, raw18302 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw18302step0 = (fun i j => raw18302 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw18302step0 raw18302; decide +kernel
      have hl : raw18302step0Labels = raw18302Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18302 raw18302Labels permutation434 hz
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw18303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18303Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw18303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw18303step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical18303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw18303 raw18303Labels = mixedMoment B node5387 node5387Labels := by
  calc
    mixedMoment B raw18303 raw18303Labels = mixedMoment B raw18303step0 raw18303step0Labels := by
      have hz : ∀ j, raw18303 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw18303step0 = (fun i j => raw18303 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw18303step0 raw18303; decide +kernel
      have hl : raw18303step0Labels = raw18303Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw18303 raw18303Labels permutation346 hz
    _ = mixedMoment B node5387 node5387Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
