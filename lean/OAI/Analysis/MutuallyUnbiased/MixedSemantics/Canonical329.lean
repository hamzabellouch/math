import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw42112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw42112Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw42112step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42112step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw42112step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42112step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw42112step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42112step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42112step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42112step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42112step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42112 raw42112Labels = mixedMoment B node3584 node3584Labels := by
  calc
    mixedMoment B raw42112 raw42112Labels = mixedMoment B raw42112step0 raw42112step0Labels := by
      have hz : ∀ j, raw42112 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42112step0 = (fun i j => raw42112 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42112step0 raw42112; decide +kernel
      have hl : raw42112step0Labels = raw42112Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42112 raw42112Labels permutation434 hz
    mixedMoment B raw42112step0 raw42112step0Labels = mixedMoment B raw42112step1 raw42112step1Labels := by
      have hz : ∀ j, raw42112step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42112step1 = (fun i j => raw42112step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42112step1 raw42112step0; decide +kernel
      have hl : raw42112step1Labels = raw42112step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42112step0 raw42112step0Labels permutation80 hz
    mixedMoment B raw42112step1 raw42112step1Labels = mixedMoment B raw42112step2 raw42112step2Labels := by
      have ha : raw42112step2 = (fun i j => raw42112step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42112step2 raw42112step1; decide +kernel
      have hl : raw42112step2Labels = raw42112step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42112step1 raw42112step1Labels permutation31 permutation2
    mixedMoment B raw42112step2 raw42112step2Labels = mixedMoment B raw42112step3 raw42112step3Labels := by
      have ha : raw42112step3 = -raw42112step2 := by apply Matrix.ext; change ∀ i j, raw42112step3 i j = -(raw42112step2 i j); unfold raw42112step3 raw42112step2; decide +kernel
      have hl : raw42112step3Labels = raw42112step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42112step3 raw42112step3Labels = mixedMoment B raw42112step4 raw42112step4Labels := by
      have ha : raw42112step4 = raw42112step3 := by apply Matrix.ext; unfold raw42112step4 raw42112step3; decide +kernel
      have hl : raw42112step3Labels = labelEmbedding1 ∘ raw42112step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42112step3 raw42112step3Labels raw42112step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3584 node3584Labels := by rfl

def raw42113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw42113Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42113step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, -2, 1], ![2, 1, -3]]
def raw42113step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42113step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -2, 1], ![2, 1, -3]]
def raw42113step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42113step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42113step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42113step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42113step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42113 raw42113Labels = mixedMoment B node5300 node5300Labels := by
  calc
    mixedMoment B raw42113 raw42113Labels = mixedMoment B raw42113step0 raw42113step0Labels := by
      have hz : ∀ j, raw42113 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42113step0 = (fun i j => raw42113 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42113step0 raw42113; decide +kernel
      have hl : raw42113step0Labels = raw42113Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42113 raw42113Labels permutation434 hz
    mixedMoment B raw42113step0 raw42113step0Labels = mixedMoment B raw42113step1 raw42113step1Labels := by
      have hz : ∀ j, raw42113step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42113step1 = (fun i j => raw42113step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42113step1 raw42113step0; decide +kernel
      have hl : raw42113step1Labels = raw42113step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42113step0 raw42113step0Labels permutation80 hz
    mixedMoment B raw42113step1 raw42113step1Labels = mixedMoment B raw42113step2 raw42113step2Labels := by
      have ha : raw42113step2 = (fun i j => raw42113step1 (permutation27 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42113step2 raw42113step1; decide +kernel
      have hl : raw42113step2Labels = raw42113step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42113step1 raw42113step1Labels permutation27 permutation7
    mixedMoment B raw42113step2 raw42113step2Labels = mixedMoment B raw42113step3 raw42113step3Labels := by
      have ha : raw42113step3 = raw42113step2 := by apply Matrix.ext; unfold raw42113step3 raw42113step2; decide +kernel
      have hl : raw42113step2Labels = labelEmbedding6 ∘ raw42113step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42113step2 raw42113step2Labels raw42113step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5300 node5300Labels := by rfl

def raw42114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw42114Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42114step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw42114step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42114step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw42114step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42114step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42114step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42114step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42114step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42114 raw42114Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw42114 raw42114Labels = mixedMoment B raw42114step0 raw42114step0Labels := by
      have hz : ∀ j, raw42114 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42114step0 = (fun i j => raw42114 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42114step0 raw42114; decide +kernel
      have hl : raw42114step0Labels = raw42114Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42114 raw42114Labels permutation346 hz
    mixedMoment B raw42114step0 raw42114step0Labels = mixedMoment B raw42114step1 raw42114step1Labels := by
      have ha : raw42114step1 = (fun i j => raw42114step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42114step1 raw42114step0; decide +kernel
      have hl : raw42114step1Labels = raw42114step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42114step0 raw42114step0Labels permutation151 permutation2
    mixedMoment B raw42114step1 raw42114step1Labels = mixedMoment B raw42114step2 raw42114step2Labels := by
      have ha : raw42114step2 = -raw42114step1 := by apply Matrix.ext; change ∀ i j, raw42114step2 i j = -(raw42114step1 i j); unfold raw42114step2 raw42114step1; decide +kernel
      have hl : raw42114step2Labels = raw42114step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42114step2 raw42114step2Labels = mixedMoment B raw42114step3 raw42114step3Labels := by
      have ha : raw42114step3 = raw42114step2 := by apply Matrix.ext; unfold raw42114step3 raw42114step2; decide +kernel
      have hl : raw42114step2Labels = labelEmbedding1 ∘ raw42114step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42114step2 raw42114step2Labels raw42114step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3535 node3535Labels := by rfl

def raw42115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw42115Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42115step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw42115step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42115step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42115step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42115step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42115step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42115 raw42115Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw42115 raw42115Labels = mixedMoment B raw42115step0 raw42115step0Labels := by
      have hz : ∀ j, raw42115 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42115step0 = (fun i j => raw42115 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42115step0 raw42115; decide +kernel
      have hl : raw42115step0Labels = raw42115Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42115 raw42115Labels permutation346 hz
    mixedMoment B raw42115step0 raw42115step0Labels = mixedMoment B raw42115step1 raw42115step1Labels := by
      have ha : raw42115step1 = (fun i j => raw42115step0 (permutation147 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42115step1 raw42115step0; decide +kernel
      have hl : raw42115step1Labels = raw42115step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42115step0 raw42115step0Labels permutation147 permutation7
    mixedMoment B raw42115step1 raw42115step1Labels = mixedMoment B raw42115step2 raw42115step2Labels := by
      have ha : raw42115step2 = raw42115step1 := by apply Matrix.ext; unfold raw42115step2 raw42115step1; decide +kernel
      have hl : raw42115step1Labels = labelEmbedding6 ∘ raw42115step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42115step1 raw42115step1Labels raw42115step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

def raw42116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw42116Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42116step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw42116step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42116step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42116step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42116step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42116step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42116 raw42116Labels = mixedMoment B node3959 node3959Labels := by
  calc
    mixedMoment B raw42116 raw42116Labels = mixedMoment B raw42116step0 raw42116step0Labels := by
      have hz : ∀ j, raw42116 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42116step0 = (fun i j => raw42116 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42116step0 raw42116; decide +kernel
      have hl : raw42116step0Labels = raw42116Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42116 raw42116Labels permutation346 hz
    mixedMoment B raw42116step0 raw42116step0Labels = mixedMoment B raw42116step1 raw42116step1Labels := by
      have ha : raw42116step1 = (fun i j => raw42116step0 (permutation139 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42116step1 raw42116step0; decide +kernel
      have hl : raw42116step1Labels = raw42116step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42116step0 raw42116step0Labels permutation139 permutation4
    mixedMoment B raw42116step1 raw42116step1Labels = mixedMoment B raw42116step2 raw42116step2Labels := by
      have ha : raw42116step2 = raw42116step1 := by apply Matrix.ext; unfold raw42116step2 raw42116step1; decide +kernel
      have hl : raw42116step1Labels = labelEmbedding1 ∘ raw42116step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42116step1 raw42116step1Labels raw42116step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3959 node3959Labels := by rfl

def raw42117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw42117Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw42117step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42117step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw42117step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42117step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42117step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42117step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42117step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42117 raw42117Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw42117 raw42117Labels = mixedMoment B raw42117step0 raw42117step0Labels := by
      have hz : ∀ j, raw42117 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42117step0 = (fun i j => raw42117 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42117step0 raw42117; decide +kernel
      have hl : raw42117step0Labels = raw42117Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42117 raw42117Labels permutation346 hz
    mixedMoment B raw42117step0 raw42117step0Labels = mixedMoment B raw42117step1 raw42117step1Labels := by
      have ha : raw42117step1 = (fun i j => raw42117step0 (permutation40 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42117step1 raw42117step0; decide +kernel
      have hl : raw42117step1Labels = raw42117step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42117step0 raw42117step0Labels permutation40 permutation5
    mixedMoment B raw42117step1 raw42117step1Labels = mixedMoment B raw42117step2 raw42117step2Labels := by
      have ha : raw42117step2 = -raw42117step1 := by apply Matrix.ext; change ∀ i j, raw42117step2 i j = -(raw42117step1 i j); unfold raw42117step2 raw42117step1; decide +kernel
      have hl : raw42117step2Labels = raw42117step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42117step2 raw42117step2Labels = mixedMoment B raw42117step3 raw42117step3Labels := by
      have ha : raw42117step3 = raw42117step2 := by apply Matrix.ext; unfold raw42117step3 raw42117step2; decide +kernel
      have hl : raw42117step2Labels = labelEmbedding9 ∘ raw42117step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42117step2 raw42117step2Labels raw42117step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

def raw42118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw42118Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42118step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw42118step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42118step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw42118step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42118step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw42118step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42118 raw42118Labels = mixedMoment B node4028 node4028Labels := by
  calc
    mixedMoment B raw42118 raw42118Labels = mixedMoment B raw42118step0 raw42118step0Labels := by
      have hz : ∀ j, raw42118 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42118step0 = (fun i j => raw42118 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42118step0 raw42118; decide +kernel
      have hl : raw42118step0Labels = raw42118Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42118 raw42118Labels permutation346 hz
    mixedMoment B raw42118step0 raw42118step0Labels = mixedMoment B raw42118step1 raw42118step1Labels := by
      have ha : raw42118step1 = (fun i j => raw42118step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42118step1 raw42118step0; decide +kernel
      have hl : raw42118step1Labels = raw42118step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42118step0 raw42118step0Labels permutation35 permutation2
    mixedMoment B raw42118step1 raw42118step1Labels = mixedMoment B raw42118step2 raw42118step2Labels := by
      have ha : raw42118step2 = raw42118step1 := by apply Matrix.ext; unfold raw42118step2 raw42118step1; decide +kernel
      have hl : raw42118step1Labels = labelEmbedding1 ∘ raw42118step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42118step1 raw42118step1Labels raw42118step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4028 node4028Labels := by rfl

def raw42119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw42119Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42119step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, 1, -2], ![1, -1, 0], ![1, -1, 0]]
def raw42119step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42119step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42119step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42119step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42119step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42119 raw42119Labels = mixedMoment B node5448 node5448Labels := by
  calc
    mixedMoment B raw42119 raw42119Labels = mixedMoment B raw42119step0 raw42119step0Labels := by
      have hz : ∀ j, raw42119 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42119step0 = (fun i j => raw42119 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42119step0 raw42119; decide +kernel
      have hl : raw42119step0Labels = raw42119Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42119 raw42119Labels permutation346 hz
    mixedMoment B raw42119step0 raw42119step0Labels = mixedMoment B raw42119step1 raw42119step1Labels := by
      have ha : raw42119step1 = (fun i j => raw42119step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42119step1 raw42119step0; decide +kernel
      have hl : raw42119step1Labels = raw42119step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42119step0 raw42119step0Labels permutation32 permutation3
    mixedMoment B raw42119step1 raw42119step1Labels = mixedMoment B raw42119step2 raw42119step2Labels := by
      have ha : raw42119step2 = raw42119step1 := by apply Matrix.ext; unfold raw42119step2 raw42119step1; decide +kernel
      have hl : raw42119step1Labels = labelEmbedding7 ∘ raw42119step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42119step1 raw42119step1Labels raw42119step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5448 node5448Labels := by rfl

def raw42120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42120Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42120step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42120step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42120step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42120step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42120 raw42120Labels = mixedMoment B node4024 node4024Labels := by
  calc
    mixedMoment B raw42120 raw42120Labels = mixedMoment B raw42120step0 raw42120step0Labels := by
      have ha : raw42120step0 = (fun i j => raw42120 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42120step0 raw42120; decide +kernel
      have hl : raw42120step0Labels = raw42120Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42120 raw42120Labels permutation157 permutation2
    mixedMoment B raw42120step0 raw42120step0Labels = mixedMoment B raw42120step1 raw42120step1Labels := by
      have ha : raw42120step1 = raw42120step0 := by apply Matrix.ext; unfold raw42120step1 raw42120step0; decide +kernel
      have hl : raw42120step0Labels = labelEmbedding1 ∘ raw42120step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42120step0 raw42120step0Labels raw42120step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4024 node4024Labels := by rfl

def raw42121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42121Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42121step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42121step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42121step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42121step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42121 raw42121Labels = mixedMoment B node5445 node5445Labels := by
  calc
    mixedMoment B raw42121 raw42121Labels = mixedMoment B raw42121step0 raw42121step0Labels := by
      have ha : raw42121step0 = (fun i j => raw42121 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42121step0 raw42121; decide +kernel
      have hl : raw42121step0Labels = raw42121Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42121 raw42121Labels permutation152 permutation3
    mixedMoment B raw42121step0 raw42121step0Labels = mixedMoment B raw42121step1 raw42121step1Labels := by
      have ha : raw42121step1 = raw42121step0 := by apply Matrix.ext; unfold raw42121step1 raw42121step0; decide +kernel
      have hl : raw42121step0Labels = labelEmbedding7 ∘ raw42121step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42121step0 raw42121step0Labels raw42121step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5445 node5445Labels := by rfl

def raw42122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42122Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42122step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42122step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42122step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42122step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42122step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42122 raw42122Labels = mixedMoment B node3541 node3541Labels := by
  calc
    mixedMoment B raw42122 raw42122Labels = mixedMoment B raw42122step0 raw42122step0Labels := by
      have hz : ∀ j, raw42122 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42122step0 = (fun i j => raw42122 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42122step0 raw42122; decide +kernel
      have hl : raw42122step0Labels = raw42122Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42122 raw42122Labels permutation434 hz
    mixedMoment B raw42122step0 raw42122step0Labels = mixedMoment B raw42122step1 raw42122step1Labels := by
      have ha : raw42122step1 = (fun i j => raw42122step0 (permutation73 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42122step1 raw42122step0; decide +kernel
      have hl : raw42122step1Labels = raw42122step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42122step0 raw42122step0Labels permutation73 permutation4
    mixedMoment B raw42122step1 raw42122step1Labels = mixedMoment B raw42122step2 raw42122step2Labels := by
      have ha : raw42122step2 = raw42122step1 := by apply Matrix.ext; unfold raw42122step2 raw42122step1; decide +kernel
      have hl : raw42122step1Labels = labelEmbedding1 ∘ raw42122step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42122step1 raw42122step1Labels raw42122step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3541 node3541Labels := by rfl

def raw42123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw42123Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42123step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw42123step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42123step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 2, 0]]
def raw42123step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42123step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw42123step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42123 raw42123Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw42123 raw42123Labels = mixedMoment B raw42123step0 raw42123step0Labels := by
      have hz : ∀ j, raw42123 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42123step0 = (fun i j => raw42123 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42123step0 raw42123; decide +kernel
      have hl : raw42123step0Labels = raw42123Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42123 raw42123Labels permutation434 hz
    mixedMoment B raw42123step0 raw42123step0Labels = mixedMoment B raw42123step1 raw42123step1Labels := by
      have ha : raw42123step1 = (fun i j => raw42123step0 (permutation68 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42123step1 raw42123step0; decide +kernel
      have hl : raw42123step1Labels = raw42123step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42123step0 raw42123step0Labels permutation68 permutation6
    mixedMoment B raw42123step1 raw42123step1Labels = mixedMoment B raw42123step2 raw42123step2Labels := by
      have ha : raw42123step2 = -raw42123step1 := by apply Matrix.ext; change ∀ i j, raw42123step2 i j = -(raw42123step1 i j); unfold raw42123step2 raw42123step1; decide +kernel
      have hl : raw42123step2Labels = raw42123step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5267 node5267Labels := by rfl

def raw42124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42124Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42124step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42124step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42124step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42124step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42124 raw42124Labels = mixedMoment B node3526 node3526Labels := by
  calc
    mixedMoment B raw42124 raw42124Labels = mixedMoment B raw42124step0 raw42124step0Labels := by
      have ha : raw42124step0 = (fun i j => raw42124 (permutation343 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42124step0 raw42124; decide +kernel
      have hl : raw42124step0Labels = raw42124Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42124 raw42124Labels permutation343 permutation4
    mixedMoment B raw42124step0 raw42124step0Labels = mixedMoment B raw42124step1 raw42124step1Labels := by
      have ha : raw42124step1 = raw42124step0 := by apply Matrix.ext; unfold raw42124step1 raw42124step0; decide +kernel
      have hl : raw42124step0Labels = labelEmbedding1 ∘ raw42124step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42124step0 raw42124step0Labels raw42124step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3526 node3526Labels := by rfl

def raw42125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42125Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42125step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw42125step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42125step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42125step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42125 raw42125Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw42125 raw42125Labels = mixedMoment B raw42125step0 raw42125step0Labels := by
      have ha : raw42125step0 = (fun i j => raw42125 (permutation336 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42125step0 raw42125; decide +kernel
      have hl : raw42125step0Labels = raw42125Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42125 raw42125Labels permutation336 permutation6
    mixedMoment B raw42125step0 raw42125step0Labels = mixedMoment B raw42125step1 raw42125step1Labels := by
      have ha : raw42125step1 = -raw42125step0 := by apply Matrix.ext; change ∀ i j, raw42125step1 i j = -(raw42125step0 i j); unfold raw42125step1 raw42125step0; decide +kernel
      have hl : raw42125step1Labels = raw42125step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5265 node5265Labels := by rfl

def raw42126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw42126Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42126step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw42126step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42126step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, -1, 0], ![2, 1, -3]]
def raw42126step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42126step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, -2, 3], ![-2, 2, 0]]
def raw42126step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42126step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw42126step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42126step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw42126step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42126 raw42126Labels = mixedMoment B node3549 node3549Labels := by
  calc
    mixedMoment B raw42126 raw42126Labels = mixedMoment B raw42126step0 raw42126step0Labels := by
      have hz : ∀ j, raw42126 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42126step0 = (fun i j => raw42126 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42126step0 raw42126; decide +kernel
      have hl : raw42126step0Labels = raw42126Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42126 raw42126Labels permutation434 hz
    mixedMoment B raw42126step0 raw42126step0Labels = mixedMoment B raw42126step1 raw42126step1Labels := by
      have hz : ∀ j, raw42126step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42126step1 = (fun i j => raw42126step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42126step1 raw42126step0; decide +kernel
      have hl : raw42126step1Labels = raw42126step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42126step0 raw42126step0Labels permutation80 hz
    mixedMoment B raw42126step1 raw42126step1Labels = mixedMoment B raw42126step2 raw42126step2Labels := by
      have ha : raw42126step2 = (fun i j => raw42126step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42126step2 raw42126step1; decide +kernel
      have hl : raw42126step2Labels = raw42126step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42126step1 raw42126step1Labels permutation31 permutation2
    mixedMoment B raw42126step2 raw42126step2Labels = mixedMoment B raw42126step3 raw42126step3Labels := by
      have ha : raw42126step3 = -raw42126step2 := by apply Matrix.ext; change ∀ i j, raw42126step3 i j = -(raw42126step2 i j); unfold raw42126step3 raw42126step2; decide +kernel
      have hl : raw42126step3Labels = raw42126step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42126step3 raw42126step3Labels = mixedMoment B raw42126step4 raw42126step4Labels := by
      have ha : raw42126step4 = raw42126step3 := by apply Matrix.ext; unfold raw42126step4 raw42126step3; decide +kernel
      have hl : raw42126step3Labels = labelEmbedding1 ∘ raw42126step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42126step3 raw42126step3Labels raw42126step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3549 node3549Labels := by rfl

def raw42127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw42127Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42127step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw42127step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42127step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, -1, 0], ![2, 1, -3]]
def raw42127step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42127step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-3, 2, 1]]
def raw42127step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42127step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![3, -2, -1]]
def raw42127step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42127 raw42127Labels = mixedMoment B node5268 node5268Labels := by
  calc
    mixedMoment B raw42127 raw42127Labels = mixedMoment B raw42127step0 raw42127step0Labels := by
      have hz : ∀ j, raw42127 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42127step0 = (fun i j => raw42127 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42127step0 raw42127; decide +kernel
      have hl : raw42127step0Labels = raw42127Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42127 raw42127Labels permutation434 hz
    mixedMoment B raw42127step0 raw42127step0Labels = mixedMoment B raw42127step1 raw42127step1Labels := by
      have hz : ∀ j, raw42127step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42127step1 = (fun i j => raw42127step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42127step1 raw42127step0; decide +kernel
      have hl : raw42127step1Labels = raw42127step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42127step0 raw42127step0Labels permutation80 hz
    mixedMoment B raw42127step1 raw42127step1Labels = mixedMoment B raw42127step2 raw42127step2Labels := by
      have ha : raw42127step2 = (fun i j => raw42127step1 (permutation16 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42127step2 raw42127step1; decide +kernel
      have hl : raw42127step2Labels = raw42127step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42127step1 raw42127step1Labels permutation16 permutation6
    mixedMoment B raw42127step2 raw42127step2Labels = mixedMoment B raw42127step3 raw42127step3Labels := by
      have ha : raw42127step3 = -raw42127step2 := by apply Matrix.ext; change ∀ i j, raw42127step3 i j = -(raw42127step2 i j); unfold raw42127step3 raw42127step2; decide +kernel
      have hl : raw42127step3Labels = raw42127step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5268 node5268Labels := by rfl

def raw42128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42128Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42128step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42128step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42128step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42128step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42128step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42128 raw42128Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw42128 raw42128Labels = mixedMoment B raw42128step0 raw42128step0Labels := by
      have hz : ∀ j, raw42128 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42128step0 = (fun i j => raw42128 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42128step0 raw42128; decide +kernel
      have hl : raw42128step0Labels = raw42128Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42128 raw42128Labels permutation346 hz
    mixedMoment B raw42128step0 raw42128step0Labels = mixedMoment B raw42128step1 raw42128step1Labels := by
      have ha : raw42128step1 = (fun i j => raw42128step0 (permutation79 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42128step1 raw42128step0; decide +kernel
      have hl : raw42128step1Labels = raw42128step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42128step0 raw42128step0Labels permutation79 permutation4
    mixedMoment B raw42128step1 raw42128step1Labels = mixedMoment B raw42128step2 raw42128step2Labels := by
      have ha : raw42128step2 = raw42128step1 := by apply Matrix.ext; unfold raw42128step2 raw42128step1; decide +kernel
      have hl : raw42128step1Labels = labelEmbedding1 ∘ raw42128step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42128step1 raw42128step1Labels raw42128step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3535 node3535Labels := by rfl

def raw42129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42129Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42129step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42129step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42129step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw42129step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw42129step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42129step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42129 raw42129Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw42129 raw42129Labels = mixedMoment B raw42129step0 raw42129step0Labels := by
      have hz : ∀ j, raw42129 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42129step0 = (fun i j => raw42129 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42129step0 raw42129; decide +kernel
      have hl : raw42129step0Labels = raw42129Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42129 raw42129Labels permutation346 hz
    mixedMoment B raw42129step0 raw42129step0Labels = mixedMoment B raw42129step1 raw42129step1Labels := by
      have ha : raw42129step1 = (fun i j => raw42129step0 (permutation75 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42129step1 raw42129step0; decide +kernel
      have hl : raw42129step1Labels = raw42129step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42129step0 raw42129step0Labels permutation75 permutation6
    mixedMoment B raw42129step1 raw42129step1Labels = mixedMoment B raw42129step2 raw42129step2Labels := by
      have ha : raw42129step2 = -raw42129step1 := by apply Matrix.ext; change ∀ i j, raw42129step2 i j = -(raw42129step1 i j); unfold raw42129step2 raw42129step1; decide +kernel
      have hl : raw42129step2Labels = raw42129step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5266 node5266Labels := by rfl

def raw42130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42130Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42130step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42130step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![3, -3, 0]]
def raw42130step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42130step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![3, -3, 0]]
def raw42130step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42130step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, -3, 0], ![-1, 2, -1], ![-2, 1, 1]]
def raw42130step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42130step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42130step4Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42130step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 3, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42130step5Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42130 raw42130Labels = mixedMoment B node3231 node3231Labels := by
  calc
    mixedMoment B raw42130 raw42130Labels = mixedMoment B raw42130step0 raw42130step0Labels := by
      have hz : ∀ j, raw42130 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42130step0 = (fun i j => raw42130 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42130step0 raw42130; decide +kernel
      have hl : raw42130step0Labels = raw42130Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42130 raw42130Labels permutation520 hz
    mixedMoment B raw42130step0 raw42130step0Labels = mixedMoment B raw42130step1 raw42130step1Labels := by
      have hz : ∀ j, raw42130step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw42130step1 = (fun i j => raw42130step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw42130step1 raw42130step0; decide +kernel
      have hl : raw42130step1Labels = raw42130step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42130step0 raw42130step0Labels permutation104 hz
    mixedMoment B raw42130step1 raw42130step1Labels = mixedMoment B raw42130step2 raw42130step2Labels := by
      have hz : ∀ j, raw42130step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw42130step2 = (fun i j => raw42130step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw42130step2 raw42130step1; decide +kernel
      have hl : raw42130step2Labels = raw42130step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42130step1 raw42130step1Labels permutation20 hz
    mixedMoment B raw42130step2 raw42130step2Labels = mixedMoment B raw42130step3 raw42130step3Labels := by
      have ha : raw42130step3 = (fun i j => raw42130step2 (permutation7 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42130step3 raw42130step2; decide +kernel
      have hl : raw42130step3Labels = raw42130step2Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42130step2 raw42130step2Labels permutation7 permutation2
    mixedMoment B raw42130step3 raw42130step3Labels = mixedMoment B raw42130step4 raw42130step4Labels := by
      have ha : raw42130step4 = -raw42130step3 := by apply Matrix.ext; change ∀ i j, raw42130step4 i j = -(raw42130step3 i j); unfold raw42130step4 raw42130step3; decide +kernel
      have hl : raw42130step4Labels = raw42130step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42130step4 raw42130step4Labels = mixedMoment B raw42130step5 raw42130step5Labels := by
      have ha : raw42130step5 = raw42130step4 := by apply Matrix.ext; unfold raw42130step5 raw42130step4; decide +kernel
      have hl : raw42130step4Labels = labelEmbedding1 ∘ raw42130step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42130step4 raw42130step4Labels raw42130step5Labels labelEmbedding1 hl
    _ = mixedMoment B node3231 node3231Labels := by rfl

def raw42131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42131Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42131step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42131step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42131step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![3, -3, 0]]
def raw42131step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42131step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![3, -3, 0]]
def raw42131step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42131step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![3, 0, -3], ![-1, -1, 2], ![-2, 1, 1]]
def raw42131step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42131step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw42131step4Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42131step5 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![1, 1, -2], ![2, -1, -1]]
def raw42131step5Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42131 raw42131Labels = mixedMoment B node4901 node4901Labels := by
  calc
    mixedMoment B raw42131 raw42131Labels = mixedMoment B raw42131step0 raw42131step0Labels := by
      have hz : ∀ j, raw42131 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42131step0 = (fun i j => raw42131 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42131step0 raw42131; decide +kernel
      have hl : raw42131step0Labels = raw42131Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42131 raw42131Labels permutation520 hz
    mixedMoment B raw42131step0 raw42131step0Labels = mixedMoment B raw42131step1 raw42131step1Labels := by
      have hz : ∀ j, raw42131step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw42131step1 = (fun i j => raw42131step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw42131step1 raw42131step0; decide +kernel
      have hl : raw42131step1Labels = raw42131step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42131step0 raw42131step0Labels permutation104 hz
    mixedMoment B raw42131step1 raw42131step1Labels = mixedMoment B raw42131step2 raw42131step2Labels := by
      have hz : ∀ j, raw42131step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw42131step2 = (fun i j => raw42131step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw42131step2 raw42131step1; decide +kernel
      have hl : raw42131step2Labels = raw42131step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42131step1 raw42131step1Labels permutation20 hz
    mixedMoment B raw42131step2 raw42131step2Labels = mixedMoment B raw42131step3 raw42131step3Labels := by
      have ha : raw42131step3 = (fun i j => raw42131step2 (permutation7 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42131step3 raw42131step2; decide +kernel
      have hl : raw42131step3Labels = raw42131step2Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42131step2 raw42131step2Labels permutation7 permutation3
    mixedMoment B raw42131step3 raw42131step3Labels = mixedMoment B raw42131step4 raw42131step4Labels := by
      have ha : raw42131step4 = -raw42131step3 := by apply Matrix.ext; change ∀ i j, raw42131step4 i j = -(raw42131step3 i j); unfold raw42131step4 raw42131step3; decide +kernel
      have hl : raw42131step4Labels = raw42131step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42131step4 raw42131step4Labels = mixedMoment B raw42131step5 raw42131step5Labels := by
      have ha : raw42131step5 = raw42131step4 := by apply Matrix.ext; unfold raw42131step5 raw42131step4; decide +kernel
      have hl : raw42131step4Labels = labelEmbedding7 ∘ raw42131step5Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42131step4 raw42131step4Labels raw42131step5Labels labelEmbedding7 hl
    _ = mixedMoment B node4901 node4901Labels := by rfl

def raw42132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42132Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42132step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42132step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42132step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -3, 1]]
def raw42132step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42132step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42132step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42132step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42132step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42132 raw42132Labels = mixedMoment B node3110 node3110Labels := by
  calc
    mixedMoment B raw42132 raw42132Labels = mixedMoment B raw42132step0 raw42132step0Labels := by
      have hz : ∀ j, raw42132 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42132step0 = (fun i j => raw42132 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42132step0 raw42132; decide +kernel
      have hl : raw42132step0Labels = raw42132Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42132 raw42132Labels permutation434 hz
    mixedMoment B raw42132step0 raw42132step0Labels = mixedMoment B raw42132step1 raw42132step1Labels := by
      have hz : ∀ j, raw42132step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42132step1 = (fun i j => raw42132step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42132step1 raw42132step0; decide +kernel
      have hl : raw42132step1Labels = raw42132step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42132step0 raw42132step0Labels permutation80 hz
    mixedMoment B raw42132step1 raw42132step1Labels = mixedMoment B raw42132step2 raw42132step2Labels := by
      have ha : raw42132step2 = (fun i j => raw42132step1 (permutation30 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42132step2 raw42132step1; decide +kernel
      have hl : raw42132step2Labels = raw42132step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42132step1 raw42132step1Labels permutation30 permutation4
    mixedMoment B raw42132step2 raw42132step2Labels = mixedMoment B raw42132step3 raw42132step3Labels := by
      have ha : raw42132step3 = raw42132step2 := by apply Matrix.ext; unfold raw42132step3 raw42132step2; decide +kernel
      have hl : raw42132step2Labels = labelEmbedding1 ∘ raw42132step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42132step2 raw42132step2Labels raw42132step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3110 node3110Labels := by rfl

def raw42133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42133Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42133step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42133step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42133step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, 0, -1], ![2, -3, 1]]
def raw42133step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42133step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42133step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42133step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42133step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42133 raw42133Labels = mixedMoment B node5275 node5275Labels := by
  calc
    mixedMoment B raw42133 raw42133Labels = mixedMoment B raw42133step0 raw42133step0Labels := by
      have hz : ∀ j, raw42133 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42133step0 = (fun i j => raw42133 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42133step0 raw42133; decide +kernel
      have hl : raw42133step0Labels = raw42133Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42133 raw42133Labels permutation434 hz
    mixedMoment B raw42133step0 raw42133step0Labels = mixedMoment B raw42133step1 raw42133step1Labels := by
      have hz : ∀ j, raw42133step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42133step1 = (fun i j => raw42133step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42133step1 raw42133step0; decide +kernel
      have hl : raw42133step1Labels = raw42133step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42133step0 raw42133step0Labels permutation80 hz
    mixedMoment B raw42133step1 raw42133step1Labels = mixedMoment B raw42133step2 raw42133step2Labels := by
      have ha : raw42133step2 = (fun i j => raw42133step1 (permutation30 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42133step2 raw42133step1; decide +kernel
      have hl : raw42133step2Labels = raw42133step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42133step1 raw42133step1Labels permutation30 permutation5
    mixedMoment B raw42133step2 raw42133step2Labels = mixedMoment B raw42133step3 raw42133step3Labels := by
      have ha : raw42133step3 = raw42133step2 := by apply Matrix.ext; unfold raw42133step3 raw42133step2; decide +kernel
      have hl : raw42133step2Labels = labelEmbedding9 ∘ raw42133step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42133step2 raw42133step2Labels raw42133step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5275 node5275Labels := by rfl

def raw42134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42134Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42134step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42134step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42134step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42134step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42134step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42134step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42134 raw42134Labels = mixedMoment B node4006 node4006Labels := by
  calc
    mixedMoment B raw42134 raw42134Labels = mixedMoment B raw42134step0 raw42134step0Labels := by
      have hz : ∀ j, raw42134 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42134step0 = (fun i j => raw42134 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42134step0 raw42134; decide +kernel
      have hl : raw42134step0Labels = raw42134Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42134 raw42134Labels permutation434 hz
    mixedMoment B raw42134step0 raw42134step0Labels = mixedMoment B raw42134step1 raw42134step1Labels := by
      have hz : ∀ j, raw42134step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42134step1 = (fun i j => raw42134step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42134step1 raw42134step0; decide +kernel
      have hl : raw42134step1Labels = raw42134step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42134step0 raw42134step0Labels permutation80 hz
    mixedMoment B raw42134step1 raw42134step1Labels = mixedMoment B raw42134step2 raw42134step2Labels := by
      have ha : raw42134step2 = raw42134step1 := by apply Matrix.ext; unfold raw42134step2 raw42134step1; decide +kernel
      have hl : raw42134step1Labels = labelEmbedding1 ∘ raw42134step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42134step1 raw42134step1Labels raw42134step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4006 node4006Labels := by rfl

def raw42135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42135Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42135step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42135step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42135step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42135step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw42135step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42135step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42135step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42135step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42135step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42135 raw42135Labels = mixedMoment B node5413 node5413Labels := by
  calc
    mixedMoment B raw42135 raw42135Labels = mixedMoment B raw42135step0 raw42135step0Labels := by
      have hz : ∀ j, raw42135 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42135step0 = (fun i j => raw42135 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42135step0 raw42135; decide +kernel
      have hl : raw42135step0Labels = raw42135Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42135 raw42135Labels permutation434 hz
    mixedMoment B raw42135step0 raw42135step0Labels = mixedMoment B raw42135step1 raw42135step1Labels := by
      have hz : ∀ j, raw42135step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42135step1 = (fun i j => raw42135step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42135step1 raw42135step0; decide +kernel
      have hl : raw42135step1Labels = raw42135step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42135step0 raw42135step0Labels permutation80 hz
    mixedMoment B raw42135step1 raw42135step1Labels = mixedMoment B raw42135step2 raw42135step2Labels := by
      have ha : raw42135step2 = (fun i j => raw42135step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42135step2 raw42135step1; decide +kernel
      have hl : raw42135step2Labels = raw42135step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42135step1 raw42135step1Labels permutation31 permutation3
    mixedMoment B raw42135step2 raw42135step2Labels = mixedMoment B raw42135step3 raw42135step3Labels := by
      have ha : raw42135step3 = -raw42135step2 := by apply Matrix.ext; change ∀ i j, raw42135step3 i j = -(raw42135step2 i j); unfold raw42135step3 raw42135step2; decide +kernel
      have hl : raw42135step3Labels = raw42135step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42135step3 raw42135step3Labels = mixedMoment B raw42135step4 raw42135step4Labels := by
      have ha : raw42135step4 = raw42135step3 := by apply Matrix.ext; unfold raw42135step4 raw42135step3; decide +kernel
      have hl : raw42135step3Labels = labelEmbedding7 ∘ raw42135step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42135step3 raw42135step3Labels raw42135step4Labels labelEmbedding7 hl
    _ = mixedMoment B node5413 node5413Labels := by rfl

def raw42136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42136Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42136step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42136step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42136step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42136step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42136step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42136step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42136 raw42136Labels = mixedMoment B node4004 node4004Labels := by
  calc
    mixedMoment B raw42136 raw42136Labels = mixedMoment B raw42136step0 raw42136step0Labels := by
      have hz : ∀ j, raw42136 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42136step0 = (fun i j => raw42136 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42136step0 raw42136; decide +kernel
      have hl : raw42136step0Labels = raw42136Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42136 raw42136Labels permutation434 hz
    mixedMoment B raw42136step0 raw42136step0Labels = mixedMoment B raw42136step1 raw42136step1Labels := by
      have hz : ∀ j, raw42136step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42136step1 = (fun i j => raw42136step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42136step1 raw42136step0; decide +kernel
      have hl : raw42136step1Labels = raw42136step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42136step0 raw42136step0Labels permutation80 hz
    mixedMoment B raw42136step1 raw42136step1Labels = mixedMoment B raw42136step2 raw42136step2Labels := by
      have ha : raw42136step2 = raw42136step1 := by apply Matrix.ext; unfold raw42136step2 raw42136step1; decide +kernel
      have hl : raw42136step1Labels = labelEmbedding1 ∘ raw42136step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42136step1 raw42136step1Labels raw42136step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4004 node4004Labels := by rfl

def raw42137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42137Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42137step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42137step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42137step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42137step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42137step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw42137step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42137step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 1, -2], ![2, -1, -1]]
def raw42137step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42137 raw42137Labels = mixedMoment B node5475 node5475Labels := by
  calc
    mixedMoment B raw42137 raw42137Labels = mixedMoment B raw42137step0 raw42137step0Labels := by
      have hz : ∀ j, raw42137 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42137step0 = (fun i j => raw42137 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42137step0 raw42137; decide +kernel
      have hl : raw42137step0Labels = raw42137Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42137 raw42137Labels permutation434 hz
    mixedMoment B raw42137step0 raw42137step0Labels = mixedMoment B raw42137step1 raw42137step1Labels := by
      have hz : ∀ j, raw42137step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42137step1 = (fun i j => raw42137step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42137step1 raw42137step0; decide +kernel
      have hl : raw42137step1Labels = raw42137step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42137step0 raw42137step0Labels permutation80 hz
    mixedMoment B raw42137step1 raw42137step1Labels = mixedMoment B raw42137step2 raw42137step2Labels := by
      have ha : raw42137step2 = (fun i j => raw42137step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42137step2 raw42137step1; decide +kernel
      have hl : raw42137step2Labels = raw42137step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42137step1 raw42137step1Labels permutation8 permutation3
    mixedMoment B raw42137step2 raw42137step2Labels = mixedMoment B raw42137step3 raw42137step3Labels := by
      have ha : raw42137step3 = raw42137step2 := by apply Matrix.ext; unfold raw42137step3 raw42137step2; decide +kernel
      have hl : raw42137step2Labels = labelEmbedding7 ∘ raw42137step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42137step2 raw42137step2Labels raw42137step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5475 node5475Labels := by rfl

def raw42138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw42138Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42138step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw42138step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42138step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -3, 2], ![2, 0, -2]]
def raw42138step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42138step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42138step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42138step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42138step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42138 raw42138Labels = mixedMoment B node2774 node2774Labels := by
  calc
    mixedMoment B raw42138 raw42138Labels = mixedMoment B raw42138step0 raw42138step0Labels := by
      have hz : ∀ j, raw42138 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42138step0 = (fun i j => raw42138 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42138step0 raw42138; decide +kernel
      have hl : raw42138step0Labels = raw42138Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42138 raw42138Labels permutation434 hz
    mixedMoment B raw42138step0 raw42138step0Labels = mixedMoment B raw42138step1 raw42138step1Labels := by
      have hz : ∀ j, raw42138step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42138step1 = (fun i j => raw42138step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42138step1 raw42138step0; decide +kernel
      have hl : raw42138step1Labels = raw42138step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42138step0 raw42138step0Labels permutation80 hz
    mixedMoment B raw42138step1 raw42138step1Labels = mixedMoment B raw42138step2 raw42138step2Labels := by
      have ha : raw42138step2 = (fun i j => raw42138step1 (permutation24 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42138step2 raw42138step1; decide +kernel
      have hl : raw42138step2Labels = raw42138step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42138step1 raw42138step1Labels permutation24 permutation4
    mixedMoment B raw42138step2 raw42138step2Labels = mixedMoment B raw42138step3 raw42138step3Labels := by
      have ha : raw42138step3 = raw42138step2 := by apply Matrix.ext; unfold raw42138step3 raw42138step2; decide +kernel
      have hl : raw42138step2Labels = labelEmbedding1 ∘ raw42138step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42138step2 raw42138step2Labels raw42138step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2774 node2774Labels := by rfl

def raw42139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw42139Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42139step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw42139step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42139step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -3, 2], ![2, 0, -2]]
def raw42139step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42139step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42139step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42139step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42139step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42139 raw42139Labels = mixedMoment B node5300 node5300Labels := by
  calc
    mixedMoment B raw42139 raw42139Labels = mixedMoment B raw42139step0 raw42139step0Labels := by
      have hz : ∀ j, raw42139 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42139step0 = (fun i j => raw42139 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42139step0 raw42139; decide +kernel
      have hl : raw42139step0Labels = raw42139Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42139 raw42139Labels permutation434 hz
    mixedMoment B raw42139step0 raw42139step0Labels = mixedMoment B raw42139step1 raw42139step1Labels := by
      have hz : ∀ j, raw42139step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42139step1 = (fun i j => raw42139step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42139step1 raw42139step0; decide +kernel
      have hl : raw42139step1Labels = raw42139step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42139step0 raw42139step0Labels permutation80 hz
    mixedMoment B raw42139step1 raw42139step1Labels = mixedMoment B raw42139step2 raw42139step2Labels := by
      have ha : raw42139step2 = (fun i j => raw42139step1 (permutation24 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42139step2 raw42139step1; decide +kernel
      have hl : raw42139step2Labels = raw42139step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42139step1 raw42139step1Labels permutation24 permutation4
    mixedMoment B raw42139step2 raw42139step2Labels = mixedMoment B raw42139step3 raw42139step3Labels := by
      have ha : raw42139step3 = raw42139step2 := by apply Matrix.ext; unfold raw42139step3 raw42139step2; decide +kernel
      have hl : raw42139step2Labels = labelEmbedding10 ∘ raw42139step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42139step2 raw42139step2Labels raw42139step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5300 node5300Labels := by rfl

def raw42140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42140Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42140step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42140step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42140step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42140step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42140 raw42140Labels = mixedMoment B node4003 node4003Labels := by
  calc
    mixedMoment B raw42140 raw42140Labels = mixedMoment B raw42140step0 raw42140step0Labels := by
      have hz : ∀ j, raw42140 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42140step0 = (fun i j => raw42140 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42140step0 raw42140; decide +kernel
      have hl : raw42140step0Labels = raw42140Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42140 raw42140Labels permutation346 hz
    mixedMoment B raw42140step0 raw42140step0Labels = mixedMoment B raw42140step1 raw42140step1Labels := by
      have ha : raw42140step1 = raw42140step0 := by apply Matrix.ext; unfold raw42140step1 raw42140step0; decide +kernel
      have hl : raw42140step0Labels = labelEmbedding1 ∘ raw42140step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42140step0 raw42140step0Labels raw42140step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4003 node4003Labels := by rfl

def raw42141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42141Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42141step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42141step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42141step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw42141step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42141step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42141step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42141step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw42141step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42141 raw42141Labels = mixedMoment B node5428 node5428Labels := by
  calc
    mixedMoment B raw42141 raw42141Labels = mixedMoment B raw42141step0 raw42141step0Labels := by
      have hz : ∀ j, raw42141 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42141step0 = (fun i j => raw42141 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42141step0 raw42141; decide +kernel
      have hl : raw42141step0Labels = raw42141Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42141 raw42141Labels permutation346 hz
    mixedMoment B raw42141step0 raw42141step0Labels = mixedMoment B raw42141step1 raw42141step1Labels := by
      have ha : raw42141step1 = (fun i j => raw42141step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42141step1 raw42141step0; decide +kernel
      have hl : raw42141step1Labels = raw42141step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42141step0 raw42141step0Labels permutation151 permutation3
    mixedMoment B raw42141step1 raw42141step1Labels = mixedMoment B raw42141step2 raw42141step2Labels := by
      have ha : raw42141step2 = -raw42141step1 := by apply Matrix.ext; change ∀ i j, raw42141step2 i j = -(raw42141step1 i j); unfold raw42141step2 raw42141step1; decide +kernel
      have hl : raw42141step2Labels = raw42141step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42141step2 raw42141step2Labels = mixedMoment B raw42141step3 raw42141step3Labels := by
      have ha : raw42141step3 = raw42141step2 := by apply Matrix.ext; unfold raw42141step3 raw42141step2; decide +kernel
      have hl : raw42141step2Labels = labelEmbedding7 ∘ raw42141step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42141step2 raw42141step2Labels raw42141step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5428 node5428Labels := by rfl

def raw42142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42142Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42142step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42142step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw42142step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42142step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42142step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42142step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42142step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42142 raw42142Labels = mixedMoment B node3995 node3995Labels := by
  calc
    mixedMoment B raw42142 raw42142Labels = mixedMoment B raw42142step0 raw42142step0Labels := by
      have hz : ∀ j, raw42142 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42142step0 = (fun i j => raw42142 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42142step0 raw42142; decide +kernel
      have hl : raw42142step0Labels = raw42142Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42142 raw42142Labels permutation346 hz
    mixedMoment B raw42142step0 raw42142step0Labels = mixedMoment B raw42142step1 raw42142step1Labels := by
      have ha : raw42142step1 = (fun i j => raw42142step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42142step1 raw42142step0; decide +kernel
      have hl : raw42142step1Labels = raw42142step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42142step0 raw42142step0Labels permutation151 permutation2
    mixedMoment B raw42142step1 raw42142step1Labels = mixedMoment B raw42142step2 raw42142step2Labels := by
      have ha : raw42142step2 = -raw42142step1 := by apply Matrix.ext; change ∀ i j, raw42142step2 i j = -(raw42142step1 i j); unfold raw42142step2 raw42142step1; decide +kernel
      have hl : raw42142step2Labels = raw42142step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42142step2 raw42142step2Labels = mixedMoment B raw42142step3 raw42142step3Labels := by
      have ha : raw42142step3 = raw42142step2 := by apply Matrix.ext; unfold raw42142step3 raw42142step2; decide +kernel
      have hl : raw42142step2Labels = labelEmbedding1 ∘ raw42142step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42142step2 raw42142step2Labels raw42142step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3995 node3995Labels := by rfl

def raw42143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42143Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42143step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42143step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42143step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42143step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42143step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42143step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42143 raw42143Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw42143 raw42143Labels = mixedMoment B raw42143step0 raw42143step0Labels := by
      have hz : ∀ j, raw42143 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42143step0 = (fun i j => raw42143 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42143step0 raw42143; decide +kernel
      have hl : raw42143step0Labels = raw42143Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42143 raw42143Labels permutation346 hz
    mixedMoment B raw42143step0 raw42143step0Labels = mixedMoment B raw42143step1 raw42143step1Labels := by
      have ha : raw42143step1 = (fun i j => raw42143step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42143step1 raw42143step0; decide +kernel
      have hl : raw42143step1Labels = raw42143step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42143step0 raw42143step0Labels permutation32 permutation3
    mixedMoment B raw42143step1 raw42143step1Labels = mixedMoment B raw42143step2 raw42143step2Labels := by
      have ha : raw42143step2 = raw42143step1 := by apply Matrix.ext; unfold raw42143step2 raw42143step1; decide +kernel
      have hl : raw42143step1Labels = labelEmbedding7 ∘ raw42143step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42143step1 raw42143step1Labels raw42143step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw42144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42144Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42144step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42144step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42144step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw42144step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42144step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42144step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42144step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42144step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42144 raw42144Labels = mixedMoment B node3881 node3881Labels := by
  calc
    mixedMoment B raw42144 raw42144Labels = mixedMoment B raw42144step0 raw42144step0Labels := by
      have hz : ∀ j, raw42144 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42144step0 = (fun i j => raw42144 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42144step0 raw42144; decide +kernel
      have hl : raw42144step0Labels = raw42144Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42144 raw42144Labels permutation346 hz
    mixedMoment B raw42144step0 raw42144step0Labels = mixedMoment B raw42144step1 raw42144step1Labels := by
      have ha : raw42144step1 = (fun i j => raw42144step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42144step1 raw42144step0; decide +kernel
      have hl : raw42144step1Labels = raw42144step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42144step0 raw42144step0Labels permutation151 permutation2
    mixedMoment B raw42144step1 raw42144step1Labels = mixedMoment B raw42144step2 raw42144step2Labels := by
      have ha : raw42144step2 = -raw42144step1 := by apply Matrix.ext; change ∀ i j, raw42144step2 i j = -(raw42144step1 i j); unfold raw42144step2 raw42144step1; decide +kernel
      have hl : raw42144step2Labels = raw42144step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42144step2 raw42144step2Labels = mixedMoment B raw42144step3 raw42144step3Labels := by
      have ha : raw42144step3 = raw42144step2 := by apply Matrix.ext; unfold raw42144step3 raw42144step2; decide +kernel
      have hl : raw42144step2Labels = labelEmbedding1 ∘ raw42144step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42144step2 raw42144step2Labels raw42144step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3881 node3881Labels := by rfl

def raw42145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42145Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42145step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42145step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw42145step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42145step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42145step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42145step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42145step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42145 raw42145Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw42145 raw42145Labels = mixedMoment B raw42145step0 raw42145step0Labels := by
      have hz : ∀ j, raw42145 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42145step0 = (fun i j => raw42145 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42145step0 raw42145; decide +kernel
      have hl : raw42145step0Labels = raw42145Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42145 raw42145Labels permutation346 hz
    mixedMoment B raw42145step0 raw42145step0Labels = mixedMoment B raw42145step1 raw42145step1Labels := by
      have ha : raw42145step1 = (fun i j => raw42145step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42145step1 raw42145step0; decide +kernel
      have hl : raw42145step1Labels = raw42145step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42145step0 raw42145step0Labels permutation151 permutation2
    mixedMoment B raw42145step1 raw42145step1Labels = mixedMoment B raw42145step2 raw42145step2Labels := by
      have ha : raw42145step2 = -raw42145step1 := by apply Matrix.ext; change ∀ i j, raw42145step2 i j = -(raw42145step1 i j); unfold raw42145step2 raw42145step1; decide +kernel
      have hl : raw42145step2Labels = raw42145step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42145step2 raw42145step2Labels = mixedMoment B raw42145step3 raw42145step3Labels := by
      have ha : raw42145step3 = raw42145step2 := by apply Matrix.ext; unfold raw42145step3 raw42145step2; decide +kernel
      have hl : raw42145step2Labels = labelEmbedding8 ∘ raw42145step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42145step2 raw42145step2Labels raw42145step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

def raw42146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42146Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42146step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42146step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42146step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw42146step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42146step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42146step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42146step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42146step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42146 raw42146Labels = mixedMoment B node3854 node3854Labels := by
  calc
    mixedMoment B raw42146 raw42146Labels = mixedMoment B raw42146step0 raw42146step0Labels := by
      have hz : ∀ j, raw42146 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42146step0 = (fun i j => raw42146 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42146step0 raw42146; decide +kernel
      have hl : raw42146step0Labels = raw42146Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42146 raw42146Labels permutation346 hz
    mixedMoment B raw42146step0 raw42146step0Labels = mixedMoment B raw42146step1 raw42146step1Labels := by
      have ha : raw42146step1 = (fun i j => raw42146step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42146step1 raw42146step0; decide +kernel
      have hl : raw42146step1Labels = raw42146step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42146step0 raw42146step0Labels permutation151 permutation2
    mixedMoment B raw42146step1 raw42146step1Labels = mixedMoment B raw42146step2 raw42146step2Labels := by
      have ha : raw42146step2 = -raw42146step1 := by apply Matrix.ext; change ∀ i j, raw42146step2 i j = -(raw42146step1 i j); unfold raw42146step2 raw42146step1; decide +kernel
      have hl : raw42146step2Labels = raw42146step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42146step2 raw42146step2Labels = mixedMoment B raw42146step3 raw42146step3Labels := by
      have ha : raw42146step3 = raw42146step2 := by apply Matrix.ext; unfold raw42146step3 raw42146step2; decide +kernel
      have hl : raw42146step2Labels = labelEmbedding1 ∘ raw42146step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42146step2 raw42146step2Labels raw42146step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3854 node3854Labels := by rfl

def raw42147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42147Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42147step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42147step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw42147step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42147step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42147step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42147step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42147step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42147 raw42147Labels = mixedMoment B node5436 node5436Labels := by
  calc
    mixedMoment B raw42147 raw42147Labels = mixedMoment B raw42147step0 raw42147step0Labels := by
      have hz : ∀ j, raw42147 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42147step0 = (fun i j => raw42147 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42147step0 raw42147; decide +kernel
      have hl : raw42147step0Labels = raw42147Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42147 raw42147Labels permutation346 hz
    mixedMoment B raw42147step0 raw42147step0Labels = mixedMoment B raw42147step1 raw42147step1Labels := by
      have ha : raw42147step1 = (fun i j => raw42147step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42147step1 raw42147step0; decide +kernel
      have hl : raw42147step1Labels = raw42147step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42147step0 raw42147step0Labels permutation151 permutation2
    mixedMoment B raw42147step1 raw42147step1Labels = mixedMoment B raw42147step2 raw42147step2Labels := by
      have ha : raw42147step2 = -raw42147step1 := by apply Matrix.ext; change ∀ i j, raw42147step2 i j = -(raw42147step1 i j); unfold raw42147step2 raw42147step1; decide +kernel
      have hl : raw42147step2Labels = raw42147step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42147step2 raw42147step2Labels = mixedMoment B raw42147step3 raw42147step3Labels := by
      have ha : raw42147step3 = raw42147step2 := by apply Matrix.ext; unfold raw42147step3 raw42147step2; decide +kernel
      have hl : raw42147step2Labels = labelEmbedding8 ∘ raw42147step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42147step2 raw42147step2Labels raw42147step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5436 node5436Labels := by rfl

def raw42148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw42148Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42148step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw42148step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42148step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42148step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42148step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42148step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42148 raw42148Labels = mixedMoment B node2751 node2751Labels := by
  calc
    mixedMoment B raw42148 raw42148Labels = mixedMoment B raw42148step0 raw42148step0Labels := by
      have hz : ∀ j, raw42148 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42148step0 = (fun i j => raw42148 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42148step0 raw42148; decide +kernel
      have hl : raw42148step0Labels = raw42148Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42148 raw42148Labels permutation346 hz
    mixedMoment B raw42148step0 raw42148step0Labels = mixedMoment B raw42148step1 raw42148step1Labels := by
      have ha : raw42148step1 = (fun i j => raw42148step0 (permutation144 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42148step1 raw42148step0; decide +kernel
      have hl : raw42148step1Labels = raw42148step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42148step0 raw42148step0Labels permutation144 permutation4
    mixedMoment B raw42148step1 raw42148step1Labels = mixedMoment B raw42148step2 raw42148step2Labels := by
      have ha : raw42148step2 = raw42148step1 := by apply Matrix.ext; unfold raw42148step2 raw42148step1; decide +kernel
      have hl : raw42148step1Labels = labelEmbedding1 ∘ raw42148step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42148step1 raw42148step1Labels raw42148step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2751 node2751Labels := by rfl

def raw42149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw42149Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42149step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw42149step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42149step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42149step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42149step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42149step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42149 raw42149Labels = mixedMoment B node5282 node5282Labels := by
  calc
    mixedMoment B raw42149 raw42149Labels = mixedMoment B raw42149step0 raw42149step0Labels := by
      have hz : ∀ j, raw42149 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42149step0 = (fun i j => raw42149 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42149step0 raw42149; decide +kernel
      have hl : raw42149step0Labels = raw42149Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42149 raw42149Labels permutation346 hz
    mixedMoment B raw42149step0 raw42149step0Labels = mixedMoment B raw42149step1 raw42149step1Labels := by
      have ha : raw42149step1 = (fun i j => raw42149step0 (permutation144 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42149step1 raw42149step0; decide +kernel
      have hl : raw42149step1Labels = raw42149step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42149step0 raw42149step0Labels permutation144 permutation4
    mixedMoment B raw42149step1 raw42149step1Labels = mixedMoment B raw42149step2 raw42149step2Labels := by
      have ha : raw42149step2 = raw42149step1 := by apply Matrix.ext; unfold raw42149step2 raw42149step1; decide +kernel
      have hl : raw42149step1Labels = labelEmbedding10 ∘ raw42149step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42149step1 raw42149step1Labels raw42149step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5282 node5282Labels := by rfl

def raw42150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw42150Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw42150step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42150step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42150step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42150step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42150step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42150 raw42150Labels = mixedMoment B node3995 node3995Labels := by
  calc
    mixedMoment B raw42150 raw42150Labels = mixedMoment B raw42150step0 raw42150step0Labels := by
      have hz : ∀ j, raw42150 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42150step0 = (fun i j => raw42150 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42150step0 raw42150; decide +kernel
      have hl : raw42150step0Labels = raw42150Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42150 raw42150Labels permutation346 hz
    mixedMoment B raw42150step0 raw42150step0Labels = mixedMoment B raw42150step1 raw42150step1Labels := by
      have ha : raw42150step1 = (fun i j => raw42150step0 (permutation150 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42150step1 raw42150step0; decide +kernel
      have hl : raw42150step1Labels = raw42150step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42150step0 raw42150step0Labels permutation150 permutation4
    mixedMoment B raw42150step1 raw42150step1Labels = mixedMoment B raw42150step2 raw42150step2Labels := by
      have ha : raw42150step2 = raw42150step1 := by apply Matrix.ext; unfold raw42150step2 raw42150step1; decide +kernel
      have hl : raw42150step1Labels = labelEmbedding1 ∘ raw42150step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42150step1 raw42150step1Labels raw42150step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3995 node3995Labels := by rfl

def raw42151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw42151Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42151step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw42151step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42151step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw42151step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42151step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42151step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42151step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42151step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42151 raw42151Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw42151 raw42151Labels = mixedMoment B raw42151step0 raw42151step0Labels := by
      have hz : ∀ j, raw42151 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42151step0 = (fun i j => raw42151 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42151step0 raw42151; decide +kernel
      have hl : raw42151step0Labels = raw42151Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42151 raw42151Labels permutation346 hz
    mixedMoment B raw42151step0 raw42151step0Labels = mixedMoment B raw42151step1 raw42151step1Labels := by
      have ha : raw42151step1 = (fun i j => raw42151step0 (permutation56 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42151step1 raw42151step0; decide +kernel
      have hl : raw42151step1Labels = raw42151step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42151step0 raw42151step0Labels permutation56 permutation5
    mixedMoment B raw42151step1 raw42151step1Labels = mixedMoment B raw42151step2 raw42151step2Labels := by
      have ha : raw42151step2 = -raw42151step1 := by apply Matrix.ext; change ∀ i j, raw42151step2 i j = -(raw42151step1 i j); unfold raw42151step2 raw42151step1; decide +kernel
      have hl : raw42151step2Labels = raw42151step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42151step2 raw42151step2Labels = mixedMoment B raw42151step3 raw42151step3Labels := by
      have ha : raw42151step3 = raw42151step2 := by apply Matrix.ext; unfold raw42151step3 raw42151step2; decide +kernel
      have hl : raw42151step2Labels = labelEmbedding9 ∘ raw42151step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42151step2 raw42151step2Labels raw42151step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw42152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42152Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42152step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42152step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42152step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42152step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42152 raw42152Labels = mixedMoment B node4005 node4005Labels := by
  calc
    mixedMoment B raw42152 raw42152Labels = mixedMoment B raw42152step0 raw42152step0Labels := by
      have hz : ∀ j, raw42152 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42152step0 = (fun i j => raw42152 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42152step0 raw42152; decide +kernel
      have hl : raw42152step0Labels = raw42152Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42152 raw42152Labels permutation346 hz
    mixedMoment B raw42152step0 raw42152step0Labels = mixedMoment B raw42152step1 raw42152step1Labels := by
      have ha : raw42152step1 = raw42152step0 := by apply Matrix.ext; unfold raw42152step1 raw42152step0; decide +kernel
      have hl : raw42152step0Labels = labelEmbedding1 ∘ raw42152step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42152step0 raw42152step0Labels raw42152step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4005 node4005Labels := by rfl

def raw42153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42153Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42153step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42153step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42153step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw42153step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42153step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw42153step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42153 raw42153Labels = mixedMoment B node5474 node5474Labels := by
  calc
    mixedMoment B raw42153 raw42153Labels = mixedMoment B raw42153step0 raw42153step0Labels := by
      have hz : ∀ j, raw42153 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42153step0 = (fun i j => raw42153 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42153step0 raw42153; decide +kernel
      have hl : raw42153step0Labels = raw42153Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42153 raw42153Labels permutation346 hz
    mixedMoment B raw42153step0 raw42153step0Labels = mixedMoment B raw42153step1 raw42153step1Labels := by
      have ha : raw42153step1 = (fun i j => raw42153step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42153step1 raw42153step0; decide +kernel
      have hl : raw42153step1Labels = raw42153step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42153step0 raw42153step0Labels permutation32 permutation3
    mixedMoment B raw42153step1 raw42153step1Labels = mixedMoment B raw42153step2 raw42153step2Labels := by
      have ha : raw42153step2 = raw42153step1 := by apply Matrix.ext; unfold raw42153step2 raw42153step1; decide +kernel
      have hl : raw42153step1Labels = labelEmbedding7 ∘ raw42153step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42153step1 raw42153step1Labels raw42153step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5474 node5474Labels := by rfl

def raw42154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42154Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42154step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw42154step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42154step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42154step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42154step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42154step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42154 raw42154Labels = mixedMoment B node3846 node3846Labels := by
  calc
    mixedMoment B raw42154 raw42154Labels = mixedMoment B raw42154step0 raw42154step0Labels := by
      have ha : raw42154step0 = (fun i j => raw42154 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42154step0 raw42154; decide +kernel
      have hl : raw42154step0Labels = raw42154Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42154 raw42154Labels permutation682 permutation2
    mixedMoment B raw42154step0 raw42154step0Labels = mixedMoment B raw42154step1 raw42154step1Labels := by
      have ha : raw42154step1 = -raw42154step0 := by apply Matrix.ext; change ∀ i j, raw42154step1 i j = -(raw42154step0 i j); unfold raw42154step1 raw42154step0; decide +kernel
      have hl : raw42154step1Labels = raw42154step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42154step1 raw42154step1Labels = mixedMoment B raw42154step2 raw42154step2Labels := by
      have ha : raw42154step2 = raw42154step1 := by apply Matrix.ext; unfold raw42154step2 raw42154step1; decide +kernel
      have hl : raw42154step1Labels = labelEmbedding1 ∘ raw42154step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42154step1 raw42154step1Labels raw42154step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3846 node3846Labels := by rfl

def raw42155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw42155Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42155step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw42155step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42155step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42155step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42155step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42155step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42155 raw42155Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw42155 raw42155Labels = mixedMoment B raw42155step0 raw42155step0Labels := by
      have ha : raw42155step0 = (fun i j => raw42155 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42155step0 raw42155; decide +kernel
      have hl : raw42155step0Labels = raw42155Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42155 raw42155Labels permutation682 permutation2
    mixedMoment B raw42155step0 raw42155step0Labels = mixedMoment B raw42155step1 raw42155step1Labels := by
      have ha : raw42155step1 = -raw42155step0 := by apply Matrix.ext; change ∀ i j, raw42155step1 i j = -(raw42155step0 i j); unfold raw42155step1 raw42155step0; decide +kernel
      have hl : raw42155step1Labels = raw42155step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42155step1 raw42155step1Labels = mixedMoment B raw42155step2 raw42155step2Labels := by
      have ha : raw42155step2 = raw42155step1 := by apply Matrix.ext; unfold raw42155step2 raw42155step1; decide +kernel
      have hl : raw42155step1Labels = labelEmbedding8 ∘ raw42155step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42155step1 raw42155step1Labels raw42155step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5429 node5429Labels := by rfl

def raw42156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw42156Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42156step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42156step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42156step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42156step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42156 raw42156Labels = mixedMoment B node3976 node3976Labels := by
  calc
    mixedMoment B raw42156 raw42156Labels = mixedMoment B raw42156step0 raw42156step0Labels := by
      have ha : raw42156step0 = (fun i j => raw42156 (permutation639 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42156step0 raw42156; decide +kernel
      have hl : raw42156step0Labels = raw42156Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42156 raw42156Labels permutation639 permutation4
    mixedMoment B raw42156step0 raw42156step0Labels = mixedMoment B raw42156step1 raw42156step1Labels := by
      have ha : raw42156step1 = raw42156step0 := by apply Matrix.ext; unfold raw42156step1 raw42156step0; decide +kernel
      have hl : raw42156step0Labels = labelEmbedding1 ∘ raw42156step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42156step0 raw42156step0Labels raw42156step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3976 node3976Labels := by rfl

def raw42157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, -2, 1]]
def raw42157Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42157step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw42157step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42157step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42157step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42157step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42157step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42157 raw42157Labels = mixedMoment B node5471 node5471Labels := by
  calc
    mixedMoment B raw42157 raw42157Labels = mixedMoment B raw42157step0 raw42157step0Labels := by
      have ha : raw42157step0 = (fun i j => raw42157 (permutation273 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42157step0 raw42157; decide +kernel
      have hl : raw42157step0Labels = raw42157Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42157 raw42157Labels permutation273 permutation5
    mixedMoment B raw42157step0 raw42157step0Labels = mixedMoment B raw42157step1 raw42157step1Labels := by
      have ha : raw42157step1 = -raw42157step0 := by apply Matrix.ext; change ∀ i j, raw42157step1 i j = -(raw42157step0 i j); unfold raw42157step1 raw42157step0; decide +kernel
      have hl : raw42157step1Labels = raw42157step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42157step1 raw42157step1Labels = mixedMoment B raw42157step2 raw42157step2Labels := by
      have ha : raw42157step2 = raw42157step1 := by apply Matrix.ext; unfold raw42157step2 raw42157step1; decide +kernel
      have hl : raw42157step1Labels = labelEmbedding9 ∘ raw42157step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42157step1 raw42157step1Labels raw42157step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5471 node5471Labels := by rfl

def raw42158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw42158Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42158step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42158step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42158step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw42158step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42158 raw42158Labels = mixedMoment B node4002 node4002Labels := by
  calc
    mixedMoment B raw42158 raw42158Labels = mixedMoment B raw42158step0 raw42158step0Labels := by
      have ha : raw42158step0 = (fun i j => raw42158 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42158step0 raw42158; decide +kernel
      have hl : raw42158step0Labels = raw42158Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42158 raw42158Labels permutation155 permutation2
    mixedMoment B raw42158step0 raw42158step0Labels = mixedMoment B raw42158step1 raw42158step1Labels := by
      have ha : raw42158step1 = raw42158step0 := by apply Matrix.ext; unfold raw42158step1 raw42158step0; decide +kernel
      have hl : raw42158step0Labels = labelEmbedding1 ∘ raw42158step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42158step0 raw42158step0Labels raw42158step1Labels labelEmbedding1 hl
    _ = mixedMoment B node4002 node4002Labels := by rfl

def raw42159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0]]
def raw42159Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42159step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42159step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42159step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw42159step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42159 raw42159Labels = mixedMoment B node5472 node5472Labels := by
  calc
    mixedMoment B raw42159 raw42159Labels = mixedMoment B raw42159step0 raw42159step0Labels := by
      have ha : raw42159step0 = (fun i j => raw42159 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42159step0 raw42159; decide +kernel
      have hl : raw42159step0Labels = raw42159Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42159 raw42159Labels permutation152 permutation3
    mixedMoment B raw42159step0 raw42159step0Labels = mixedMoment B raw42159step1 raw42159step1Labels := by
      have ha : raw42159step1 = raw42159step0 := by apply Matrix.ext; unfold raw42159step1 raw42159step0; decide +kernel
      have hl : raw42159step0Labels = labelEmbedding7 ∘ raw42159step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42159step0 raw42159step0Labels raw42159step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5472 node5472Labels := by rfl

def raw42160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42160Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42160step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42160step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42160step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42160step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42160 raw42160Labels = mixedMoment B node3846 node3846Labels := by
  calc
    mixedMoment B raw42160 raw42160Labels = mixedMoment B raw42160step0 raw42160step0Labels := by
      have ha : raw42160step0 = (fun i j => raw42160 (permutation426 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42160step0 raw42160; decide +kernel
      have hl : raw42160step0Labels = raw42160Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42160 raw42160Labels permutation426 permutation4
    mixedMoment B raw42160step0 raw42160step0Labels = mixedMoment B raw42160step1 raw42160step1Labels := by
      have ha : raw42160step1 = raw42160step0 := by apply Matrix.ext; unfold raw42160step1 raw42160step0; decide +kernel
      have hl : raw42160step0Labels = labelEmbedding1 ∘ raw42160step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42160step0 raw42160step0Labels raw42160step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3846 node3846Labels := by rfl

def raw42161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw42161Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42161step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42161step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42161step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42161step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42161 raw42161Labels = mixedMoment B node5429 node5429Labels := by
  calc
    mixedMoment B raw42161 raw42161Labels = mixedMoment B raw42161step0 raw42161step0Labels := by
      have ha : raw42161step0 = (fun i j => raw42161 (permutation426 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42161step0 raw42161; decide +kernel
      have hl : raw42161step0Labels = raw42161Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42161 raw42161Labels permutation426 permutation4
    mixedMoment B raw42161step0 raw42161step0Labels = mixedMoment B raw42161step1 raw42161step1Labels := by
      have ha : raw42161step1 = raw42161step0 := by apply Matrix.ext; unfold raw42161step1 raw42161step0; decide +kernel
      have hl : raw42161step0Labels = labelEmbedding10 ∘ raw42161step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42161step0 raw42161step0Labels raw42161step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5429 node5429Labels := by rfl

def raw42162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42162Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw42162step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42162step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![3, -3, 0]]
def raw42162step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42162step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![-1, 1, 0], ![-2, 1, 1]]
def raw42162step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42162step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42162step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42162step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42162step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42162 raw42162Labels = mixedMoment B node3229 node3229Labels := by
  calc
    mixedMoment B raw42162 raw42162Labels = mixedMoment B raw42162step0 raw42162step0Labels := by
      have hz : ∀ j, raw42162 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42162step0 = (fun i j => raw42162 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42162step0 raw42162; decide +kernel
      have hl : raw42162step0Labels = raw42162Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42162 raw42162Labels permutation520 hz
    mixedMoment B raw42162step0 raw42162step0Labels = mixedMoment B raw42162step1 raw42162step1Labels := by
      have hz : ∀ j, raw42162step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw42162step1 = (fun i j => raw42162step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw42162step1 raw42162step0; decide +kernel
      have hl : raw42162step1Labels = raw42162step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42162step0 raw42162step0Labels permutation104 hz
    mixedMoment B raw42162step1 raw42162step1Labels = mixedMoment B raw42162step2 raw42162step2Labels := by
      have ha : raw42162step2 = (fun i j => raw42162step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42162step2 raw42162step1; decide +kernel
      have hl : raw42162step2Labels = raw42162step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42162step1 raw42162step1Labels permutation31 permutation2
    mixedMoment B raw42162step2 raw42162step2Labels = mixedMoment B raw42162step3 raw42162step3Labels := by
      have ha : raw42162step3 = -raw42162step2 := by apply Matrix.ext; change ∀ i j, raw42162step3 i j = -(raw42162step2 i j); unfold raw42162step3 raw42162step2; decide +kernel
      have hl : raw42162step3Labels = raw42162step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42162step3 raw42162step3Labels = mixedMoment B raw42162step4 raw42162step4Labels := by
      have ha : raw42162step4 = raw42162step3 := by apply Matrix.ext; unfold raw42162step4 raw42162step3; decide +kernel
      have hl : raw42162step3Labels = labelEmbedding1 ∘ raw42162step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42162step3 raw42162step3Labels raw42162step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3229 node3229Labels := by rfl

def raw42163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42163Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42163step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw42163step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42163step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![3, -3, 0]]
def raw42163step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42163step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw42163step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42163step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42163step3Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42163step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42163step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42163 raw42163Labels = mixedMoment B node4895 node4895Labels := by
  calc
    mixedMoment B raw42163 raw42163Labels = mixedMoment B raw42163step0 raw42163step0Labels := by
      have hz : ∀ j, raw42163 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42163step0 = (fun i j => raw42163 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42163step0 raw42163; decide +kernel
      have hl : raw42163step0Labels = raw42163Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42163 raw42163Labels permutation520 hz
    mixedMoment B raw42163step0 raw42163step0Labels = mixedMoment B raw42163step1 raw42163step1Labels := by
      have hz : ∀ j, raw42163step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw42163step1 = (fun i j => raw42163step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw42163step1 raw42163step0; decide +kernel
      have hl : raw42163step1Labels = raw42163step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42163step0 raw42163step0Labels permutation104 hz
    mixedMoment B raw42163step1 raw42163step1Labels = mixedMoment B raw42163step2 raw42163step2Labels := by
      have ha : raw42163step2 = (fun i j => raw42163step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42163step2 raw42163step1; decide +kernel
      have hl : raw42163step2Labels = raw42163step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42163step1 raw42163step1Labels permutation31 permutation3
    mixedMoment B raw42163step2 raw42163step2Labels = mixedMoment B raw42163step3 raw42163step3Labels := by
      have ha : raw42163step3 = -raw42163step2 := by apply Matrix.ext; change ∀ i j, raw42163step3 i j = -(raw42163step2 i j); unfold raw42163step3 raw42163step2; decide +kernel
      have hl : raw42163step3Labels = raw42163step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42163step3 raw42163step3Labels = mixedMoment B raw42163step4 raw42163step4Labels := by
      have ha : raw42163step4 = raw42163step3 := by apply Matrix.ext; unfold raw42163step4 raw42163step3; decide +kernel
      have hl : raw42163step3Labels = labelEmbedding7 ∘ raw42163step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42163step3 raw42163step3Labels raw42163step4Labels labelEmbedding7 hl
    _ = mixedMoment B node4895 node4895Labels := by rfl

def raw42164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42164Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42164step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw42164step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42164step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42164step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42164step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42164step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42164 raw42164Labels = mixedMoment B node3109 node3109Labels := by
  calc
    mixedMoment B raw42164 raw42164Labels = mixedMoment B raw42164step0 raw42164step0Labels := by
      have hz : ∀ j, raw42164 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42164step0 = (fun i j => raw42164 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42164step0 raw42164; decide +kernel
      have hl : raw42164step0Labels = raw42164Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42164 raw42164Labels permutation434 hz
    mixedMoment B raw42164step0 raw42164step0Labels = mixedMoment B raw42164step1 raw42164step1Labels := by
      have ha : raw42164step1 = (fun i j => raw42164step0 (permutation146 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42164step1 raw42164step0; decide +kernel
      have hl : raw42164step1Labels = raw42164step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42164step0 raw42164step0Labels permutation146 permutation4
    mixedMoment B raw42164step1 raw42164step1Labels = mixedMoment B raw42164step2 raw42164step2Labels := by
      have ha : raw42164step2 = raw42164step1 := by apply Matrix.ext; unfold raw42164step2 raw42164step1; decide +kernel
      have hl : raw42164step1Labels = labelEmbedding1 ∘ raw42164step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42164step1 raw42164step1Labels raw42164step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3109 node3109Labels := by rfl

def raw42165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42165Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw42165step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42165step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42165step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42165step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42165step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42165 raw42165Labels = mixedMoment B node5271 node5271Labels := by
  calc
    mixedMoment B raw42165 raw42165Labels = mixedMoment B raw42165step0 raw42165step0Labels := by
      have hz : ∀ j, raw42165 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42165step0 = (fun i j => raw42165 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42165step0 raw42165; decide +kernel
      have hl : raw42165step0Labels = raw42165Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42165 raw42165Labels permutation434 hz
    mixedMoment B raw42165step0 raw42165step0Labels = mixedMoment B raw42165step1 raw42165step1Labels := by
      have ha : raw42165step1 = (fun i j => raw42165step0 (permutation151 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42165step1 raw42165step0; decide +kernel
      have hl : raw42165step1Labels = raw42165step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42165step0 raw42165step0Labels permutation151 permutation5
    mixedMoment B raw42165step1 raw42165step1Labels = mixedMoment B raw42165step2 raw42165step2Labels := by
      have ha : raw42165step2 = raw42165step1 := by apply Matrix.ext; unfold raw42165step2 raw42165step1; decide +kernel
      have hl : raw42165step1Labels = labelEmbedding9 ∘ raw42165step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42165step1 raw42165step1Labels raw42165step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5271 node5271Labels := by rfl

def raw42166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42166Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42166step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42166step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42166step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42166step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42166 raw42166Labels = mixedMoment B node3996 node3996Labels := by
  calc
    mixedMoment B raw42166 raw42166Labels = mixedMoment B raw42166step0 raw42166step0Labels := by
      have hz : ∀ j, raw42166 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42166step0 = (fun i j => raw42166 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42166step0 raw42166; decide +kernel
      have hl : raw42166step0Labels = raw42166Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42166 raw42166Labels permutation434 hz
    mixedMoment B raw42166step0 raw42166step0Labels = mixedMoment B raw42166step1 raw42166step1Labels := by
      have ha : raw42166step1 = raw42166step0 := by apply Matrix.ext; unfold raw42166step1 raw42166step0; decide +kernel
      have hl : raw42166step0Labels = labelEmbedding1 ∘ raw42166step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42166step0 raw42166step0Labels raw42166step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3996 node3996Labels := by rfl

def raw42167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42167Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42167step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42167step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw42167step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42167step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42167step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42167step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42167step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42167 raw42167Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw42167 raw42167Labels = mixedMoment B raw42167step0 raw42167step0Labels := by
      have hz : ∀ j, raw42167 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42167step0 = (fun i j => raw42167 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42167step0 raw42167; decide +kernel
      have hl : raw42167step0Labels = raw42167Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42167 raw42167Labels permutation434 hz
    mixedMoment B raw42167step0 raw42167step0Labels = mixedMoment B raw42167step1 raw42167step1Labels := by
      have ha : raw42167step1 = (fun i j => raw42167step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42167step1 raw42167step0; decide +kernel
      have hl : raw42167step1Labels = raw42167step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42167step0 raw42167step0Labels permutation151 permutation3
    mixedMoment B raw42167step1 raw42167step1Labels = mixedMoment B raw42167step2 raw42167step2Labels := by
      have ha : raw42167step2 = -raw42167step1 := by apply Matrix.ext; change ∀ i j, raw42167step2 i j = -(raw42167step1 i j); unfold raw42167step2 raw42167step1; decide +kernel
      have hl : raw42167step2Labels = raw42167step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42167step2 raw42167step2Labels = mixedMoment B raw42167step3 raw42167step3Labels := by
      have ha : raw42167step3 = raw42167step2 := by apply Matrix.ext; unfold raw42167step3 raw42167step2; decide +kernel
      have hl : raw42167step2Labels = labelEmbedding7 ∘ raw42167step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42167step2 raw42167step2Labels raw42167step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5410 node5410Labels := by rfl

def raw42168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42168Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42168step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42168step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42168step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42168step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42168 raw42168Labels = mixedMoment B node3995 node3995Labels := by
  calc
    mixedMoment B raw42168 raw42168Labels = mixedMoment B raw42168step0 raw42168step0Labels := by
      have hz : ∀ j, raw42168 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42168step0 = (fun i j => raw42168 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42168step0 raw42168; decide +kernel
      have hl : raw42168step0Labels = raw42168Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42168 raw42168Labels permutation434 hz
    mixedMoment B raw42168step0 raw42168step0Labels = mixedMoment B raw42168step1 raw42168step1Labels := by
      have ha : raw42168step1 = raw42168step0 := by apply Matrix.ext; unfold raw42168step1 raw42168step0; decide +kernel
      have hl : raw42168step0Labels = labelEmbedding1 ∘ raw42168step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42168step0 raw42168step0Labels raw42168step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3995 node3995Labels := by rfl

def raw42169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42169Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42169step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42169step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42169step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw42169step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42169step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42169step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42169step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42169step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42169 raw42169Labels = mixedMoment B node5473 node5473Labels := by
  calc
    mixedMoment B raw42169 raw42169Labels = mixedMoment B raw42169step0 raw42169step0Labels := by
      have hz : ∀ j, raw42169 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42169step0 = (fun i j => raw42169 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42169step0 raw42169; decide +kernel
      have hl : raw42169step0Labels = raw42169Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42169 raw42169Labels permutation434 hz
    mixedMoment B raw42169step0 raw42169step0Labels = mixedMoment B raw42169step1 raw42169step1Labels := by
      have ha : raw42169step1 = (fun i j => raw42169step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42169step1 raw42169step0; decide +kernel
      have hl : raw42169step1Labels = raw42169step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42169step0 raw42169step0Labels permutation151 permutation3
    mixedMoment B raw42169step1 raw42169step1Labels = mixedMoment B raw42169step2 raw42169step2Labels := by
      have ha : raw42169step2 = -raw42169step1 := by apply Matrix.ext; change ∀ i j, raw42169step2 i j = -(raw42169step1 i j); unfold raw42169step2 raw42169step1; decide +kernel
      have hl : raw42169step2Labels = raw42169step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42169step2 raw42169step2Labels = mixedMoment B raw42169step3 raw42169step3Labels := by
      have ha : raw42169step3 = raw42169step2 := by apply Matrix.ext; unfold raw42169step3 raw42169step2; decide +kernel
      have hl : raw42169step2Labels = labelEmbedding7 ∘ raw42169step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42169step2 raw42169step2Labels raw42169step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5473 node5473Labels := by rfl

def raw42170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw42170Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw42170step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42170step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42170step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42170step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42170step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42170 raw42170Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw42170 raw42170Labels = mixedMoment B raw42170step0 raw42170step0Labels := by
      have hz : ∀ j, raw42170 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42170step0 = (fun i j => raw42170 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42170step0 raw42170; decide +kernel
      have hl : raw42170step0Labels = raw42170Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42170 raw42170Labels permutation434 hz
    mixedMoment B raw42170step0 raw42170step0Labels = mixedMoment B raw42170step1 raw42170step1Labels := by
      have ha : raw42170step1 = (fun i j => raw42170step0 (permutation122 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42170step1 raw42170step0; decide +kernel
      have hl : raw42170step1Labels = raw42170step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42170step0 raw42170step0Labels permutation122 permutation4
    mixedMoment B raw42170step1 raw42170step1Labels = mixedMoment B raw42170step2 raw42170step2Labels := by
      have ha : raw42170step2 = raw42170step1 := by apply Matrix.ext; unfold raw42170step2 raw42170step1; decide +kernel
      have hl : raw42170step1Labels = labelEmbedding1 ∘ raw42170step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42170step1 raw42170step1Labels raw42170step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2773 node2773Labels := by rfl

def raw42171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw42171Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42171step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw42171step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42171step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42171step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42171step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42171step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42171 raw42171Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw42171 raw42171Labels = mixedMoment B raw42171step0 raw42171step0Labels := by
      have hz : ∀ j, raw42171 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42171step0 = (fun i j => raw42171 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42171step0 raw42171; decide +kernel
      have hl : raw42171step0Labels = raw42171Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42171 raw42171Labels permutation434 hz
    mixedMoment B raw42171step0 raw42171step0Labels = mixedMoment B raw42171step1 raw42171step1Labels := by
      have ha : raw42171step1 = (fun i j => raw42171step0 (permutation122 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42171step1 raw42171step0; decide +kernel
      have hl : raw42171step1Labels = raw42171step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42171step0 raw42171step0Labels permutation122 permutation4
    mixedMoment B raw42171step1 raw42171step1Labels = mixedMoment B raw42171step2 raw42171step2Labels := by
      have ha : raw42171step2 = raw42171step1 := by apply Matrix.ext; unfold raw42171step2 raw42171step1; decide +kernel
      have hl : raw42171step1Labels = labelEmbedding10 ∘ raw42171step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42171step1 raw42171step1Labels raw42171step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw42172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42172Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42172step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42172step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42172step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42172step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42172 raw42172Labels = mixedMoment B node3990 node3990Labels := by
  calc
    mixedMoment B raw42172 raw42172Labels = mixedMoment B raw42172step0 raw42172step0Labels := by
      have ha : raw42172step0 = (fun i j => raw42172 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42172step0 raw42172; decide +kernel
      have hl : raw42172step0Labels = raw42172Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42172 raw42172Labels permutation158 permutation2
    mixedMoment B raw42172step0 raw42172step0Labels = mixedMoment B raw42172step1 raw42172step1Labels := by
      have ha : raw42172step1 = raw42172step0 := by apply Matrix.ext; unfold raw42172step1 raw42172step0; decide +kernel
      have hl : raw42172step0Labels = labelEmbedding1 ∘ raw42172step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42172step0 raw42172step0Labels raw42172step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3990 node3990Labels := by rfl

def raw42173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42173Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42173step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw42173step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42173step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42173step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42173step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42173step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42173 raw42173Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw42173 raw42173Labels = mixedMoment B raw42173step0 raw42173step0Labels := by
      have ha : raw42173step0 = (fun i j => raw42173 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42173step0 raw42173; decide +kernel
      have hl : raw42173step0Labels = raw42173Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42173 raw42173Labels permutation688 permutation3
    mixedMoment B raw42173step0 raw42173step0Labels = mixedMoment B raw42173step1 raw42173step1Labels := by
      have ha : raw42173step1 = -raw42173step0 := by apply Matrix.ext; change ∀ i j, raw42173step1 i j = -(raw42173step0 i j); unfold raw42173step1 raw42173step0; decide +kernel
      have hl : raw42173step1Labels = raw42173step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42173step1 raw42173step1Labels = mixedMoment B raw42173step2 raw42173step2Labels := by
      have ha : raw42173step2 = raw42173step1 := by apply Matrix.ext; unfold raw42173step2 raw42173step1; decide +kernel
      have hl : raw42173step1Labels = labelEmbedding7 ∘ raw42173step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42173step1 raw42173step1Labels raw42173step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw42174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42174Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42174step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw42174step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42174step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42174step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42174step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42174step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42174 raw42174Labels = mixedMoment B node3871 node3871Labels := by
  calc
    mixedMoment B raw42174 raw42174Labels = mixedMoment B raw42174step0 raw42174step0Labels := by
      have ha : raw42174step0 = (fun i j => raw42174 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42174step0 raw42174; decide +kernel
      have hl : raw42174step0Labels = raw42174Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42174 raw42174Labels permutation682 permutation2
    mixedMoment B raw42174step0 raw42174step0Labels = mixedMoment B raw42174step1 raw42174step1Labels := by
      have ha : raw42174step1 = -raw42174step0 := by apply Matrix.ext; change ∀ i j, raw42174step1 i j = -(raw42174step0 i j); unfold raw42174step1 raw42174step0; decide +kernel
      have hl : raw42174step1Labels = raw42174step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42174step1 raw42174step1Labels = mixedMoment B raw42174step2 raw42174step2Labels := by
      have ha : raw42174step2 = raw42174step1 := by apply Matrix.ext; unfold raw42174step2 raw42174step1; decide +kernel
      have hl : raw42174step1Labels = labelEmbedding1 ∘ raw42174step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42174step1 raw42174step1Labels raw42174step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3871 node3871Labels := by rfl

def raw42175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42175Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42175step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42175step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42175step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42175step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42175 raw42175Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw42175 raw42175Labels = mixedMoment B raw42175step0 raw42175step0Labels := by
      have ha : raw42175step0 = (fun i j => raw42175 (permutation634 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42175step0 raw42175; decide +kernel
      have hl : raw42175step0Labels = raw42175Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42175 raw42175Labels permutation634 permutation7
    mixedMoment B raw42175step0 raw42175step0Labels = mixedMoment B raw42175step1 raw42175step1Labels := by
      have ha : raw42175step1 = raw42175step0 := by apply Matrix.ext; unfold raw42175step1 raw42175step0; decide +kernel
      have hl : raw42175step0Labels = labelEmbedding6 ∘ raw42175step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42175step0 raw42175step0Labels raw42175step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

def raw42176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42176Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42176step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw42176step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42176step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42176step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42176step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42176step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42176 raw42176Labels = mixedMoment B node3840 node3840Labels := by
  calc
    mixedMoment B raw42176 raw42176Labels = mixedMoment B raw42176step0 raw42176step0Labels := by
      have ha : raw42176step0 = (fun i j => raw42176 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42176step0 raw42176; decide +kernel
      have hl : raw42176step0Labels = raw42176Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42176 raw42176Labels permutation682 permutation2
    mixedMoment B raw42176step0 raw42176step0Labels = mixedMoment B raw42176step1 raw42176step1Labels := by
      have ha : raw42176step1 = -raw42176step0 := by apply Matrix.ext; change ∀ i j, raw42176step1 i j = -(raw42176step0 i j); unfold raw42176step1 raw42176step0; decide +kernel
      have hl : raw42176step1Labels = raw42176step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42176step1 raw42176step1Labels = mixedMoment B raw42176step2 raw42176step2Labels := by
      have ha : raw42176step2 = raw42176step1 := by apply Matrix.ext; unfold raw42176step2 raw42176step1; decide +kernel
      have hl : raw42176step1Labels = labelEmbedding1 ∘ raw42176step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42176step1 raw42176step1Labels raw42176step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3840 node3840Labels := by rfl

def raw42177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42177Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42177step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42177step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42177step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42177step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42177 raw42177Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw42177 raw42177Labels = mixedMoment B raw42177step0 raw42177step0Labels := by
      have ha : raw42177step0 = (fun i j => raw42177 (permutation643 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42177step0 raw42177; decide +kernel
      have hl : raw42177step0Labels = raw42177Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42177 raw42177Labels permutation643 permutation7
    mixedMoment B raw42177step0 raw42177step0Labels = mixedMoment B raw42177step1 raw42177step1Labels := by
      have ha : raw42177step1 = raw42177step0 := by apply Matrix.ext; unfold raw42177step1 raw42177step0; decide +kernel
      have hl : raw42177step0Labels = labelEmbedding6 ∘ raw42177step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42177step0 raw42177step0Labels raw42177step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw42178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw42178Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42178step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42178step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42178step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42178step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42178 raw42178Labels = mixedMoment B node2750 node2750Labels := by
  calc
    mixedMoment B raw42178 raw42178Labels = mixedMoment B raw42178step0 raw42178step0Labels := by
      have ha : raw42178step0 = (fun i j => raw42178 (permutation659 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42178step0 raw42178; decide +kernel
      have hl : raw42178step0Labels = raw42178Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42178 raw42178Labels permutation659 permutation4
    mixedMoment B raw42178step0 raw42178step0Labels = mixedMoment B raw42178step1 raw42178step1Labels := by
      have ha : raw42178step1 = raw42178step0 := by apply Matrix.ext; unfold raw42178step1 raw42178step0; decide +kernel
      have hl : raw42178step0Labels = labelEmbedding1 ∘ raw42178step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42178step0 raw42178step0Labels raw42178step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2750 node2750Labels := by rfl

def raw42179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw42179Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42179step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42179step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42179step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42179step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42179 raw42179Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw42179 raw42179Labels = mixedMoment B raw42179step0 raw42179step0Labels := by
      have ha : raw42179step0 = (fun i j => raw42179 (permutation659 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42179step0 raw42179; decide +kernel
      have hl : raw42179step0Labels = raw42179Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42179 raw42179Labels permutation659 permutation4
    mixedMoment B raw42179step0 raw42179step0Labels = mixedMoment B raw42179step1 raw42179step1Labels := by
      have ha : raw42179step1 = raw42179step0 := by apply Matrix.ext; unfold raw42179step1 raw42179step0; decide +kernel
      have hl : raw42179step0Labels = labelEmbedding10 ∘ raw42179step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42179step0 raw42179step0Labels raw42179step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5281 node5281Labels := by rfl

def raw42180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw42180Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42180step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42180step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42180step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42180step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42180 raw42180Labels = mixedMoment B node3994 node3994Labels := by
  calc
    mixedMoment B raw42180 raw42180Labels = mixedMoment B raw42180step0 raw42180step0Labels := by
      have ha : raw42180step0 = (fun i j => raw42180 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42180step0 raw42180; decide +kernel
      have hl : raw42180step0Labels = raw42180Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42180 raw42180Labels permutation157 permutation2
    mixedMoment B raw42180step0 raw42180step0Labels = mixedMoment B raw42180step1 raw42180step1Labels := by
      have ha : raw42180step1 = raw42180step0 := by apply Matrix.ext; unfold raw42180step1 raw42180step0; decide +kernel
      have hl : raw42180step0Labels = labelEmbedding1 ∘ raw42180step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42180step0 raw42180step0Labels raw42180step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3994 node3994Labels := by rfl

def raw42181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw42181Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42181step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42181step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42181step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42181step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42181 raw42181Labels = mixedMoment B node5478 node5478Labels := by
  calc
    mixedMoment B raw42181 raw42181Labels = mixedMoment B raw42181step0 raw42181step0Labels := by
      have ha : raw42181step0 = (fun i j => raw42181 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42181step0 raw42181; decide +kernel
      have hl : raw42181step0Labels = raw42181Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42181 raw42181Labels permutation152 permutation3
    mixedMoment B raw42181step0 raw42181step0Labels = mixedMoment B raw42181step1 raw42181step1Labels := by
      have ha : raw42181step1 = raw42181step0 := by apply Matrix.ext; unfold raw42181step1 raw42181step0; decide +kernel
      have hl : raw42181step0Labels = labelEmbedding7 ∘ raw42181step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42181step0 raw42181step0Labels raw42181step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5478 node5478Labels := by rfl

def raw42182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw42182Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42182step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw42182step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42182step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw42182step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42182step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42182step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42182step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42182step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42182 raw42182Labels = mixedMoment B node3119 node3119Labels := by
  calc
    mixedMoment B raw42182 raw42182Labels = mixedMoment B raw42182step0 raw42182step0Labels := by
      have hz : ∀ j, raw42182 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42182step0 = (fun i j => raw42182 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42182step0 raw42182; decide +kernel
      have hl : raw42182step0Labels = raw42182Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42182 raw42182Labels permutation434 hz
    mixedMoment B raw42182step0 raw42182step0Labels = mixedMoment B raw42182step1 raw42182step1Labels := by
      have hz : ∀ j, raw42182step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42182step1 = (fun i j => raw42182step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42182step1 raw42182step0; decide +kernel
      have hl : raw42182step1Labels = raw42182step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42182step0 raw42182step0Labels permutation80 hz
    mixedMoment B raw42182step1 raw42182step1Labels = mixedMoment B raw42182step2 raw42182step2Labels := by
      have ha : raw42182step2 = (fun i j => raw42182step1 (permutation26 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42182step2 raw42182step1; decide +kernel
      have hl : raw42182step2Labels = raw42182step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42182step1 raw42182step1Labels permutation26 permutation4
    mixedMoment B raw42182step2 raw42182step2Labels = mixedMoment B raw42182step3 raw42182step3Labels := by
      have ha : raw42182step3 = raw42182step2 := by apply Matrix.ext; unfold raw42182step3 raw42182step2; decide +kernel
      have hl : raw42182step2Labels = labelEmbedding1 ∘ raw42182step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42182step2 raw42182step2Labels raw42182step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3119 node3119Labels := by rfl

def raw42183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw42183Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42183step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw42183step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42183step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -3, 1]]
def raw42183step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42183step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42183step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42183step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42183step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42183 raw42183Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw42183 raw42183Labels = mixedMoment B raw42183step0 raw42183step0Labels := by
      have hz : ∀ j, raw42183 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42183step0 = (fun i j => raw42183 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42183step0 raw42183; decide +kernel
      have hl : raw42183step0Labels = raw42183Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42183 raw42183Labels permutation434 hz
    mixedMoment B raw42183step0 raw42183step0Labels = mixedMoment B raw42183step1 raw42183step1Labels := by
      have hz : ∀ j, raw42183step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42183step1 = (fun i j => raw42183step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42183step1 raw42183step0; decide +kernel
      have hl : raw42183step1Labels = raw42183step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42183step0 raw42183step0Labels permutation80 hz
    mixedMoment B raw42183step1 raw42183step1Labels = mixedMoment B raw42183step2 raw42183step2Labels := by
      have ha : raw42183step2 = (fun i j => raw42183step1 (permutation31 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42183step2 raw42183step1; decide +kernel
      have hl : raw42183step2Labels = raw42183step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42183step1 raw42183step1Labels permutation31 permutation5
    mixedMoment B raw42183step2 raw42183step2Labels = mixedMoment B raw42183step3 raw42183step3Labels := by
      have ha : raw42183step3 = raw42183step2 := by apply Matrix.ext; unfold raw42183step3 raw42183step2; decide +kernel
      have hl : raw42183step2Labels = labelEmbedding9 ∘ raw42183step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42183step2 raw42183step2Labels raw42183step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

def raw42184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw42184Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw42184step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42184step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -3, 2], ![2, 1, -3]]
def raw42184step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42184step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw42184step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42184step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, -1, 0], ![1, 2, -3]]
def raw42184step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42184 raw42184Labels = mixedMoment B node2781 node2781Labels := by
  calc
    mixedMoment B raw42184 raw42184Labels = mixedMoment B raw42184step0 raw42184step0Labels := by
      have hz : ∀ j, raw42184 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42184step0 = (fun i j => raw42184 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42184step0 raw42184; decide +kernel
      have hl : raw42184step0Labels = raw42184Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42184 raw42184Labels permutation434 hz
    mixedMoment B raw42184step0 raw42184step0Labels = mixedMoment B raw42184step1 raw42184step1Labels := by
      have hz : ∀ j, raw42184step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42184step1 = (fun i j => raw42184step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42184step1 raw42184step0; decide +kernel
      have hl : raw42184step1Labels = raw42184step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42184step0 raw42184step0Labels permutation80 hz
    mixedMoment B raw42184step1 raw42184step1Labels = mixedMoment B raw42184step2 raw42184step2Labels := by
      have ha : raw42184step2 = (fun i j => raw42184step1 (permutation20 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42184step2 raw42184step1; decide +kernel
      have hl : raw42184step2Labels = raw42184step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42184step1 raw42184step1Labels permutation20 permutation4
    mixedMoment B raw42184step2 raw42184step2Labels = mixedMoment B raw42184step3 raw42184step3Labels := by
      have ha : raw42184step3 = raw42184step2 := by apply Matrix.ext; unfold raw42184step3 raw42184step2; decide +kernel
      have hl : raw42184step2Labels = labelEmbedding1 ∘ raw42184step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42184step2 raw42184step2Labels raw42184step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2781 node2781Labels := by rfl

def raw42185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw42185Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw42185step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42185step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -3, 2], ![2, 1, -3]]
def raw42185step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42185step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw42185step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42185step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw42185step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42185 raw42185Labels = mixedMoment B node5295 node5295Labels := by
  calc
    mixedMoment B raw42185 raw42185Labels = mixedMoment B raw42185step0 raw42185step0Labels := by
      have hz : ∀ j, raw42185 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42185step0 = (fun i j => raw42185 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42185step0 raw42185; decide +kernel
      have hl : raw42185step0Labels = raw42185Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42185 raw42185Labels permutation434 hz
    mixedMoment B raw42185step0 raw42185step0Labels = mixedMoment B raw42185step1 raw42185step1Labels := by
      have hz : ∀ j, raw42185step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw42185step1 = (fun i j => raw42185step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw42185step1 raw42185step0; decide +kernel
      have hl : raw42185step1Labels = raw42185step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42185step0 raw42185step0Labels permutation80 hz
    mixedMoment B raw42185step1 raw42185step1Labels = mixedMoment B raw42185step2 raw42185step2Labels := by
      have ha : raw42185step2 = (fun i j => raw42185step1 (permutation28 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42185step2 raw42185step1; decide +kernel
      have hl : raw42185step2Labels = raw42185step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42185step1 raw42185step1Labels permutation28 permutation7
    mixedMoment B raw42185step2 raw42185step2Labels = mixedMoment B raw42185step3 raw42185step3Labels := by
      have ha : raw42185step3 = raw42185step2 := by apply Matrix.ext; unfold raw42185step3 raw42185step2; decide +kernel
      have hl : raw42185step2Labels = labelEmbedding6 ∘ raw42185step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42185step2 raw42185step2Labels raw42185step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5295 node5295Labels := by rfl

def raw42186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42186Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42186step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42186step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42186step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42186 raw42186Labels = mixedMoment B node3993 node3993Labels := by
  calc
    mixedMoment B raw42186 raw42186Labels = mixedMoment B raw42186step0 raw42186step0Labels := by
      have hz : ∀ j, raw42186 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42186step0 = (fun i j => raw42186 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42186step0 raw42186; decide +kernel
      have hl : raw42186step0Labels = raw42186Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42186 raw42186Labels permutation346 hz
    mixedMoment B raw42186step0 raw42186step0Labels = mixedMoment B raw42186step1 raw42186step1Labels := by
      have ha : raw42186step1 = raw42186step0 := by apply Matrix.ext; unfold raw42186step1 raw42186step0; decide +kernel
      have hl : raw42186step0Labels = labelEmbedding1 ∘ raw42186step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42186step0 raw42186step0Labels raw42186step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3993 node3993Labels := by rfl

def raw42187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42187Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42187step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42187step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42187step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42187step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42187step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42187step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42187 raw42187Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw42187 raw42187Labels = mixedMoment B raw42187step0 raw42187step0Labels := by
      have hz : ∀ j, raw42187 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42187step0 = (fun i j => raw42187 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42187step0 raw42187; decide +kernel
      have hl : raw42187step0Labels = raw42187Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42187 raw42187Labels permutation346 hz
    mixedMoment B raw42187step0 raw42187step0Labels = mixedMoment B raw42187step1 raw42187step1Labels := by
      have ha : raw42187step1 = (fun i j => raw42187step0 (permutation145 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42187step1 raw42187step0; decide +kernel
      have hl : raw42187step1Labels = raw42187step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42187step0 raw42187step0Labels permutation145 permutation5
    mixedMoment B raw42187step1 raw42187step1Labels = mixedMoment B raw42187step2 raw42187step2Labels := by
      have ha : raw42187step2 = raw42187step1 := by apply Matrix.ext; unfold raw42187step2 raw42187step1; decide +kernel
      have hl : raw42187step1Labels = labelEmbedding9 ∘ raw42187step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42187step1 raw42187step1Labels raw42187step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw42188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw42188Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw42188step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42188step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw42188step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42188step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42188step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42188step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42188step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42188 raw42188Labels = mixedMoment B node3572 node3572Labels := by
  calc
    mixedMoment B raw42188 raw42188Labels = mixedMoment B raw42188step0 raw42188step0Labels := by
      have hz : ∀ j, raw42188 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42188step0 = (fun i j => raw42188 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42188step0 raw42188; decide +kernel
      have hl : raw42188step0Labels = raw42188Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42188 raw42188Labels permutation346 hz
    mixedMoment B raw42188step0 raw42188step0Labels = mixedMoment B raw42188step1 raw42188step1Labels := by
      have ha : raw42188step1 = (fun i j => raw42188step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42188step1 raw42188step0; decide +kernel
      have hl : raw42188step1Labels = raw42188step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42188step0 raw42188step0Labels permutation151 permutation2
    mixedMoment B raw42188step1 raw42188step1Labels = mixedMoment B raw42188step2 raw42188step2Labels := by
      have ha : raw42188step2 = -raw42188step1 := by apply Matrix.ext; change ∀ i j, raw42188step2 i j = -(raw42188step1 i j); unfold raw42188step2 raw42188step1; decide +kernel
      have hl : raw42188step2Labels = raw42188step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42188step2 raw42188step2Labels = mixedMoment B raw42188step3 raw42188step3Labels := by
      have ha : raw42188step3 = raw42188step2 := by apply Matrix.ext; unfold raw42188step3 raw42188step2; decide +kernel
      have hl : raw42188step2Labels = labelEmbedding1 ∘ raw42188step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42188step2 raw42188step2Labels raw42188step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3572 node3572Labels := by rfl

def raw42189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw42189Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![2, 1, -3]]
def raw42189step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42189step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42189step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42189step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42189step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42189 raw42189Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw42189 raw42189Labels = mixedMoment B raw42189step0 raw42189step0Labels := by
      have hz : ∀ j, raw42189 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42189step0 = (fun i j => raw42189 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42189step0 raw42189; decide +kernel
      have hl : raw42189step0Labels = raw42189Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42189 raw42189Labels permutation346 hz
    mixedMoment B raw42189step0 raw42189step0Labels = mixedMoment B raw42189step1 raw42189step1Labels := by
      have ha : raw42189step1 = (fun i j => raw42189step0 (permutation139 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42189step1 raw42189step0; decide +kernel
      have hl : raw42189step1Labels = raw42189step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42189step0 raw42189step0Labels permutation139 permutation7
    mixedMoment B raw42189step1 raw42189step1Labels = mixedMoment B raw42189step2 raw42189step2Labels := by
      have ha : raw42189step2 = raw42189step1 := by apply Matrix.ext; unfold raw42189step2 raw42189step1; decide +kernel
      have hl : raw42189step1Labels = labelEmbedding6 ∘ raw42189step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42189step1 raw42189step1Labels raw42189step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

def raw42190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42190Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42190step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42190step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw42190step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42190step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42190step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42190step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw42190step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42190 raw42190Labels = mixedMoment B node3540 node3540Labels := by
  calc
    mixedMoment B raw42190 raw42190Labels = mixedMoment B raw42190step0 raw42190step0Labels := by
      have hz : ∀ j, raw42190 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42190step0 = (fun i j => raw42190 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42190step0 raw42190; decide +kernel
      have hl : raw42190step0Labels = raw42190Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42190 raw42190Labels permutation346 hz
    mixedMoment B raw42190step0 raw42190step0Labels = mixedMoment B raw42190step1 raw42190step1Labels := by
      have ha : raw42190step1 = (fun i j => raw42190step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42190step1 raw42190step0; decide +kernel
      have hl : raw42190step1Labels = raw42190step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42190step0 raw42190step0Labels permutation151 permutation2
    mixedMoment B raw42190step1 raw42190step1Labels = mixedMoment B raw42190step2 raw42190step2Labels := by
      have ha : raw42190step2 = -raw42190step1 := by apply Matrix.ext; change ∀ i j, raw42190step2 i j = -(raw42190step1 i j); unfold raw42190step2 raw42190step1; decide +kernel
      have hl : raw42190step2Labels = raw42190step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42190step2 raw42190step2Labels = mixedMoment B raw42190step3 raw42190step3Labels := by
      have ha : raw42190step3 = raw42190step2 := by apply Matrix.ext; unfold raw42190step3 raw42190step2; decide +kernel
      have hl : raw42190step2Labels = labelEmbedding1 ∘ raw42190step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42190step2 raw42190step2Labels raw42190step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3540 node3540Labels := by rfl

def raw42191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42191Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, -1, 0], ![2, 1, -3]]
def raw42191step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42191step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42191step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42191step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42191step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42191 raw42191Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw42191 raw42191Labels = mixedMoment B raw42191step0 raw42191step0Labels := by
      have hz : ∀ j, raw42191 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42191step0 = (fun i j => raw42191 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42191step0 raw42191; decide +kernel
      have hl : raw42191step0Labels = raw42191Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42191 raw42191Labels permutation346 hz
    mixedMoment B raw42191step0 raw42191step0Labels = mixedMoment B raw42191step1 raw42191step1Labels := by
      have ha : raw42191step1 = (fun i j => raw42191step0 (permutation148 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42191step1 raw42191step0; decide +kernel
      have hl : raw42191step1Labels = raw42191step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42191step0 raw42191step0Labels permutation148 permutation7
    mixedMoment B raw42191step1 raw42191step1Labels = mixedMoment B raw42191step2 raw42191step2Labels := by
      have ha : raw42191step2 = raw42191step1 := by apply Matrix.ext; unfold raw42191step2 raw42191step1; decide +kernel
      have hl : raw42191step1Labels = labelEmbedding6 ∘ raw42191step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42191step1 raw42191step1Labels raw42191step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5260 node5260Labels := by rfl

def raw42192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw42192Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42192step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw42192step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42192step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42192step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42192step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42192step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42192 raw42192Labels = mixedMoment B node2763 node2763Labels := by
  calc
    mixedMoment B raw42192 raw42192Labels = mixedMoment B raw42192step0 raw42192step0Labels := by
      have hz : ∀ j, raw42192 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42192step0 = (fun i j => raw42192 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42192step0 raw42192; decide +kernel
      have hl : raw42192step0Labels = raw42192Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42192 raw42192Labels permutation346 hz
    mixedMoment B raw42192step0 raw42192step0Labels = mixedMoment B raw42192step1 raw42192step1Labels := by
      have ha : raw42192step1 = (fun i j => raw42192step0 (permutation146 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42192step1 raw42192step0; decide +kernel
      have hl : raw42192step1Labels = raw42192step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42192step0 raw42192step0Labels permutation146 permutation4
    mixedMoment B raw42192step1 raw42192step1Labels = mixedMoment B raw42192step2 raw42192step2Labels := by
      have ha : raw42192step2 = raw42192step1 := by apply Matrix.ext; unfold raw42192step2 raw42192step1; decide +kernel
      have hl : raw42192step1Labels = labelEmbedding1 ∘ raw42192step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42192step1 raw42192step1Labels raw42192step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2763 node2763Labels := by rfl

def raw42193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw42193Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![1, 0, -1], ![1, -3, 2]]
def raw42193step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42193step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42193step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42193step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42193step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42193 raw42193Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw42193 raw42193Labels = mixedMoment B raw42193step0 raw42193step0Labels := by
      have hz : ∀ j, raw42193 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42193step0 = (fun i j => raw42193 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42193step0 raw42193; decide +kernel
      have hl : raw42193step0Labels = raw42193Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42193 raw42193Labels permutation346 hz
    mixedMoment B raw42193step0 raw42193step0Labels = mixedMoment B raw42193step1 raw42193step1Labels := by
      have ha : raw42193step1 = (fun i j => raw42193step0 (permutation146 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42193step1 raw42193step0; decide +kernel
      have hl : raw42193step1Labels = raw42193step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42193step0 raw42193step0Labels permutation146 permutation4
    mixedMoment B raw42193step1 raw42193step1Labels = mixedMoment B raw42193step2 raw42193step2Labels := by
      have ha : raw42193step2 = raw42193step1 := by apply Matrix.ext; unfold raw42193step2 raw42193step1; decide +kernel
      have hl : raw42193step1Labels = labelEmbedding10 ∘ raw42193step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42193step1 raw42193step1Labels raw42193step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

def raw42194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw42194Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42194step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw42194step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42194step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42194step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42194step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42194step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42194 raw42194Labels = mixedMoment B node3997 node3997Labels := by
  calc
    mixedMoment B raw42194 raw42194Labels = mixedMoment B raw42194step0 raw42194step0Labels := by
      have hz : ∀ j, raw42194 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42194step0 = (fun i j => raw42194 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42194step0 raw42194; decide +kernel
      have hl : raw42194step0Labels = raw42194Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42194 raw42194Labels permutation346 hz
    mixedMoment B raw42194step0 raw42194step0Labels = mixedMoment B raw42194step1 raw42194step1Labels := by
      have ha : raw42194step1 = (fun i j => raw42194step0 (permutation37 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42194step1 raw42194step0; decide +kernel
      have hl : raw42194step1Labels = raw42194step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42194step0 raw42194step0Labels permutation37 permutation2
    mixedMoment B raw42194step1 raw42194step1Labels = mixedMoment B raw42194step2 raw42194step2Labels := by
      have ha : raw42194step2 = raw42194step1 := by apply Matrix.ext; unfold raw42194step2 raw42194step1; decide +kernel
      have hl : raw42194step1Labels = labelEmbedding1 ∘ raw42194step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42194step1 raw42194step1Labels raw42194step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3997 node3997Labels := by rfl

def raw42195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw42195Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![1, -1, 0], ![1, -2, 1]]
def raw42195step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42195step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42195step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42195step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42195step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42195 raw42195Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw42195 raw42195Labels = mixedMoment B raw42195step0 raw42195step0Labels := by
      have hz : ∀ j, raw42195 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw42195step0 = (fun i j => raw42195 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw42195step0 raw42195; decide +kernel
      have hl : raw42195step0Labels = raw42195Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42195 raw42195Labels permutation346 hz
    mixedMoment B raw42195step0 raw42195step0Labels = mixedMoment B raw42195step1 raw42195step1Labels := by
      have ha : raw42195step1 = (fun i j => raw42195step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42195step1 raw42195step0; decide +kernel
      have hl : raw42195step1Labels = raw42195step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42195step0 raw42195step0Labels permutation32 permutation3
    mixedMoment B raw42195step1 raw42195step1Labels = mixedMoment B raw42195step2 raw42195step2Labels := by
      have ha : raw42195step2 = raw42195step1 := by apply Matrix.ext; unfold raw42195step2 raw42195step1; decide +kernel
      have hl : raw42195step1Labels = labelEmbedding7 ∘ raw42195step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42195step1 raw42195step1Labels raw42195step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5484 node5484Labels := by rfl

def raw42196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw42196Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42196step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42196step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42196step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42196step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42196 raw42196Labels = mixedMoment B node3978 node3978Labels := by
  calc
    mixedMoment B raw42196 raw42196Labels = mixedMoment B raw42196step0 raw42196step0Labels := by
      have ha : raw42196step0 = (fun i j => raw42196 (permutation641 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42196step0 raw42196; decide +kernel
      have hl : raw42196step0Labels = raw42196Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42196 raw42196Labels permutation641 permutation4
    mixedMoment B raw42196step0 raw42196step0Labels = mixedMoment B raw42196step1 raw42196step1Labels := by
      have ha : raw42196step1 = raw42196step0 := by apply Matrix.ext; unfold raw42196step1 raw42196step0; decide +kernel
      have hl : raw42196step0Labels = labelEmbedding1 ∘ raw42196step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42196step0 raw42196step0Labels raw42196step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3978 node3978Labels := by rfl

def raw42197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, 0, -1], ![1, -2, 1]]
def raw42197Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42197step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42197step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42197step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42197step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42197 raw42197Labels = mixedMoment B node5480 node5480Labels := by
  calc
    mixedMoment B raw42197 raw42197Labels = mixedMoment B raw42197step0 raw42197step0Labels := by
      have ha : raw42197step0 = (fun i j => raw42197 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42197step0 raw42197; decide +kernel
      have hl : raw42197step0Labels = raw42197Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42197 raw42197Labels permutation152 permutation3
    mixedMoment B raw42197step0 raw42197step0Labels = mixedMoment B raw42197step1 raw42197step1Labels := by
      have ha : raw42197step1 = raw42197step0 := by apply Matrix.ext; unfold raw42197step1 raw42197step0; decide +kernel
      have hl : raw42197step0Labels = labelEmbedding7 ∘ raw42197step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42197step0 raw42197step0Labels raw42197step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5480 node5480Labels := by rfl

def raw42198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42198Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42198step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42198step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42198step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42198step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42198 raw42198Labels = mixedMoment B node3848 node3848Labels := by
  calc
    mixedMoment B raw42198 raw42198Labels = mixedMoment B raw42198step0 raw42198step0Labels := by
      have ha : raw42198step0 = (fun i j => raw42198 (permutation428 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42198step0 raw42198; decide +kernel
      have hl : raw42198step0Labels = raw42198Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42198 raw42198Labels permutation428 permutation4
    mixedMoment B raw42198step0 raw42198step0Labels = mixedMoment B raw42198step1 raw42198step1Labels := by
      have ha : raw42198step1 = raw42198step0 := by apply Matrix.ext; unfold raw42198step1 raw42198step0; decide +kernel
      have hl : raw42198step0Labels = labelEmbedding1 ∘ raw42198step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42198step0 raw42198step0Labels raw42198step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3848 node3848Labels := by rfl

def raw42199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 1, -2], ![1, 0, -1], ![1, -1, 0]]
def raw42199Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42199step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42199step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42199step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42199step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42199 raw42199Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw42199 raw42199Labels = mixedMoment B raw42199step0 raw42199step0Labels := by
      have ha : raw42199step0 = (fun i j => raw42199 (permutation428 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42199step0 raw42199; decide +kernel
      have hl : raw42199step0Labels = raw42199Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42199 raw42199Labels permutation428 permutation4
    mixedMoment B raw42199step0 raw42199step0Labels = mixedMoment B raw42199step1 raw42199step1Labels := by
      have ha : raw42199step1 = raw42199step0 := by apply Matrix.ext; unfold raw42199step1 raw42199step0; decide +kernel
      have hl : raw42199step0Labels = labelEmbedding10 ∘ raw42199step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42199step0 raw42199step0Labels raw42199step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

def raw42200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42200Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![3, -3, 0]]
def raw42200step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42200step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![3, -3, 0]]
def raw42200step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42200step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -3, 0], ![0, 2, -2], ![-1, 0, 1], ![-2, 1, 1]]
def raw42200step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42200step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw42200step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42200step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw42200step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42200 raw42200Labels = mixedMoment B node3225 node3225Labels := by
  calc
    mixedMoment B raw42200 raw42200Labels = mixedMoment B raw42200step0 raw42200step0Labels := by
      have hz : ∀ j, raw42200 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42200step0 = (fun i j => raw42200 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42200step0 raw42200; decide +kernel
      have hl : raw42200step0Labels = raw42200Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42200 raw42200Labels permutation520 hz
    mixedMoment B raw42200step0 raw42200step0Labels = mixedMoment B raw42200step1 raw42200step1Labels := by
      have hz : ∀ j, raw42200step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw42200step1 = (fun i j => raw42200step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw42200step1 raw42200step0; decide +kernel
      have hl : raw42200step1Labels = raw42200step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42200step0 raw42200step0Labels permutation104 hz
    mixedMoment B raw42200step1 raw42200step1Labels = mixedMoment B raw42200step2 raw42200step2Labels := by
      have ha : raw42200step2 = (fun i j => raw42200step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42200step2 raw42200step1; decide +kernel
      have hl : raw42200step2Labels = raw42200step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42200step1 raw42200step1Labels permutation31 permutation2
    mixedMoment B raw42200step2 raw42200step2Labels = mixedMoment B raw42200step3 raw42200step3Labels := by
      have ha : raw42200step3 = -raw42200step2 := by apply Matrix.ext; change ∀ i j, raw42200step3 i j = -(raw42200step2 i j); unfold raw42200step3 raw42200step2; decide +kernel
      have hl : raw42200step3Labels = raw42200step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42200step3 raw42200step3Labels = mixedMoment B raw42200step4 raw42200step4Labels := by
      have ha : raw42200step4 = raw42200step3 := by apply Matrix.ext; unfold raw42200step4 raw42200step3; decide +kernel
      have hl : raw42200step3Labels = labelEmbedding1 ∘ raw42200step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42200step3 raw42200step3Labels raw42200step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3225 node3225Labels := by rfl

def raw42201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![0, 0, 0], ![3, -3, 0]]
def raw42201Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![3, -3, 0]]
def raw42201step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42201step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![3, -3, 0]]
def raw42201step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42201step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42201step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42201step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42201step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42201 raw42201Labels = mixedMoment B node4896 node4896Labels := by
  calc
    mixedMoment B raw42201 raw42201Labels = mixedMoment B raw42201step0 raw42201step0Labels := by
      have hz : ∀ j, raw42201 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42201step0 = (fun i j => raw42201 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42201step0 raw42201; decide +kernel
      have hl : raw42201step0Labels = raw42201Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42201 raw42201Labels permutation520 hz
    mixedMoment B raw42201step0 raw42201step0Labels = mixedMoment B raw42201step1 raw42201step1Labels := by
      have hz : ∀ j, raw42201step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw42201step1 = (fun i j => raw42201step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw42201step1 raw42201step0; decide +kernel
      have hl : raw42201step1Labels = raw42201step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42201step0 raw42201step0Labels permutation104 hz
    mixedMoment B raw42201step1 raw42201step1Labels = mixedMoment B raw42201step2 raw42201step2Labels := by
      have ha : raw42201step2 = (fun i j => raw42201step1 (permutation28 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42201step2 raw42201step1; decide +kernel
      have hl : raw42201step2Labels = raw42201step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42201step1 raw42201step1Labels permutation28 permutation5
    mixedMoment B raw42201step2 raw42201step2Labels = mixedMoment B raw42201step3 raw42201step3Labels := by
      have ha : raw42201step3 = raw42201step2 := by apply Matrix.ext; unfold raw42201step3 raw42201step2; decide +kernel
      have hl : raw42201step2Labels = labelEmbedding9 ∘ raw42201step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42201step2 raw42201step2Labels raw42201step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4896 node4896Labels := by rfl

def raw42202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42202Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42202step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw42202step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42202step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42202step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42202step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42202step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42202 raw42202Labels = mixedMoment B node3086 node3086Labels := by
  calc
    mixedMoment B raw42202 raw42202Labels = mixedMoment B raw42202step0 raw42202step0Labels := by
      have hz : ∀ j, raw42202 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42202step0 = (fun i j => raw42202 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42202step0 raw42202; decide +kernel
      have hl : raw42202step0Labels = raw42202Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42202 raw42202Labels permutation434 hz
    mixedMoment B raw42202step0 raw42202step0Labels = mixedMoment B raw42202step1 raw42202step1Labels := by
      have ha : raw42202step1 = (fun i j => raw42202step0 (permutation138 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42202step1 raw42202step0; decide +kernel
      have hl : raw42202step1Labels = raw42202step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42202step0 raw42202step0Labels permutation138 permutation4
    mixedMoment B raw42202step1 raw42202step1Labels = mixedMoment B raw42202step2 raw42202step2Labels := by
      have ha : raw42202step2 = raw42202step1 := by apply Matrix.ext; unfold raw42202step2 raw42202step1; decide +kernel
      have hl : raw42202step1Labels = labelEmbedding1 ∘ raw42202step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42202step1 raw42202step1Labels raw42202step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3086 node3086Labels := by rfl

def raw42203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1]]
def raw42203Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![2, -3, 1]]
def raw42203step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42203step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42203step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42203step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42203step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42203 raw42203Labels = mixedMoment B node5260 node5260Labels := by
  calc
    mixedMoment B raw42203 raw42203Labels = mixedMoment B raw42203step0 raw42203step0Labels := by
      have hz : ∀ j, raw42203 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42203step0 = (fun i j => raw42203 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42203step0 raw42203; decide +kernel
      have hl : raw42203step0Labels = raw42203Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42203 raw42203Labels permutation434 hz
    mixedMoment B raw42203step0 raw42203step0Labels = mixedMoment B raw42203step1 raw42203step1Labels := by
      have ha : raw42203step1 = (fun i j => raw42203step0 (permutation148 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42203step1 raw42203step0; decide +kernel
      have hl : raw42203step1Labels = raw42203step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42203step0 raw42203step0Labels permutation148 permutation5
    mixedMoment B raw42203step1 raw42203step1Labels = mixedMoment B raw42203step2 raw42203step2Labels := by
      have ha : raw42203step2 = raw42203step1 := by apply Matrix.ext; unfold raw42203step2 raw42203step1; decide +kernel
      have hl : raw42203step1Labels = labelEmbedding9 ∘ raw42203step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42203step1 raw42203step1Labels raw42203step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5260 node5260Labels := by rfl

def raw42204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42204Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42204step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42204step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42204step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw42204step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42204step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42204step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42204step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42204step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42204 raw42204Labels = mixedMoment B node3883 node3883Labels := by
  calc
    mixedMoment B raw42204 raw42204Labels = mixedMoment B raw42204step0 raw42204step0Labels := by
      have hz : ∀ j, raw42204 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42204step0 = (fun i j => raw42204 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42204step0 raw42204; decide +kernel
      have hl : raw42204step0Labels = raw42204Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42204 raw42204Labels permutation434 hz
    mixedMoment B raw42204step0 raw42204step0Labels = mixedMoment B raw42204step1 raw42204step1Labels := by
      have ha : raw42204step1 = (fun i j => raw42204step0 (permutation80 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42204step1 raw42204step0; decide +kernel
      have hl : raw42204step1Labels = raw42204step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42204step0 raw42204step0Labels permutation80 permutation4
    mixedMoment B raw42204step1 raw42204step1Labels = mixedMoment B raw42204step2 raw42204step2Labels := by
      have ha : raw42204step2 = -raw42204step1 := by apply Matrix.ext; change ∀ i j, raw42204step2 i j = -(raw42204step1 i j); unfold raw42204step2 raw42204step1; decide +kernel
      have hl : raw42204step2Labels = raw42204step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42204step2 raw42204step2Labels = mixedMoment B raw42204step3 raw42204step3Labels := by
      have ha : raw42204step3 = raw42204step2 := by apply Matrix.ext; unfold raw42204step3 raw42204step2; decide +kernel
      have hl : raw42204step2Labels = labelEmbedding1 ∘ raw42204step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42204step2 raw42204step2Labels raw42204step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3883 node3883Labels := by rfl

def raw42205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0]]
def raw42205Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -2, 0]]
def raw42205step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42205step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42205step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42205step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42205step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42205 raw42205Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw42205 raw42205Labels = mixedMoment B raw42205step0 raw42205step0Labels := by
      have hz : ∀ j, raw42205 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42205step0 = (fun i j => raw42205 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42205step0 raw42205; decide +kernel
      have hl : raw42205step0Labels = raw42205Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42205 raw42205Labels permutation434 hz
    mixedMoment B raw42205step0 raw42205step0Labels = mixedMoment B raw42205step1 raw42205step1Labels := by
      have ha : raw42205step1 = (fun i j => raw42205step0 (permutation148 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42205step1 raw42205step0; decide +kernel
      have hl : raw42205step1Labels = raw42205step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42205step0 raw42205step0Labels permutation148 permutation5
    mixedMoment B raw42205step1 raw42205step1Labels = mixedMoment B raw42205step2 raw42205step2Labels := by
      have ha : raw42205step2 = raw42205step1 := by apply Matrix.ext; unfold raw42205step2 raw42205step1; decide +kernel
      have hl : raw42205step1Labels = labelEmbedding9 ∘ raw42205step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42205step1 raw42205step1Labels raw42205step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw42206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42206Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42206step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42206step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42206step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw42206step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42206step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42206step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42206step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42206step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42206 raw42206Labels = mixedMoment B node3881 node3881Labels := by
  calc
    mixedMoment B raw42206 raw42206Labels = mixedMoment B raw42206step0 raw42206step0Labels := by
      have hz : ∀ j, raw42206 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42206step0 = (fun i j => raw42206 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42206step0 raw42206; decide +kernel
      have hl : raw42206step0Labels = raw42206Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42206 raw42206Labels permutation434 hz
    mixedMoment B raw42206step0 raw42206step0Labels = mixedMoment B raw42206step1 raw42206step1Labels := by
      have ha : raw42206step1 = (fun i j => raw42206step0 (permutation81 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42206step1 raw42206step0; decide +kernel
      have hl : raw42206step1Labels = raw42206step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42206step0 raw42206step0Labels permutation81 permutation4
    mixedMoment B raw42206step1 raw42206step1Labels = mixedMoment B raw42206step2 raw42206step2Labels := by
      have ha : raw42206step2 = -raw42206step1 := by apply Matrix.ext; change ∀ i j, raw42206step2 i j = -(raw42206step1 i j); unfold raw42206step2 raw42206step1; decide +kernel
      have hl : raw42206step2Labels = raw42206step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42206step2 raw42206step2Labels = mixedMoment B raw42206step3 raw42206step3Labels := by
      have ha : raw42206step3 = raw42206step2 := by apply Matrix.ext; unfold raw42206step3 raw42206step2; decide +kernel
      have hl : raw42206step2Labels = labelEmbedding1 ∘ raw42206step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42206step2 raw42206step2Labels raw42206step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3881 node3881Labels := by rfl

def raw42207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1]]
def raw42207Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42207step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw42207step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42207step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw42207step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42207step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42207step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42207step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42207step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42207 raw42207Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw42207 raw42207Labels = mixedMoment B raw42207step0 raw42207step0Labels := by
      have hz : ∀ j, raw42207 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42207step0 = (fun i j => raw42207 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42207step0 raw42207; decide +kernel
      have hl : raw42207step0Labels = raw42207Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42207 raw42207Labels permutation434 hz
    mixedMoment B raw42207step0 raw42207step0Labels = mixedMoment B raw42207step1 raw42207step1Labels := by
      have ha : raw42207step1 = (fun i j => raw42207step0 (permutation81 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42207step1 raw42207step0; decide +kernel
      have hl : raw42207step1Labels = raw42207step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42207step0 raw42207step0Labels permutation81 permutation4
    mixedMoment B raw42207step1 raw42207step1Labels = mixedMoment B raw42207step2 raw42207step2Labels := by
      have ha : raw42207step2 = -raw42207step1 := by apply Matrix.ext; change ∀ i j, raw42207step2 i j = -(raw42207step1 i j); unfold raw42207step2 raw42207step1; decide +kernel
      have hl : raw42207step2Labels = raw42207step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42207step2 raw42207step2Labels = mixedMoment B raw42207step3 raw42207step3Labels := by
      have ha : raw42207step3 = raw42207step2 := by apply Matrix.ext; unfold raw42207step3 raw42207step2; decide +kernel
      have hl : raw42207step2Labels = labelEmbedding10 ∘ raw42207step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42207step2 raw42207step2Labels raw42207step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

def raw42208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw42208Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw42208step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42208step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw42208step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42208step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw42208step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42208 raw42208Labels = mixedMoment B node2729 node2729Labels := by
  calc
    mixedMoment B raw42208 raw42208Labels = mixedMoment B raw42208step0 raw42208step0Labels := by
      have hz : ∀ j, raw42208 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42208step0 = (fun i j => raw42208 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42208step0 raw42208; decide +kernel
      have hl : raw42208step0Labels = raw42208Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42208 raw42208Labels permutation434 hz
    mixedMoment B raw42208step0 raw42208step0Labels = mixedMoment B raw42208step1 raw42208step1Labels := by
      have ha : raw42208step1 = (fun i j => raw42208step0 (permutation114 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42208step1 raw42208step0; decide +kernel
      have hl : raw42208step1Labels = raw42208step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42208step0 raw42208step0Labels permutation114 permutation4
    mixedMoment B raw42208step1 raw42208step1Labels = mixedMoment B raw42208step2 raw42208step2Labels := by
      have ha : raw42208step2 = raw42208step1 := by apply Matrix.ext; unfold raw42208step2 raw42208step1; decide +kernel
      have hl : raw42208step1Labels = labelEmbedding1 ∘ raw42208step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42208step1 raw42208step1Labels raw42208step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2729 node2729Labels := by rfl

def raw42209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, 0, 0], ![1, -3, 2], ![2, 0, -2]]
def raw42209Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42209step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -3, 2], ![2, 0, -2]]
def raw42209step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42209step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw42209step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42209step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw42209step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42209 raw42209Labels = mixedMoment B node5264 node5264Labels := by
  calc
    mixedMoment B raw42209 raw42209Labels = mixedMoment B raw42209step0 raw42209step0Labels := by
      have hz : ∀ j, raw42209 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42209step0 = (fun i j => raw42209 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42209step0 raw42209; decide +kernel
      have hl : raw42209step0Labels = raw42209Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42209 raw42209Labels permutation434 hz
    mixedMoment B raw42209step0 raw42209step0Labels = mixedMoment B raw42209step1 raw42209step1Labels := by
      have ha : raw42209step1 = (fun i j => raw42209step0 (permutation114 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42209step1 raw42209step0; decide +kernel
      have hl : raw42209step1Labels = raw42209step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42209step0 raw42209step0Labels permutation114 permutation4
    mixedMoment B raw42209step1 raw42209step1Labels = mixedMoment B raw42209step2 raw42209step2Labels := by
      have ha : raw42209step2 = raw42209step1 := by apply Matrix.ext; unfold raw42209step2 raw42209step1; decide +kernel
      have hl : raw42209step1Labels = labelEmbedding10 ∘ raw42209step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42209step1 raw42209step1Labels raw42209step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5264 node5264Labels := by rfl

def raw42210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42210Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42210step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw42210step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42210step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42210step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42210step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw42210step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42210 raw42210Labels = mixedMoment B node3872 node3872Labels := by
  calc
    mixedMoment B raw42210 raw42210Labels = mixedMoment B raw42210step0 raw42210step0Labels := by
      have ha : raw42210step0 = (fun i j => raw42210 (permutation356 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42210step0 raw42210; decide +kernel
      have hl : raw42210step0Labels = raw42210Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42210 raw42210Labels permutation356 permutation4
    mixedMoment B raw42210step0 raw42210step0Labels = mixedMoment B raw42210step1 raw42210step1Labels := by
      have ha : raw42210step1 = -raw42210step0 := by apply Matrix.ext; change ∀ i j, raw42210step1 i j = -(raw42210step0 i j); unfold raw42210step1 raw42210step0; decide +kernel
      have hl : raw42210step1Labels = raw42210step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42210step1 raw42210step1Labels = mixedMoment B raw42210step2 raw42210step2Labels := by
      have ha : raw42210step2 = raw42210step1 := by apply Matrix.ext; unfold raw42210step2 raw42210step1; decide +kernel
      have hl : raw42210step1Labels = labelEmbedding1 ∘ raw42210step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42210step1 raw42210step1Labels raw42210step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3872 node3872Labels := by rfl

def raw42211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw42211Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42211step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42211step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42211step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42211step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42211 raw42211Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw42211 raw42211Labels = mixedMoment B raw42211step0 raw42211step0Labels := by
      have ha : raw42211step0 = (fun i j => raw42211 (permutation661 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42211step0 raw42211; decide +kernel
      have hl : raw42211step0Labels = raw42211Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42211 raw42211Labels permutation661 permutation5
    mixedMoment B raw42211step0 raw42211step0Labels = mixedMoment B raw42211step1 raw42211step1Labels := by
      have ha : raw42211step1 = raw42211step0 := by apply Matrix.ext; unfold raw42211step1 raw42211step0; decide +kernel
      have hl : raw42211step0Labels = labelEmbedding9 ∘ raw42211step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42211step0 raw42211step0Labels raw42211step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw42212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42212Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42212step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw42212step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42212step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42212step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42212step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42212step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42212 raw42212Labels = mixedMoment B node3880 node3880Labels := by
  calc
    mixedMoment B raw42212 raw42212Labels = mixedMoment B raw42212step0 raw42212step0Labels := by
      have ha : raw42212step0 = (fun i j => raw42212 (permutation351 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42212step0 raw42212; decide +kernel
      have hl : raw42212step0Labels = raw42212Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42212 raw42212Labels permutation351 permutation4
    mixedMoment B raw42212step0 raw42212step0Labels = mixedMoment B raw42212step1 raw42212step1Labels := by
      have ha : raw42212step1 = -raw42212step0 := by apply Matrix.ext; change ∀ i j, raw42212step1 i j = -(raw42212step0 i j); unfold raw42212step1 raw42212step0; decide +kernel
      have hl : raw42212step1Labels = raw42212step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42212step1 raw42212step1Labels = mixedMoment B raw42212step2 raw42212step2Labels := by
      have ha : raw42212step2 = raw42212step1 := by apply Matrix.ext; unfold raw42212step2 raw42212step1; decide +kernel
      have hl : raw42212step1Labels = labelEmbedding1 ∘ raw42212step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42212step1 raw42212step1Labels raw42212step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3880 node3880Labels := by rfl

def raw42213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw42213Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42213step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw42213step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42213step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42213step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42213step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw42213step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42213 raw42213Labels = mixedMoment B node5445 node5445Labels := by
  calc
    mixedMoment B raw42213 raw42213Labels = mixedMoment B raw42213step0 raw42213step0Labels := by
      have ha : raw42213step0 = (fun i j => raw42213 (permutation351 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42213step0 raw42213; decide +kernel
      have hl : raw42213step0Labels = raw42213Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42213 raw42213Labels permutation351 permutation4
    mixedMoment B raw42213step0 raw42213step0Labels = mixedMoment B raw42213step1 raw42213step1Labels := by
      have ha : raw42213step1 = -raw42213step0 := by apply Matrix.ext; change ∀ i j, raw42213step1 i j = -(raw42213step0 i j); unfold raw42213step1 raw42213step0; decide +kernel
      have hl : raw42213step1Labels = raw42213step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42213step1 raw42213step1Labels = mixedMoment B raw42213step2 raw42213step2Labels := by
      have ha : raw42213step2 = raw42213step1 := by apply Matrix.ext; unfold raw42213step2 raw42213step1; decide +kernel
      have hl : raw42213step1Labels = labelEmbedding10 ∘ raw42213step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42213step1 raw42213step1Labels raw42213step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5445 node5445Labels := by rfl

def raw42214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42214Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42214step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw42214step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42214step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42214step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42214step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw42214step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42214 raw42214Labels = mixedMoment B node3866 node3866Labels := by
  calc
    mixedMoment B raw42214 raw42214Labels = mixedMoment B raw42214step0 raw42214step0Labels := by
      have ha : raw42214step0 = (fun i j => raw42214 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42214step0 raw42214; decide +kernel
      have hl : raw42214step0Labels = raw42214Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42214 raw42214Labels permutation682 permutation2
    mixedMoment B raw42214step0 raw42214step0Labels = mixedMoment B raw42214step1 raw42214step1Labels := by
      have ha : raw42214step1 = -raw42214step0 := by apply Matrix.ext; change ∀ i j, raw42214step1 i j = -(raw42214step0 i j); unfold raw42214step1 raw42214step0; decide +kernel
      have hl : raw42214step1Labels = raw42214step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42214step1 raw42214step1Labels = mixedMoment B raw42214step2 raw42214step2Labels := by
      have ha : raw42214step2 = raw42214step1 := by apply Matrix.ext; unfold raw42214step2 raw42214step1; decide +kernel
      have hl : raw42214step1Labels = labelEmbedding1 ∘ raw42214step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42214step1 raw42214step1Labels raw42214step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3866 node3866Labels := by rfl

def raw42215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -1, 1], ![1, -2, 1], ![2, 0, -2]]
def raw42215Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42215step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw42215step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42215 raw42215Labels = mixedMoment B node5382 node5382Labels := by
  calc
    mixedMoment B raw42215 raw42215Labels = mixedMoment B raw42215step0 raw42215step0Labels := by
      have ha : raw42215step0 = (fun i j => raw42215 (permutation414 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42215step0 raw42215; decide +kernel
      have hl : raw42215step0Labels = raw42215Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42215 raw42215Labels permutation414 permutation6
    _ = mixedMoment B node5382 node5382Labels := by rfl

def raw42216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42216Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42216step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw42216step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42216step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42216step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42216step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw42216step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42216 raw42216Labels = mixedMoment B node3834 node3834Labels := by
  calc
    mixedMoment B raw42216 raw42216Labels = mixedMoment B raw42216step0 raw42216step0Labels := by
      have ha : raw42216step0 = (fun i j => raw42216 (permutation682 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42216step0 raw42216; decide +kernel
      have hl : raw42216step0Labels = raw42216Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42216 raw42216Labels permutation682 permutation2
    mixedMoment B raw42216step0 raw42216step0Labels = mixedMoment B raw42216step1 raw42216step1Labels := by
      have ha : raw42216step1 = -raw42216step0 := by apply Matrix.ext; change ∀ i j, raw42216step1 i j = -(raw42216step0 i j); unfold raw42216step1 raw42216step0; decide +kernel
      have hl : raw42216step1Labels = raw42216step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42216step1 raw42216step1Labels = mixedMoment B raw42216step2 raw42216step2Labels := by
      have ha : raw42216step2 = raw42216step1 := by apply Matrix.ext; unfold raw42216step2 raw42216step1; decide +kernel
      have hl : raw42216step1Labels = labelEmbedding1 ∘ raw42216step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42216step1 raw42216step1Labels raw42216step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3834 node3834Labels := by rfl

def raw42217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![0, -2, 2], ![1, -1, 0], ![2, 0, -2]]
def raw42217Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42217step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42217step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42217step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42217step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42217 raw42217Labels = mixedMoment B node5381 node5381Labels := by
  calc
    mixedMoment B raw42217 raw42217Labels = mixedMoment B raw42217step0 raw42217step0Labels := by
      have ha : raw42217step0 = (fun i j => raw42217 (permutation643 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42217step0 raw42217; decide +kernel
      have hl : raw42217step0Labels = raw42217Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42217 raw42217Labels permutation643 permutation7
    mixedMoment B raw42217step0 raw42217step0Labels = mixedMoment B raw42217step1 raw42217step1Labels := by
      have ha : raw42217step1 = raw42217step0 := by apply Matrix.ext; unfold raw42217step1 raw42217step0; decide +kernel
      have hl : raw42217step0Labels = labelEmbedding6 ∘ raw42217step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42217step0 raw42217step0Labels raw42217step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5381 node5381Labels := by rfl

def raw42218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw42218Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42218step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42218step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42218step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42218step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42218 raw42218Labels = mixedMoment B node2708 node2708Labels := by
  calc
    mixedMoment B raw42218 raw42218Labels = mixedMoment B raw42218step0 raw42218step0Labels := by
      have ha : raw42218step0 = (fun i j => raw42218 (permutation615 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42218step0 raw42218; decide +kernel
      have hl : raw42218step0Labels = raw42218Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42218 raw42218Labels permutation615 permutation4
    mixedMoment B raw42218step0 raw42218step0Labels = mixedMoment B raw42218step1 raw42218step1Labels := by
      have ha : raw42218step1 = raw42218step0 := by apply Matrix.ext; unfold raw42218step1 raw42218step0; decide +kernel
      have hl : raw42218step0Labels = labelEmbedding1 ∘ raw42218step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42218step0 raw42218step0Labels raw42218step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2708 node2708Labels := by rfl

def raw42219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, -3, 2]]
def raw42219Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42219step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42219step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42219step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw42219step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42219 raw42219Labels = mixedMoment B node5249 node5249Labels := by
  calc
    mixedMoment B raw42219 raw42219Labels = mixedMoment B raw42219step0 raw42219step0Labels := by
      have ha : raw42219step0 = (fun i j => raw42219 (permutation615 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42219step0 raw42219; decide +kernel
      have hl : raw42219step0Labels = raw42219Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42219 raw42219Labels permutation615 permutation4
    mixedMoment B raw42219step0 raw42219step0Labels = mixedMoment B raw42219step1 raw42219step1Labels := by
      have ha : raw42219step1 = raw42219step0 := by apply Matrix.ext; unfold raw42219step1 raw42219step0; decide +kernel
      have hl : raw42219step0Labels = labelEmbedding10 ∘ raw42219step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42219step0 raw42219step0Labels raw42219step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5249 node5249Labels := by rfl

def raw42220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw42220Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42220step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw42220step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42220step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42220step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42220step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42220step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42220 raw42220Labels = mixedMoment B node3871 node3871Labels := by
  calc
    mixedMoment B raw42220 raw42220Labels = mixedMoment B raw42220step0 raw42220step0Labels := by
      have ha : raw42220step0 = (fun i j => raw42220 (permutation352 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42220step0 raw42220; decide +kernel
      have hl : raw42220step0Labels = raw42220Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42220 raw42220Labels permutation352 permutation4
    mixedMoment B raw42220step0 raw42220step0Labels = mixedMoment B raw42220step1 raw42220step1Labels := by
      have ha : raw42220step1 = -raw42220step0 := by apply Matrix.ext; change ∀ i j, raw42220step1 i j = -(raw42220step0 i j); unfold raw42220step1 raw42220step0; decide +kernel
      have hl : raw42220step1Labels = raw42220step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42220step1 raw42220step1Labels = mixedMoment B raw42220step2 raw42220step2Labels := by
      have ha : raw42220step2 = raw42220step1 := by apply Matrix.ext; unfold raw42220step2 raw42220step1; decide +kernel
      have hl : raw42220step1Labels = labelEmbedding1 ∘ raw42220step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42220step1 raw42220step1Labels raw42220step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3871 node3871Labels := by rfl

def raw42221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, 0, -1], ![1, -1, 0], ![1, -2, 1]]
def raw42221Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42221step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42221step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42221 raw42221Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw42221 raw42221Labels = mixedMoment B raw42221step0 raw42221step0Labels := by
      have ha : raw42221step0 = (fun i j => raw42221 (permutation389 i) (permutation6 j)) := by apply Matrix.ext; unfold raw42221step0 raw42221; decide +kernel
      have hl : raw42221step0Labels = raw42221Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42221 raw42221Labels permutation389 permutation6
    _ = mixedMoment B node5430 node5430Labels := by rfl

def raw42222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42222Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42222step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw42222step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42222step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42222step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42222step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42222step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42222 raw42222Labels = mixedMoment B node3882 node3882Labels := by
  calc
    mixedMoment B raw42222 raw42222Labels = mixedMoment B raw42222step0 raw42222step0Labels := by
      have ha : raw42222step0 = (fun i j => raw42222 (permutation346 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42222step0 raw42222; decide +kernel
      have hl : raw42222step0Labels = raw42222Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42222 raw42222Labels permutation346 permutation4
    mixedMoment B raw42222step0 raw42222step0Labels = mixedMoment B raw42222step1 raw42222step1Labels := by
      have ha : raw42222step1 = -raw42222step0 := by apply Matrix.ext; change ∀ i j, raw42222step1 i j = -(raw42222step0 i j); unfold raw42222step1 raw42222step0; decide +kernel
      have hl : raw42222step1Labels = raw42222step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42222step1 raw42222step1Labels = mixedMoment B raw42222step2 raw42222step2Labels := by
      have ha : raw42222step2 = raw42222step1 := by apply Matrix.ext; unfold raw42222step2 raw42222step1; decide +kernel
      have hl : raw42222step1Labels = labelEmbedding1 ∘ raw42222step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42222step1 raw42222step1Labels raw42222step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3882 node3882Labels := by rfl

def raw42223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42223Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42223step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw42223step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42223step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42223step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42223step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw42223step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42223 raw42223Labels = mixedMoment B node5447 node5447Labels := by
  calc
    mixedMoment B raw42223 raw42223Labels = mixedMoment B raw42223step0 raw42223step0Labels := by
      have ha : raw42223step0 = (fun i j => raw42223 (permutation346 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42223step0 raw42223; decide +kernel
      have hl : raw42223step0Labels = raw42223Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42223 raw42223Labels permutation346 permutation4
    mixedMoment B raw42223step0 raw42223step0Labels = mixedMoment B raw42223step1 raw42223step1Labels := by
      have ha : raw42223step1 = -raw42223step0 := by apply Matrix.ext; change ∀ i j, raw42223step1 i j = -(raw42223step0 i j); unfold raw42223step1 raw42223step0; decide +kernel
      have hl : raw42223step1Labels = raw42223step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42223step1 raw42223step1Labels = mixedMoment B raw42223step2 raw42223step2Labels := by
      have ha : raw42223step2 = raw42223step1 := by apply Matrix.ext; unfold raw42223step2 raw42223step1; decide +kernel
      have hl : raw42223step1Labels = labelEmbedding10 ∘ raw42223step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42223step1 raw42223step1Labels raw42223step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5447 node5447Labels := by rfl

def raw42224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw42224Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42224step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw42224step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42224step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -3, 0], ![0, 1, -1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw42224step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42224step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw42224step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42224step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw42224step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42224 raw42224Labels = mixedMoment B node3227 node3227Labels := by
  calc
    mixedMoment B raw42224 raw42224Labels = mixedMoment B raw42224step0 raw42224step0Labels := by
      have hz : ∀ j, raw42224 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42224step0 = (fun i j => raw42224 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42224step0 raw42224; decide +kernel
      have hl : raw42224step0Labels = raw42224Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42224 raw42224Labels permutation520 hz
    mixedMoment B raw42224step0 raw42224step0Labels = mixedMoment B raw42224step1 raw42224step1Labels := by
      have ha : raw42224step1 = (fun i j => raw42224step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42224step1 raw42224step0; decide +kernel
      have hl : raw42224step1Labels = raw42224step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42224step0 raw42224step0Labels permutation145 permutation2
    mixedMoment B raw42224step1 raw42224step1Labels = mixedMoment B raw42224step2 raw42224step2Labels := by
      have ha : raw42224step2 = -raw42224step1 := by apply Matrix.ext; change ∀ i j, raw42224step2 i j = -(raw42224step1 i j); unfold raw42224step2 raw42224step1; decide +kernel
      have hl : raw42224step2Labels = raw42224step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42224step2 raw42224step2Labels = mixedMoment B raw42224step3 raw42224step3Labels := by
      have ha : raw42224step3 = raw42224step2 := by apply Matrix.ext; unfold raw42224step3 raw42224step2; decide +kernel
      have hl : raw42224step2Labels = labelEmbedding1 ∘ raw42224step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42224step2 raw42224step2Labels raw42224step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3227 node3227Labels := by rfl

def raw42225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![0, 0, 0], ![3, -3, 0]]
def raw42225Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42225step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw42225step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42225step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw42225step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42225step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42225step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42225step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42225step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42225 raw42225Labels = mixedMoment B node4888 node4888Labels := by
  calc
    mixedMoment B raw42225 raw42225Labels = mixedMoment B raw42225step0 raw42225step0Labels := by
      have hz : ∀ j, raw42225 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw42225step0 = (fun i j => raw42225 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw42225step0 raw42225; decide +kernel
      have hl : raw42225step0Labels = raw42225Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42225 raw42225Labels permutation520 hz
    mixedMoment B raw42225step0 raw42225step0Labels = mixedMoment B raw42225step1 raw42225step1Labels := by
      have ha : raw42225step1 = (fun i j => raw42225step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42225step1 raw42225step0; decide +kernel
      have hl : raw42225step1Labels = raw42225step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42225step0 raw42225step0Labels permutation145 permutation3
    mixedMoment B raw42225step1 raw42225step1Labels = mixedMoment B raw42225step2 raw42225step2Labels := by
      have ha : raw42225step2 = -raw42225step1 := by apply Matrix.ext; change ∀ i j, raw42225step2 i j = -(raw42225step1 i j); unfold raw42225step2 raw42225step1; decide +kernel
      have hl : raw42225step2Labels = raw42225step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42225step2 raw42225step2Labels = mixedMoment B raw42225step3 raw42225step3Labels := by
      have ha : raw42225step3 = raw42225step2 := by apply Matrix.ext; unfold raw42225step3 raw42225step2; decide +kernel
      have hl : raw42225step2Labels = labelEmbedding7 ∘ raw42225step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42225step2 raw42225step2Labels raw42225step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4888 node4888Labels := by rfl

def raw42226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw42226Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42226step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42226step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42226step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42226step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42226 raw42226Labels = mixedMoment B node3085 node3085Labels := by
  calc
    mixedMoment B raw42226 raw42226Labels = mixedMoment B raw42226step0 raw42226step0Labels := by
      have ha : raw42226step0 = (fun i j => raw42226 (permutation617 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42226step0 raw42226; decide +kernel
      have hl : raw42226step0Labels = raw42226Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42226 raw42226Labels permutation617 permutation4
    mixedMoment B raw42226step0 raw42226step0Labels = mixedMoment B raw42226step1 raw42226step1Labels := by
      have ha : raw42226step1 = raw42226step0 := by apply Matrix.ext; unfold raw42226step1 raw42226step0; decide +kernel
      have hl : raw42226step0Labels = labelEmbedding1 ∘ raw42226step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42226step0 raw42226step0Labels raw42226step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3085 node3085Labels := by rfl

def raw42227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw42227Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42227step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw42227step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42227step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw42227step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42227 raw42227Labels = mixedMoment B node5256 node5256Labels := by
  calc
    mixedMoment B raw42227 raw42227Labels = mixedMoment B raw42227step0 raw42227step0Labels := by
      have ha : raw42227step0 = (fun i j => raw42227 (permutation674 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42227step0 raw42227; decide +kernel
      have hl : raw42227step0Labels = raw42227Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42227 raw42227Labels permutation674 permutation5
    mixedMoment B raw42227step0 raw42227step0Labels = mixedMoment B raw42227step1 raw42227step1Labels := by
      have ha : raw42227step1 = raw42227step0 := by apply Matrix.ext; unfold raw42227step1 raw42227step0; decide +kernel
      have hl : raw42227step0Labels = labelEmbedding9 ∘ raw42227step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42227step0 raw42227step0Labels raw42227step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5256 node5256Labels := by rfl

def raw42228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42228Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42228step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42228step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42228 raw42228Labels = mixedMoment B node3977 node3977Labels := by
  calc
    mixedMoment B raw42228 raw42228Labels = mixedMoment B raw42228step0 raw42228step0Labels := by
      have ha : raw42228step0 = raw42228 := by apply Matrix.ext; unfold raw42228step0 raw42228; decide +kernel
      have hl : raw42228Labels = labelEmbedding1 ∘ raw42228step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42228 raw42228Labels raw42228step0Labels labelEmbedding1 hl
    _ = mixedMoment B node3977 node3977Labels := by rfl

def raw42229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw42229Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42229step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw42229step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42229step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42229step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42229step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42229step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42229 raw42229Labels = mixedMoment B node5405 node5405Labels := by
  calc
    mixedMoment B raw42229 raw42229Labels = mixedMoment B raw42229step0 raw42229step0Labels := by
      have ha : raw42229step0 = (fun i j => raw42229 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42229step0 raw42229; decide +kernel
      have hl : raw42229step0Labels = raw42229Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42229 raw42229Labels permutation682 permutation3
    mixedMoment B raw42229step0 raw42229step0Labels = mixedMoment B raw42229step1 raw42229step1Labels := by
      have ha : raw42229step1 = -raw42229step0 := by apply Matrix.ext; change ∀ i j, raw42229step1 i j = -(raw42229step0 i j); unfold raw42229step1 raw42229step0; decide +kernel
      have hl : raw42229step1Labels = raw42229step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42229step1 raw42229step1Labels = mixedMoment B raw42229step2 raw42229step2Labels := by
      have ha : raw42229step2 = raw42229step1 := by apply Matrix.ext; unfold raw42229step2 raw42229step1; decide +kernel
      have hl : raw42229step1Labels = labelEmbedding7 ∘ raw42229step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42229step1 raw42229step1Labels raw42229step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5405 node5405Labels := by rfl

def raw42230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42230Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42230step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42230step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42230 raw42230Labels = mixedMoment B node3976 node3976Labels := by
  calc
    mixedMoment B raw42230 raw42230Labels = mixedMoment B raw42230step0 raw42230step0Labels := by
      have ha : raw42230step0 = raw42230 := by apply Matrix.ext; unfold raw42230step0 raw42230; decide +kernel
      have hl : raw42230Labels = labelEmbedding1 ∘ raw42230step0Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42230 raw42230Labels raw42230step0Labels labelEmbedding1 hl
    _ = mixedMoment B node3976 node3976Labels := by rfl

def raw42231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw42231Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42231step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw42231step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42231step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42231step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw42231step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw42231step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42231 raw42231Labels = mixedMoment B node5471 node5471Labels := by
  calc
    mixedMoment B raw42231 raw42231Labels = mixedMoment B raw42231step0 raw42231step0Labels := by
      have ha : raw42231step0 = (fun i j => raw42231 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw42231step0 raw42231; decide +kernel
      have hl : raw42231step0Labels = raw42231Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42231 raw42231Labels permutation682 permutation3
    mixedMoment B raw42231step0 raw42231step0Labels = mixedMoment B raw42231step1 raw42231step1Labels := by
      have ha : raw42231step1 = -raw42231step0 := by apply Matrix.ext; change ∀ i j, raw42231step1 i j = -(raw42231step0 i j); unfold raw42231step1 raw42231step0; decide +kernel
      have hl : raw42231step1Labels = raw42231step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw42231step1 raw42231step1Labels = mixedMoment B raw42231step2 raw42231step2Labels := by
      have ha : raw42231step2 = raw42231step1 := by apply Matrix.ext; unfold raw42231step2 raw42231step1; decide +kernel
      have hl : raw42231step1Labels = labelEmbedding7 ∘ raw42231step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42231step1 raw42231step1Labels raw42231step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5471 node5471Labels := by rfl

def raw42232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw42232Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42232step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42232step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42232step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42232step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42232 raw42232Labels = mixedMoment B node2728 node2728Labels := by
  calc
    mixedMoment B raw42232 raw42232Labels = mixedMoment B raw42232step0 raw42232step0Labels := by
      have ha : raw42232step0 = (fun i j => raw42232 (permutation538 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42232step0 raw42232; decide +kernel
      have hl : raw42232step0Labels = raw42232Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42232 raw42232Labels permutation538 permutation4
    mixedMoment B raw42232step0 raw42232step0Labels = mixedMoment B raw42232step1 raw42232step1Labels := by
      have ha : raw42232step1 = raw42232step0 := by apply Matrix.ext; unfold raw42232step1 raw42232step0; decide +kernel
      have hl : raw42232step0Labels = labelEmbedding1 ∘ raw42232step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42232step0 raw42232step0Labels raw42232step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2728 node2728Labels := by rfl

def raw42233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw42233Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42233step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42233step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw42233step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw42233step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42233 raw42233Labels = mixedMoment B node5263 node5263Labels := by
  calc
    mixedMoment B raw42233 raw42233Labels = mixedMoment B raw42233step0 raw42233step0Labels := by
      have ha : raw42233step0 = (fun i j => raw42233 (permutation538 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42233step0 raw42233; decide +kernel
      have hl : raw42233step0Labels = raw42233Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42233 raw42233Labels permutation538 permutation4
    mixedMoment B raw42233step0 raw42233step0Labels = mixedMoment B raw42233step1 raw42233step1Labels := by
      have ha : raw42233step1 = raw42233step0 := by apply Matrix.ext; unfold raw42233step1 raw42233step0; decide +kernel
      have hl : raw42233step0Labels = labelEmbedding10 ∘ raw42233step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42233step0 raw42233step0Labels raw42233step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5263 node5263Labels := by rfl

def raw42234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw42234Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw42234step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42234step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42234step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42234step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw42234step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42234 raw42234Labels = mixedMoment B node3097 node3097Labels := by
  calc
    mixedMoment B raw42234 raw42234Labels = mixedMoment B raw42234step0 raw42234step0Labels := by
      have hz : ∀ j, raw42234 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42234step0 = (fun i j => raw42234 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42234step0 raw42234; decide +kernel
      have hl : raw42234step0Labels = raw42234Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42234 raw42234Labels permutation434 hz
    mixedMoment B raw42234step0 raw42234step0Labels = mixedMoment B raw42234step1 raw42234step1Labels := by
      have ha : raw42234step1 = (fun i j => raw42234step0 (permutation134 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42234step1 raw42234step0; decide +kernel
      have hl : raw42234step1Labels = raw42234step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42234step0 raw42234step0Labels permutation134 permutation4
    mixedMoment B raw42234step1 raw42234step1Labels = mixedMoment B raw42234step2 raw42234step2Labels := by
      have ha : raw42234step2 = raw42234step1 := by apply Matrix.ext; unfold raw42234step2 raw42234step1; decide +kernel
      have hl : raw42234step1Labels = labelEmbedding1 ∘ raw42234step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42234step1 raw42234step1Labels raw42234step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3097 node3097Labels := by rfl

def raw42235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, 1, -2], ![2, -3, 1]]
def raw42235Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42235step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw42235step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42235step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42235step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42235step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42235step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42235 raw42235Labels = mixedMoment B node5289 node5289Labels := by
  calc
    mixedMoment B raw42235 raw42235Labels = mixedMoment B raw42235step0 raw42235step0Labels := by
      have hz : ∀ j, raw42235 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42235step0 = (fun i j => raw42235 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42235step0 raw42235; decide +kernel
      have hl : raw42235step0Labels = raw42235Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42235 raw42235Labels permutation434 hz
    mixedMoment B raw42235step0 raw42235step0Labels = mixedMoment B raw42235step1 raw42235step1Labels := by
      have ha : raw42235step1 = (fun i j => raw42235step0 (permutation139 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42235step1 raw42235step0; decide +kernel
      have hl : raw42235step1Labels = raw42235step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42235step0 raw42235step0Labels permutation139 permutation5
    mixedMoment B raw42235step1 raw42235step1Labels = mixedMoment B raw42235step2 raw42235step2Labels := by
      have ha : raw42235step2 = raw42235step1 := by apply Matrix.ext; unfold raw42235step2 raw42235step1; decide +kernel
      have hl : raw42235step1Labels = labelEmbedding9 ∘ raw42235step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42235step1 raw42235step1Labels raw42235step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5289 node5289Labels := by rfl

def raw42236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw42236Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42236step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw42236step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42236step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw42236step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42236step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw42236step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42236 raw42236Labels = mixedMoment B node2735 node2735Labels := by
  calc
    mixedMoment B raw42236 raw42236Labels = mixedMoment B raw42236step0 raw42236step0Labels := by
      have hz : ∀ j, raw42236 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42236step0 = (fun i j => raw42236 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42236step0 raw42236; decide +kernel
      have hl : raw42236step0Labels = raw42236Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42236 raw42236Labels permutation434 hz
    mixedMoment B raw42236step0 raw42236step0Labels = mixedMoment B raw42236step1 raw42236step1Labels := by
      have ha : raw42236step1 = (fun i j => raw42236step0 (permutation110 i) (permutation4 j)) := by apply Matrix.ext; unfold raw42236step1 raw42236step0; decide +kernel
      have hl : raw42236step1Labels = raw42236step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42236step0 raw42236step0Labels permutation110 permutation4
    mixedMoment B raw42236step1 raw42236step1Labels = mixedMoment B raw42236step2 raw42236step2Labels := by
      have ha : raw42236step2 = raw42236step1 := by apply Matrix.ext; unfold raw42236step2 raw42236step1; decide +kernel
      have hl : raw42236step1Labels = labelEmbedding1 ∘ raw42236step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42236step1 raw42236step1Labels raw42236step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2735 node2735Labels := by rfl

def raw42237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -3, 2], ![2, 1, -3]]
def raw42237Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -3, 2], ![2, 1, -3]]
def raw42237step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42237step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw42237step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw42237step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw42237step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42237 raw42237Labels = mixedMoment B node5173 node5173Labels := by
  calc
    mixedMoment B raw42237 raw42237Labels = mixedMoment B raw42237step0 raw42237step0Labels := by
      have hz : ∀ j, raw42237 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw42237step0 = (fun i j => raw42237 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw42237step0 raw42237; decide +kernel
      have hl : raw42237step0Labels = raw42237Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw42237 raw42237Labels permutation434 hz
    mixedMoment B raw42237step0 raw42237step0Labels = mixedMoment B raw42237step1 raw42237step1Labels := by
      have ha : raw42237step1 = (fun i j => raw42237step0 (permutation142 i) (permutation7 j)) := by apply Matrix.ext; unfold raw42237step1 raw42237step0; decide +kernel
      have hl : raw42237step1Labels = raw42237step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42237step0 raw42237step0Labels permutation142 permutation7
    mixedMoment B raw42237step1 raw42237step1Labels = mixedMoment B raw42237step2 raw42237step2Labels := by
      have ha : raw42237step2 = raw42237step1 := by apply Matrix.ext; unfold raw42237step2 raw42237step1; decide +kernel
      have hl : raw42237step1Labels = labelEmbedding6 ∘ raw42237step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42237step1 raw42237step1Labels raw42237step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5173 node5173Labels := by rfl

def raw42238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42238Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42238step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42238step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw42238step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw42238step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical42238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42238 raw42238Labels = mixedMoment B node3972 node3972Labels := by
  calc
    mixedMoment B raw42238 raw42238Labels = mixedMoment B raw42238step0 raw42238step0Labels := by
      have ha : raw42238step0 = (fun i j => raw42238 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw42238step0 raw42238; decide +kernel
      have hl : raw42238step0Labels = raw42238Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42238 raw42238Labels permutation158 permutation2
    mixedMoment B raw42238step0 raw42238step0Labels = mixedMoment B raw42238step1 raw42238step1Labels := by
      have ha : raw42238step1 = raw42238step0 := by apply Matrix.ext; unfold raw42238step1 raw42238step0; decide +kernel
      have hl : raw42238step0Labels = labelEmbedding1 ∘ raw42238step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42238step0 raw42238step0Labels raw42238step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3972 node3972Labels := by rfl

def raw42239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw42239Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw42239step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42239step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw42239step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw42239step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical42239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw42239 raw42239Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw42239 raw42239Labels = mixedMoment B raw42239step0 raw42239step0Labels := by
      have ha : raw42239step0 = (fun i j => raw42239 (permutation654 i) (permutation5 j)) := by apply Matrix.ext; unfold raw42239step0 raw42239; decide +kernel
      have hl : raw42239step0Labels = raw42239Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw42239 raw42239Labels permutation654 permutation5
    mixedMoment B raw42239step0 raw42239step0Labels = mixedMoment B raw42239step1 raw42239step1Labels := by
      have ha : raw42239step1 = raw42239step0 := by apply Matrix.ext; unfold raw42239step1 raw42239step0; decide +kernel
      have hl : raw42239step0Labels = labelEmbedding9 ∘ raw42239step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw42239step0 raw42239step0Labels raw42239step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
