import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw17280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw17280Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17280step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw17280step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17280step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17280step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17280step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17280step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17280 raw17280Labels = mixedMoment B node3859 node3859Labels := by
  calc
    mixedMoment B raw17280 raw17280Labels = mixedMoment B raw17280step0 raw17280step0Labels := by
      have hz : ∀ j, raw17280 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17280step0 = (fun i j => raw17280 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17280step0 raw17280; decide +kernel
      have hl : raw17280step0Labels = raw17280Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17280 raw17280Labels permutation434 hz
    mixedMoment B raw17280step0 raw17280step0Labels = mixedMoment B raw17280step1 raw17280step1Labels := by
      have ha : raw17280step1 = (fun i j => raw17280step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17280step1 raw17280step0; decide +kernel
      have hl : raw17280step1Labels = raw17280step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17280step0 raw17280step0Labels permutation144 permutation7
    mixedMoment B raw17280step1 raw17280step1Labels = mixedMoment B raw17280step2 raw17280step2Labels := by
      have ha : raw17280step2 = raw17280step1 := by apply Matrix.ext; unfold raw17280step2 raw17280step1; decide +kernel
      have hl : raw17280step1Labels = labelEmbedding1 ∘ raw17280step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17280step1 raw17280step1Labels raw17280step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3859 node3859Labels := by rfl

def raw17281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw17281Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17281step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw17281step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17281step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17281step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17281step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17281step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17281 raw17281Labels = mixedMoment B node3998 node3998Labels := by
  calc
    mixedMoment B raw17281 raw17281Labels = mixedMoment B raw17281step0 raw17281step0Labels := by
      have hz : ∀ j, raw17281 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17281step0 = (fun i j => raw17281 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17281step0 raw17281; decide +kernel
      have hl : raw17281step0Labels = raw17281Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17281 raw17281Labels permutation434 hz
    mixedMoment B raw17281step0 raw17281step0Labels = mixedMoment B raw17281step1 raw17281step1Labels := by
      have ha : raw17281step1 = (fun i j => raw17281step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17281step1 raw17281step0; decide +kernel
      have hl : raw17281step1Labels = raw17281step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17281step0 raw17281step0Labels permutation144 permutation7
    mixedMoment B raw17281step1 raw17281step1Labels = mixedMoment B raw17281step2 raw17281step2Labels := by
      have ha : raw17281step2 = raw17281step1 := by apply Matrix.ext; unfold raw17281step2 raw17281step1; decide +kernel
      have hl : raw17281step1Labels = labelEmbedding1 ∘ raw17281step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17281step1 raw17281step1Labels raw17281step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3998 node3998Labels := by rfl

def raw17282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17282Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17282step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17282step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw17282step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17282step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17282step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17282step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw17282step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17282 raw17282Labels = mixedMoment B node3540 node3540Labels := by
  calc
    mixedMoment B raw17282 raw17282Labels = mixedMoment B raw17282step0 raw17282step0Labels := by
      have hz : ∀ j, raw17282 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17282step0 = (fun i j => raw17282 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17282step0 raw17282; decide +kernel
      have hl : raw17282step0Labels = raw17282Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17282 raw17282Labels permutation434 hz
    mixedMoment B raw17282step0 raw17282step0Labels = mixedMoment B raw17282step1 raw17282step1Labels := by
      have ha : raw17282step1 = (fun i j => raw17282step0 (permutation42 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17282step1 raw17282step0; decide +kernel
      have hl : raw17282step1Labels = raw17282step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17282step0 raw17282step0Labels permutation42 permutation5
    mixedMoment B raw17282step1 raw17282step1Labels = mixedMoment B raw17282step2 raw17282step2Labels := by
      have ha : raw17282step2 = -raw17282step1 := by apply Matrix.ext; change ∀ i j, raw17282step2 i j = -(raw17282step1 i j); unfold raw17282step2 raw17282step1; decide +kernel
      have hl : raw17282step2Labels = raw17282step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17282step2 raw17282step2Labels = mixedMoment B raw17282step3 raw17282step3Labels := by
      have ha : raw17282step3 = raw17282step2 := by apply Matrix.ext; unfold raw17282step3 raw17282step2; decide +kernel
      have hl : raw17282step2Labels = labelEmbedding1 ∘ raw17282step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17282step2 raw17282step2Labels raw17282step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3540 node3540Labels := by rfl

def raw17283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17283Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 2, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17283step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17283step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17283step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17283step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17283step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17283 raw17283Labels = mixedMoment B node3884 node3884Labels := by
  calc
    mixedMoment B raw17283 raw17283Labels = mixedMoment B raw17283step0 raw17283step0Labels := by
      have hz : ∀ j, raw17283 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17283step0 = (fun i j => raw17283 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17283step0 raw17283; decide +kernel
      have hl : raw17283step0Labels = raw17283Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17283 raw17283Labels permutation434 hz
    mixedMoment B raw17283step0 raw17283step0Labels = mixedMoment B raw17283step1 raw17283step1Labels := by
      have ha : raw17283step1 = (fun i j => raw17283step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17283step1 raw17283step0; decide +kernel
      have hl : raw17283step1Labels = raw17283step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17283step0 raw17283step0Labels permutation145 permutation7
    mixedMoment B raw17283step1 raw17283step1Labels = mixedMoment B raw17283step2 raw17283step2Labels := by
      have ha : raw17283step2 = raw17283step1 := by apply Matrix.ext; unfold raw17283step2 raw17283step1; decide +kernel
      have hl : raw17283step1Labels = labelEmbedding1 ∘ raw17283step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17283step1 raw17283step1Labels raw17283step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3884 node3884Labels := by rfl

def raw17284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17284Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17284step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17284step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17284step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17284step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17284 raw17284Labels = mixedMoment B node3848 node3848Labels := by
  calc
    mixedMoment B raw17284 raw17284Labels = mixedMoment B raw17284step0 raw17284step0Labels := by
      have ha : raw17284step0 = (fun i j => raw17284 (permutation640 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17284step0 raw17284; decide +kernel
      have hl : raw17284step0Labels = raw17284Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17284 raw17284Labels permutation640 permutation7
    mixedMoment B raw17284step0 raw17284step0Labels = mixedMoment B raw17284step1 raw17284step1Labels := by
      have ha : raw17284step1 = raw17284step0 := by apply Matrix.ext; unfold raw17284step1 raw17284step0; decide +kernel
      have hl : raw17284step0Labels = labelEmbedding1 ∘ raw17284step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17284step0 raw17284step0Labels raw17284step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3848 node3848Labels := by rfl

def raw17285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw17285Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17285step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw17285step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17285step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17285step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17285step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw17285step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17285 raw17285Labels = mixedMoment B node3858 node3858Labels := by
  calc
    mixedMoment B raw17285 raw17285Labels = mixedMoment B raw17285step0 raw17285step0Labels := by
      have hz : ∀ j, raw17285 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17285step0 = (fun i j => raw17285 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17285step0 raw17285; decide +kernel
      have hl : raw17285step0Labels = raw17285Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17285 raw17285Labels permutation434 hz
    mixedMoment B raw17285step0 raw17285step0Labels = mixedMoment B raw17285step1 raw17285step1Labels := by
      have ha : raw17285step1 = (fun i j => raw17285step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17285step1 raw17285step0; decide +kernel
      have hl : raw17285step1Labels = raw17285step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17285step0 raw17285step0Labels permutation143 permutation7
    mixedMoment B raw17285step1 raw17285step1Labels = mixedMoment B raw17285step2 raw17285step2Labels := by
      have ha : raw17285step2 = raw17285step1 := by apply Matrix.ext; unfold raw17285step2 raw17285step1; decide +kernel
      have hl : raw17285step1Labels = labelEmbedding1 ∘ raw17285step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17285step1 raw17285step1Labels raw17285step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3858 node3858Labels := by rfl

def raw17286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw17286Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17286step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw17286step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17286step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17286step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17286step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17286step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17286 raw17286Labels = mixedMoment B node3997 node3997Labels := by
  calc
    mixedMoment B raw17286 raw17286Labels = mixedMoment B raw17286step0 raw17286step0Labels := by
      have hz : ∀ j, raw17286 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17286step0 = (fun i j => raw17286 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17286step0 raw17286; decide +kernel
      have hl : raw17286step0Labels = raw17286Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17286 raw17286Labels permutation434 hz
    mixedMoment B raw17286step0 raw17286step0Labels = mixedMoment B raw17286step1 raw17286step1Labels := by
      have ha : raw17286step1 = (fun i j => raw17286step0 (permutation115 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17286step1 raw17286step0; decide +kernel
      have hl : raw17286step1Labels = raw17286step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17286step0 raw17286step0Labels permutation115 permutation5
    mixedMoment B raw17286step1 raw17286step1Labels = mixedMoment B raw17286step2 raw17286step2Labels := by
      have ha : raw17286step2 = raw17286step1 := by apply Matrix.ext; unfold raw17286step2 raw17286step1; decide +kernel
      have hl : raw17286step1Labels = labelEmbedding1 ∘ raw17286step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17286step1 raw17286step1Labels raw17286step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3997 node3997Labels := by rfl

def raw17287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17287Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17287step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17287step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![0, -2, 2], ![-2, 1, 1]]
def raw17287step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17287step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw17287step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17287step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -1, 1], ![0, 1, -1], ![0, 2, -2], ![2, -1, -1]]
def raw17287step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17287 raw17287Labels = mixedMoment B node3606 node3606Labels := by
  calc
    mixedMoment B raw17287 raw17287Labels = mixedMoment B raw17287step0 raw17287step0Labels := by
      have hz : ∀ j, raw17287 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17287step0 = (fun i j => raw17287 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17287step0 raw17287; decide +kernel
      have hl : raw17287step0Labels = raw17287Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17287 raw17287Labels permutation434 hz
    mixedMoment B raw17287step0 raw17287step0Labels = mixedMoment B raw17287step1 raw17287step1Labels := by
      have ha : raw17287step1 = (fun i j => raw17287step0 (permutation33 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17287step1 raw17287step0; decide +kernel
      have hl : raw17287step1Labels = raw17287step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17287step0 raw17287step0Labels permutation33 permutation5
    mixedMoment B raw17287step1 raw17287step1Labels = mixedMoment B raw17287step2 raw17287step2Labels := by
      have ha : raw17287step2 = -raw17287step1 := by apply Matrix.ext; change ∀ i j, raw17287step2 i j = -(raw17287step1 i j); unfold raw17287step2 raw17287step1; decide +kernel
      have hl : raw17287step2Labels = raw17287step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17287step2 raw17287step2Labels = mixedMoment B raw17287step3 raw17287step3Labels := by
      have ha : raw17287step3 = raw17287step2 := by apply Matrix.ext; unfold raw17287step3 raw17287step2; decide +kernel
      have hl : raw17287step2Labels = labelEmbedding1 ∘ raw17287step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17287step2 raw17287step2Labels raw17287step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3606 node3606Labels := by rfl

def raw17288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17288Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17288step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17288step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17288step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw17288step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17288step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw17288step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17288 raw17288Labels = mixedMoment B node3815 node3815Labels := by
  calc
    mixedMoment B raw17288 raw17288Labels = mixedMoment B raw17288step0 raw17288step0Labels := by
      have hz : ∀ j, raw17288 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17288step0 = (fun i j => raw17288 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17288step0 raw17288; decide +kernel
      have hl : raw17288step0Labels = raw17288Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17288 raw17288Labels permutation434 hz
    mixedMoment B raw17288step0 raw17288step0Labels = mixedMoment B raw17288step1 raw17288step1Labels := by
      have ha : raw17288step1 = (fun i j => raw17288step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17288step1 raw17288step0; decide +kernel
      have hl : raw17288step1Labels = raw17288step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17288step0 raw17288step0Labels permutation144 permutation7
    mixedMoment B raw17288step1 raw17288step1Labels = mixedMoment B raw17288step2 raw17288step2Labels := by
      have ha : raw17288step2 = raw17288step1 := by apply Matrix.ext; unfold raw17288step2 raw17288step1; decide +kernel
      have hl : raw17288step1Labels = labelEmbedding1 ∘ raw17288step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17288step1 raw17288step1Labels raw17288step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3815 node3815Labels := by rfl

def raw17289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17289Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17289step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17289step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17289step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17289step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17289 raw17289Labels = mixedMoment B node3804 node3804Labels := by
  calc
    mixedMoment B raw17289 raw17289Labels = mixedMoment B raw17289step0 raw17289step0Labels := by
      have ha : raw17289step0 = (fun i j => raw17289 (permutation640 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17289step0 raw17289; decide +kernel
      have hl : raw17289step0Labels = raw17289Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17289 raw17289Labels permutation640 permutation7
    mixedMoment B raw17289step0 raw17289step0Labels = mixedMoment B raw17289step1 raw17289step1Labels := by
      have ha : raw17289step1 = raw17289step0 := by apply Matrix.ext; unfold raw17289step1 raw17289step0; decide +kernel
      have hl : raw17289step0Labels = labelEmbedding1 ∘ raw17289step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17289step0 raw17289step0Labels raw17289step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3804 node3804Labels := by rfl

def raw17290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![2, 0, -2]]
def raw17290Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17290step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw17290step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17290step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17290step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17290step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17290step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17290 raw17290Labels = mixedMoment B node3816 node3816Labels := by
  calc
    mixedMoment B raw17290 raw17290Labels = mixedMoment B raw17290step0 raw17290step0Labels := by
      have hz : ∀ j, raw17290 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17290step0 = (fun i j => raw17290 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17290step0 raw17290; decide +kernel
      have hl : raw17290step0Labels = raw17290Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17290 raw17290Labels permutation434 hz
    mixedMoment B raw17290step0 raw17290step0Labels = mixedMoment B raw17290step1 raw17290step1Labels := by
      have ha : raw17290step1 = (fun i j => raw17290step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17290step1 raw17290step0; decide +kernel
      have hl : raw17290step1Labels = raw17290step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17290step0 raw17290step0Labels permutation145 permutation7
    mixedMoment B raw17290step1 raw17290step1Labels = mixedMoment B raw17290step2 raw17290step2Labels := by
      have ha : raw17290step2 = raw17290step1 := by apply Matrix.ext; unfold raw17290step2 raw17290step1; decide +kernel
      have hl : raw17290step1Labels = labelEmbedding1 ∘ raw17290step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17290step1 raw17290step1Labels raw17290step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3816 node3816Labels := by rfl

def raw17291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![1, 1, -2]]
def raw17291Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17291step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw17291step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17291step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17291step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17291step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17291step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17291 raw17291Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw17291 raw17291Labels = mixedMoment B raw17291step0 raw17291step0Labels := by
      have hz : ∀ j, raw17291 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17291step0 = (fun i j => raw17291 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17291step0 raw17291; decide +kernel
      have hl : raw17291step0Labels = raw17291Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17291 raw17291Labels permutation434 hz
    mixedMoment B raw17291step0 raw17291step0Labels = mixedMoment B raw17291step1 raw17291step1Labels := by
      have ha : raw17291step1 = (fun i j => raw17291step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17291step1 raw17291step0; decide +kernel
      have hl : raw17291step1Labels = raw17291step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17291step0 raw17291step0Labels permutation145 permutation7
    mixedMoment B raw17291step1 raw17291step1Labels = mixedMoment B raw17291step2 raw17291step2Labels := by
      have ha : raw17291step2 = raw17291step1 := by apply Matrix.ext; unfold raw17291step2 raw17291step1; decide +kernel
      have hl : raw17291step1Labels = labelEmbedding1 ∘ raw17291step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17291step1 raw17291step1Labels raw17291step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3983 node3983Labels := by rfl

def raw17292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17292Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17292step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw17292step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17292step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw17292step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17292step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw17292step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17292 raw17292Labels = mixedMoment B node3517 node3517Labels := by
  calc
    mixedMoment B raw17292 raw17292Labels = mixedMoment B raw17292step0 raw17292step0Labels := by
      have ha : raw17292step0 = (fun i j => raw17292 (permutation180 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17292step0 raw17292; decide +kernel
      have hl : raw17292step0Labels = raw17292Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17292 raw17292Labels permutation180 permutation5
    mixedMoment B raw17292step0 raw17292step0Labels = mixedMoment B raw17292step1 raw17292step1Labels := by
      have ha : raw17292step1 = -raw17292step0 := by apply Matrix.ext; change ∀ i j, raw17292step1 i j = -(raw17292step0 i j); unfold raw17292step1 raw17292step0; decide +kernel
      have hl : raw17292step1Labels = raw17292step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17292step1 raw17292step1Labels = mixedMoment B raw17292step2 raw17292step2Labels := by
      have ha : raw17292step2 = raw17292step1 := by apply Matrix.ext; unfold raw17292step2 raw17292step1; decide +kernel
      have hl : raw17292step1Labels = labelEmbedding1 ∘ raw17292step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17292step1 raw17292step1Labels raw17292step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3517 node3517Labels := by rfl

def raw17293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17293Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17293step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw17293step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17293step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw17293step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17293 raw17293Labels = mixedMoment B node3842 node3842Labels := by
  calc
    mixedMoment B raw17293 raw17293Labels = mixedMoment B raw17293step0 raw17293step0Labels := by
      have ha : raw17293step0 = (fun i j => raw17293 (permutation639 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17293step0 raw17293; decide +kernel
      have hl : raw17293step0Labels = raw17293Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17293 raw17293Labels permutation639 permutation7
    mixedMoment B raw17293step0 raw17293step0Labels = mixedMoment B raw17293step1 raw17293step1Labels := by
      have ha : raw17293step1 = raw17293step0 := by apply Matrix.ext; unfold raw17293step1 raw17293step0; decide +kernel
      have hl : raw17293step0Labels = labelEmbedding1 ∘ raw17293step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17293step0 raw17293step0Labels raw17293step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3842 node3842Labels := by rfl

def raw17294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17294Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17294step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17294step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17294step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17294step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17294 raw17294Labels = mixedMoment B node3873 node3873Labels := by
  calc
    mixedMoment B raw17294 raw17294Labels = mixedMoment B raw17294step0 raw17294step0Labels := by
      have ha : raw17294step0 = (fun i j => raw17294 (permutation640 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17294step0 raw17294; decide +kernel
      have hl : raw17294step0Labels = raw17294Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17294 raw17294Labels permutation640 permutation7
    mixedMoment B raw17294step0 raw17294step0Labels = mixedMoment B raw17294step1 raw17294step1Labels := by
      have ha : raw17294step1 = raw17294step0 := by apply Matrix.ext; unfold raw17294step1 raw17294step0; decide +kernel
      have hl : raw17294step0Labels = labelEmbedding1 ∘ raw17294step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17294step0 raw17294step0Labels raw17294step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3873 node3873Labels := by rfl

def raw17295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![2, 0, -2]]
def raw17295Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17295step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17295step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17295step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17295step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17295 raw17295Labels = mixedMoment B node3843 node3843Labels := by
  calc
    mixedMoment B raw17295 raw17295Labels = mixedMoment B raw17295step0 raw17295step0Labels := by
      have ha : raw17295step0 = (fun i j => raw17295 (permutation640 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17295step0 raw17295; decide +kernel
      have hl : raw17295step0Labels = raw17295Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17295 raw17295Labels permutation640 permutation7
    mixedMoment B raw17295step0 raw17295step0Labels = mixedMoment B raw17295step1 raw17295step1Labels := by
      have ha : raw17295step1 = raw17295step0 := by apply Matrix.ext; unfold raw17295step1 raw17295step0; decide +kernel
      have hl : raw17295step0Labels = labelEmbedding1 ∘ raw17295step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17295step0 raw17295step0Labels raw17295step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3843 node3843Labels := by rfl

def raw17296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![1, 1, -2]]
def raw17296Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17296step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17296step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17296step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17296step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17296 raw17296Labels = mixedMoment B node3978 node3978Labels := by
  calc
    mixedMoment B raw17296 raw17296Labels = mixedMoment B raw17296step0 raw17296step0Labels := by
      have ha : raw17296step0 = (fun i j => raw17296 (permutation559 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17296step0 raw17296; decide +kernel
      have hl : raw17296step0Labels = raw17296Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17296 raw17296Labels permutation559 permutation5
    mixedMoment B raw17296step0 raw17296step0Labels = mixedMoment B raw17296step1 raw17296step1Labels := by
      have ha : raw17296step1 = raw17296step0 := by apply Matrix.ext; unfold raw17296step1 raw17296step0; decide +kernel
      have hl : raw17296step0Labels = labelEmbedding1 ∘ raw17296step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17296step0 raw17296step0Labels raw17296step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3978 node3978Labels := by rfl

def raw17297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw17297Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw17297step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17297step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw17297step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17297step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw17297step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17297 raw17297Labels = mixedMoment B node2670 node2670Labels := by
  calc
    mixedMoment B raw17297 raw17297Labels = mixedMoment B raw17297step0 raw17297step0Labels := by
      have hz : ∀ j, raw17297 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17297step0 = (fun i j => raw17297 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17297step0 raw17297; decide +kernel
      have hl : raw17297step0Labels = raw17297Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17297 raw17297Labels permutation434 hz
    mixedMoment B raw17297step0 raw17297step0Labels = mixedMoment B raw17297step1 raw17297step1Labels := by
      have ha : raw17297step1 = (fun i j => raw17297step0 (permutation125 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17297step1 raw17297step0; decide +kernel
      have hl : raw17297step1Labels = raw17297step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17297step0 raw17297step0Labels permutation125 permutation5
    mixedMoment B raw17297step1 raw17297step1Labels = mixedMoment B raw17297step2 raw17297step2Labels := by
      have ha : raw17297step2 = raw17297step1 := by apply Matrix.ext; unfold raw17297step2 raw17297step1; decide +kernel
      have hl : raw17297step1Labels = labelEmbedding1 ∘ raw17297step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17297step1 raw17297step1Labels raw17297step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2670 node2670Labels := by rfl

def raw17298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw17298Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw17298step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17298step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw17298step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17298step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw17298step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17298 raw17298Labels = mixedMoment B node2682 node2682Labels := by
  calc
    mixedMoment B raw17298 raw17298Labels = mixedMoment B raw17298step0 raw17298step0Labels := by
      have hz : ∀ j, raw17298 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17298step0 = (fun i j => raw17298 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17298step0 raw17298; decide +kernel
      have hl : raw17298step0Labels = raw17298Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17298 raw17298Labels permutation434 hz
    mixedMoment B raw17298step0 raw17298step0Labels = mixedMoment B raw17298step1 raw17298step1Labels := by
      have ha : raw17298step1 = (fun i j => raw17298step0 (permutation126 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17298step1 raw17298step0; decide +kernel
      have hl : raw17298step1Labels = raw17298step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17298step0 raw17298step0Labels permutation126 permutation5
    mixedMoment B raw17298step1 raw17298step1Labels = mixedMoment B raw17298step2 raw17298step2Labels := by
      have ha : raw17298step2 = raw17298step1 := by apply Matrix.ext; unfold raw17298step2 raw17298step1; decide +kernel
      have hl : raw17298step1Labels = labelEmbedding1 ∘ raw17298step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17298step1 raw17298step1Labels raw17298step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2682 node2682Labels := by rfl

def raw17299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw17299Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![2, -3, 1], ![2, 0, -2]]
def raw17299step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17299step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17299step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17299step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, -1, -1]]
def raw17299step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17299 raw17299Labels = mixedMoment B node2673 node2673Labels := by
  calc
    mixedMoment B raw17299 raw17299Labels = mixedMoment B raw17299step0 raw17299step0Labels := by
      have hz : ∀ j, raw17299 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17299step0 = (fun i j => raw17299 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17299step0 raw17299; decide +kernel
      have hl : raw17299step0Labels = raw17299Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17299 raw17299Labels permutation434 hz
    mixedMoment B raw17299step0 raw17299step0Labels = mixedMoment B raw17299step1 raw17299step1Labels := by
      have ha : raw17299step1 = (fun i j => raw17299step0 (permutation124 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17299step1 raw17299step0; decide +kernel
      have hl : raw17299step1Labels = raw17299step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17299step0 raw17299step0Labels permutation124 permutation5
    mixedMoment B raw17299step1 raw17299step1Labels = mixedMoment B raw17299step2 raw17299step2Labels := by
      have ha : raw17299step2 = raw17299step1 := by apply Matrix.ext; unfold raw17299step2 raw17299step1; decide +kernel
      have hl : raw17299step1Labels = labelEmbedding1 ∘ raw17299step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17299step1 raw17299step1Labels raw17299step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2673 node2673Labels := by rfl

def raw17300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![2, -3, 1], ![2, 0, -2]]
def raw17300Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17300step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17300step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17300step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17300step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17300 raw17300Labels = mixedMoment B node2669 node2669Labels := by
  calc
    mixedMoment B raw17300 raw17300Labels = mixedMoment B raw17300step0 raw17300step0Labels := by
      have ha : raw17300step0 = (fun i j => raw17300 (permutation577 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17300step0 raw17300; decide +kernel
      have hl : raw17300step0Labels = raw17300Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17300 raw17300Labels permutation577 permutation5
    mixedMoment B raw17300step0 raw17300step0Labels = mixedMoment B raw17300step1 raw17300step1Labels := by
      have ha : raw17300step1 = raw17300step0 := by apply Matrix.ext; unfold raw17300step1 raw17300step0; decide +kernel
      have hl : raw17300step0Labels = labelEmbedding1 ∘ raw17300step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17300step0 raw17300step0Labels raw17300step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2669 node2669Labels := by rfl

def raw17301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![1, 1, -2]]
def raw17301Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![1, 1, -2]]
def raw17301step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17301step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17301step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17301step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17301step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17301 raw17301Labels = mixedMoment B node2763 node2763Labels := by
  calc
    mixedMoment B raw17301 raw17301Labels = mixedMoment B raw17301step0 raw17301step0Labels := by
      have hz : ∀ j, raw17301 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17301step0 = (fun i j => raw17301 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17301step0 raw17301; decide +kernel
      have hl : raw17301step0Labels = raw17301Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17301 raw17301Labels permutation434 hz
    mixedMoment B raw17301step0 raw17301step0Labels = mixedMoment B raw17301step1 raw17301step1Labels := by
      have ha : raw17301step1 = (fun i j => raw17301step0 (permutation115 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17301step1 raw17301step0; decide +kernel
      have hl : raw17301step1Labels = raw17301step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17301step0 raw17301step0Labels permutation115 permutation5
    mixedMoment B raw17301step1 raw17301step1Labels = mixedMoment B raw17301step2 raw17301step2Labels := by
      have ha : raw17301step2 = raw17301step1 := by apply Matrix.ext; unfold raw17301step2 raw17301step1; decide +kernel
      have hl : raw17301step1Labels = labelEmbedding1 ∘ raw17301step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17301step1 raw17301step1Labels raw17301step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2763 node2763Labels := by rfl

def raw17302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw17302Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw17302step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17302step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -2, 3], ![-2, 1, 1]]
def raw17302step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17302step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw17302step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17302step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 2, -3], ![2, -1, -1]]
def raw17302step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17302 raw17302Labels = mixedMoment B node3523 node3523Labels := by
  calc
    mixedMoment B raw17302 raw17302Labels = mixedMoment B raw17302step0 raw17302step0Labels := by
      have hz : ∀ j, raw17302 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17302step0 = (fun i j => raw17302 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17302step0 raw17302; decide +kernel
      have hl : raw17302step0Labels = raw17302Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17302 raw17302Labels permutation434 hz
    mixedMoment B raw17302step0 raw17302step0Labels = mixedMoment B raw17302step1 raw17302step1Labels := by
      have ha : raw17302step1 = (fun i j => raw17302step0 (permutation39 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17302step1 raw17302step0; decide +kernel
      have hl : raw17302step1Labels = raw17302step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17302step0 raw17302step0Labels permutation39 permutation5
    mixedMoment B raw17302step1 raw17302step1Labels = mixedMoment B raw17302step2 raw17302step2Labels := by
      have ha : raw17302step2 = -raw17302step1 := by apply Matrix.ext; change ∀ i j, raw17302step2 i j = -(raw17302step1 i j); unfold raw17302step2 raw17302step1; decide +kernel
      have hl : raw17302step2Labels = raw17302step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17302step2 raw17302step2Labels = mixedMoment B raw17302step3 raw17302step3Labels := by
      have ha : raw17302step3 = raw17302step2 := by apply Matrix.ext; unfold raw17302step3 raw17302step2; decide +kernel
      have hl : raw17302step2Labels = labelEmbedding1 ∘ raw17302step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17302step2 raw17302step2Labels raw17302step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3523 node3523Labels := by rfl

def raw17303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw17303Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw17303step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17303step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw17303step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17303step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw17303step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17303 raw17303Labels = mixedMoment B node3542 node3542Labels := by
  calc
    mixedMoment B raw17303 raw17303Labels = mixedMoment B raw17303step0 raw17303step0Labels := by
      have hz : ∀ j, raw17303 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17303step0 = (fun i j => raw17303 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17303step0 raw17303; decide +kernel
      have hl : raw17303step0Labels = raw17303Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17303 raw17303Labels permutation434 hz
    mixedMoment B raw17303step0 raw17303step0Labels = mixedMoment B raw17303step1 raw17303step1Labels := by
      have ha : raw17303step1 = (fun i j => raw17303step0 (permutation144 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17303step1 raw17303step0; decide +kernel
      have hl : raw17303step1Labels = raw17303step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17303step0 raw17303step0Labels permutation144 permutation7
    mixedMoment B raw17303step1 raw17303step1Labels = mixedMoment B raw17303step2 raw17303step2Labels := by
      have ha : raw17303step2 = raw17303step1 := by apply Matrix.ext; unfold raw17303step2 raw17303step1; decide +kernel
      have hl : raw17303step1Labels = labelEmbedding1 ∘ raw17303step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17303step1 raw17303step1Labels raw17303step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3542 node3542Labels := by rfl

def raw17304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw17304Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -2, 1], ![3, -1, -2]]
def raw17304step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17304step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17304step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17304step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17304step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17304 raw17304Labels = mixedMoment B node3578 node3578Labels := by
  calc
    mixedMoment B raw17304 raw17304Labels = mixedMoment B raw17304step0 raw17304step0Labels := by
      have hz : ∀ j, raw17304 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17304step0 = (fun i j => raw17304 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17304step0 raw17304; decide +kernel
      have hl : raw17304step0Labels = raw17304Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17304 raw17304Labels permutation434 hz
    mixedMoment B raw17304step0 raw17304step0Labels = mixedMoment B raw17304step1 raw17304step1Labels := by
      have ha : raw17304step1 = (fun i j => raw17304step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17304step1 raw17304step0; decide +kernel
      have hl : raw17304step1Labels = raw17304step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17304step0 raw17304step0Labels permutation145 permutation7
    mixedMoment B raw17304step1 raw17304step1Labels = mixedMoment B raw17304step2 raw17304step2Labels := by
      have ha : raw17304step2 = raw17304step1 := by apply Matrix.ext; unfold raw17304step2 raw17304step1; decide +kernel
      have hl : raw17304step1Labels = labelEmbedding1 ∘ raw17304step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17304step1 raw17304step1Labels raw17304step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3578 node3578Labels := by rfl

def raw17305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![3, -1, -2]]
def raw17305Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17305step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17305step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17305step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17305step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17305 raw17305Labels = mixedMoment B node3529 node3529Labels := by
  calc
    mixedMoment B raw17305 raw17305Labels = mixedMoment B raw17305step0 raw17305step0Labels := by
      have ha : raw17305step0 = (fun i j => raw17305 (permutation640 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17305step0 raw17305; decide +kernel
      have hl : raw17305step0Labels = raw17305Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17305 raw17305Labels permutation640 permutation7
    mixedMoment B raw17305step0 raw17305step0Labels = mixedMoment B raw17305step1 raw17305step1Labels := by
      have ha : raw17305step1 = raw17305step0 := by apply Matrix.ext; unfold raw17305step1 raw17305step0; decide +kernel
      have hl : raw17305step0Labels = labelEmbedding1 ∘ raw17305step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17305step0 raw17305step0Labels raw17305step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3529 node3529Labels := by rfl

def raw17306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![3, -1, -2]]
def raw17306Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, -1, 1], ![3, -1, -2]]
def raw17306step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw17306step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17306step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw17306step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17306step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17306 raw17306Labels = mixedMoment B node3544 node3544Labels := by
  calc
    mixedMoment B raw17306 raw17306Labels = mixedMoment B raw17306step0 raw17306step0Labels := by
      have hz : ∀ j, raw17306 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17306step0 = (fun i j => raw17306 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17306step0 raw17306; decide +kernel
      have hl : raw17306step0Labels = raw17306Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17306 raw17306Labels permutation434 hz
    mixedMoment B raw17306step0 raw17306step0Labels = mixedMoment B raw17306step1 raw17306step1Labels := by
      have ha : raw17306step1 = (fun i j => raw17306step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17306step1 raw17306step0; decide +kernel
      have hl : raw17306step1Labels = raw17306step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17306step0 raw17306step0Labels permutation145 permutation7
    mixedMoment B raw17306step1 raw17306step1Labels = mixedMoment B raw17306step2 raw17306step2Labels := by
      have ha : raw17306step2 = raw17306step1 := by apply Matrix.ext; unfold raw17306step2 raw17306step1; decide +kernel
      have hl : raw17306step1Labels = labelEmbedding1 ∘ raw17306step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17306step1 raw17306step1Labels raw17306step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3544 node3544Labels := by rfl

def raw17307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17307Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17307step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17307step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17307step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17307step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17307step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17307 raw17307Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw17307 raw17307Labels = mixedMoment B raw17307step0 raw17307step0Labels := by
      have hz : ∀ j, raw17307 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17307step0 = (fun i j => raw17307 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17307step0 raw17307; decide +kernel
      have hl : raw17307step0Labels = raw17307Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17307 raw17307Labels permutation434 hz
    mixedMoment B raw17307step0 raw17307step0Labels = mixedMoment B raw17307step1 raw17307step1Labels := by
      have ha : raw17307step1 = (fun i j => raw17307step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17307step1 raw17307step0; decide +kernel
      have hl : raw17307step1Labels = raw17307step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17307step0 raw17307step0Labels permutation150 permutation2
    mixedMoment B raw17307step1 raw17307step1Labels = mixedMoment B raw17307step2 raw17307step2Labels := by
      have ha : raw17307step2 = -raw17307step1 := by apply Matrix.ext; change ∀ i j, raw17307step2 i j = -(raw17307step1 i j); unfold raw17307step2 raw17307step1; decide +kernel
      have hl : raw17307step2Labels = raw17307step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3876 node3876Labels := by rfl

def raw17308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17308Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17308step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17308step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17308step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17308step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17308step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17308 raw17308Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw17308 raw17308Labels = mixedMoment B raw17308step0 raw17308step0Labels := by
      have hz : ∀ j, raw17308 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17308step0 = (fun i j => raw17308 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17308step0 raw17308; decide +kernel
      have hl : raw17308step0Labels = raw17308Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17308 raw17308Labels permutation434 hz
    mixedMoment B raw17308step0 raw17308step0Labels = mixedMoment B raw17308step1 raw17308step1Labels := by
      have ha : raw17308step1 = (fun i j => raw17308step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17308step1 raw17308step0; decide +kernel
      have hl : raw17308step1Labels = raw17308step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17308step0 raw17308step0Labels permutation151 permutation2
    mixedMoment B raw17308step1 raw17308step1Labels = mixedMoment B raw17308step2 raw17308step2Labels := by
      have ha : raw17308step2 = -raw17308step1 := by apply Matrix.ext; change ∀ i j, raw17308step2 i j = -(raw17308step1 i j); unfold raw17308step2 raw17308step1; decide +kernel
      have hl : raw17308step2Labels = raw17308step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3876 node3876Labels := by rfl

def raw17309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17309Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17309step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17309step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17309step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17309step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw17309step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17309 raw17309Labels = mixedMoment B node3790 node3790Labels := by
  calc
    mixedMoment B raw17309 raw17309Labels = mixedMoment B raw17309step0 raw17309step0Labels := by
      have hz : ∀ j, raw17309 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17309step0 = (fun i j => raw17309 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17309step0 raw17309; decide +kernel
      have hl : raw17309step0Labels = raw17309Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17309 raw17309Labels permutation434 hz
    mixedMoment B raw17309step0 raw17309step0Labels = mixedMoment B raw17309step1 raw17309step1Labels := by
      have ha : raw17309step1 = (fun i j => raw17309step0 (permutation144 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17309step1 raw17309step0; decide +kernel
      have hl : raw17309step1Labels = raw17309step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17309step0 raw17309step0Labels permutation144 permutation2
    mixedMoment B raw17309step1 raw17309step1Labels = mixedMoment B raw17309step2 raw17309step2Labels := by
      have ha : raw17309step2 = -raw17309step1 := by apply Matrix.ext; change ∀ i j, raw17309step2 i j = -(raw17309step1 i j); unfold raw17309step2 raw17309step1; decide +kernel
      have hl : raw17309step2Labels = raw17309step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3790 node3790Labels := by rfl

def raw17310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -2, 1], ![2, 0, -2]]
def raw17310Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17310step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17310step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17310step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw17310step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17310 raw17310Labels = mixedMoment B node3825 node3825Labels := by
  calc
    mixedMoment B raw17310 raw17310Labels = mixedMoment B raw17310step0 raw17310step0Labels := by
      have ha : raw17310step0 = (fun i j => raw17310 (permutation663 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17310step0 raw17310; decide +kernel
      have hl : raw17310step0Labels = raw17310Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17310 raw17310Labels permutation663 permutation2
    mixedMoment B raw17310step0 raw17310step0Labels = mixedMoment B raw17310step1 raw17310step1Labels := by
      have ha : raw17310step1 = -raw17310step0 := by apply Matrix.ext; change ∀ i j, raw17310step1 i j = -(raw17310step0 i j); unfold raw17310step1 raw17310step0; decide +kernel
      have hl : raw17310step1Labels = raw17310step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3825 node3825Labels := by rfl

def raw17311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![2, -3, 1], ![2, 0, -2]]
def raw17311Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw17311step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17311step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 2, -2], ![1, -2, 1], ![1, -2, 1], ![1, 0, -1]]
def raw17311step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17311 raw17311Labels = mixedMoment B node3115 node3115Labels := by
  calc
    mixedMoment B raw17311 raw17311Labels = mixedMoment B raw17311step0 raw17311step0Labels := by
      have hz : ∀ j, raw17311 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17311step0 = (fun i j => raw17311 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17311step0 raw17311; decide +kernel
      have hl : raw17311step0Labels = raw17311Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17311 raw17311Labels permutation434 hz
    mixedMoment B raw17311step0 raw17311step0Labels = mixedMoment B raw17311step1 raw17311step1Labels := by
      have ha : raw17311step1 = (fun i j => raw17311step0 (permutation122 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17311step1 raw17311step0; decide +kernel
      have hl : raw17311step1Labels = raw17311step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17311step0 raw17311step0Labels permutation122 permutation4
    _ = mixedMoment B node3115 node3115Labels := by rfl

def raw17312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![3, -1, -2]]
def raw17312Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw17312step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17312step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 1, 1]]
def raw17312step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17312step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, -1, -1]]
def raw17312step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17312 raw17312Labels = mixedMoment B node2621 node2621Labels := by
  calc
    mixedMoment B raw17312 raw17312Labels = mixedMoment B raw17312step0 raw17312step0Labels := by
      have hz : ∀ j, raw17312 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17312step0 = (fun i j => raw17312 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17312step0 raw17312; decide +kernel
      have hl : raw17312step0Labels = raw17312Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17312 raw17312Labels permutation434 hz
    mixedMoment B raw17312step0 raw17312step0Labels = mixedMoment B raw17312step1 raw17312step1Labels := by
      have ha : raw17312step1 = (fun i j => raw17312step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17312step1 raw17312step0; decide +kernel
      have hl : raw17312step1Labels = raw17312step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17312step0 raw17312step0Labels permutation150 permutation2
    mixedMoment B raw17312step1 raw17312step1Labels = mixedMoment B raw17312step2 raw17312step2Labels := by
      have ha : raw17312step2 = -raw17312step1 := by apply Matrix.ext; change ∀ i j, raw17312step2 i j = -(raw17312step1 i j); unfold raw17312step2 raw17312step1; decide +kernel
      have hl : raw17312step2Labels = raw17312step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2621 node2621Labels := by rfl

def raw17313 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![0, 0], ![-1, 1], ![2, -2]]
def raw17313Labels : Fin 2 → Fin 2 := ![0, 1]

def raw17313step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-1, 1], ![1, -1], ![-1, 1], ![2, -2]]
def raw17313step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw17313step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![2, -2], ![1, -1], ![-1, 1], ![-1, 1], ![-1, 1]]
def raw17313step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw17313step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw17313step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical17313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17313 raw17313Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw17313 raw17313Labels = mixedMoment B raw17313step0 raw17313step0Labels := by
      have hz : ∀ j, raw17313 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17313step0 = (fun i j => raw17313 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17313step0 raw17313; decide +kernel
      have hl : raw17313step0Labels = raw17313Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17313 raw17313Labels permutation434 hz
    mixedMoment B raw17313step0 raw17313step0Labels = mixedMoment B raw17313step1 raw17313step1Labels := by
      have ha : raw17313step1 = (fun i j => raw17313step0 (permutation140 i) (permutation0 j)) := by apply Matrix.ext; unfold raw17313step1 raw17313step0; decide +kernel
      have hl : raw17313step1Labels = raw17313step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17313step0 raw17313step0Labels permutation140 permutation0
    mixedMoment B raw17313step1 raw17313step1Labels = mixedMoment B raw17313step2 raw17313step2Labels := by
      have ha : raw17313step2 = -raw17313step1 := by apply Matrix.ext; change ∀ i j, raw17313step2 i j = -(raw17313step1 i j); unfold raw17313step2 raw17313step1; decide +kernel
      have hl : raw17313step2Labels = raw17313step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw17314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17314Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17314step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17314step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17314step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17314step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17314step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17314 raw17314Labels = mixedMoment B node5432 node5432Labels := by
  calc
    mixedMoment B raw17314 raw17314Labels = mixedMoment B raw17314step0 raw17314step0Labels := by
      have hz : ∀ j, raw17314 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17314step0 = (fun i j => raw17314 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17314step0 raw17314; decide +kernel
      have hl : raw17314step0Labels = raw17314Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17314 raw17314Labels permutation434 hz
    mixedMoment B raw17314step0 raw17314step0Labels = mixedMoment B raw17314step1 raw17314step1Labels := by
      have ha : raw17314step1 = (fun i j => raw17314step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17314step1 raw17314step0; decide +kernel
      have hl : raw17314step1Labels = raw17314step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17314step0 raw17314step0Labels permutation56 permutation3
    mixedMoment B raw17314step1 raw17314step1Labels = mixedMoment B raw17314step2 raw17314step2Labels := by
      have ha : raw17314step2 = raw17314step1 := by apply Matrix.ext; unfold raw17314step2 raw17314step1; decide +kernel
      have hl : raw17314step1Labels = labelEmbedding6 ∘ raw17314step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17314step1 raw17314step1Labels raw17314step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5432 node5432Labels := by rfl

def raw17315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17315Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17315step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17315step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw17315step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17315step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17315step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17315step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17315step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17315 raw17315Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw17315 raw17315Labels = mixedMoment B raw17315step0 raw17315step0Labels := by
      have hz : ∀ j, raw17315 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17315step0 = (fun i j => raw17315 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17315step0 raw17315; decide +kernel
      have hl : raw17315step0Labels = raw17315Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17315 raw17315Labels permutation434 hz
    mixedMoment B raw17315step0 raw17315step0Labels = mixedMoment B raw17315step1 raw17315step1Labels := by
      have ha : raw17315step1 = (fun i j => raw17315step0 (permutation147 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17315step1 raw17315step0; decide +kernel
      have hl : raw17315step1Labels = raw17315step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17315step0 raw17315step0Labels permutation147 permutation3
    mixedMoment B raw17315step1 raw17315step1Labels = mixedMoment B raw17315step2 raw17315step2Labels := by
      have ha : raw17315step2 = -raw17315step1 := by apply Matrix.ext; change ∀ i j, raw17315step2 i j = -(raw17315step1 i j); unfold raw17315step2 raw17315step1; decide +kernel
      have hl : raw17315step2Labels = raw17315step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17315step2 raw17315step2Labels = mixedMoment B raw17315step3 raw17315step3Labels := by
      have ha : raw17315step3 = raw17315step2 := by apply Matrix.ext; unfold raw17315step3 raw17315step2; decide +kernel
      have hl : raw17315step2Labels = labelEmbedding6 ∘ raw17315step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17315step2 raw17315step2Labels raw17315step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw17316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17316Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17316step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17316step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17316step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17316step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17316 raw17316Labels = mixedMoment B node5431 node5431Labels := by
  calc
    mixedMoment B raw17316 raw17316Labels = mixedMoment B raw17316step0 raw17316step0Labels := by
      have ha : raw17316step0 = (fun i j => raw17316 (permutation627 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17316step0 raw17316; decide +kernel
      have hl : raw17316step0Labels = raw17316Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17316 raw17316Labels permutation627 permutation5
    mixedMoment B raw17316step0 raw17316step0Labels = mixedMoment B raw17316step1 raw17316step1Labels := by
      have ha : raw17316step1 = raw17316step0 := by apply Matrix.ext; unfold raw17316step1 raw17316step0; decide +kernel
      have hl : raw17316step0Labels = labelEmbedding8 ∘ raw17316step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17316step0 raw17316step0Labels raw17316step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5431 node5431Labels := by rfl

def raw17317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw17317Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0]]
def raw17317step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17317step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw17317step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17317step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17317step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17317step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17317step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17317 raw17317Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw17317 raw17317Labels = mixedMoment B raw17317step0 raw17317step0Labels := by
      have hz : ∀ j, raw17317 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17317step0 = (fun i j => raw17317 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17317step0 raw17317; decide +kernel
      have hl : raw17317step0Labels = raw17317Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17317 raw17317Labels permutation434 hz
    mixedMoment B raw17317step0 raw17317step0Labels = mixedMoment B raw17317step1 raw17317step1Labels := by
      have ha : raw17317step1 = (fun i j => raw17317step0 (permutation110 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17317step1 raw17317step0; decide +kernel
      have hl : raw17317step1Labels = raw17317step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17317step0 raw17317step0Labels permutation110 permutation4
    mixedMoment B raw17317step1 raw17317step1Labels = mixedMoment B raw17317step2 raw17317step2Labels := by
      have ha : raw17317step2 = -raw17317step1 := by apply Matrix.ext; change ∀ i j, raw17317step2 i j = -(raw17317step1 i j); unfold raw17317step2 raw17317step1; decide +kernel
      have hl : raw17317step2Labels = raw17317step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17317step2 raw17317step2Labels = mixedMoment B raw17317step3 raw17317step3Labels := by
      have ha : raw17317step3 = raw17317step2 := by apply Matrix.ext; unfold raw17317step3 raw17317step2; decide +kernel
      have hl : raw17317step2Labels = labelEmbedding7 ∘ raw17317step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17317step2 raw17317step2Labels raw17317step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5435 node5435Labels := by rfl

def raw17318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw17318Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0]]
def raw17318step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17318step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17318step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17318step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17318step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17318 raw17318Labels = mixedMoment B node5490 node5490Labels := by
  calc
    mixedMoment B raw17318 raw17318Labels = mixedMoment B raw17318step0 raw17318step0Labels := by
      have hz : ∀ j, raw17318 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17318step0 = (fun i j => raw17318 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17318step0 raw17318; decide +kernel
      have hl : raw17318step0Labels = raw17318Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17318 raw17318Labels permutation434 hz
    mixedMoment B raw17318step0 raw17318step0Labels = mixedMoment B raw17318step1 raw17318step1Labels := by
      have ha : raw17318step1 = (fun i j => raw17318step0 (permutation114 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17318step1 raw17318step0; decide +kernel
      have hl : raw17318step1Labels = raw17318step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17318step0 raw17318step0Labels permutation114 permutation6
    mixedMoment B raw17318step1 raw17318step1Labels = mixedMoment B raw17318step2 raw17318step2Labels := by
      have ha : raw17318step2 = raw17318step1 := by apply Matrix.ext; unfold raw17318step2 raw17318step1; decide +kernel
      have hl : raw17318step1Labels = labelEmbedding9 ∘ raw17318step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17318step1 raw17318step1Labels raw17318step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5490 node5490Labels := by rfl

def raw17319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17319Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17319step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17319step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17319step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17319step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17319step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17319step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17319step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17319 raw17319Labels = mixedMoment B node5291 node5291Labels := by
  calc
    mixedMoment B raw17319 raw17319Labels = mixedMoment B raw17319step0 raw17319step0Labels := by
      have hz : ∀ j, raw17319 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17319step0 = (fun i j => raw17319 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17319step0 raw17319; decide +kernel
      have hl : raw17319step0Labels = raw17319Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17319 raw17319Labels permutation434 hz
    mixedMoment B raw17319step0 raw17319step0Labels = mixedMoment B raw17319step1 raw17319step1Labels := by
      have hz : ∀ j, raw17319step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw17319step1 = (fun i j => raw17319step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw17319step1 raw17319step0; decide +kernel
      have hl : raw17319step1Labels = raw17319step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17319step0 raw17319step0Labels permutation56 hz
    mixedMoment B raw17319step1 raw17319step1Labels = mixedMoment B raw17319step2 raw17319step2Labels := by
      have ha : raw17319step2 = (fun i j => raw17319step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17319step2 raw17319step1; decide +kernel
      have hl : raw17319step2Labels = raw17319step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17319step1 raw17319step1Labels permutation8 permutation3
    mixedMoment B raw17319step2 raw17319step2Labels = mixedMoment B raw17319step3 raw17319step3Labels := by
      have ha : raw17319step3 = raw17319step2 := by apply Matrix.ext; unfold raw17319step3 raw17319step2; decide +kernel
      have hl : raw17319step2Labels = labelEmbedding6 ∘ raw17319step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17319step2 raw17319step2Labels raw17319step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5291 node5291Labels := by rfl

def raw17320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17320Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17320step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17320step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17320step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17320step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17320step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17320step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17320step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17320step3Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17320step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17320step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17320 raw17320Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw17320 raw17320Labels = mixedMoment B raw17320step0 raw17320step0Labels := by
      have hz : ∀ j, raw17320 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17320step0 = (fun i j => raw17320 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17320step0 raw17320; decide +kernel
      have hl : raw17320step0Labels = raw17320Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17320 raw17320Labels permutation434 hz
    mixedMoment B raw17320step0 raw17320step0Labels = mixedMoment B raw17320step1 raw17320step1Labels := by
      have hz : ∀ j, raw17320step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw17320step1 = (fun i j => raw17320step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw17320step1 raw17320step0; decide +kernel
      have hl : raw17320step1Labels = raw17320step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17320step0 raw17320step0Labels permutation56 hz
    mixedMoment B raw17320step1 raw17320step1Labels = mixedMoment B raw17320step2 raw17320step2Labels := by
      have ha : raw17320step2 = (fun i j => raw17320step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17320step2 raw17320step1; decide +kernel
      have hl : raw17320step2Labels = raw17320step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17320step1 raw17320step1Labels permutation31 permutation3
    mixedMoment B raw17320step2 raw17320step2Labels = mixedMoment B raw17320step3 raw17320step3Labels := by
      have ha : raw17320step3 = -raw17320step2 := by apply Matrix.ext; change ∀ i j, raw17320step3 i j = -(raw17320step2 i j); unfold raw17320step3 raw17320step2; decide +kernel
      have hl : raw17320step3Labels = raw17320step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17320step3 raw17320step3Labels = mixedMoment B raw17320step4 raw17320step4Labels := by
      have ha : raw17320step4 = raw17320step3 := by apply Matrix.ext; unfold raw17320step4 raw17320step3; decide +kernel
      have hl : raw17320step3Labels = labelEmbedding6 ∘ raw17320step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17320step3 raw17320step3Labels raw17320step4Labels labelEmbedding6 hl
    _ = mixedMoment B node5451 node5451Labels := by rfl

def raw17321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17321Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17321step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17321step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17321step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17321step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17321step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17321step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17321 raw17321Labels = mixedMoment B node5438 node5438Labels := by
  calc
    mixedMoment B raw17321 raw17321Labels = mixedMoment B raw17321step0 raw17321step0Labels := by
      have hz : ∀ j, raw17321 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw17321step0 = (fun i j => raw17321 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw17321step0 raw17321; decide +kernel
      have hl : raw17321step0Labels = raw17321Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17321 raw17321Labels permutation265 hz
    mixedMoment B raw17321step0 raw17321step0Labels = mixedMoment B raw17321step1 raw17321step1Labels := by
      have ha : raw17321step1 = (fun i j => raw17321step0 (permutation139 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17321step1 raw17321step0; decide +kernel
      have hl : raw17321step1Labels = raw17321step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17321step0 raw17321step0Labels permutation139 permutation5
    mixedMoment B raw17321step1 raw17321step1Labels = mixedMoment B raw17321step2 raw17321step2Labels := by
      have ha : raw17321step2 = raw17321step1 := by apply Matrix.ext; unfold raw17321step2 raw17321step1; decide +kernel
      have hl : raw17321step1Labels = labelEmbedding8 ∘ raw17321step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17321step1 raw17321step1Labels raw17321step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5438 node5438Labels := by rfl

def raw17322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw17322Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17322step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0]]
def raw17322step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17322step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0]]
def raw17322step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17322step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17322step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17322step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17322step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17322 raw17322Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw17322 raw17322Labels = mixedMoment B raw17322step0 raw17322step0Labels := by
      have hz : ∀ j, raw17322 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17322step0 = (fun i j => raw17322 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17322step0 raw17322; decide +kernel
      have hl : raw17322step0Labels = raw17322Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17322 raw17322Labels permutation434 hz
    mixedMoment B raw17322step0 raw17322step0Labels = mixedMoment B raw17322step1 raw17322step1Labels := by
      have hz : ∀ j, raw17322step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw17322step1 = (fun i j => raw17322step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw17322step1 raw17322step0; decide +kernel
      have hl : raw17322step1Labels = raw17322step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17322step0 raw17322step0Labels permutation56 hz
    mixedMoment B raw17322step1 raw17322step1Labels = mixedMoment B raw17322step2 raw17322step2Labels := by
      have ha : raw17322step2 = (fun i j => raw17322step1 (permutation28 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17322step2 raw17322step1; decide +kernel
      have hl : raw17322step2Labels = raw17322step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17322step1 raw17322step1Labels permutation28 permutation5
    mixedMoment B raw17322step2 raw17322step2Labels = mixedMoment B raw17322step3 raw17322step3Labels := by
      have ha : raw17322step3 = raw17322step2 := by apply Matrix.ext; unfold raw17322step3 raw17322step2; decide +kernel
      have hl : raw17322step2Labels = labelEmbedding8 ∘ raw17322step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17322step2 raw17322step2Labels raw17322step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw17323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw17323Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17323step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0]]
def raw17323step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17323step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0]]
def raw17323step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17323step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17323step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17323 raw17323Labels = mixedMoment B node5492 node5492Labels := by
  calc
    mixedMoment B raw17323 raw17323Labels = mixedMoment B raw17323step0 raw17323step0Labels := by
      have hz : ∀ j, raw17323 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17323step0 = (fun i j => raw17323 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17323step0 raw17323; decide +kernel
      have hl : raw17323step0Labels = raw17323Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17323 raw17323Labels permutation434 hz
    mixedMoment B raw17323step0 raw17323step0Labels = mixedMoment B raw17323step1 raw17323step1Labels := by
      have hz : ∀ j, raw17323step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw17323step1 = (fun i j => raw17323step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw17323step1 raw17323step0; decide +kernel
      have hl : raw17323step1Labels = raw17323step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17323step0 raw17323step0Labels permutation56 hz
    mixedMoment B raw17323step1 raw17323step1Labels = mixedMoment B raw17323step2 raw17323step2Labels := by
      have ha : raw17323step2 = (fun i j => raw17323step1 (permutation9 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17323step2 raw17323step1; decide +kernel
      have hl : raw17323step2Labels = raw17323step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17323step1 raw17323step1Labels permutation9 permutation2
    _ = mixedMoment B node5492 node5492Labels := by rfl

def raw17324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17324Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17324step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17324step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw17324step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17324step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw17324step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17324 raw17324Labels = mixedMoment B node5095 node5095Labels := by
  calc
    mixedMoment B raw17324 raw17324Labels = mixedMoment B raw17324step0 raw17324step0Labels := by
      have hz : ∀ j, raw17324 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17324step0 = (fun i j => raw17324 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17324step0 raw17324; decide +kernel
      have hl : raw17324step0Labels = raw17324Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17324 raw17324Labels permutation434 hz
    mixedMoment B raw17324step0 raw17324step0Labels = mixedMoment B raw17324step1 raw17324step1Labels := by
      have ha : raw17324step1 = (fun i j => raw17324step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17324step1 raw17324step0; decide +kernel
      have hl : raw17324step1Labels = raw17324step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17324step0 raw17324step0Labels permutation34 permutation3
    mixedMoment B raw17324step1 raw17324step1Labels = mixedMoment B raw17324step2 raw17324step2Labels := by
      have ha : raw17324step2 = raw17324step1 := by apply Matrix.ext; unfold raw17324step2 raw17324step1; decide +kernel
      have hl : raw17324step1Labels = labelEmbedding6 ∘ raw17324step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17324step1 raw17324step1Labels raw17324step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5095 node5095Labels := by rfl

def raw17325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17325Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17325step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17325step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17325step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw17325step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17325step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw17325step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17325 raw17325Labels = mixedMoment B node5364 node5364Labels := by
  calc
    mixedMoment B raw17325 raw17325Labels = mixedMoment B raw17325step0 raw17325step0Labels := by
      have hz : ∀ j, raw17325 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17325step0 = (fun i j => raw17325 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17325step0 raw17325; decide +kernel
      have hl : raw17325step0Labels = raw17325Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17325 raw17325Labels permutation434 hz
    mixedMoment B raw17325step0 raw17325step0Labels = mixedMoment B raw17325step1 raw17325step1Labels := by
      have ha : raw17325step1 = (fun i j => raw17325step0 (permutation58 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17325step1 raw17325step0; decide +kernel
      have hl : raw17325step1Labels = raw17325step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17325step0 raw17325step0Labels permutation58 permutation3
    mixedMoment B raw17325step1 raw17325step1Labels = mixedMoment B raw17325step2 raw17325step2Labels := by
      have ha : raw17325step2 = raw17325step1 := by apply Matrix.ext; unfold raw17325step2 raw17325step1; decide +kernel
      have hl : raw17325step1Labels = labelEmbedding6 ∘ raw17325step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17325step1 raw17325step1Labels raw17325step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5364 node5364Labels := by rfl

def raw17326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17326Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17326step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw17326step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17326step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw17326step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17326 raw17326Labels = mixedMoment B node5363 node5363Labels := by
  calc
    mixedMoment B raw17326 raw17326Labels = mixedMoment B raw17326step0 raw17326step0Labels := by
      have ha : raw17326step0 = (fun i j => raw17326 (permutation644 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17326step0 raw17326; decide +kernel
      have hl : raw17326step0Labels = raw17326Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17326 raw17326Labels permutation644 permutation5
    mixedMoment B raw17326step0 raw17326step0Labels = mixedMoment B raw17326step1 raw17326step1Labels := by
      have ha : raw17326step1 = raw17326step0 := by apply Matrix.ext; unfold raw17326step1 raw17326step0; decide +kernel
      have hl : raw17326step0Labels = labelEmbedding8 ∘ raw17326step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17326step0 raw17326step0Labels raw17326step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5363 node5363Labels := by rfl

def raw17327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw17327Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 2, -2], ![2, -2, 0]]
def raw17327step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17327step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17327step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17327step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17327step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17327 raw17327Labels = mixedMoment B node5370 node5370Labels := by
  calc
    mixedMoment B raw17327 raw17327Labels = mixedMoment B raw17327step0 raw17327step0Labels := by
      have hz : ∀ j, raw17327 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17327step0 = (fun i j => raw17327 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17327step0 raw17327; decide +kernel
      have hl : raw17327step0Labels = raw17327Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17327 raw17327Labels permutation434 hz
    mixedMoment B raw17327step0 raw17327step0Labels = mixedMoment B raw17327step1 raw17327step1Labels := by
      have ha : raw17327step1 = (fun i j => raw17327step0 (permutation142 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17327step1 raw17327step0; decide +kernel
      have hl : raw17327step1Labels = raw17327step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17327step0 raw17327step0Labels permutation142 permutation5
    mixedMoment B raw17327step1 raw17327step1Labels = mixedMoment B raw17327step2 raw17327step2Labels := by
      have ha : raw17327step2 = raw17327step1 := by apply Matrix.ext; unfold raw17327step2 raw17327step1; decide +kernel
      have hl : raw17327step1Labels = labelEmbedding8 ∘ raw17327step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17327step1 raw17327step1Labels raw17327step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5370 node5370Labels := by rfl

def raw17328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw17328Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17328step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, -1, 0]]
def raw17328step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17328step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17328step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17328step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17328step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17328 raw17328Labels = mixedMoment B node5484 node5484Labels := by
  calc
    mixedMoment B raw17328 raw17328Labels = mixedMoment B raw17328step0 raw17328step0Labels := by
      have hz : ∀ j, raw17328 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17328step0 = (fun i j => raw17328 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17328step0 raw17328; decide +kernel
      have hl : raw17328step0Labels = raw17328Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17328 raw17328Labels permutation434 hz
    mixedMoment B raw17328step0 raw17328step0Labels = mixedMoment B raw17328step1 raw17328step1Labels := by
      have ha : raw17328step1 = (fun i j => raw17328step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17328step1 raw17328step0; decide +kernel
      have hl : raw17328step1Labels = raw17328step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17328step0 raw17328step0Labels permutation35 permutation3
    mixedMoment B raw17328step1 raw17328step1Labels = mixedMoment B raw17328step2 raw17328step2Labels := by
      have ha : raw17328step2 = raw17328step1 := by apply Matrix.ext; unfold raw17328step2 raw17328step1; decide +kernel
      have hl : raw17328step1Labels = labelEmbedding6 ∘ raw17328step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17328step1 raw17328step1Labels raw17328step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5484 node5484Labels := by rfl

def raw17329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17329Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17329step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17329step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17329step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17329step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17329 raw17329Labels = mixedMoment B node5070 node5070Labels := by
  calc
    mixedMoment B raw17329 raw17329Labels = mixedMoment B raw17329step0 raw17329step0Labels := by
      have ha : raw17329step0 = (fun i j => raw17329 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17329step0 raw17329; decide +kernel
      have hl : raw17329step0Labels = raw17329Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17329 raw17329Labels permutation154 permutation3
    mixedMoment B raw17329step0 raw17329step0Labels = mixedMoment B raw17329step1 raw17329step1Labels := by
      have ha : raw17329step1 = raw17329step0 := by apply Matrix.ext; unfold raw17329step1 raw17329step0; decide +kernel
      have hl : raw17329step0Labels = labelEmbedding6 ∘ raw17329step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17329step0 raw17329step0Labels raw17329step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5070 node5070Labels := by rfl

def raw17330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17330Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17330step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17330step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17330step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17330step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17330 raw17330Labels = mixedMoment B node5349 node5349Labels := by
  calc
    mixedMoment B raw17330 raw17330Labels = mixedMoment B raw17330step0 raw17330step0Labels := by
      have ha : raw17330step0 = (fun i j => raw17330 (permutation267 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17330step0 raw17330; decide +kernel
      have hl : raw17330step0Labels = raw17330Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17330 raw17330Labels permutation267 permutation3
    mixedMoment B raw17330step0 raw17330step0Labels = mixedMoment B raw17330step1 raw17330step1Labels := by
      have ha : raw17330step1 = raw17330step0 := by apply Matrix.ext; unfold raw17330step1 raw17330step0; decide +kernel
      have hl : raw17330step0Labels = labelEmbedding6 ∘ raw17330step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17330step0 raw17330step0Labels raw17330step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5349 node5349Labels := by rfl

def raw17331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17331Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17331step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17331step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17331step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17331step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17331step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17331step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17331 raw17331Labels = mixedMoment B node5401 node5401Labels := by
  calc
    mixedMoment B raw17331 raw17331Labels = mixedMoment B raw17331step0 raw17331step0Labels := by
      have ha : raw17331step0 = (fun i j => raw17331 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17331step0 raw17331; decide +kernel
      have hl : raw17331step0Labels = raw17331Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17331 raw17331Labels permutation664 permutation3
    mixedMoment B raw17331step0 raw17331step0Labels = mixedMoment B raw17331step1 raw17331step1Labels := by
      have ha : raw17331step1 = -raw17331step0 := by apply Matrix.ext; change ∀ i j, raw17331step1 i j = -(raw17331step0 i j); unfold raw17331step1 raw17331step0; decide +kernel
      have hl : raw17331step1Labels = raw17331step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17331step1 raw17331step1Labels = mixedMoment B raw17331step2 raw17331step2Labels := by
      have ha : raw17331step2 = raw17331step1 := by apply Matrix.ext; unfold raw17331step2 raw17331step1; decide +kernel
      have hl : raw17331step1Labels = labelEmbedding6 ∘ raw17331step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17331step1 raw17331step1Labels raw17331step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5401 node5401Labels := by rfl

def raw17332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw17332Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17332step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17332step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17332step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17332step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17332 raw17332Labels = mixedMoment B node5397 node5397Labels := by
  calc
    mixedMoment B raw17332 raw17332Labels = mixedMoment B raw17332step0 raw17332step0Labels := by
      have ha : raw17332step0 = (fun i j => raw17332 (permutation656 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17332step0 raw17332; decide +kernel
      have hl : raw17332step0Labels = raw17332Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17332 raw17332Labels permutation656 permutation5
    mixedMoment B raw17332step0 raw17332step0Labels = mixedMoment B raw17332step1 raw17332step1Labels := by
      have ha : raw17332step1 = raw17332step0 := by apply Matrix.ext; unfold raw17332step1 raw17332step0; decide +kernel
      have hl : raw17332step0Labels = labelEmbedding8 ∘ raw17332step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17332step0 raw17332step0Labels raw17332step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5397 node5397Labels := by rfl

def raw17333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw17333Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17333step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17333step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17333step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17333step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17333 raw17333Labels = mixedMoment B node5481 node5481Labels := by
  calc
    mixedMoment B raw17333 raw17333Labels = mixedMoment B raw17333step0 raw17333step0Labels := by
      have ha : raw17333step0 = (fun i j => raw17333 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17333step0 raw17333; decide +kernel
      have hl : raw17333step0Labels = raw17333Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17333 raw17333Labels permutation154 permutation3
    mixedMoment B raw17333step0 raw17333step0Labels = mixedMoment B raw17333step1 raw17333step1Labels := by
      have ha : raw17333step1 = raw17333step0 := by apply Matrix.ext; unfold raw17333step1 raw17333step0; decide +kernel
      have hl : raw17333step0Labels = labelEmbedding6 ∘ raw17333step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17333step0 raw17333step0Labels raw17333step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5481 node5481Labels := by rfl

def raw17334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw17334Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17334step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw17334step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17334step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw17334step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17334step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw17334step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17334 raw17334Labels = mixedMoment B node5080 node5080Labels := by
  calc
    mixedMoment B raw17334 raw17334Labels = mixedMoment B raw17334step0 raw17334step0Labels := by
      have hz : ∀ j, raw17334 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17334step0 = (fun i j => raw17334 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17334step0 raw17334; decide +kernel
      have hl : raw17334step0Labels = raw17334Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17334 raw17334Labels permutation434 hz
    mixedMoment B raw17334step0 raw17334step0Labels = mixedMoment B raw17334step1 raw17334step1Labels := by
      have ha : raw17334step1 = (fun i j => raw17334step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17334step1 raw17334step0; decide +kernel
      have hl : raw17334step1Labels = raw17334step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17334step0 raw17334step0Labels permutation32 permutation3
    mixedMoment B raw17334step1 raw17334step1Labels = mixedMoment B raw17334step2 raw17334step2Labels := by
      have ha : raw17334step2 = raw17334step1 := by apply Matrix.ext; unfold raw17334step2 raw17334step1; decide +kernel
      have hl : raw17334step1Labels = labelEmbedding6 ∘ raw17334step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17334step1 raw17334step1Labels raw17334step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5080 node5080Labels := by rfl

def raw17335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw17335Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw17335step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17335step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw17335step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17335step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw17335step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17335 raw17335Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw17335 raw17335Labels = mixedMoment B raw17335step0 raw17335step0Labels := by
      have hz : ∀ j, raw17335 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17335step0 = (fun i j => raw17335 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17335step0 raw17335; decide +kernel
      have hl : raw17335step0Labels = raw17335Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17335 raw17335Labels permutation434 hz
    mixedMoment B raw17335step0 raw17335step0Labels = mixedMoment B raw17335step1 raw17335step1Labels := by
      have ha : raw17335step1 = (fun i j => raw17335step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17335step1 raw17335step0; decide +kernel
      have hl : raw17335step1Labels = raw17335step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17335step0 raw17335step0Labels permutation56 permutation3
    mixedMoment B raw17335step1 raw17335step1Labels = mixedMoment B raw17335step2 raw17335step2Labels := by
      have ha : raw17335step2 = raw17335step1 := by apply Matrix.ext; unfold raw17335step2 raw17335step1; decide +kernel
      have hl : raw17335step1Labels = labelEmbedding6 ∘ raw17335step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17335step1 raw17335step1Labels raw17335step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

def raw17336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw17336Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17336step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -2, 0]]
def raw17336step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17336step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17336step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17336step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17336step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17336 raw17336Labels = mixedMoment B node5388 node5388Labels := by
  calc
    mixedMoment B raw17336 raw17336Labels = mixedMoment B raw17336step0 raw17336step0Labels := by
      have hz : ∀ j, raw17336 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17336step0 = (fun i j => raw17336 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17336step0 raw17336; decide +kernel
      have hl : raw17336step0Labels = raw17336Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17336 raw17336Labels permutation434 hz
    mixedMoment B raw17336step0 raw17336step0Labels = mixedMoment B raw17336step1 raw17336step1Labels := by
      have ha : raw17336step1 = (fun i j => raw17336step0 (permutation125 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17336step1 raw17336step0; decide +kernel
      have hl : raw17336step1Labels = raw17336step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17336step0 raw17336step0Labels permutation125 permutation2
    mixedMoment B raw17336step1 raw17336step1Labels = mixedMoment B raw17336step2 raw17336step2Labels := by
      have ha : raw17336step2 = -raw17336step1 := by apply Matrix.ext; change ∀ i j, raw17336step2 i j = -(raw17336step1 i j); unfold raw17336step2 raw17336step1; decide +kernel
      have hl : raw17336step2Labels = raw17336step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5388 node5388Labels := by rfl

def raw17337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw17337Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17337step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17337step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17337step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17337step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17337step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17337step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17337 raw17337Labels = mixedMoment B node5380 node5380Labels := by
  calc
    mixedMoment B raw17337 raw17337Labels = mixedMoment B raw17337step0 raw17337step0Labels := by
      have ha : raw17337step0 = (fun i j => raw17337 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17337step0 raw17337; decide +kernel
      have hl : raw17337step0Labels = raw17337Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17337 raw17337Labels permutation680 permutation3
    mixedMoment B raw17337step0 raw17337step0Labels = mixedMoment B raw17337step1 raw17337step1Labels := by
      have ha : raw17337step1 = -raw17337step0 := by apply Matrix.ext; change ∀ i j, raw17337step1 i j = -(raw17337step0 i j); unfold raw17337step1 raw17337step0; decide +kernel
      have hl : raw17337step1Labels = raw17337step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17337step1 raw17337step1Labels = mixedMoment B raw17337step2 raw17337step2Labels := by
      have ha : raw17337step2 = raw17337step1 := by apply Matrix.ext; unfold raw17337step2 raw17337step1; decide +kernel
      have hl : raw17337step1Labels = labelEmbedding6 ∘ raw17337step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17337step1 raw17337step1Labels raw17337step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5380 node5380Labels := by rfl

def raw17338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw17338Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17338step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![1, -1, 0]]
def raw17338step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17338step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17338step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17338step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17338step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17338 raw17338Labels = mixedMoment B node5434 node5434Labels := by
  calc
    mixedMoment B raw17338 raw17338Labels = mixedMoment B raw17338step0 raw17338step0Labels := by
      have hz : ∀ j, raw17338 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17338step0 = (fun i j => raw17338 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17338step0 raw17338; decide +kernel
      have hl : raw17338step0Labels = raw17338Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17338 raw17338Labels permutation434 hz
    mixedMoment B raw17338step0 raw17338step0Labels = mixedMoment B raw17338step1 raw17338step1Labels := by
      have ha : raw17338step1 = (fun i j => raw17338step0 (permutation127 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17338step1 raw17338step0; decide +kernel
      have hl : raw17338step1Labels = raw17338step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17338step0 raw17338step0Labels permutation127 permutation2
    mixedMoment B raw17338step1 raw17338step1Labels = mixedMoment B raw17338step2 raw17338step2Labels := by
      have ha : raw17338step2 = -raw17338step1 := by apply Matrix.ext; change ∀ i j, raw17338step2 i j = -(raw17338step1 i j); unfold raw17338step2 raw17338step1; decide +kernel
      have hl : raw17338step2Labels = raw17338step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5434 node5434Labels := by rfl

def raw17339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw17339Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw17339step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17339step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw17339step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17339step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw17339step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17339 raw17339Labels = mixedMoment B node4827 node4827Labels := by
  calc
    mixedMoment B raw17339 raw17339Labels = mixedMoment B raw17339step0 raw17339step0Labels := by
      have hz : ∀ j, raw17339 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17339step0 = (fun i j => raw17339 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17339step0 raw17339; decide +kernel
      have hl : raw17339step0Labels = raw17339Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17339 raw17339Labels permutation434 hz
    mixedMoment B raw17339step0 raw17339step0Labels = mixedMoment B raw17339step1 raw17339step1Labels := by
      have ha : raw17339step1 = (fun i j => raw17339step0 (permutation145 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17339step1 raw17339step0; decide +kernel
      have hl : raw17339step1Labels = raw17339step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17339step0 raw17339step0Labels permutation145 permutation5
    mixedMoment B raw17339step1 raw17339step1Labels = mixedMoment B raw17339step2 raw17339step2Labels := by
      have ha : raw17339step2 = raw17339step1 := by apply Matrix.ext; unfold raw17339step2 raw17339step1; decide +kernel
      have hl : raw17339step1Labels = labelEmbedding8 ∘ raw17339step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17339step1 raw17339step1Labels raw17339step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4827 node4827Labels := by rfl

def raw17340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw17340Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw17340step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17340step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw17340step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17340step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw17340step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17340 raw17340Labels = mixedMoment B node4828 node4828Labels := by
  calc
    mixedMoment B raw17340 raw17340Labels = mixedMoment B raw17340step0 raw17340step0Labels := by
      have hz : ∀ j, raw17340 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17340step0 = (fun i j => raw17340 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17340step0 raw17340; decide +kernel
      have hl : raw17340step0Labels = raw17340Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17340 raw17340Labels permutation434 hz
    mixedMoment B raw17340step0 raw17340step0Labels = mixedMoment B raw17340step1 raw17340step1Labels := by
      have ha : raw17340step1 = (fun i j => raw17340step0 (permutation144 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17340step1 raw17340step0; decide +kernel
      have hl : raw17340step1Labels = raw17340step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17340step0 raw17340step0Labels permutation144 permutation5
    mixedMoment B raw17340step1 raw17340step1Labels = mixedMoment B raw17340step2 raw17340step2Labels := by
      have ha : raw17340step2 = raw17340step1 := by apply Matrix.ext; unfold raw17340step2 raw17340step1; decide +kernel
      have hl : raw17340step1Labels = labelEmbedding8 ∘ raw17340step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17340step1 raw17340step1Labels raw17340step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4828 node4828Labels := by rfl

def raw17341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw17341Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17341step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -3, 0]]
def raw17341step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17341step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17341step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17341step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17341step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17341step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17341step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17341 raw17341Labels = mixedMoment B node4866 node4866Labels := by
  calc
    mixedMoment B raw17341 raw17341Labels = mixedMoment B raw17341step0 raw17341step0Labels := by
      have hz : ∀ j, raw17341 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17341step0 = (fun i j => raw17341 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17341step0 raw17341; decide +kernel
      have hl : raw17341step0Labels = raw17341Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17341 raw17341Labels permutation434 hz
    mixedMoment B raw17341step0 raw17341step0Labels = mixedMoment B raw17341step1 raw17341step1Labels := by
      have ha : raw17341step1 = (fun i j => raw17341step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17341step1 raw17341step0; decide +kernel
      have hl : raw17341step1Labels = raw17341step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17341step0 raw17341step0Labels permutation151 permutation3
    mixedMoment B raw17341step1 raw17341step1Labels = mixedMoment B raw17341step2 raw17341step2Labels := by
      have ha : raw17341step2 = -raw17341step1 := by apply Matrix.ext; change ∀ i j, raw17341step2 i j = -(raw17341step1 i j); unfold raw17341step2 raw17341step1; decide +kernel
      have hl : raw17341step2Labels = raw17341step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17341step2 raw17341step2Labels = mixedMoment B raw17341step3 raw17341step3Labels := by
      have ha : raw17341step3 = raw17341step2 := by apply Matrix.ext; unfold raw17341step3 raw17341step2; decide +kernel
      have hl : raw17341step2Labels = labelEmbedding6 ∘ raw17341step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17341step2 raw17341step2Labels raw17341step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4866 node4866Labels := by rfl

def raw17342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw17342Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17342step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw17342step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17342step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw17342step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17342 raw17342Labels = mixedMoment B node4826 node4826Labels := by
  calc
    mixedMoment B raw17342 raw17342Labels = mixedMoment B raw17342step0 raw17342step0Labels := by
      have ha : raw17342step0 = (fun i j => raw17342 (permutation644 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17342step0 raw17342; decide +kernel
      have hl : raw17342step0Labels = raw17342Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17342 raw17342Labels permutation644 permutation5
    mixedMoment B raw17342step0 raw17342step0Labels = mixedMoment B raw17342step1 raw17342step1Labels := by
      have ha : raw17342step1 = raw17342step0 := by apply Matrix.ext; unfold raw17342step1 raw17342step0; decide +kernel
      have hl : raw17342step0Labels = labelEmbedding8 ∘ raw17342step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17342step0 raw17342step0Labels raw17342step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4826 node4826Labels := by rfl

def raw17343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw17343Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17343step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![3, -3, 0]]
def raw17343step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17343step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17343step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw17343step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17343step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17343 raw17343Labels = mixedMoment B node4839 node4839Labels := by
  calc
    mixedMoment B raw17343 raw17343Labels = mixedMoment B raw17343step0 raw17343step0Labels := by
      have hz : ∀ j, raw17343 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17343step0 = (fun i j => raw17343 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17343step0 raw17343; decide +kernel
      have hl : raw17343step0Labels = raw17343Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17343 raw17343Labels permutation434 hz
    mixedMoment B raw17343step0 raw17343step0Labels = mixedMoment B raw17343step1 raw17343step1Labels := by
      have ha : raw17343step1 = (fun i j => raw17343step0 (permutation142 i) (permutation5 j)) := by apply Matrix.ext; unfold raw17343step1 raw17343step0; decide +kernel
      have hl : raw17343step1Labels = raw17343step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17343step0 raw17343step0Labels permutation142 permutation5
    mixedMoment B raw17343step1 raw17343step1Labels = mixedMoment B raw17343step2 raw17343step2Labels := by
      have ha : raw17343step2 = raw17343step1 := by apply Matrix.ext; unfold raw17343step2 raw17343step1; decide +kernel
      have hl : raw17343step1Labels = labelEmbedding8 ∘ raw17343step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17343step1 raw17343step1Labels raw17343step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4839 node4839Labels := by rfl

def raw17344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17344Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17344step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17344step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17344step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17344 raw17344Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw17344 raw17344Labels = mixedMoment B raw17344step0 raw17344step0Labels := by
      have hz : ∀ j, raw17344 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17344step0 = (fun i j => raw17344 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17344step0 raw17344; decide +kernel
      have hl : raw17344step0Labels = raw17344Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17344 raw17344Labels permutation434 hz
    mixedMoment B raw17344step0 raw17344step0Labels = mixedMoment B raw17344step1 raw17344step1Labels := by
      have ha : raw17344step1 = (fun i j => raw17344step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17344step1 raw17344step0; decide +kernel
      have hl : raw17344step1Labels = raw17344step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17344step0 raw17344step0Labels permutation56 permutation3
    _ = mixedMoment B node3850 node3850Labels := by rfl

def raw17345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17345Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17345step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17345step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw17345step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17345step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw17345step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17345 raw17345Labels = mixedMoment B node3887 node3887Labels := by
  calc
    mixedMoment B raw17345 raw17345Labels = mixedMoment B raw17345step0 raw17345step0Labels := by
      have hz : ∀ j, raw17345 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17345step0 = (fun i j => raw17345 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17345step0 raw17345; decide +kernel
      have hl : raw17345step0Labels = raw17345Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17345 raw17345Labels permutation434 hz
    mixedMoment B raw17345step0 raw17345step0Labels = mixedMoment B raw17345step1 raw17345step1Labels := by
      have ha : raw17345step1 = (fun i j => raw17345step0 (permutation147 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17345step1 raw17345step0; decide +kernel
      have hl : raw17345step1Labels = raw17345step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17345step0 raw17345step0Labels permutation147 permutation3
    mixedMoment B raw17345step1 raw17345step1Labels = mixedMoment B raw17345step2 raw17345step2Labels := by
      have ha : raw17345step2 = -raw17345step1 := by apply Matrix.ext; change ∀ i j, raw17345step2 i j = -(raw17345step1 i j); unfold raw17345step2 raw17345step1; decide +kernel
      have hl : raw17345step2Labels = raw17345step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3887 node3887Labels := by rfl

def raw17346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17346Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17346step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw17346step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17346step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw17346step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17346 raw17346Labels = mixedMoment B node3875 node3875Labels := by
  calc
    mixedMoment B raw17346 raw17346Labels = mixedMoment B raw17346step0 raw17346step0Labels := by
      have ha : raw17346step0 = (fun i j => raw17346 (permutation677 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17346step0 raw17346; decide +kernel
      have hl : raw17346step0Labels = raw17346Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17346 raw17346Labels permutation677 permutation3
    mixedMoment B raw17346step0 raw17346step0Labels = mixedMoment B raw17346step1 raw17346step1Labels := by
      have ha : raw17346step1 = -raw17346step0 := by apply Matrix.ext; change ∀ i j, raw17346step1 i j = -(raw17346step0 i j); unfold raw17346step1 raw17346step0; decide +kernel
      have hl : raw17346step1Labels = raw17346step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3875 node3875Labels := by rfl

def raw17347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw17347Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17347step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0]]
def raw17347step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17347step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1]]
def raw17347step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17347step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1]]
def raw17347step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17347 raw17347Labels = mixedMoment B node3906 node3906Labels := by
  calc
    mixedMoment B raw17347 raw17347Labels = mixedMoment B raw17347step0 raw17347step0Labels := by
      have hz : ∀ j, raw17347 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17347step0 = (fun i j => raw17347 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17347step0 raw17347; decide +kernel
      have hl : raw17347step0Labels = raw17347Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17347 raw17347Labels permutation434 hz
    mixedMoment B raw17347step0 raw17347step0Labels = mixedMoment B raw17347step1 raw17347step1Labels := by
      have ha : raw17347step1 = (fun i j => raw17347step0 (permutation144 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17347step1 raw17347step0; decide +kernel
      have hl : raw17347step1Labels = raw17347step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17347step0 raw17347step0Labels permutation144 permutation3
    mixedMoment B raw17347step1 raw17347step1Labels = mixedMoment B raw17347step2 raw17347step2Labels := by
      have ha : raw17347step2 = -raw17347step1 := by apply Matrix.ext; change ∀ i j, raw17347step2 i j = -(raw17347step1 i j); unfold raw17347step2 raw17347step1; decide +kernel
      have hl : raw17347step2Labels = raw17347step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3906 node3906Labels := by rfl

def raw17348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw17348Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17348step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0]]
def raw17348step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17348step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw17348step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17348 raw17348Labels = mixedMoment B node4013 node4013Labels := by
  calc
    mixedMoment B raw17348 raw17348Labels = mixedMoment B raw17348step0 raw17348step0Labels := by
      have hz : ∀ j, raw17348 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17348step0 = (fun i j => raw17348 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17348step0 raw17348; decide +kernel
      have hl : raw17348step0Labels = raw17348Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17348 raw17348Labels permutation434 hz
    mixedMoment B raw17348step0 raw17348step0Labels = mixedMoment B raw17348step1 raw17348step1Labels := by
      have ha : raw17348step1 = (fun i j => raw17348step0 (permutation114 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17348step1 raw17348step0; decide +kernel
      have hl : raw17348step1Labels = raw17348step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17348step0 raw17348step0Labels permutation114 permutation6
    _ = mixedMoment B node4013 node4013Labels := by rfl

def raw17349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17349Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17349step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17349step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17349step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17349step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw17349step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17349 raw17349Labels = mixedMoment B node2765 node2765Labels := by
  calc
    mixedMoment B raw17349 raw17349Labels = mixedMoment B raw17349step0 raw17349step0Labels := by
      have hz : ∀ j, raw17349 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17349step0 = (fun i j => raw17349 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17349step0 raw17349; decide +kernel
      have hl : raw17349step0Labels = raw17349Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17349 raw17349Labels permutation434 hz
    mixedMoment B raw17349step0 raw17349step0Labels = mixedMoment B raw17349step1 raw17349step1Labels := by
      have hz : ∀ j, raw17349step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw17349step1 = (fun i j => raw17349step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw17349step1 raw17349step0; decide +kernel
      have hl : raw17349step1Labels = raw17349step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17349step0 raw17349step0Labels permutation56 hz
    mixedMoment B raw17349step1 raw17349step1Labels = mixedMoment B raw17349step2 raw17349step2Labels := by
      have ha : raw17349step2 = (fun i j => raw17349step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17349step2 raw17349step1; decide +kernel
      have hl : raw17349step2Labels = raw17349step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17349step1 raw17349step1Labels permutation8 permutation3
    _ = mixedMoment B node2765 node2765Labels := by rfl

def raw17350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17350Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17350step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17350step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17350step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17350step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17350step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17350step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17350step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17350 raw17350Labels = mixedMoment B node3888 node3888Labels := by
  calc
    mixedMoment B raw17350 raw17350Labels = mixedMoment B raw17350step0 raw17350step0Labels := by
      have hz : ∀ j, raw17350 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17350step0 = (fun i j => raw17350 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17350step0 raw17350; decide +kernel
      have hl : raw17350step0Labels = raw17350Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17350 raw17350Labels permutation434 hz
    mixedMoment B raw17350step0 raw17350step0Labels = mixedMoment B raw17350step1 raw17350step1Labels := by
      have hz : ∀ j, raw17350step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw17350step1 = (fun i j => raw17350step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw17350step1 raw17350step0; decide +kernel
      have hl : raw17350step1Labels = raw17350step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17350step0 raw17350step0Labels permutation56 hz
    mixedMoment B raw17350step1 raw17350step1Labels = mixedMoment B raw17350step2 raw17350step2Labels := by
      have ha : raw17350step2 = (fun i j => raw17350step1 (permutation31 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17350step2 raw17350step1; decide +kernel
      have hl : raw17350step2Labels = raw17350step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17350step1 raw17350step1Labels permutation31 permutation3
    mixedMoment B raw17350step2 raw17350step2Labels = mixedMoment B raw17350step3 raw17350step3Labels := by
      have ha : raw17350step3 = -raw17350step2 := by apply Matrix.ext; change ∀ i j, raw17350step3 i j = -(raw17350step2 i j); unfold raw17350step3 raw17350step2; decide +kernel
      have hl : raw17350step3Labels = raw17350step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3888 node3888Labels := by rfl

def raw17351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17351Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17351step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17351step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17351step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17351step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17351step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw17351step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17351 raw17351Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw17351 raw17351Labels = mixedMoment B raw17351step0 raw17351step0Labels := by
      have hz : ∀ j, raw17351 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw17351step0 = (fun i j => raw17351 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw17351step0 raw17351; decide +kernel
      have hl : raw17351step0Labels = raw17351Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17351 raw17351Labels permutation265 hz
    mixedMoment B raw17351step0 raw17351step0Labels = mixedMoment B raw17351step1 raw17351step1Labels := by
      have ha : raw17351step1 = (fun i j => raw17351step0 (permutation149 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17351step1 raw17351step0; decide +kernel
      have hl : raw17351step1Labels = raw17351step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17351step0 raw17351step0Labels permutation149 permutation3
    mixedMoment B raw17351step1 raw17351step1Labels = mixedMoment B raw17351step2 raw17351step2Labels := by
      have ha : raw17351step2 = -raw17351step1 := by apply Matrix.ext; change ∀ i j, raw17351step2 i j = -(raw17351step1 i j); unfold raw17351step2 raw17351step1; decide +kernel
      have hl : raw17351step2Labels = raw17351step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3876 node3876Labels := by rfl

def raw17352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw17352Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17352step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0]]
def raw17352step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17352step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![0, 2, -2], ![2, -2, 0]]
def raw17352step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17352step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, -2, 2], ![-2, 1, 1]]
def raw17352step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17352step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![0, -1, 1], ![0, 2, -2], ![2, -1, -1]]
def raw17352step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17352 raw17352Labels = mixedMoment B node3907 node3907Labels := by
  calc
    mixedMoment B raw17352 raw17352Labels = mixedMoment B raw17352step0 raw17352step0Labels := by
      have hz : ∀ j, raw17352 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17352step0 = (fun i j => raw17352 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17352step0 raw17352; decide +kernel
      have hl : raw17352step0Labels = raw17352Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17352 raw17352Labels permutation434 hz
    mixedMoment B raw17352step0 raw17352step0Labels = mixedMoment B raw17352step1 raw17352step1Labels := by
      have hz : ∀ j, raw17352step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw17352step1 = (fun i j => raw17352step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw17352step1 raw17352step0; decide +kernel
      have hl : raw17352step1Labels = raw17352step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17352step0 raw17352step0Labels permutation56 hz
    mixedMoment B raw17352step1 raw17352step1Labels = mixedMoment B raw17352step2 raw17352step2Labels := by
      have ha : raw17352step2 = (fun i j => raw17352step1 (permutation29 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17352step2 raw17352step1; decide +kernel
      have hl : raw17352step2Labels = raw17352step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17352step1 raw17352step1Labels permutation29 permutation3
    mixedMoment B raw17352step2 raw17352step2Labels = mixedMoment B raw17352step3 raw17352step3Labels := by
      have ha : raw17352step3 = -raw17352step2 := by apply Matrix.ext; change ∀ i j, raw17352step3 i j = -(raw17352step2 i j); unfold raw17352step3 raw17352step2; decide +kernel
      have hl : raw17352step3Labels = raw17352step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3907 node3907Labels := by rfl

def raw17353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw17353Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17353step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0]]
def raw17353step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17353step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![1, -1, 0]]
def raw17353step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17353step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw17353step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17353 raw17353Labels = mixedMoment B node4017 node4017Labels := by
  calc
    mixedMoment B raw17353 raw17353Labels = mixedMoment B raw17353step0 raw17353step0Labels := by
      have hz : ∀ j, raw17353 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17353step0 = (fun i j => raw17353 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17353step0 raw17353; decide +kernel
      have hl : raw17353step0Labels = raw17353Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17353 raw17353Labels permutation434 hz
    mixedMoment B raw17353step0 raw17353step0Labels = mixedMoment B raw17353step1 raw17353step1Labels := by
      have hz : ∀ j, raw17353step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw17353step1 = (fun i j => raw17353step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw17353step1 raw17353step0; decide +kernel
      have hl : raw17353step1Labels = raw17353step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17353step0 raw17353step0Labels permutation56 hz
    mixedMoment B raw17353step1 raw17353step1Labels = mixedMoment B raw17353step2 raw17353step2Labels := by
      have ha : raw17353step2 = (fun i j => raw17353step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17353step2 raw17353step1; decide +kernel
      have hl : raw17353step2Labels = raw17353step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17353step1 raw17353step1Labels permutation8 permutation3
    _ = mixedMoment B node4017 node4017Labels := by rfl

def raw17354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17354Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17354step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17354step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17354step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw17354step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17354 raw17354Labels = mixedMoment B node2505 node2505Labels := by
  calc
    mixedMoment B raw17354 raw17354Labels = mixedMoment B raw17354step0 raw17354step0Labels := by
      have hz : ∀ j, raw17354 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17354step0 = (fun i j => raw17354 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17354step0 raw17354; decide +kernel
      have hl : raw17354step0Labels = raw17354Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17354 raw17354Labels permutation434 hz
    mixedMoment B raw17354step0 raw17354step0Labels = mixedMoment B raw17354step1 raw17354step1Labels := by
      have ha : raw17354step1 = (fun i j => raw17354step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17354step1 raw17354step0; decide +kernel
      have hl : raw17354step1Labels = raw17354step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17354step0 raw17354step0Labels permutation34 permutation3
    _ = mixedMoment B node2505 node2505Labels := by rfl

def raw17355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17355Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17355step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17355step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw17355step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17355 raw17355Labels = mixedMoment B node3702 node3702Labels := by
  calc
    mixedMoment B raw17355 raw17355Labels = mixedMoment B raw17355step0 raw17355step0Labels := by
      have hz : ∀ j, raw17355 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17355step0 = (fun i j => raw17355 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17355step0 raw17355; decide +kernel
      have hl : raw17355step0Labels = raw17355Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17355 raw17355Labels permutation434 hz
    mixedMoment B raw17355step0 raw17355step0Labels = mixedMoment B raw17355step1 raw17355step1Labels := by
      have ha : raw17355step1 = (fun i j => raw17355step0 (permutation58 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17355step1 raw17355step0; decide +kernel
      have hl : raw17355step1Labels = raw17355step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17355step0 raw17355step0Labels permutation58 permutation3
    _ = mixedMoment B node3702 node3702Labels := by rfl

def raw17356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17356Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17356step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![1, -2, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17356step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17356step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17356step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17356 raw17356Labels = mixedMoment B node3751 node3751Labels := by
  calc
    mixedMoment B raw17356 raw17356Labels = mixedMoment B raw17356step0 raw17356step0Labels := by
      have ha : raw17356step0 = (fun i j => raw17356 (permutation644 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17356step0 raw17356; decide +kernel
      have hl : raw17356step0Labels = raw17356Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17356 raw17356Labels permutation644 permutation3
    mixedMoment B raw17356step0 raw17356step0Labels = mixedMoment B raw17356step1 raw17356step1Labels := by
      have ha : raw17356step1 = -raw17356step0 := by apply Matrix.ext; change ∀ i j, raw17356step1 i j = -(raw17356step0 i j); unfold raw17356step1 raw17356step0; decide +kernel
      have hl : raw17356step1Labels = raw17356step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3751 node3751Labels := by rfl

def raw17357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0]]
def raw17357Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17357step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 2, -2], ![2, -2, 0]]
def raw17357step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17357step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw17357step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17357step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw17357step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17357 raw17357Labels = mixedMoment B node3771 node3771Labels := by
  calc
    mixedMoment B raw17357 raw17357Labels = mixedMoment B raw17357step0 raw17357step0Labels := by
      have hz : ∀ j, raw17357 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17357step0 = (fun i j => raw17357 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17357step0 raw17357; decide +kernel
      have hl : raw17357step0Labels = raw17357Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17357 raw17357Labels permutation434 hz
    mixedMoment B raw17357step0 raw17357step0Labels = mixedMoment B raw17357step1 raw17357step1Labels := by
      have ha : raw17357step1 = (fun i j => raw17357step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17357step1 raw17357step0; decide +kernel
      have hl : raw17357step1Labels = raw17357step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17357step0 raw17357step0Labels permutation145 permutation3
    mixedMoment B raw17357step1 raw17357step1Labels = mixedMoment B raw17357step2 raw17357step2Labels := by
      have ha : raw17357step2 = -raw17357step1 := by apply Matrix.ext; change ∀ i j, raw17357step2 i j = -(raw17357step1 i j); unfold raw17357step2 raw17357step1; decide +kernel
      have hl : raw17357step2Labels = raw17357step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3771 node3771Labels := by rfl

def raw17358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 0, 0], ![1, 1, -2], ![1, -1, 0]]
def raw17358Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![1, -1, 0]]
def raw17358step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17358step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17358step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17358 raw17358Labels = mixedMoment B node3983 node3983Labels := by
  calc
    mixedMoment B raw17358 raw17358Labels = mixedMoment B raw17358step0 raw17358step0Labels := by
      have hz : ∀ j, raw17358 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17358step0 = (fun i j => raw17358 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17358step0 raw17358; decide +kernel
      have hl : raw17358step0Labels = raw17358Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17358 raw17358Labels permutation434 hz
    mixedMoment B raw17358step0 raw17358step0Labels = mixedMoment B raw17358step1 raw17358step1Labels := by
      have ha : raw17358step1 = (fun i j => raw17358step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17358step1 raw17358step0; decide +kernel
      have hl : raw17358step1Labels = raw17358step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17358step0 raw17358step0Labels permutation35 permutation3
    _ = mixedMoment B node3983 node3983Labels := by rfl

def raw17359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17359Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17359step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17359step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17359 raw17359Labels = mixedMoment B node2477 node2477Labels := by
  calc
    mixedMoment B raw17359 raw17359Labels = mixedMoment B raw17359step0 raw17359step0Labels := by
      have ha : raw17359step0 = (fun i j => raw17359 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17359step0 raw17359; decide +kernel
      have hl : raw17359step0Labels = raw17359Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17359 raw17359Labels permutation154 permutation3
    _ = mixedMoment B node2477 node2477Labels := by rfl

def raw17360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17360Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17360step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17360step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17360 raw17360Labels = mixedMoment B node3687 node3687Labels := by
  calc
    mixedMoment B raw17360 raw17360Labels = mixedMoment B raw17360step0 raw17360step0Labels := by
      have ha : raw17360step0 = (fun i j => raw17360 (permutation267 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17360step0 raw17360; decide +kernel
      have hl : raw17360step0Labels = raw17360Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17360 raw17360Labels permutation267 permutation3
    _ = mixedMoment B node3687 node3687Labels := by rfl

def raw17361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17361Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17361step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17361step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17361step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17361step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17361 raw17361Labels = mixedMoment B node3787 node3787Labels := by
  calc
    mixedMoment B raw17361 raw17361Labels = mixedMoment B raw17361step0 raw17361step0Labels := by
      have ha : raw17361step0 = (fun i j => raw17361 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17361step0 raw17361; decide +kernel
      have hl : raw17361step0Labels = raw17361Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17361 raw17361Labels permutation664 permutation3
    mixedMoment B raw17361step0 raw17361step0Labels = mixedMoment B raw17361step1 raw17361step1Labels := by
      have ha : raw17361step1 = -raw17361step0 := by apply Matrix.ext; change ∀ i j, raw17361step1 i j = -(raw17361step0 i j); unfold raw17361step1 raw17361step0; decide +kernel
      have hl : raw17361step1Labels = raw17361step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3787 node3787Labels := by rfl

def raw17362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw17362Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17362step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw17362step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17362step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw17362step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17362 raw17362Labels = mixedMoment B node3796 node3796Labels := by
  calc
    mixedMoment B raw17362 raw17362Labels = mixedMoment B raw17362step0 raw17362step0Labels := by
      have ha : raw17362step0 = (fun i j => raw17362 (permutation658 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17362step0 raw17362; decide +kernel
      have hl : raw17362step0Labels = raw17362Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17362 raw17362Labels permutation658 permutation3
    mixedMoment B raw17362step0 raw17362step0Labels = mixedMoment B raw17362step1 raw17362step1Labels := by
      have ha : raw17362step1 = -raw17362step0 := by apply Matrix.ext; change ∀ i j, raw17362step1 i j = -(raw17362step0 i j); unfold raw17362step1 raw17362step0; decide +kernel
      have hl : raw17362step1Labels = raw17362step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3796 node3796Labels := by rfl

def raw17363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw17363Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17363step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17363step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17363 raw17363Labels = mixedMoment B node3979 node3979Labels := by
  calc
    mixedMoment B raw17363 raw17363Labels = mixedMoment B raw17363step0 raw17363step0Labels := by
      have ha : raw17363step0 = (fun i j => raw17363 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17363step0 raw17363; decide +kernel
      have hl : raw17363step0Labels = raw17363Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17363 raw17363Labels permutation154 permutation3
    _ = mixedMoment B node3979 node3979Labels := by rfl

def raw17364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw17364Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw17364step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17364step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw17364step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17364 raw17364Labels = mixedMoment B node2488 node2488Labels := by
  calc
    mixedMoment B raw17364 raw17364Labels = mixedMoment B raw17364step0 raw17364step0Labels := by
      have hz : ∀ j, raw17364 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17364step0 = (fun i j => raw17364 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17364step0 raw17364; decide +kernel
      have hl : raw17364step0Labels = raw17364Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17364 raw17364Labels permutation434 hz
    mixedMoment B raw17364step0 raw17364step0Labels = mixedMoment B raw17364step1 raw17364step1Labels := by
      have ha : raw17364step1 = (fun i j => raw17364step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17364step1 raw17364step0; decide +kernel
      have hl : raw17364step1Labels = raw17364step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17364step0 raw17364step0Labels permutation32 permutation3
    _ = mixedMoment B node2488 node2488Labels := by rfl

def raw17365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw17365Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![2, -2, 0]]
def raw17365step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17365step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw17365step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17365 raw17365Labels = mixedMoment B node3693 node3693Labels := by
  calc
    mixedMoment B raw17365 raw17365Labels = mixedMoment B raw17365step0 raw17365step0Labels := by
      have hz : ∀ j, raw17365 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17365step0 = (fun i j => raw17365 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17365step0 raw17365; decide +kernel
      have hl : raw17365step0Labels = raw17365Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17365 raw17365Labels permutation434 hz
    mixedMoment B raw17365step0 raw17365step0Labels = mixedMoment B raw17365step1 raw17365step1Labels := by
      have ha : raw17365step1 = (fun i j => raw17365step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17365step1 raw17365step0; decide +kernel
      have hl : raw17365step1Labels = raw17365step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17365step0 raw17365step0Labels permutation56 permutation3
    _ = mixedMoment B node3693 node3693Labels := by rfl

def raw17366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![2, 0, -2], ![2, -2, 0]]
def raw17366Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![2, 0, -2], ![2, -2, 0]]
def raw17366step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17366step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17366step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17366step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17366step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17366 raw17366Labels = mixedMoment B node3737 node3737Labels := by
  calc
    mixedMoment B raw17366 raw17366Labels = mixedMoment B raw17366step0 raw17366step0Labels := by
      have hz : ∀ j, raw17366 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17366step0 = (fun i j => raw17366 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17366step0 raw17366; decide +kernel
      have hl : raw17366step0Labels = raw17366Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17366 raw17366Labels permutation434 hz
    mixedMoment B raw17366step0 raw17366step0Labels = mixedMoment B raw17366step1 raw17366step1Labels := by
      have ha : raw17366step1 = (fun i j => raw17366step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17366step1 raw17366step0; decide +kernel
      have hl : raw17366step1Labels = raw17366step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17366step0 raw17366step0Labels permutation151 permutation3
    mixedMoment B raw17366step1 raw17366step1Labels = mixedMoment B raw17366step2 raw17366step2Labels := by
      have ha : raw17366step2 = -raw17366step1 := by apply Matrix.ext; change ∀ i j, raw17366step2 i j = -(raw17366step1 i j); unfold raw17366step2 raw17366step1; decide +kernel
      have hl : raw17366step2Labels = raw17366step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3737 node3737Labels := by rfl

def raw17367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 1, 0], ![2, 0, -2], ![2, -2, 0]]
def raw17367Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17367step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17367step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17367step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17367step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17367 raw17367Labels = mixedMoment B node3721 node3721Labels := by
  calc
    mixedMoment B raw17367 raw17367Labels = mixedMoment B raw17367step0 raw17367step0Labels := by
      have ha : raw17367step0 = (fun i j => raw17367 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17367step0 raw17367; decide +kernel
      have hl : raw17367step0Labels = raw17367Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17367 raw17367Labels permutation680 permutation3
    mixedMoment B raw17367step0 raw17367step0Labels = mixedMoment B raw17367step1 raw17367step1Labels := by
      have ha : raw17367step1 = -raw17367step0 := by apply Matrix.ext; change ∀ i j, raw17367step1 i j = -(raw17367step0 i j); unfold raw17367step1 raw17367step0; decide +kernel
      have hl : raw17367step1Labels = raw17367step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3721 node3721Labels := by rfl

def raw17368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![2, 0, -2], ![1, -1, 0]]
def raw17368Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![1, -1, 0]]
def raw17368step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17368step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17368step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17368 raw17368Labels = mixedMoment B node3982 node3982Labels := by
  calc
    mixedMoment B raw17368 raw17368Labels = mixedMoment B raw17368step0 raw17368step0Labels := by
      have hz : ∀ j, raw17368 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17368step0 = (fun i j => raw17368 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17368step0 raw17368; decide +kernel
      have hl : raw17368step0Labels = raw17368Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17368 raw17368Labels permutation434 hz
    mixedMoment B raw17368step0 raw17368step0Labels = mixedMoment B raw17368step1 raw17368step1Labels := by
      have ha : raw17368step1 = (fun i j => raw17368step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17368step1 raw17368step0; decide +kernel
      have hl : raw17368step1Labels = raw17368step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17368step0 raw17368step0Labels permutation33 permutation3
    _ = mixedMoment B node3982 node3982Labels := by rfl

def raw17369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw17369Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17369step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw17369step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17369step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-3, 1, 2]]
def raw17369step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17369step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw17369step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17369 raw17369Labels = mixedMoment B node2079 node2079Labels := by
  calc
    mixedMoment B raw17369 raw17369Labels = mixedMoment B raw17369step0 raw17369step0Labels := by
      have hz : ∀ j, raw17369 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17369step0 = (fun i j => raw17369 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17369step0 raw17369; decide +kernel
      have hl : raw17369step0Labels = raw17369Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17369 raw17369Labels permutation434 hz
    mixedMoment B raw17369step0 raw17369step0Labels = mixedMoment B raw17369step1 raw17369step1Labels := by
      have ha : raw17369step1 = (fun i j => raw17369step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17369step1 raw17369step0; decide +kernel
      have hl : raw17369step1Labels = raw17369step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17369step0 raw17369step0Labels permutation151 permutation3
    mixedMoment B raw17369step1 raw17369step1Labels = mixedMoment B raw17369step2 raw17369step2Labels := by
      have ha : raw17369step2 = -raw17369step1 := by apply Matrix.ext; change ∀ i j, raw17369step2 i j = -(raw17369step1 i j); unfold raw17369step2 raw17369step1; decide +kernel
      have hl : raw17369step2Labels = raw17369step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2079 node2079Labels := by rfl

def raw17370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw17370Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17370step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, 1, -2], ![3, -3, 0]]
def raw17370step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17370step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-2, 1, 1], ![-2, 0, 2]]
def raw17370step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17370step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw17370step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17370 raw17370Labels = mixedMoment B node2082 node2082Labels := by
  calc
    mixedMoment B raw17370 raw17370Labels = mixedMoment B raw17370step0 raw17370step0Labels := by
      have hz : ∀ j, raw17370 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17370step0 = (fun i j => raw17370 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17370step0 raw17370; decide +kernel
      have hl : raw17370step0Labels = raw17370Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17370 raw17370Labels permutation434 hz
    mixedMoment B raw17370step0 raw17370step0Labels = mixedMoment B raw17370step1 raw17370step1Labels := by
      have ha : raw17370step1 = (fun i j => raw17370step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17370step1 raw17370step0; decide +kernel
      have hl : raw17370step1Labels = raw17370step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17370step0 raw17370step0Labels permutation150 permutation3
    mixedMoment B raw17370step1 raw17370step1Labels = mixedMoment B raw17370step2 raw17370step2Labels := by
      have ha : raw17370step2 = -raw17370step1 := by apply Matrix.ext; change ∀ i j, raw17370step2 i j = -(raw17370step1 i j); unfold raw17370step2 raw17370step1; decide +kernel
      have hl : raw17370step2Labels = raw17370step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2082 node2082Labels := by rfl

def raw17371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![0, 0, 0], ![1, 1, -2], ![3, -3, 0]]
def raw17371Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 0, 1], ![1, 1, -2], ![3, -3, 0]]
def raw17371step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17371step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw17371step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17371step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw17371step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17371 raw17371Labels = mixedMoment B node2107 node2107Labels := by
  calc
    mixedMoment B raw17371 raw17371Labels = mixedMoment B raw17371step0 raw17371step0Labels := by
      have hz : ∀ j, raw17371 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17371step0 = (fun i j => raw17371 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17371step0 raw17371; decide +kernel
      have hl : raw17371step0Labels = raw17371Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17371 raw17371Labels permutation434 hz
    mixedMoment B raw17371step0 raw17371step0Labels = mixedMoment B raw17371step1 raw17371step1Labels := by
      have ha : raw17371step1 = (fun i j => raw17371step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17371step1 raw17371step0; decide +kernel
      have hl : raw17371step1Labels = raw17371step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17371step0 raw17371step0Labels permutation151 permutation3
    mixedMoment B raw17371step1 raw17371step1Labels = mixedMoment B raw17371step2 raw17371step2Labels := by
      have ha : raw17371step2 = -raw17371step1 := by apply Matrix.ext; change ∀ i j, raw17371step2 i j = -(raw17371step1 i j); unfold raw17371step2 raw17371step1; decide +kernel
      have hl : raw17371step2Labels = raw17371step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2107 node2107Labels := by rfl

def raw17372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![-1, 1, 0], ![1, 1, -2], ![3, -3, 0]]
def raw17372Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17372step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17372step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17372step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17372step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17372 raw17372Labels = mixedMoment B node2077 node2077Labels := by
  calc
    mixedMoment B raw17372 raw17372Labels = mixedMoment B raw17372step0 raw17372step0Labels := by
      have ha : raw17372step0 = (fun i j => raw17372 (permutation680 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17372step0 raw17372; decide +kernel
      have hl : raw17372step0Labels = raw17372Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17372 raw17372Labels permutation680 permutation3
    mixedMoment B raw17372step0 raw17372step0Labels = mixedMoment B raw17372step1 raw17372step1Labels := by
      have ha : raw17372step1 = -raw17372step0 := by apply Matrix.ext; change ∀ i j, raw17372step1 i j = -(raw17372step0 i j); unfold raw17372step1 raw17372step0; decide +kernel
      have hl : raw17372step1Labels = raw17372step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2077 node2077Labels := by rfl

def raw17373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 0, 0], ![0, 2, -2], ![3, -3, 0]]
def raw17373Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -1, 1], ![0, 2, -2], ![3, -3, 0]]
def raw17373step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17373step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw17373step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17373step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw17373step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17373 raw17373Labels = mixedMoment B node2216 node2216Labels := by
  calc
    mixedMoment B raw17373 raw17373Labels = mixedMoment B raw17373step0 raw17373step0Labels := by
      have hz : ∀ j, raw17373 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17373step0 = (fun i j => raw17373 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17373step0 raw17373; decide +kernel
      have hl : raw17373step0Labels = raw17373Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17373 raw17373Labels permutation434 hz
    mixedMoment B raw17373step0 raw17373step0Labels = mixedMoment B raw17373step1 raw17373step1Labels := by
      have ha : raw17373step1 = (fun i j => raw17373step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17373step1 raw17373step0; decide +kernel
      have hl : raw17373step1Labels = raw17373step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17373step0 raw17373step0Labels permutation145 permutation3
    mixedMoment B raw17373step1 raw17373step1Labels = mixedMoment B raw17373step2 raw17373step2Labels := by
      have ha : raw17373step2 = -raw17373step1 := by apply Matrix.ext; change ∀ i j, raw17373step2 i j = -(raw17373step1 i j); unfold raw17373step2 raw17373step1; decide +kernel
      have hl : raw17373step2Labels = raw17373step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2216 node2216Labels := by rfl

def raw17374 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17374Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17374step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17374step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -2, 2], ![-1, 2, -1], ![-2, 1, 1]]
def raw17374step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17374step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 2, -2], ![1, -2, 1], ![2, -1, -1]]
def raw17374step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17374 raw17374Labels = mixedMoment B node5436 node5436Labels := by
  calc
    mixedMoment B raw17374 raw17374Labels = mixedMoment B raw17374step0 raw17374step0Labels := by
      have hz : ∀ j, raw17374 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17374step0 = (fun i j => raw17374 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17374step0 raw17374; decide +kernel
      have hl : raw17374step0Labels = raw17374Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17374 raw17374Labels permutation434 hz
    mixedMoment B raw17374step0 raw17374step0Labels = mixedMoment B raw17374step1 raw17374step1Labels := by
      have ha : raw17374step1 = (fun i j => raw17374step0 (permutation42 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17374step1 raw17374step0; decide +kernel
      have hl : raw17374step1Labels = raw17374step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17374step0 raw17374step0Labels permutation42 permutation2
    mixedMoment B raw17374step1 raw17374step1Labels = mixedMoment B raw17374step2 raw17374step2Labels := by
      have ha : raw17374step2 = -raw17374step1 := by apply Matrix.ext; change ∀ i j, raw17374step2 i j = -(raw17374step1 i j); unfold raw17374step2 raw17374step1; decide +kernel
      have hl : raw17374step2Labels = raw17374step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5436 node5436Labels := by rfl

def raw17375 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17375Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17375step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17375step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17375step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-2, 1, 1], ![0, -2, 2]]
def raw17375step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17375step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17375step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17375step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw17375step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17375 raw17375Labels = mixedMoment B node5443 node5443Labels := by
  calc
    mixedMoment B raw17375 raw17375Labels = mixedMoment B raw17375step0 raw17375step0Labels := by
      have hz : ∀ j, raw17375 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17375step0 = (fun i j => raw17375 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17375step0 raw17375; decide +kernel
      have hl : raw17375step0Labels = raw17375Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17375 raw17375Labels permutation434 hz
    mixedMoment B raw17375step0 raw17375step0Labels = mixedMoment B raw17375step1 raw17375step1Labels := by
      have hz : ∀ j, raw17375step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17375step1 = (fun i j => raw17375step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17375step1 raw17375step0; decide +kernel
      have hl : raw17375step1Labels = raw17375step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17375step0 raw17375step0Labels permutation80 hz
    mixedMoment B raw17375step1 raw17375step1Labels = mixedMoment B raw17375step2 raw17375step2Labels := by
      have ha : raw17375step2 = (fun i j => raw17375step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17375step2 raw17375step1; decide +kernel
      have hl : raw17375step2Labels = raw17375step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17375step1 raw17375step1Labels permutation8 permutation7
    mixedMoment B raw17375step2 raw17375step2Labels = mixedMoment B raw17375step3 raw17375step3Labels := by
      have ha : raw17375step3 = raw17375step2 := by apply Matrix.ext; unfold raw17375step3 raw17375step2; decide +kernel
      have hl : raw17375step2Labels = labelEmbedding10 ∘ raw17375step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17375step2 raw17375step2Labels raw17375step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5443 node5443Labels := by rfl

def raw17376 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17376Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17376step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17376step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw17376step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw17376step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17376 raw17376Labels = mixedMoment B node5425 node5425Labels := by
  calc
    mixedMoment B raw17376 raw17376Labels = mixedMoment B raw17376step0 raw17376step0Labels := by
      have ha : raw17376step0 = (fun i j => raw17376 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw17376step0 raw17376; decide +kernel
      have hl : raw17376step0Labels = raw17376Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17376 raw17376Labels permutation152 permutation7
    mixedMoment B raw17376step0 raw17376step0Labels = mixedMoment B raw17376step1 raw17376step1Labels := by
      have ha : raw17376step1 = raw17376step0 := by apply Matrix.ext; unfold raw17376step1 raw17376step0; decide +kernel
      have hl : raw17376step0Labels = labelEmbedding10 ∘ raw17376step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17376step0 raw17376step0Labels raw17376step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5425 node5425Labels := by rfl

def raw17377 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw17377Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17377step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw17377step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17377step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw17377step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17377step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw17377step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17377 raw17377Labels = mixedMoment B node5267 node5267Labels := by
  calc
    mixedMoment B raw17377 raw17377Labels = mixedMoment B raw17377step0 raw17377step0Labels := by
      have hz : ∀ j, raw17377 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17377step0 = (fun i j => raw17377 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17377step0 raw17377; decide +kernel
      have hl : raw17377step0Labels = raw17377Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17377 raw17377Labels permutation434 hz
    mixedMoment B raw17377step0 raw17377step0Labels = mixedMoment B raw17377step1 raw17377step1Labels := by
      have ha : raw17377step1 = (fun i j => raw17377step0 (permutation115 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17377step1 raw17377step0; decide +kernel
      have hl : raw17377step1Labels = raw17377step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17377step0 raw17377step0Labels permutation115 permutation3
    mixedMoment B raw17377step1 raw17377step1Labels = mixedMoment B raw17377step2 raw17377step2Labels := by
      have ha : raw17377step2 = raw17377step1 := by apply Matrix.ext; unfold raw17377step2 raw17377step1; decide +kernel
      have hl : raw17377step1Labels = labelEmbedding6 ∘ raw17377step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17377step1 raw17377step1Labels raw17377step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5267 node5267Labels := by rfl

def raw17378 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17378Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17378step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17378step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17378step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw17378step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17378step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17378step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17378 raw17378Labels = mixedMoment B node5428 node5428Labels := by
  calc
    mixedMoment B raw17378 raw17378Labels = mixedMoment B raw17378step0 raw17378step0Labels := by
      have hz : ∀ j, raw17378 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17378step0 = (fun i j => raw17378 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17378step0 raw17378; decide +kernel
      have hl : raw17378step0Labels = raw17378Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17378 raw17378Labels permutation434 hz
    mixedMoment B raw17378step0 raw17378step0Labels = mixedMoment B raw17378step1 raw17378step1Labels := by
      have ha : raw17378step1 = (fun i j => raw17378step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw17378step1 raw17378step0; decide +kernel
      have hl : raw17378step1Labels = raw17378step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17378step0 raw17378step0Labels permutation39 permutation2
    mixedMoment B raw17378step1 raw17378step1Labels = mixedMoment B raw17378step2 raw17378step2Labels := by
      have ha : raw17378step2 = -raw17378step1 := by apply Matrix.ext; change ∀ i j, raw17378step2 i j = -(raw17378step1 i j); unfold raw17378step2 raw17378step1; decide +kernel
      have hl : raw17378step2Labels = raw17378step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5428 node5428Labels := by rfl

def raw17379 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17379Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17379step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17379step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17379step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-2, 1, 1], ![0, -2, 2]]
def raw17379step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17379step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17379step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17379step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17379step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17379step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17379step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17379 raw17379Labels = mixedMoment B node5451 node5451Labels := by
  calc
    mixedMoment B raw17379 raw17379Labels = mixedMoment B raw17379step0 raw17379step0Labels := by
      have hz : ∀ j, raw17379 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17379step0 = (fun i j => raw17379 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17379step0 raw17379; decide +kernel
      have hl : raw17379step0Labels = raw17379Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17379 raw17379Labels permutation434 hz
    mixedMoment B raw17379step0 raw17379step0Labels = mixedMoment B raw17379step1 raw17379step1Labels := by
      have hz : ∀ j, raw17379step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17379step1 = (fun i j => raw17379step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17379step1 raw17379step0; decide +kernel
      have hl : raw17379step1Labels = raw17379step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17379step0 raw17379step0Labels permutation80 hz
    mixedMoment B raw17379step1 raw17379step1Labels = mixedMoment B raw17379step2 raw17379step2Labels := by
      have ha : raw17379step2 = (fun i j => raw17379step1 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17379step2 raw17379step1; decide +kernel
      have hl : raw17379step2Labels = raw17379step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17379step1 raw17379step1Labels permutation31 permutation6
    mixedMoment B raw17379step2 raw17379step2Labels = mixedMoment B raw17379step3 raw17379step3Labels := by
      have ha : raw17379step3 = -raw17379step2 := by apply Matrix.ext; change ∀ i j, raw17379step3 i j = -(raw17379step2 i j); unfold raw17379step3 raw17379step2; decide +kernel
      have hl : raw17379step3Labels = raw17379step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17379step3 raw17379step3Labels = mixedMoment B raw17379step4 raw17379step4Labels := by
      have ha : raw17379step4 = raw17379step3 := by apply Matrix.ext; unfold raw17379step4 raw17379step3; decide +kernel
      have hl : raw17379step3Labels = labelEmbedding9 ∘ raw17379step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17379step3 raw17379step3Labels raw17379step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5451 node5451Labels := by rfl

def raw17380 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17380Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17380step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17380step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17380step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw17380step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17380 raw17380Labels = mixedMoment B node5430 node5430Labels := by
  calc
    mixedMoment B raw17380 raw17380Labels = mixedMoment B raw17380step0 raw17380step0Labels := by
      have ha : raw17380step0 = (fun i j => raw17380 (permutation634 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17380step0 raw17380; decide +kernel
      have hl : raw17380step0Labels = raw17380Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17380 raw17380Labels permutation634 permutation4
    mixedMoment B raw17380step0 raw17380step0Labels = mixedMoment B raw17380step1 raw17380step1Labels := by
      have ha : raw17380step1 = raw17380step0 := by apply Matrix.ext; unfold raw17380step1 raw17380step0; decide +kernel
      have hl : raw17380step0Labels = labelEmbedding7 ∘ raw17380step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17380step0 raw17380step0Labels raw17380step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5430 node5430Labels := by rfl

def raw17381 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw17381Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw17381step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17381step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17381step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17381step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17381step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17381 raw17381Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw17381 raw17381Labels = mixedMoment B raw17381step0 raw17381step0Labels := by
      have hz : ∀ j, raw17381 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17381step0 = (fun i j => raw17381 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17381step0 raw17381; decide +kernel
      have hl : raw17381step0Labels = raw17381Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17381 raw17381Labels permutation434 hz
    mixedMoment B raw17381step0 raw17381step0Labels = mixedMoment B raw17381step1 raw17381step1Labels := by
      have ha : raw17381step1 = (fun i j => raw17381step0 (permutation122 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17381step1 raw17381step0; decide +kernel
      have hl : raw17381step1Labels = raw17381step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17381step0 raw17381step0Labels permutation122 permutation3
    mixedMoment B raw17381step1 raw17381step1Labels = mixedMoment B raw17381step2 raw17381step2Labels := by
      have ha : raw17381step2 = raw17381step1 := by apply Matrix.ext; unfold raw17381step2 raw17381step1; decide +kernel
      have hl : raw17381step1Labels = labelEmbedding6 ∘ raw17381step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17381step1 raw17381step1Labels raw17381step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw17382 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17382Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17382step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17382step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17382step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17382step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17382step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17382step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17382 raw17382Labels = mixedMoment B node5384 node5384Labels := by
  calc
    mixedMoment B raw17382 raw17382Labels = mixedMoment B raw17382step0 raw17382step0Labels := by
      have hz : ∀ j, raw17382 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17382step0 = (fun i j => raw17382 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17382step0 raw17382; decide +kernel
      have hl : raw17382step0Labels = raw17382Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17382 raw17382Labels permutation434 hz
    mixedMoment B raw17382step0 raw17382step0Labels = mixedMoment B raw17382step1 raw17382step1Labels := by
      have ha : raw17382step1 = (fun i j => raw17382step0 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17382step1 raw17382step0; decide +kernel
      have hl : raw17382step1Labels = raw17382step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17382step0 raw17382step0Labels permutation145 permutation4
    mixedMoment B raw17382step1 raw17382step1Labels = mixedMoment B raw17382step2 raw17382step2Labels := by
      have ha : raw17382step2 = raw17382step1 := by apply Matrix.ext; unfold raw17382step2 raw17382step1; decide +kernel
      have hl : raw17382step1Labels = labelEmbedding7 ∘ raw17382step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17382step1 raw17382step1Labels raw17382step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5384 node5384Labels := by rfl

def raw17383 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17383Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17383step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17383step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17383step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17383step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17383step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17383step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17383 raw17383Labels = mixedMoment B node5385 node5385Labels := by
  calc
    mixedMoment B raw17383 raw17383Labels = mixedMoment B raw17383step0 raw17383step0Labels := by
      have hz : ∀ j, raw17383 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17383step0 = (fun i j => raw17383 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17383step0 raw17383; decide +kernel
      have hl : raw17383step0Labels = raw17383Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17383 raw17383Labels permutation434 hz
    mixedMoment B raw17383step0 raw17383step0Labels = mixedMoment B raw17383step1 raw17383step1Labels := by
      have ha : raw17383step1 = (fun i j => raw17383step0 (permutation144 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17383step1 raw17383step0; decide +kernel
      have hl : raw17383step1Labels = raw17383step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17383step0 raw17383step0Labels permutation144 permutation4
    mixedMoment B raw17383step1 raw17383step1Labels = mixedMoment B raw17383step2 raw17383step2Labels := by
      have ha : raw17383step2 = raw17383step1 := by apply Matrix.ext; unfold raw17383step2 raw17383step1; decide +kernel
      have hl : raw17383step1Labels = labelEmbedding7 ∘ raw17383step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17383step1 raw17383step1Labels raw17383step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5385 node5385Labels := by rfl

def raw17384 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17384Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17384step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17384step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17384step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17384step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17384 raw17384Labels = mixedMoment B node5382 node5382Labels := by
  calc
    mixedMoment B raw17384 raw17384Labels = mixedMoment B raw17384step0 raw17384step0Labels := by
      have ha : raw17384step0 = (fun i j => raw17384 (permutation646 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17384step0 raw17384; decide +kernel
      have hl : raw17384step0Labels = raw17384Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17384 raw17384Labels permutation646 permutation4
    mixedMoment B raw17384step0 raw17384step0Labels = mixedMoment B raw17384step1 raw17384step1Labels := by
      have ha : raw17384step1 = raw17384step0 := by apply Matrix.ext; unfold raw17384step1 raw17384step0; decide +kernel
      have hl : raw17384step0Labels = labelEmbedding7 ∘ raw17384step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17384step0 raw17384step0Labels raw17384step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5382 node5382Labels := by rfl

def raw17385 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw17385Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw17385step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17385step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw17385step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17385step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw17385step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17385 raw17385Labels = mixedMoment B node5264 node5264Labels := by
  calc
    mixedMoment B raw17385 raw17385Labels = mixedMoment B raw17385step0 raw17385step0Labels := by
      have hz : ∀ j, raw17385 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17385step0 = (fun i j => raw17385 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17385step0 raw17385; decide +kernel
      have hl : raw17385step0Labels = raw17385Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17385 raw17385Labels permutation434 hz
    mixedMoment B raw17385step0 raw17385step0Labels = mixedMoment B raw17385step1 raw17385step1Labels := by
      have ha : raw17385step1 = (fun i j => raw17385step0 (permutation114 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17385step1 raw17385step0; decide +kernel
      have hl : raw17385step1Labels = raw17385step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17385step0 raw17385step0Labels permutation114 permutation3
    mixedMoment B raw17385step1 raw17385step1Labels = mixedMoment B raw17385step2 raw17385step2Labels := by
      have ha : raw17385step2 = raw17385step1 := by apply Matrix.ext; unfold raw17385step2 raw17385step1; decide +kernel
      have hl : raw17385step1Labels = labelEmbedding6 ∘ raw17385step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17385step1 raw17385step1Labels raw17385step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5264 node5264Labels := by rfl

def raw17386 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17386Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17386step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17386step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw17386step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17386step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17386step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17386step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17386step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17386 raw17386Labels = mixedMoment B node5446 node5446Labels := by
  calc
    mixedMoment B raw17386 raw17386Labels = mixedMoment B raw17386step0 raw17386step0Labels := by
      have hz : ∀ j, raw17386 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17386step0 = (fun i j => raw17386 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17386step0 raw17386; decide +kernel
      have hl : raw17386step0Labels = raw17386Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17386 raw17386Labels permutation434 hz
    mixedMoment B raw17386step0 raw17386step0Labels = mixedMoment B raw17386step1 raw17386step1Labels := by
      have ha : raw17386step1 = (fun i j => raw17386step0 (permutation81 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17386step1 raw17386step0; decide +kernel
      have hl : raw17386step1Labels = raw17386step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17386step0 raw17386step0Labels permutation81 permutation3
    mixedMoment B raw17386step1 raw17386step1Labels = mixedMoment B raw17386step2 raw17386step2Labels := by
      have ha : raw17386step2 = -raw17386step1 := by apply Matrix.ext; change ∀ i j, raw17386step2 i j = -(raw17386step1 i j); unfold raw17386step2 raw17386step1; decide +kernel
      have hl : raw17386step2Labels = raw17386step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17386step2 raw17386step2Labels = mixedMoment B raw17386step3 raw17386step3Labels := by
      have ha : raw17386step3 = raw17386step2 := by apply Matrix.ext; unfold raw17386step3 raw17386step2; decide +kernel
      have hl : raw17386step2Labels = labelEmbedding6 ∘ raw17386step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17386step2 raw17386step2Labels raw17386step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5446 node5446Labels := by rfl

def raw17387 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw17387Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17387step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17387step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw17387step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw17387step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17387 raw17387Labels = mixedMoment B node5263 node5263Labels := by
  calc
    mixedMoment B raw17387 raw17387Labels = mixedMoment B raw17387step0 raw17387step0Labels := by
      have ha : raw17387step0 = (fun i j => raw17387 (permutation538 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17387step0 raw17387; decide +kernel
      have hl : raw17387step0Labels = raw17387Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17387 raw17387Labels permutation538 permutation3
    mixedMoment B raw17387step0 raw17387step0Labels = mixedMoment B raw17387step1 raw17387step1Labels := by
      have ha : raw17387step1 = raw17387step0 := by apply Matrix.ext; unfold raw17387step1 raw17387step0; decide +kernel
      have hl : raw17387step0Labels = labelEmbedding6 ∘ raw17387step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17387step0 raw17387step0Labels raw17387step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5263 node5263Labels := by rfl

def raw17388 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17388Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17388step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17388step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw17388step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17388step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17388step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17388step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw17388step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17388 raw17388Labels = mixedMoment B node5409 node5409Labels := by
  calc
    mixedMoment B raw17388 raw17388Labels = mixedMoment B raw17388step0 raw17388step0Labels := by
      have hz : ∀ j, raw17388 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17388step0 = (fun i j => raw17388 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17388step0 raw17388; decide +kernel
      have hl : raw17388step0Labels = raw17388Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17388 raw17388Labels permutation434 hz
    mixedMoment B raw17388step0 raw17388step0Labels = mixedMoment B raw17388step1 raw17388step1Labels := by
      have ha : raw17388step1 = (fun i j => raw17388step0 (permutation34 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17388step1 raw17388step0; decide +kernel
      have hl : raw17388step1Labels = raw17388step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17388step0 raw17388step0Labels permutation34 permutation4
    mixedMoment B raw17388step1 raw17388step1Labels = mixedMoment B raw17388step2 raw17388step2Labels := by
      have ha : raw17388step2 = -raw17388step1 := by apply Matrix.ext; change ∀ i j, raw17388step2 i j = -(raw17388step1 i j); unfold raw17388step2 raw17388step1; decide +kernel
      have hl : raw17388step2Labels = raw17388step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17388step2 raw17388step2Labels = mixedMoment B raw17388step3 raw17388step3Labels := by
      have ha : raw17388step3 = raw17388step2 := by apply Matrix.ext; unfold raw17388step3 raw17388step2; decide +kernel
      have hl : raw17388step2Labels = labelEmbedding7 ∘ raw17388step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17388step2 raw17388step2Labels raw17388step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5409 node5409Labels := by rfl

def raw17389 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![0, -2, 2]]
def raw17389Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17389step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17389step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17389step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17389step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw17389step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17389step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17389 raw17389Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw17389 raw17389Labels = mixedMoment B raw17389step0 raw17389step0Labels := by
      have ha : raw17389step0 = (fun i j => raw17389 (permutation682 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17389step0 raw17389; decide +kernel
      have hl : raw17389step0Labels = raw17389Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17389 raw17389Labels permutation682 permutation6
    mixedMoment B raw17389step0 raw17389step0Labels = mixedMoment B raw17389step1 raw17389step1Labels := by
      have ha : raw17389step1 = -raw17389step0 := by apply Matrix.ext; change ∀ i j, raw17389step1 i j = -(raw17389step0 i j); unfold raw17389step1 raw17389step0; decide +kernel
      have hl : raw17389step1Labels = raw17389step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw17389step1 raw17389step1Labels = mixedMoment B raw17389step2 raw17389step2Labels := by
      have ha : raw17389step2 = raw17389step1 := by apply Matrix.ext; unfold raw17389step2 raw17389step1; decide +kernel
      have hl : raw17389step1Labels = labelEmbedding9 ∘ raw17389step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17389step1 raw17389step1Labels raw17389step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw17390 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw17390Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17390step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw17390step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17390step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17390step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17390step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw17390step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17390 raw17390Labels = mixedMoment B node5163 node5163Labels := by
  calc
    mixedMoment B raw17390 raw17390Labels = mixedMoment B raw17390step0 raw17390step0Labels := by
      have hz : ∀ j, raw17390 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17390step0 = (fun i j => raw17390 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17390step0 raw17390; decide +kernel
      have hl : raw17390step0Labels = raw17390Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17390 raw17390Labels permutation434 hz
    mixedMoment B raw17390step0 raw17390step0Labels = mixedMoment B raw17390step1 raw17390step1Labels := by
      have ha : raw17390step1 = (fun i j => raw17390step0 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17390step1 raw17390step0; decide +kernel
      have hl : raw17390step1Labels = raw17390step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17390step0 raw17390step0Labels permutation145 permutation4
    mixedMoment B raw17390step1 raw17390step1Labels = mixedMoment B raw17390step2 raw17390step2Labels := by
      have ha : raw17390step2 = raw17390step1 := by apply Matrix.ext; unfold raw17390step2 raw17390step1; decide +kernel
      have hl : raw17390step1Labels = labelEmbedding7 ∘ raw17390step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17390step1 raw17390step1Labels raw17390step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5163 node5163Labels := by rfl

def raw17391 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw17391Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17391step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![1, -1, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw17391step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17391step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17391step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17391step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw17391step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17391 raw17391Labels = mixedMoment B node5164 node5164Labels := by
  calc
    mixedMoment B raw17391 raw17391Labels = mixedMoment B raw17391step0 raw17391step0Labels := by
      have hz : ∀ j, raw17391 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17391step0 = (fun i j => raw17391 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17391step0 raw17391; decide +kernel
      have hl : raw17391step0Labels = raw17391Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17391 raw17391Labels permutation434 hz
    mixedMoment B raw17391step0 raw17391step0Labels = mixedMoment B raw17391step1 raw17391step1Labels := by
      have ha : raw17391step1 = (fun i j => raw17391step0 (permutation144 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17391step1 raw17391step0; decide +kernel
      have hl : raw17391step1Labels = raw17391step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17391step0 raw17391step0Labels permutation144 permutation4
    mixedMoment B raw17391step1 raw17391step1Labels = mixedMoment B raw17391step2 raw17391step2Labels := by
      have ha : raw17391step2 = raw17391step1 := by apply Matrix.ext; unfold raw17391step2 raw17391step1; decide +kernel
      have hl : raw17391step1Labels = labelEmbedding7 ∘ raw17391step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17391step1 raw17391step1Labels raw17391step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5164 node5164Labels := by rfl

def raw17392 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw17392Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17392step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![0, 0, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw17392step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17392step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![-2, 1, 1], ![1, -3, 2]]
def raw17392step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17392step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17392step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17392step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw17392step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17392 raw17392Labels = mixedMoment B node5304 node5304Labels := by
  calc
    mixedMoment B raw17392 raw17392Labels = mixedMoment B raw17392step0 raw17392step0Labels := by
      have hz : ∀ j, raw17392 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17392step0 = (fun i j => raw17392 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17392step0 raw17392; decide +kernel
      have hl : raw17392step0Labels = raw17392Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17392 raw17392Labels permutation434 hz
    mixedMoment B raw17392step0 raw17392step0Labels = mixedMoment B raw17392step1 raw17392step1Labels := by
      have hz : ∀ j, raw17392step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17392step1 = (fun i j => raw17392step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17392step1 raw17392step0; decide +kernel
      have hl : raw17392step1Labels = raw17392step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17392step0 raw17392step0Labels permutation80 hz
    mixedMoment B raw17392step1 raw17392step1Labels = mixedMoment B raw17392step2 raw17392step2Labels := by
      have ha : raw17392step2 = (fun i j => raw17392step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17392step2 raw17392step1; decide +kernel
      have hl : raw17392step2Labels = raw17392step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17392step1 raw17392step1Labels permutation31 permutation4
    mixedMoment B raw17392step2 raw17392step2Labels = mixedMoment B raw17392step3 raw17392step3Labels := by
      have ha : raw17392step3 = raw17392step2 := by apply Matrix.ext; unfold raw17392step3 raw17392step2; decide +kernel
      have hl : raw17392step2Labels = labelEmbedding7 ∘ raw17392step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17392step2 raw17392step2Labels raw17392step3Labels labelEmbedding7 hl
    _ = mixedMoment B node5304 node5304Labels := by rfl

def raw17393 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![1, -3, 2]]
def raw17393Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17393step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17393step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17393step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw17393step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17393 raw17393Labels = mixedMoment B node5160 node5160Labels := by
  calc
    mixedMoment B raw17393 raw17393Labels = mixedMoment B raw17393step0 raw17393step0Labels := by
      have ha : raw17393step0 = (fun i j => raw17393 (permutation646 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17393step0 raw17393; decide +kernel
      have hl : raw17393step0Labels = raw17393Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17393 raw17393Labels permutation646 permutation4
    mixedMoment B raw17393step0 raw17393step0Labels = mixedMoment B raw17393step1 raw17393step1Labels := by
      have ha : raw17393step1 = raw17393step0 := by apply Matrix.ext; unfold raw17393step1 raw17393step0; decide +kernel
      have hl : raw17393step0Labels = labelEmbedding7 ∘ raw17393step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17393step0 raw17393step0Labels raw17393step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5160 node5160Labels := by rfl

def raw17394 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-3, 2, 1], ![1, -3, 2]]
def raw17394Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17394step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![1, -1, 0], ![-3, 2, 1], ![1, -3, 2]]
def raw17394step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw17394step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw17394step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw17394step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw17394step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical17394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17394 raw17394Labels = mixedMoment B node5173 node5173Labels := by
  calc
    mixedMoment B raw17394 raw17394Labels = mixedMoment B raw17394step0 raw17394step0Labels := by
      have hz : ∀ j, raw17394 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17394step0 = (fun i j => raw17394 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17394step0 raw17394; decide +kernel
      have hl : raw17394step0Labels = raw17394Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17394 raw17394Labels permutation434 hz
    mixedMoment B raw17394step0 raw17394step0Labels = mixedMoment B raw17394step1 raw17394step1Labels := by
      have ha : raw17394step1 = (fun i j => raw17394step0 (permutation142 i) (permutation4 j)) := by apply Matrix.ext; unfold raw17394step1 raw17394step0; decide +kernel
      have hl : raw17394step1Labels = raw17394step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17394step0 raw17394step0Labels permutation142 permutation4
    mixedMoment B raw17394step1 raw17394step1Labels = mixedMoment B raw17394step2 raw17394step2Labels := by
      have ha : raw17394step2 = raw17394step1 := by apply Matrix.ext; unfold raw17394step2 raw17394step1; decide +kernel
      have hl : raw17394step1Labels = labelEmbedding7 ∘ raw17394step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw17394step1 raw17394step1Labels raw17394step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5173 node5173Labels := by rfl

def raw17395 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17395Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![-1, 2, -1], ![1, -1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17395step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17395step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 2, 0]]
def raw17395step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17395step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw17395step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17395 raw17395Labels = mixedMoment B node3877 node3877Labels := by
  calc
    mixedMoment B raw17395 raw17395Labels = mixedMoment B raw17395step0 raw17395step0Labels := by
      have hz : ∀ j, raw17395 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17395step0 = (fun i j => raw17395 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17395step0 raw17395; decide +kernel
      have hl : raw17395step0Labels = raw17395Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17395 raw17395Labels permutation434 hz
    mixedMoment B raw17395step0 raw17395step0Labels = mixedMoment B raw17395step1 raw17395step1Labels := by
      have ha : raw17395step1 = (fun i j => raw17395step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17395step1 raw17395step0; decide +kernel
      have hl : raw17395step1Labels = raw17395step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17395step0 raw17395step0Labels permutation151 permutation6
    mixedMoment B raw17395step1 raw17395step1Labels = mixedMoment B raw17395step2 raw17395step2Labels := by
      have ha : raw17395step2 = -raw17395step1 := by apply Matrix.ext; change ∀ i j, raw17395step2 i j = -(raw17395step1 i j); unfold raw17395step2 raw17395step1; decide +kernel
      have hl : raw17395step2Labels = raw17395step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3877 node3877Labels := by rfl

def raw17396 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17396Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17396step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17396step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17396step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![-2, 1, 1], ![0, -2, 2]]
def raw17396step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17396step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw17396step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17396step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17396step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17396 raw17396Labels = mixedMoment B node3889 node3889Labels := by
  calc
    mixedMoment B raw17396 raw17396Labels = mixedMoment B raw17396step0 raw17396step0Labels := by
      have hz : ∀ j, raw17396 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17396step0 = (fun i j => raw17396 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17396step0 raw17396; decide +kernel
      have hl : raw17396step0Labels = raw17396Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17396 raw17396Labels permutation434 hz
    mixedMoment B raw17396step0 raw17396step0Labels = mixedMoment B raw17396step1 raw17396step1Labels := by
      have hz : ∀ j, raw17396step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17396step1 = (fun i j => raw17396step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17396step1 raw17396step0; decide +kernel
      have hl : raw17396step1Labels = raw17396step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17396step0 raw17396step0Labels permutation80 hz
    mixedMoment B raw17396step1 raw17396step1Labels = mixedMoment B raw17396step2 raw17396step2Labels := by
      have ha : raw17396step2 = (fun i j => raw17396step1 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17396step2 raw17396step1; decide +kernel
      have hl : raw17396step2Labels = raw17396step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17396step1 raw17396step1Labels permutation31 permutation6
    mixedMoment B raw17396step2 raw17396step2Labels = mixedMoment B raw17396step3 raw17396step3Labels := by
      have ha : raw17396step3 = -raw17396step2 := by apply Matrix.ext; change ∀ i j, raw17396step3 i j = -(raw17396step2 i j); unfold raw17396step3 raw17396step2; decide +kernel
      have hl : raw17396step3Labels = raw17396step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3889 node3889Labels := by rfl

def raw17397 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17397Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17397step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw17397step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17397step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw17397step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17397 raw17397Labels = mixedMoment B node3872 node3872Labels := by
  calc
    mixedMoment B raw17397 raw17397Labels = mixedMoment B raw17397step0 raw17397step0Labels := by
      have ha : raw17397step0 = (fun i j => raw17397 (permutation682 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17397step0 raw17397; decide +kernel
      have hl : raw17397step0Labels = raw17397Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17397 raw17397Labels permutation682 permutation6
    mixedMoment B raw17397step0 raw17397step0Labels = mixedMoment B raw17397step1 raw17397step1Labels := by
      have ha : raw17397step1 = -raw17397step0 := by apply Matrix.ext; change ∀ i j, raw17397step1 i j = -(raw17397step0 i j); unfold raw17397step1 raw17397step0; decide +kernel
      have hl : raw17397step1Labels = raw17397step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3872 node3872Labels := by rfl

def raw17398 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw17398Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17398step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw17398step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17398step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -2, 0]]
def raw17398step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17398 raw17398Labels = mixedMoment B node2732 node2732Labels := by
  calc
    mixedMoment B raw17398 raw17398Labels = mixedMoment B raw17398step0 raw17398step0Labels := by
      have hz : ∀ j, raw17398 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17398step0 = (fun i j => raw17398 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17398step0 raw17398; decide +kernel
      have hl : raw17398step0Labels = raw17398Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17398 raw17398Labels permutation434 hz
    mixedMoment B raw17398step0 raw17398step0Labels = mixedMoment B raw17398step1 raw17398step1Labels := by
      have ha : raw17398step1 = (fun i j => raw17398step0 (permutation115 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17398step1 raw17398step0; decide +kernel
      have hl : raw17398step1Labels = raw17398step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17398step0 raw17398step0Labels permutation115 permutation3
    _ = mixedMoment B node2732 node2732Labels := by rfl

def raw17399 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17399Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![0, 1, -1], ![1, -1, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17399step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17399step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -2, 0]]
def raw17399step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17399 raw17399Labels = mixedMoment B node4003 node4003Labels := by
  calc
    mixedMoment B raw17399 raw17399Labels = mixedMoment B raw17399step0 raw17399step0Labels := by
      have hz : ∀ j, raw17399 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17399step0 = (fun i j => raw17399 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17399step0 raw17399; decide +kernel
      have hl : raw17399step0Labels = raw17399Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17399 raw17399Labels permutation434 hz
    mixedMoment B raw17399step0 raw17399step0Labels = mixedMoment B raw17399step1 raw17399step1Labels := by
      have ha : raw17399step1 = (fun i j => raw17399step0 (permutation125 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17399step1 raw17399step0; decide +kernel
      have hl : raw17399step1Labels = raw17399step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17399step0 raw17399step0Labels permutation125 permutation3
    _ = mixedMoment B node4003 node4003Labels := by rfl

def raw17400 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17400Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17400step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17400step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17400step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![-2, 1, 1], ![0, -2, 2]]
def raw17400step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17400step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17400step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17400step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17400step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17400 raw17400Labels = mixedMoment B node3888 node3888Labels := by
  calc
    mixedMoment B raw17400 raw17400Labels = mixedMoment B raw17400step0 raw17400step0Labels := by
      have hz : ∀ j, raw17400 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17400step0 = (fun i j => raw17400 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17400step0 raw17400; decide +kernel
      have hl : raw17400step0Labels = raw17400Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17400 raw17400Labels permutation434 hz
    mixedMoment B raw17400step0 raw17400step0Labels = mixedMoment B raw17400step1 raw17400step1Labels := by
      have hz : ∀ j, raw17400step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw17400step1 = (fun i j => raw17400step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw17400step1 raw17400step0; decide +kernel
      have hl : raw17400step1Labels = raw17400step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17400step0 raw17400step0Labels permutation80 hz
    mixedMoment B raw17400step1 raw17400step1Labels = mixedMoment B raw17400step2 raw17400step2Labels := by
      have ha : raw17400step2 = (fun i j => raw17400step1 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17400step2 raw17400step1; decide +kernel
      have hl : raw17400step2Labels = raw17400step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17400step1 raw17400step1Labels permutation31 permutation6
    mixedMoment B raw17400step2 raw17400step2Labels = mixedMoment B raw17400step3 raw17400step3Labels := by
      have ha : raw17400step3 = -raw17400step2 := by apply Matrix.ext; change ∀ i j, raw17400step3 i j = -(raw17400step2 i j); unfold raw17400step3 raw17400step2; decide +kernel
      have hl : raw17400step3Labels = raw17400step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3888 node3888Labels := by rfl

def raw17401 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17401Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17401step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 1, 1]]
def raw17401step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17401step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw17401step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17401 raw17401Labels = mixedMoment B node3871 node3871Labels := by
  calc
    mixedMoment B raw17401 raw17401Labels = mixedMoment B raw17401step0 raw17401step0Labels := by
      have ha : raw17401step0 = (fun i j => raw17401 (permutation682 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17401step0 raw17401; decide +kernel
      have hl : raw17401step0Labels = raw17401Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17401 raw17401Labels permutation682 permutation6
    mixedMoment B raw17401step0 raw17401step0Labels = mixedMoment B raw17401step1 raw17401step1Labels := by
      have ha : raw17401step1 = -raw17401step0 := by apply Matrix.ext; change ∀ i j, raw17401step1 i j = -(raw17401step0 i j); unfold raw17401step1 raw17401step0; decide +kernel
      have hl : raw17401step1Labels = raw17401step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3871 node3871Labels := by rfl

def raw17402 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw17402Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17402step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 0, -1], ![1, -1, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw17402step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17402step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw17402step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17402 raw17402Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw17402 raw17402Labels = mixedMoment B raw17402step0 raw17402step0Labels := by
      have hz : ∀ j, raw17402 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17402step0 = (fun i j => raw17402 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17402step0 raw17402; decide +kernel
      have hl : raw17402step0Labels = raw17402Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17402 raw17402Labels permutation434 hz
    mixedMoment B raw17402step0 raw17402step0Labels = mixedMoment B raw17402step1 raw17402step1Labels := by
      have ha : raw17402step1 = (fun i j => raw17402step0 (permutation122 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17402step1 raw17402step0; decide +kernel
      have hl : raw17402step1Labels = raw17402step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17402step0 raw17402step0Labels permutation122 permutation3
    _ = mixedMoment B node2773 node2773Labels := by rfl

def raw17403 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17403Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 2, -2], ![0, 1, -1], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17403step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17403step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw17403step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17403 raw17403Labels = mixedMoment B node3811 node3811Labels := by
  calc
    mixedMoment B raw17403 raw17403Labels = mixedMoment B raw17403step0 raw17403step0Labels := by
      have hz : ∀ j, raw17403 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17403step0 = (fun i j => raw17403 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17403step0 raw17403; decide +kernel
      have hl : raw17403step0Labels = raw17403Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17403 raw17403Labels permutation434 hz
    mixedMoment B raw17403step0 raw17403step0Labels = mixedMoment B raw17403step1 raw17403step1Labels := by
      have ha : raw17403step1 = (fun i j => raw17403step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw17403step1 raw17403step0; decide +kernel
      have hl : raw17403step1Labels = raw17403step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17403step0 raw17403step0Labels permutation32 permutation6
    _ = mixedMoment B node3811 node3811Labels := by rfl

def raw17404 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17404Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![-1, 2, -1], ![2, -2, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17404step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17404step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 2, -2], ![-1, -1, 2], ![-2, 1, 1]]
def raw17404step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17404step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, -1, -1]]
def raw17404step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17404 raw17404Labels = mixedMoment B node3868 node3868Labels := by
  calc
    mixedMoment B raw17404 raw17404Labels = mixedMoment B raw17404step0 raw17404step0Labels := by
      have hz : ∀ j, raw17404 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17404step0 = (fun i j => raw17404 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17404step0 raw17404; decide +kernel
      have hl : raw17404step0Labels = raw17404Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17404 raw17404Labels permutation434 hz
    mixedMoment B raw17404step0 raw17404step0Labels = mixedMoment B raw17404step1 raw17404step1Labels := by
      have ha : raw17404step1 = (fun i j => raw17404step0 (permutation84 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17404step1 raw17404step0; decide +kernel
      have hl : raw17404step1Labels = raw17404step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17404step0 raw17404step0Labels permutation84 permutation3
    mixedMoment B raw17404step1 raw17404step1Labels = mixedMoment B raw17404step2 raw17404step2Labels := by
      have ha : raw17404step2 = -raw17404step1 := by apply Matrix.ext; change ∀ i j, raw17404step2 i j = -(raw17404step1 i j); unfold raw17404step2 raw17404step1; decide +kernel
      have hl : raw17404step2Labels = raw17404step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3868 node3868Labels := by rfl

def raw17405 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-1, 1, 0], ![-2, 1, 1], ![0, -2, 2]]
def raw17405Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17405step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw17405step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17405step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw17405step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17405 raw17405Labels = mixedMoment B node3866 node3866Labels := by
  calc
    mixedMoment B raw17405 raw17405Labels = mixedMoment B raw17405step0 raw17405step0Labels := by
      have ha : raw17405step0 = (fun i j => raw17405 (permutation361 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17405step0 raw17405; decide +kernel
      have hl : raw17405step0Labels = raw17405Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17405 raw17405Labels permutation361 permutation3
    mixedMoment B raw17405step0 raw17405step0Labels = mixedMoment B raw17405step1 raw17405step1Labels := by
      have ha : raw17405step1 = -raw17405step0 := by apply Matrix.ext; change ∀ i j, raw17405step1 i j = -(raw17405step0 i j); unfold raw17405step1 raw17405step0; decide +kernel
      have hl : raw17405step1Labels = raw17405step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3866 node3866Labels := by rfl

def raw17406 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw17406Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17406step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-3, 2, 1], ![0, -2, 2]]
def raw17406step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17406step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![2, 0, -2]]
def raw17406step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17406 raw17406Labels = mixedMoment B node2729 node2729Labels := by
  calc
    mixedMoment B raw17406 raw17406Labels = mixedMoment B raw17406step0 raw17406step0Labels := by
      have hz : ∀ j, raw17406 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17406step0 = (fun i j => raw17406 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17406step0 raw17406; decide +kernel
      have hl : raw17406step0Labels = raw17406Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17406 raw17406Labels permutation434 hz
    mixedMoment B raw17406step0 raw17406step0Labels = mixedMoment B raw17406step1 raw17406step1Labels := by
      have ha : raw17406step1 = (fun i j => raw17406step0 (permutation114 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17406step1 raw17406step0; decide +kernel
      have hl : raw17406step1Labels = raw17406step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17406step0 raw17406step0Labels permutation114 permutation3
    _ = mixedMoment B node2729 node2729Labels := by rfl

def raw17407 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17407Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17407step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 1, -1], ![2, -2, 0], ![-2, 1, 1], ![-1, -1, 2]]
def raw17407step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw17407step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 1, 1]]
def raw17407step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw17407step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw17407step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical17407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw17407 raw17407Labels = mixedMoment B node3881 node3881Labels := by
  calc
    mixedMoment B raw17407 raw17407Labels = mixedMoment B raw17407step0 raw17407step0Labels := by
      have hz : ∀ j, raw17407 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw17407step0 = (fun i j => raw17407 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw17407step0 raw17407; decide +kernel
      have hl : raw17407step0Labels = raw17407Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw17407 raw17407Labels permutation434 hz
    mixedMoment B raw17407step0 raw17407step0Labels = mixedMoment B raw17407step1 raw17407step1Labels := by
      have ha : raw17407step1 = (fun i j => raw17407step0 (permutation81 i) (permutation3 j)) := by apply Matrix.ext; unfold raw17407step1 raw17407step0; decide +kernel
      have hl : raw17407step1Labels = raw17407step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw17407step0 raw17407step0Labels permutation81 permutation3
    mixedMoment B raw17407step1 raw17407step1Labels = mixedMoment B raw17407step2 raw17407step2Labels := by
      have ha : raw17407step2 = -raw17407step1 := by apply Matrix.ext; change ∀ i j, raw17407step2 i j = -(raw17407step1 i j); unfold raw17407step2 raw17407step1; decide +kernel
      have hl : raw17407step2Labels = raw17407step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3881 node3881Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
