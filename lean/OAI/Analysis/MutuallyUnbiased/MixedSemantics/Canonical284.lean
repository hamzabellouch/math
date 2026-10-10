import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw36352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![3, -3, 0]]
def raw36352Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36352step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw36352step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36352step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw36352step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36352step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw36352step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36352 raw36352Labels = mixedMoment B node4717 node4717Labels := by
  calc
    mixedMoment B raw36352 raw36352Labels = mixedMoment B raw36352step0 raw36352step0Labels := by
      have ha : raw36352step0 = (fun i j => raw36352 (permutation663 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36352step0 raw36352; decide +kernel
      have hl : raw36352step0Labels = raw36352Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36352 raw36352Labels permutation663 permutation3
    mixedMoment B raw36352step0 raw36352step0Labels = mixedMoment B raw36352step1 raw36352step1Labels := by
      have ha : raw36352step1 = -raw36352step0 := by apply Matrix.ext; change ∀ i j, raw36352step1 i j = -(raw36352step0 i j); unfold raw36352step1 raw36352step0; decide +kernel
      have hl : raw36352step1Labels = raw36352step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36352step1 raw36352step1Labels = mixedMoment B raw36352step2 raw36352step2Labels := by
      have ha : raw36352step2 = raw36352step1 := by apply Matrix.ext; unfold raw36352step2 raw36352step1; decide +kernel
      have hl : raw36352step1Labels = labelEmbedding6 ∘ raw36352step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36352step1 raw36352step1Labels raw36352step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4717 node4717Labels := by rfl

def raw36353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![0, 0, 0], ![1, 0, -1], ![3, -3, 0]]
def raw36353Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36353step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw36353step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36353step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36353step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36353step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36353step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36353step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36353step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36353 raw36353Labels = mixedMoment B node4811 node4811Labels := by
  calc
    mixedMoment B raw36353 raw36353Labels = mixedMoment B raw36353step0 raw36353step0Labels := by
      have hz : ∀ j, raw36353 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw36353step0 = (fun i j => raw36353 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw36353step0 raw36353; decide +kernel
      have hl : raw36353step0Labels = raw36353Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36353 raw36353Labels permutation434 hz
    mixedMoment B raw36353step0 raw36353step0Labels = mixedMoment B raw36353step1 raw36353step1Labels := by
      have ha : raw36353step1 = (fun i j => raw36353step0 (permutation150 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36353step1 raw36353step0; decide +kernel
      have hl : raw36353step1Labels = raw36353step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36353step0 raw36353step0Labels permutation150 permutation3
    mixedMoment B raw36353step1 raw36353step1Labels = mixedMoment B raw36353step2 raw36353step2Labels := by
      have ha : raw36353step2 = -raw36353step1 := by apply Matrix.ext; change ∀ i j, raw36353step2 i j = -(raw36353step1 i j); unfold raw36353step2 raw36353step1; decide +kernel
      have hl : raw36353step2Labels = raw36353step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36353step2 raw36353step2Labels = mixedMoment B raw36353step3 raw36353step3Labels := by
      have ha : raw36353step3 = raw36353step2 := by apply Matrix.ext; unfold raw36353step3 raw36353step2; decide +kernel
      have hl : raw36353step2Labels = labelEmbedding6 ∘ raw36353step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36353step2 raw36353step2Labels raw36353step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4811 node4811Labels := by rfl

def raw36354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![0, 1, -1], ![3, -3, 0]]
def raw36354Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36354step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36354step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36354step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36354step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36354step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36354step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36354 raw36354Labels = mixedMoment B node4732 node4732Labels := by
  calc
    mixedMoment B raw36354 raw36354Labels = mixedMoment B raw36354step0 raw36354step0Labels := by
      have ha : raw36354step0 = (fun i j => raw36354 (permutation657 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36354step0 raw36354; decide +kernel
      have hl : raw36354step0Labels = raw36354Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36354 raw36354Labels permutation657 permutation3
    mixedMoment B raw36354step0 raw36354step0Labels = mixedMoment B raw36354step1 raw36354step1Labels := by
      have ha : raw36354step1 = -raw36354step0 := by apply Matrix.ext; change ∀ i j, raw36354step1 i j = -(raw36354step0 i j); unfold raw36354step1 raw36354step0; decide +kernel
      have hl : raw36354step1Labels = raw36354step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36354step1 raw36354step1Labels = mixedMoment B raw36354step2 raw36354step2Labels := by
      have ha : raw36354step2 = raw36354step1 := by apply Matrix.ext; unfold raw36354step2 raw36354step1; decide +kernel
      have hl : raw36354step1Labels = labelEmbedding6 ∘ raw36354step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36354step1 raw36354step1Labels raw36354step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4732 node4732Labels := by rfl

def raw36355 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![0, 2, -2], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw36355Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36355step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36355step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36355step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36355step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36355 raw36355Labels = mixedMoment B node5378 node5378Labels := by
  calc
    mixedMoment B raw36355 raw36355Labels = mixedMoment B raw36355step0 raw36355step0Labels := by
      have ha : raw36355step0 = (fun i j => raw36355 (permutation267 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36355step0 raw36355; decide +kernel
      have hl : raw36355step0Labels = raw36355Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36355 raw36355Labels permutation267 permutation6
    mixedMoment B raw36355step0 raw36355step0Labels = mixedMoment B raw36355step1 raw36355step1Labels := by
      have ha : raw36355step1 = raw36355step0 := by apply Matrix.ext; unfold raw36355step1 raw36355step0; decide +kernel
      have hl : raw36355step0Labels = labelEmbedding9 ∘ raw36355step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36355step0 raw36355step0Labels raw36355step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5378 node5378Labels := by rfl

def raw36356 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw36356Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36356step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw36356step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36356step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw36356step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36356 raw36356Labels = mixedMoment B node5360 node5360Labels := by
  calc
    mixedMoment B raw36356 raw36356Labels = mixedMoment B raw36356step0 raw36356step0Labels := by
      have ha : raw36356step0 = (fun i j => raw36356 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36356step0 raw36356; decide +kernel
      have hl : raw36356step0Labels = raw36356Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36356 raw36356Labels permutation152 permutation7
    mixedMoment B raw36356step0 raw36356step0Labels = mixedMoment B raw36356step1 raw36356step1Labels := by
      have ha : raw36356step1 = raw36356step0 := by apply Matrix.ext; unfold raw36356step1 raw36356step0; decide +kernel
      have hl : raw36356step0Labels = labelEmbedding10 ∘ raw36356step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36356step0 raw36356step0Labels raw36356step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5360 node5360Labels := by rfl

def raw36357 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw36357Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36357step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36357step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36357step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36357step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36357 raw36357Labels = mixedMoment B node5354 node5354Labels := by
  calc
    mixedMoment B raw36357 raw36357Labels = mixedMoment B raw36357step0 raw36357step0Labels := by
      have ha : raw36357step0 = (fun i j => raw36357 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36357step0 raw36357; decide +kernel
      have hl : raw36357step0Labels = raw36357Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36357 raw36357Labels permutation152 permutation7
    mixedMoment B raw36357step0 raw36357step0Labels = mixedMoment B raw36357step1 raw36357step1Labels := by
      have ha : raw36357step1 = raw36357step0 := by apply Matrix.ext; unfold raw36357step1 raw36357step0; decide +kernel
      have hl : raw36357step0Labels = labelEmbedding10 ∘ raw36357step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36357step0 raw36357step0Labels raw36357step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5354 node5354Labels := by rfl

def raw36358 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-1, 1, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw36358Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36358step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw36358step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36358step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw36358step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36358 raw36358Labels = mixedMoment B node5353 node5353Labels := by
  calc
    mixedMoment B raw36358 raw36358Labels = mixedMoment B raw36358step0 raw36358step0Labels := by
      have ha : raw36358step0 = (fun i j => raw36358 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36358step0 raw36358; decide +kernel
      have hl : raw36358step0Labels = raw36358Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36358 raw36358Labels permutation152 permutation7
    mixedMoment B raw36358step0 raw36358step0Labels = mixedMoment B raw36358step1 raw36358step1Labels := by
      have ha : raw36358step1 = raw36358step0 := by apply Matrix.ext; unfold raw36358step1 raw36358step0; decide +kernel
      have hl : raw36358step0Labels = labelEmbedding10 ∘ raw36358step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36358step0 raw36358step0Labels raw36358step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5353 node5353Labels := by rfl

def raw36359 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw36359Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36359step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36359step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36359step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36359step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36359 raw36359Labels = mixedMoment B node5352 node5352Labels := by
  calc
    mixedMoment B raw36359 raw36359Labels = mixedMoment B raw36359step0 raw36359step0Labels := by
      have ha : raw36359step0 = (fun i j => raw36359 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36359step0 raw36359; decide +kernel
      have hl : raw36359step0Labels = raw36359Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36359 raw36359Labels permutation152 permutation7
    mixedMoment B raw36359step0 raw36359step0Labels = mixedMoment B raw36359step1 raw36359step1Labels := by
      have ha : raw36359step1 = raw36359step0 := by apply Matrix.ext; unfold raw36359step1 raw36359step0; decide +kernel
      have hl : raw36359step0Labels = labelEmbedding10 ∘ raw36359step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36359step0 raw36359step0Labels raw36359step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5352 node5352Labels := by rfl

def raw36360 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw36360Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36360step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw36360step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36360step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw36360step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36360 raw36360Labels = mixedMoment B node5360 node5360Labels := by
  calc
    mixedMoment B raw36360 raw36360Labels = mixedMoment B raw36360step0 raw36360step0Labels := by
      have ha : raw36360step0 = (fun i j => raw36360 (permutation265 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36360step0 raw36360; decide +kernel
      have hl : raw36360step0Labels = raw36360Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36360 raw36360Labels permutation265 permutation7
    mixedMoment B raw36360step0 raw36360step0Labels = mixedMoment B raw36360step1 raw36360step1Labels := by
      have ha : raw36360step1 = raw36360step0 := by apply Matrix.ext; unfold raw36360step1 raw36360step0; decide +kernel
      have hl : raw36360step0Labels = labelEmbedding10 ∘ raw36360step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36360step0 raw36360step0Labels raw36360step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5360 node5360Labels := by rfl

def raw36361 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-1, 1, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw36361Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36361step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw36361step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36361step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw36361step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36361 raw36361Labels = mixedMoment B node5353 node5353Labels := by
  calc
    mixedMoment B raw36361 raw36361Labels = mixedMoment B raw36361step0 raw36361step0Labels := by
      have ha : raw36361step0 = (fun i j => raw36361 (permutation265 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36361step0 raw36361; decide +kernel
      have hl : raw36361step0Labels = raw36361Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36361 raw36361Labels permutation265 permutation7
    mixedMoment B raw36361step0 raw36361step0Labels = mixedMoment B raw36361step1 raw36361step1Labels := by
      have ha : raw36361step1 = raw36361step0 := by apply Matrix.ext; unfold raw36361step1 raw36361step0; decide +kernel
      have hl : raw36361step0Labels = labelEmbedding10 ∘ raw36361step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36361step0 raw36361step0Labels raw36361step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5353 node5353Labels := by rfl

def raw36362 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![2, 0, -2], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw36362Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36362step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36362step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw36362step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36362step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36362 raw36362Labels = mixedMoment B node5352 node5352Labels := by
  calc
    mixedMoment B raw36362 raw36362Labels = mixedMoment B raw36362step0 raw36362step0Labels := by
      have ha : raw36362step0 = (fun i j => raw36362 (permutation265 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36362step0 raw36362; decide +kernel
      have hl : raw36362step0Labels = raw36362Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36362 raw36362Labels permutation265 permutation7
    mixedMoment B raw36362step0 raw36362step0Labels = mixedMoment B raw36362step1 raw36362step1Labels := by
      have ha : raw36362step1 = raw36362step0 := by apply Matrix.ext; unfold raw36362step1 raw36362step0; decide +kernel
      have hl : raw36362step0Labels = labelEmbedding10 ∘ raw36362step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36362step0 raw36362step0Labels raw36362step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5352 node5352Labels := by rfl

def raw36363 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw36363Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw36363step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36363step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36363step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36363step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw36363step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36363 raw36363Labels = mixedMoment B node5367 node5367Labels := by
  calc
    mixedMoment B raw36363 raw36363Labels = mixedMoment B raw36363step0 raw36363step0Labels := by
      have hz : ∀ j, raw36363 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36363step0 = (fun i j => raw36363 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36363step0 raw36363; decide +kernel
      have hl : raw36363step0Labels = raw36363Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36363 raw36363Labels permutation346 hz
    mixedMoment B raw36363step0 raw36363step0Labels = mixedMoment B raw36363step1 raw36363step1Labels := by
      have ha : raw36363step1 = (fun i j => raw36363step0 (permutation58 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36363step1 raw36363step0; decide +kernel
      have hl : raw36363step1Labels = raw36363step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36363step0 raw36363step0Labels permutation58 permutation6
    mixedMoment B raw36363step1 raw36363step1Labels = mixedMoment B raw36363step2 raw36363step2Labels := by
      have ha : raw36363step2 = raw36363step1 := by apply Matrix.ext; unfold raw36363step2 raw36363step1; decide +kernel
      have hl : raw36363step1Labels = labelEmbedding9 ∘ raw36363step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36363step1 raw36363step1Labels raw36363step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5367 node5367Labels := by rfl

def raw36364 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw36364Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw36364step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36364step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36364step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36364step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36364step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36364step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36364step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36364 raw36364Labels = mixedMoment B node5404 node5404Labels := by
  calc
    mixedMoment B raw36364 raw36364Labels = mixedMoment B raw36364step0 raw36364step0Labels := by
      have hz : ∀ j, raw36364 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36364step0 = (fun i j => raw36364 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36364step0 raw36364; decide +kernel
      have hl : raw36364step0Labels = raw36364Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36364 raw36364Labels permutation346 hz
    mixedMoment B raw36364step0 raw36364step0Labels = mixedMoment B raw36364step1 raw36364step1Labels := by
      have ha : raw36364step1 = (fun i j => raw36364step0 (permutation144 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36364step1 raw36364step0; decide +kernel
      have hl : raw36364step1Labels = raw36364step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36364step0 raw36364step0Labels permutation144 permutation6
    mixedMoment B raw36364step1 raw36364step1Labels = mixedMoment B raw36364step2 raw36364step2Labels := by
      have ha : raw36364step2 = -raw36364step1 := by apply Matrix.ext; change ∀ i j, raw36364step2 i j = -(raw36364step1 i j); unfold raw36364step2 raw36364step1; decide +kernel
      have hl : raw36364step2Labels = raw36364step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36364step2 raw36364step2Labels = mixedMoment B raw36364step3 raw36364step3Labels := by
      have ha : raw36364step3 = raw36364step2 := by apply Matrix.ext; unfold raw36364step3 raw36364step2; decide +kernel
      have hl : raw36364step2Labels = labelEmbedding9 ∘ raw36364step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36364step2 raw36364step2Labels raw36364step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5404 node5404Labels := by rfl

def raw36365 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw36365Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw36365step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36365step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36365step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36365step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36365step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36365 raw36365Labels = mixedMoment B node5465 node5465Labels := by
  calc
    mixedMoment B raw36365 raw36365Labels = mixedMoment B raw36365step0 raw36365step0Labels := by
      have hz : ∀ j, raw36365 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw36365step0 = (fun i j => raw36365 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw36365step0 raw36365; decide +kernel
      have hl : raw36365step0Labels = raw36365Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36365 raw36365Labels permutation346 hz
    mixedMoment B raw36365step0 raw36365step0Labels = mixedMoment B raw36365step1 raw36365step1Labels := by
      have ha : raw36365step1 = (fun i j => raw36365step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36365step1 raw36365step0; decide +kernel
      have hl : raw36365step1Labels = raw36365step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36365step0 raw36365step0Labels permutation34 permutation6
    mixedMoment B raw36365step1 raw36365step1Labels = mixedMoment B raw36365step2 raw36365step2Labels := by
      have ha : raw36365step2 = raw36365step1 := by apply Matrix.ext; unfold raw36365step2 raw36365step1; decide +kernel
      have hl : raw36365step1Labels = labelEmbedding9 ∘ raw36365step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36365step1 raw36365step1Labels raw36365step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5465 node5465Labels := by rfl

def raw36366 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw36366Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36366step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw36366step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36366step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw36366step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36366 raw36366Labels = mixedMoment B node5344 node5344Labels := by
  calc
    mixedMoment B raw36366 raw36366Labels = mixedMoment B raw36366step0 raw36366step0Labels := by
      have ha : raw36366step0 = (fun i j => raw36366 (permutation664 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36366step0 raw36366; decide +kernel
      have hl : raw36366step0Labels = raw36366Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36366 raw36366Labels permutation664 permutation4
    mixedMoment B raw36366step0 raw36366step0Labels = mixedMoment B raw36366step1 raw36366step1Labels := by
      have ha : raw36366step1 = raw36366step0 := by apply Matrix.ext; unfold raw36366step1 raw36366step0; decide +kernel
      have hl : raw36366step0Labels = labelEmbedding7 ∘ raw36366step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36366step0 raw36366step0Labels raw36366step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5344 node5344Labels := by rfl

def raw36367 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw36367Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36367step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw36367step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36367step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw36367step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36367 raw36367Labels = mixedMoment B node5344 node5344Labels := by
  calc
    mixedMoment B raw36367 raw36367Labels = mixedMoment B raw36367step0 raw36367step0Labels := by
      have ha : raw36367step0 = (fun i j => raw36367 (permutation663 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36367step0 raw36367; decide +kernel
      have hl : raw36367step0Labels = raw36367Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36367 raw36367Labels permutation663 permutation4
    mixedMoment B raw36367step0 raw36367step0Labels = mixedMoment B raw36367step1 raw36367step1Labels := by
      have ha : raw36367step1 = raw36367step0 := by apply Matrix.ext; unfold raw36367step1 raw36367step0; decide +kernel
      have hl : raw36367step0Labels = labelEmbedding7 ∘ raw36367step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36367step0 raw36367step0Labels raw36367step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5344 node5344Labels := by rfl

def raw36368 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-2, 2, 0], ![1, -2, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw36368Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36368step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw36368step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36368step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw36368step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36368 raw36368Labels = mixedMoment B node5347 node5347Labels := by
  calc
    mixedMoment B raw36368 raw36368Labels = mixedMoment B raw36368step0 raw36368step0Labels := by
      have ha : raw36368step0 = (fun i j => raw36368 (permutation659 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36368step0 raw36368; decide +kernel
      have hl : raw36368step0Labels = raw36368Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36368 raw36368Labels permutation659 permutation4
    mixedMoment B raw36368step0 raw36368step0Labels = mixedMoment B raw36368step1 raw36368step1Labels := by
      have ha : raw36368step1 = raw36368step0 := by apply Matrix.ext; unfold raw36368step1 raw36368step0; decide +kernel
      have hl : raw36368step0Labels = labelEmbedding7 ∘ raw36368step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36368step0 raw36368step0Labels raw36368step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5347 node5347Labels := by rfl

def raw36369 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-1, 1, 0], ![1, -2, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw36369Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36369step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36369step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36369step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36369step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36369 raw36369Labels = mixedMoment B node5362 node5362Labels := by
  calc
    mixedMoment B raw36369 raw36369Labels = mixedMoment B raw36369step0 raw36369step0Labels := by
      have ha : raw36369step0 = (fun i j => raw36369 (permutation663 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36369step0 raw36369; decide +kernel
      have hl : raw36369step0Labels = raw36369Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36369 raw36369Labels permutation663 permutation4
    mixedMoment B raw36369step0 raw36369step0Labels = mixedMoment B raw36369step1 raw36369step1Labels := by
      have ha : raw36369step1 = raw36369step0 := by apply Matrix.ext; unfold raw36369step1 raw36369step0; decide +kernel
      have hl : raw36369step0Labels = labelEmbedding7 ∘ raw36369step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36369step0 raw36369step0Labels raw36369step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5362 node5362Labels := by rfl

def raw36370 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-1, 1, 0], ![1, -2, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw36370Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36370step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36370step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36370step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw36370step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36370 raw36370Labels = mixedMoment B node5459 node5459Labels := by
  calc
    mixedMoment B raw36370 raw36370Labels = mixedMoment B raw36370step0 raw36370step0Labels := by
      have ha : raw36370step0 = (fun i j => raw36370 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36370step0 raw36370; decide +kernel
      have hl : raw36370step0Labels = raw36370Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36370 raw36370Labels permutation154 permutation6
    mixedMoment B raw36370step0 raw36370step0Labels = mixedMoment B raw36370step1 raw36370step1Labels := by
      have ha : raw36370step1 = raw36370step0 := by apply Matrix.ext; unfold raw36370step1 raw36370step0; decide +kernel
      have hl : raw36370step0Labels = labelEmbedding9 ∘ raw36370step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36370step0 raw36370step0Labels raw36370step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5459 node5459Labels := by rfl

def raw36371 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw36371Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36371step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36371step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36371step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36371step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36371 raw36371Labels = mixedMoment B node5345 node5345Labels := by
  calc
    mixedMoment B raw36371 raw36371Labels = mixedMoment B raw36371step0 raw36371step0Labels := by
      have ha : raw36371step0 = (fun i j => raw36371 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36371step0 raw36371; decide +kernel
      have hl : raw36371step0Labels = raw36371Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36371 raw36371Labels permutation152 permutation6
    mixedMoment B raw36371step0 raw36371step0Labels = mixedMoment B raw36371step1 raw36371step1Labels := by
      have ha : raw36371step1 = raw36371step0 := by apply Matrix.ext; unfold raw36371step1 raw36371step0; decide +kernel
      have hl : raw36371step0Labels = labelEmbedding9 ∘ raw36371step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36371step0 raw36371step0Labels raw36371step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5345 node5345Labels := by rfl

def raw36372 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw36372Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36372step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36372step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36372step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw36372step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36372 raw36372Labels = mixedMoment B node5345 node5345Labels := by
  calc
    mixedMoment B raw36372 raw36372Labels = mixedMoment B raw36372step0 raw36372step0Labels := by
      have ha : raw36372step0 = (fun i j => raw36372 (permutation265 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36372step0 raw36372; decide +kernel
      have hl : raw36372step0Labels = raw36372Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36372 raw36372Labels permutation265 permutation6
    mixedMoment B raw36372step0 raw36372step0Labels = mixedMoment B raw36372step1 raw36372step1Labels := by
      have ha : raw36372step1 = raw36372step0 := by apply Matrix.ext; unfold raw36372step1 raw36372step0; decide +kernel
      have hl : raw36372step0Labels = labelEmbedding9 ∘ raw36372step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36372step0 raw36372step0Labels raw36372step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5345 node5345Labels := by rfl

def raw36373 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-2, 2, 0], ![0, -1, 1], ![0, -1, 1], ![0, -2, 2]]
def raw36373Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36373step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, 0, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw36373step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36373step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw36373step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36373step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw36373step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36373 raw36373Labels = mixedMoment B node5391 node5391Labels := by
  calc
    mixedMoment B raw36373 raw36373Labels = mixedMoment B raw36373step0 raw36373step0Labels := by
      have ha : raw36373step0 = (fun i j => raw36373 (permutation663 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36373step0 raw36373; decide +kernel
      have hl : raw36373step0Labels = raw36373Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36373 raw36373Labels permutation663 permutation6
    mixedMoment B raw36373step0 raw36373step0Labels = mixedMoment B raw36373step1 raw36373step1Labels := by
      have ha : raw36373step1 = -raw36373step0 := by apply Matrix.ext; change ∀ i j, raw36373step1 i j = -(raw36373step0 i j); unfold raw36373step1 raw36373step0; decide +kernel
      have hl : raw36373step1Labels = raw36373step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36373step1 raw36373step1Labels = mixedMoment B raw36373step2 raw36373step2Labels := by
      have ha : raw36373step2 = raw36373step1 := by apply Matrix.ext; unfold raw36373step2 raw36373step1; decide +kernel
      have hl : raw36373step1Labels = labelEmbedding9 ∘ raw36373step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36373step1 raw36373step1Labels raw36373step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5391 node5391Labels := by rfl

def raw36374 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -2, 2]]
def raw36374Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36374step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw36374step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36374step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36374step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36374step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36374step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36374 raw36374Labels = mixedMoment B node5393 node5393Labels := by
  calc
    mixedMoment B raw36374 raw36374Labels = mixedMoment B raw36374step0 raw36374step0Labels := by
      have ha : raw36374step0 = (fun i j => raw36374 (permutation687 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36374step0 raw36374; decide +kernel
      have hl : raw36374step0Labels = raw36374Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36374 raw36374Labels permutation687 permutation6
    mixedMoment B raw36374step0 raw36374step0Labels = mixedMoment B raw36374step1 raw36374step1Labels := by
      have ha : raw36374step1 = -raw36374step0 := by apply Matrix.ext; change ∀ i j, raw36374step1 i j = -(raw36374step0 i j); unfold raw36374step1 raw36374step0; decide +kernel
      have hl : raw36374step1Labels = raw36374step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36374step1 raw36374step1Labels = mixedMoment B raw36374step2 raw36374step2Labels := by
      have ha : raw36374step2 = raw36374step1 := by apply Matrix.ext; unfold raw36374step2 raw36374step1; decide +kernel
      have hl : raw36374step1Labels = labelEmbedding9 ∘ raw36374step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36374step1 raw36374step1Labels raw36374step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5393 node5393Labels := by rfl

def raw36375 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-1, 1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw36375Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36375step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36375step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw36375step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36375step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36375 raw36375Labels = mixedMoment B node5460 node5460Labels := by
  calc
    mixedMoment B raw36375 raw36375Labels = mixedMoment B raw36375step0 raw36375step0Labels := by
      have ha : raw36375step0 = (fun i j => raw36375 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw36375step0 raw36375; decide +kernel
      have hl : raw36375step0Labels = raw36375Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36375 raw36375Labels permutation152 permutation6
    mixedMoment B raw36375step0 raw36375step0Labels = mixedMoment B raw36375step1 raw36375step1Labels := by
      have ha : raw36375step1 = raw36375step0 := by apply Matrix.ext; unfold raw36375step1 raw36375step0; decide +kernel
      have hl : raw36375step0Labels = labelEmbedding9 ∘ raw36375step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36375step0 raw36375step0Labels raw36375step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5460 node5460Labels := by rfl

def raw36376 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 2, -2], ![1, 1, -2], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw36376Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36376step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw36376step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36376step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw36376step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36376 raw36376Labels = mixedMoment B node5056 node5056Labels := by
  calc
    mixedMoment B raw36376 raw36376Labels = mixedMoment B raw36376step0 raw36376step0Labels := by
      have ha : raw36376step0 = (fun i j => raw36376 (permutation664 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36376step0 raw36376; decide +kernel
      have hl : raw36376step0Labels = raw36376Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36376 raw36376Labels permutation664 permutation4
    mixedMoment B raw36376step0 raw36376step0Labels = mixedMoment B raw36376step1 raw36376step1Labels := by
      have ha : raw36376step1 = raw36376step0 := by apply Matrix.ext; unfold raw36376step1 raw36376step0; decide +kernel
      have hl : raw36376step0Labels = labelEmbedding7 ∘ raw36376step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36376step0 raw36376step0Labels raw36376step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5056 node5056Labels := by rfl

def raw36377 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![0, 2, -2], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw36377Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36377step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw36377step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36377step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw36377step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36377 raw36377Labels = mixedMoment B node5056 node5056Labels := by
  calc
    mixedMoment B raw36377 raw36377Labels = mixedMoment B raw36377step0 raw36377step0Labels := by
      have ha : raw36377step0 = (fun i j => raw36377 (permutation663 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36377step0 raw36377; decide +kernel
      have hl : raw36377step0Labels = raw36377Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36377 raw36377Labels permutation663 permutation4
    mixedMoment B raw36377step0 raw36377step0Labels = mixedMoment B raw36377step1 raw36377step1Labels := by
      have ha : raw36377step1 = raw36377step0 := by apply Matrix.ext; unfold raw36377step1 raw36377step0; decide +kernel
      have hl : raw36377step0Labels = labelEmbedding7 ∘ raw36377step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36377step0 raw36377step0Labels raw36377step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5056 node5056Labels := by rfl

def raw36378 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-2, 2, 0], ![0, -1, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw36378Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36378step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw36378step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36378step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 1, -2], ![1, 1, -2], ![2, -2, 0]]
def raw36378step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36378 raw36378Labels = mixedMoment B node5061 node5061Labels := by
  calc
    mixedMoment B raw36378 raw36378Labels = mixedMoment B raw36378step0 raw36378step0Labels := by
      have ha : raw36378step0 = (fun i j => raw36378 (permutation659 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36378step0 raw36378; decide +kernel
      have hl : raw36378step0Labels = raw36378Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36378 raw36378Labels permutation659 permutation4
    mixedMoment B raw36378step0 raw36378step0Labels = mixedMoment B raw36378step1 raw36378step1Labels := by
      have ha : raw36378step1 = raw36378step0 := by apply Matrix.ext; unfold raw36378step1 raw36378step0; decide +kernel
      have hl : raw36378step0Labels = labelEmbedding7 ∘ raw36378step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36378step0 raw36378step0Labels raw36378step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5061 node5061Labels := by rfl

def raw36379 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -3, 2]]
def raw36379Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36379step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36379step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36379step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36379step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36379 raw36379Labels = mixedMoment B node5246 node5246Labels := by
  calc
    mixedMoment B raw36379 raw36379Labels = mixedMoment B raw36379step0 raw36379step0Labels := by
      have ha : raw36379step0 = (fun i j => raw36379 (permutation663 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36379step0 raw36379; decide +kernel
      have hl : raw36379step0Labels = raw36379Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36379 raw36379Labels permutation663 permutation4
    mixedMoment B raw36379step0 raw36379step0Labels = mixedMoment B raw36379step1 raw36379step1Labels := by
      have ha : raw36379step1 = raw36379step0 := by apply Matrix.ext; unfold raw36379step1 raw36379step0; decide +kernel
      have hl : raw36379step0Labels = labelEmbedding7 ∘ raw36379step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36379step0 raw36379step0Labels raw36379step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5246 node5246Labels := by rfl

def raw36380 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 1, -2], ![1, 1, -2], ![-1, 1, 0], ![0, -1, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw36380Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36380step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36380step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw36380step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36380step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36380 raw36380Labels = mixedMoment B node5092 node5092Labels := by
  calc
    mixedMoment B raw36380 raw36380Labels = mixedMoment B raw36380step0 raw36380step0Labels := by
      have ha : raw36380step0 = (fun i j => raw36380 (permutation663 i) (permutation4 j)) := by apply Matrix.ext; unfold raw36380step0 raw36380; decide +kernel
      have hl : raw36380step0Labels = raw36380Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36380 raw36380Labels permutation663 permutation4
    mixedMoment B raw36380step0 raw36380step0Labels = mixedMoment B raw36380step1 raw36380step1Labels := by
      have ha : raw36380step1 = raw36380step0 := by apply Matrix.ext; unfold raw36380step1 raw36380step0; decide +kernel
      have hl : raw36380step0Labels = labelEmbedding7 ∘ raw36380step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36380step0 raw36380step0Labels raw36380step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5092 node5092Labels := by rfl

def raw36381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36381Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36381step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36381step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36381 raw36381Labels = mixedMoment B node5076 node5076Labels := by
  calc
    mixedMoment B raw36381 raw36381Labels = mixedMoment B raw36381step0 raw36381step0Labels := by
      have ha : raw36381step0 = (fun i j => raw36381 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36381step0 raw36381; decide +kernel
      have hl : raw36381step0Labels = raw36381Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36381 raw36381Labels permutation265 permutation2
    _ = mixedMoment B node5076 node5076Labels := by rfl

def raw36382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36382Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36382step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36382step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36382 raw36382Labels = mixedMoment B node5403 node5403Labels := by
  calc
    mixedMoment B raw36382 raw36382Labels = mixedMoment B raw36382step0 raw36382step0Labels := by
      have ha : raw36382step0 = (fun i j => raw36382 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36382step0 raw36382; decide +kernel
      have hl : raw36382step0Labels = raw36382Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36382 raw36382Labels permutation265 permutation2
    _ = mixedMoment B node5403 node5403Labels := by rfl

def raw36383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36383Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36383step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36383step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36383 raw36383Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw36383 raw36383Labels = mixedMoment B raw36383step0 raw36383step0Labels := by
      have ha : raw36383step0 = (fun i j => raw36383 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36383step0 raw36383; decide +kernel
      have hl : raw36383step0Labels = raw36383Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36383 raw36383Labels permutation265 permutation2
    _ = mixedMoment B node5406 node5406Labels := by rfl

def raw36384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw36384Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36384step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36384step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36384 raw36384Labels = mixedMoment B node5406 node5406Labels := by
  calc
    mixedMoment B raw36384 raw36384Labels = mixedMoment B raw36384step0 raw36384step0Labels := by
      have ha : raw36384step0 = (fun i j => raw36384 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36384step0 raw36384; decide +kernel
      have hl : raw36384step0Labels = raw36384Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36384 raw36384Labels permutation267 permutation2
    _ = mixedMoment B node5406 node5406Labels := by rfl

def raw36385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw36385Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36385step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw36385step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36385 raw36385Labels = mixedMoment B node5472 node5472Labels := by
  calc
    mixedMoment B raw36385 raw36385Labels = mixedMoment B raw36385step0 raw36385step0Labels := by
      have ha : raw36385step0 = (fun i j => raw36385 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36385step0 raw36385; decide +kernel
      have hl : raw36385step0Labels = raw36385Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36385 raw36385Labels permutation156 permutation2
    _ = mixedMoment B node5472 node5472Labels := by rfl

def raw36386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36386Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36386step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36386step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36386step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36386step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36386 raw36386Labels = mixedMoment B node4967 node4967Labels := by
  calc
    mixedMoment B raw36386 raw36386Labels = mixedMoment B raw36386step0 raw36386step0Labels := by
      have ha : raw36386step0 = (fun i j => raw36386 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36386step0 raw36386; decide +kernel
      have hl : raw36386step0Labels = raw36386Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36386 raw36386Labels permutation152 permutation3
    mixedMoment B raw36386step0 raw36386step0Labels = mixedMoment B raw36386step1 raw36386step1Labels := by
      have ha : raw36386step1 = raw36386step0 := by apply Matrix.ext; unfold raw36386step1 raw36386step0; decide +kernel
      have hl : raw36386step0Labels = labelEmbedding6 ∘ raw36386step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36386step0 raw36386step0Labels raw36386step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4967 node4967Labels := by rfl

def raw36387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36387Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36387step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36387step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36387 raw36387Labels = mixedMoment B node4947 node4947Labels := by
  calc
    mixedMoment B raw36387 raw36387Labels = mixedMoment B raw36387step0 raw36387step0Labels := by
      have ha : raw36387step0 = (fun i j => raw36387 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36387step0 raw36387; decide +kernel
      have hl : raw36387step0Labels = raw36387Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36387 raw36387Labels permutation265 permutation2
    _ = mixedMoment B node4947 node4947Labels := by rfl

def raw36388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36388Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36388step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36388step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36388 raw36388Labels = mixedMoment B node5354 node5354Labels := by
  calc
    mixedMoment B raw36388 raw36388Labels = mixedMoment B raw36388step0 raw36388step0Labels := by
      have ha : raw36388step0 = (fun i j => raw36388 (permutation271 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36388step0 raw36388; decide +kernel
      have hl : raw36388step0Labels = raw36388Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36388 raw36388Labels permutation271 permutation2
    _ = mixedMoment B node5354 node5354Labels := by rfl

def raw36389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw36389Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36389step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36389step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36389 raw36389Labels = mixedMoment B node5354 node5354Labels := by
  calc
    mixedMoment B raw36389 raw36389Labels = mixedMoment B raw36389step0 raw36389step0Labels := by
      have ha : raw36389step0 = (fun i j => raw36389 (permutation277 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36389step0 raw36389; decide +kernel
      have hl : raw36389step0Labels = raw36389Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36389 raw36389Labels permutation277 permutation2
    _ = mixedMoment B node5354 node5354Labels := by rfl

def raw36390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36390Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36390step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36390step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36390step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36390step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36390 raw36390Labels = mixedMoment B node4955 node4955Labels := by
  calc
    mixedMoment B raw36390 raw36390Labels = mixedMoment B raw36390step0 raw36390step0Labels := by
      have ha : raw36390step0 = (fun i j => raw36390 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36390step0 raw36390; decide +kernel
      have hl : raw36390step0Labels = raw36390Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36390 raw36390Labels permutation154 permutation3
    mixedMoment B raw36390step0 raw36390step0Labels = mixedMoment B raw36390step1 raw36390step1Labels := by
      have ha : raw36390step1 = raw36390step0 := by apply Matrix.ext; unfold raw36390step1 raw36390step0; decide +kernel
      have hl : raw36390step0Labels = labelEmbedding6 ∘ raw36390step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36390step0 raw36390step0Labels raw36390step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4955 node4955Labels := by rfl

def raw36391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36391Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36391step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36391step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36391 raw36391Labels = mixedMoment B node4933 node4933Labels := by
  calc
    mixedMoment B raw36391 raw36391Labels = mixedMoment B raw36391step0 raw36391step0Labels := by
      have ha : raw36391step0 = (fun i j => raw36391 (permutation268 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36391step0 raw36391; decide +kernel
      have hl : raw36391step0Labels = raw36391Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36391 raw36391Labels permutation268 permutation2
    _ = mixedMoment B node4933 node4933Labels := by rfl

def raw36392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36392Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36392step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw36392step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36392step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36392step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36392step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36392step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36392 raw36392Labels = mixedMoment B node5338 node5338Labels := by
  calc
    mixedMoment B raw36392 raw36392Labels = mixedMoment B raw36392step0 raw36392step0Labels := by
      have ha : raw36392step0 = (fun i j => raw36392 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36392step0 raw36392; decide +kernel
      have hl : raw36392step0Labels = raw36392Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36392 raw36392Labels permutation664 permutation3
    mixedMoment B raw36392step0 raw36392step0Labels = mixedMoment B raw36392step1 raw36392step1Labels := by
      have ha : raw36392step1 = -raw36392step0 := by apply Matrix.ext; change ∀ i j, raw36392step1 i j = -(raw36392step0 i j); unfold raw36392step1 raw36392step0; decide +kernel
      have hl : raw36392step1Labels = raw36392step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36392step1 raw36392step1Labels = mixedMoment B raw36392step2 raw36392step2Labels := by
      have ha : raw36392step2 = raw36392step1 := by apply Matrix.ext; unfold raw36392step2 raw36392step1; decide +kernel
      have hl : raw36392step1Labels = labelEmbedding6 ∘ raw36392step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36392step1 raw36392step1Labels raw36392step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5338 node5338Labels := by rfl

def raw36393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw36393Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36393step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36393step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36393 raw36393Labels = mixedMoment B node5348 node5348Labels := by
  calc
    mixedMoment B raw36393 raw36393Labels = mixedMoment B raw36393step0 raw36393step0Labels := by
      have ha : raw36393step0 = (fun i j => raw36393 (permutation268 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36393step0 raw36393; decide +kernel
      have hl : raw36393step0Labels = raw36393Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36393 raw36393Labels permutation268 permutation2
    _ = mixedMoment B node5348 node5348Labels := by rfl

def raw36394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw36394Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36394step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36394step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36394step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36394step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36394 raw36394Labels = mixedMoment B node4955 node4955Labels := by
  calc
    mixedMoment B raw36394 raw36394Labels = mixedMoment B raw36394step0 raw36394step0Labels := by
      have ha : raw36394step0 = (fun i j => raw36394 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36394step0 raw36394; decide +kernel
      have hl : raw36394step0Labels = raw36394Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36394 raw36394Labels permutation152 permutation3
    mixedMoment B raw36394step0 raw36394step0Labels = mixedMoment B raw36394step1 raw36394step1Labels := by
      have ha : raw36394step1 = raw36394step0 := by apply Matrix.ext; unfold raw36394step1 raw36394step0; decide +kernel
      have hl : raw36394step0Labels = labelEmbedding6 ∘ raw36394step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36394step0 raw36394step0Labels raw36394step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4955 node4955Labels := by rfl

def raw36395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw36395Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36395step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36395step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36395 raw36395Labels = mixedMoment B node4933 node4933Labels := by
  calc
    mixedMoment B raw36395 raw36395Labels = mixedMoment B raw36395step0 raw36395step0Labels := by
      have ha : raw36395step0 = (fun i j => raw36395 (permutation266 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36395step0 raw36395; decide +kernel
      have hl : raw36395step0Labels = raw36395Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36395 raw36395Labels permutation266 permutation2
    _ = mixedMoment B node4933 node4933Labels := by rfl

def raw36396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw36396Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36396step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw36396step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36396step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36396step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36396step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36396step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36396 raw36396Labels = mixedMoment B node5338 node5338Labels := by
  calc
    mixedMoment B raw36396 raw36396Labels = mixedMoment B raw36396step0 raw36396step0Labels := by
      have ha : raw36396step0 = (fun i j => raw36396 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36396step0 raw36396; decide +kernel
      have hl : raw36396step0Labels = raw36396Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36396 raw36396Labels permutation688 permutation3
    mixedMoment B raw36396step0 raw36396step0Labels = mixedMoment B raw36396step1 raw36396step1Labels := by
      have ha : raw36396step1 = -raw36396step0 := by apply Matrix.ext; change ∀ i j, raw36396step1 i j = -(raw36396step0 i j); unfold raw36396step1 raw36396step0; decide +kernel
      have hl : raw36396step1Labels = raw36396step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36396step1 raw36396step1Labels = mixedMoment B raw36396step2 raw36396step2Labels := by
      have ha : raw36396step2 = raw36396step1 := by apply Matrix.ext; unfold raw36396step2 raw36396step1; decide +kernel
      have hl : raw36396step1Labels = labelEmbedding6 ∘ raw36396step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36396step1 raw36396step1Labels raw36396step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5338 node5338Labels := by rfl

def raw36397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw36397Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36397step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36397step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36397 raw36397Labels = mixedMoment B node5348 node5348Labels := by
  calc
    mixedMoment B raw36397 raw36397Labels = mixedMoment B raw36397step0 raw36397step0Labels := by
      have ha : raw36397step0 = (fun i j => raw36397 (permutation266 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36397step0 raw36397; decide +kernel
      have hl : raw36397step0Labels = raw36397Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36397 raw36397Labels permutation266 permutation2
    _ = mixedMoment B node5348 node5348Labels := by rfl

def raw36398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw36398Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36398step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-3, 1, 2]]
def raw36398step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36398step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw36398step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36398step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![3, -1, -2]]
def raw36398step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36398 raw36398Labels = mixedMoment B node4756 node4756Labels := by
  calc
    mixedMoment B raw36398 raw36398Labels = mixedMoment B raw36398step0 raw36398step0Labels := by
      have ha : raw36398step0 = (fun i j => raw36398 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36398step0 raw36398; decide +kernel
      have hl : raw36398step0Labels = raw36398Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36398 raw36398Labels permutation664 permutation3
    mixedMoment B raw36398step0 raw36398step0Labels = mixedMoment B raw36398step1 raw36398step1Labels := by
      have ha : raw36398step1 = -raw36398step0 := by apply Matrix.ext; change ∀ i j, raw36398step1 i j = -(raw36398step0 i j); unfold raw36398step1 raw36398step0; decide +kernel
      have hl : raw36398step1Labels = raw36398step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36398step1 raw36398step1Labels = mixedMoment B raw36398step2 raw36398step2Labels := by
      have ha : raw36398step2 = raw36398step1 := by apply Matrix.ext; unfold raw36398step2 raw36398step1; decide +kernel
      have hl : raw36398step1Labels = labelEmbedding6 ∘ raw36398step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36398step1 raw36398step1Labels raw36398step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4756 node4756Labels := by rfl

def raw36399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw36399Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36399step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-3, 2, 1]]
def raw36399step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36399step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw36399step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36399step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![3, -2, -1]]
def raw36399step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36399 raw36399Labels = mixedMoment B node4757 node4757Labels := by
  calc
    mixedMoment B raw36399 raw36399Labels = mixedMoment B raw36399step0 raw36399step0Labels := by
      have ha : raw36399step0 = (fun i j => raw36399 (permutation663 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36399step0 raw36399; decide +kernel
      have hl : raw36399step0Labels = raw36399Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36399 raw36399Labels permutation663 permutation3
    mixedMoment B raw36399step0 raw36399step0Labels = mixedMoment B raw36399step1 raw36399step1Labels := by
      have ha : raw36399step1 = -raw36399step0 := by apply Matrix.ext; change ∀ i j, raw36399step1 i j = -(raw36399step0 i j); unfold raw36399step1 raw36399step0; decide +kernel
      have hl : raw36399step1Labels = raw36399step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36399step1 raw36399step1Labels = mixedMoment B raw36399step2 raw36399step2Labels := by
      have ha : raw36399step2 = raw36399step1 := by apply Matrix.ext; unfold raw36399step2 raw36399step1; decide +kernel
      have hl : raw36399step1Labels = labelEmbedding6 ∘ raw36399step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36399step1 raw36399step1Labels raw36399step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4757 node4757Labels := by rfl

def raw36400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw36400Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36400step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw36400step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36400step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36400step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36400step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36400step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36400 raw36400Labels = mixedMoment B node4768 node4768Labels := by
  calc
    mixedMoment B raw36400 raw36400Labels = mixedMoment B raw36400step0 raw36400step0Labels := by
      have ha : raw36400step0 = (fun i j => raw36400 (permutation664 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36400step0 raw36400; decide +kernel
      have hl : raw36400step0Labels = raw36400Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36400 raw36400Labels permutation664 permutation3
    mixedMoment B raw36400step0 raw36400step0Labels = mixedMoment B raw36400step1 raw36400step1Labels := by
      have ha : raw36400step1 = -raw36400step0 := by apply Matrix.ext; change ∀ i j, raw36400step1 i j = -(raw36400step0 i j); unfold raw36400step1 raw36400step0; decide +kernel
      have hl : raw36400step1Labels = raw36400step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36400step1 raw36400step1Labels = mixedMoment B raw36400step2 raw36400step2Labels := by
      have ha : raw36400step2 = raw36400step1 := by apply Matrix.ext; unfold raw36400step2 raw36400step1; decide +kernel
      have hl : raw36400step1Labels = labelEmbedding6 ∘ raw36400step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36400step1 raw36400step1Labels raw36400step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4768 node4768Labels := by rfl

def raw36401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw36401Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36401step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw36401step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36401step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36401step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36401step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36401step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36401 raw36401Labels = mixedMoment B node4795 node4795Labels := by
  calc
    mixedMoment B raw36401 raw36401Labels = mixedMoment B raw36401step0 raw36401step0Labels := by
      have ha : raw36401step0 = (fun i j => raw36401 (permutation682 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36401step0 raw36401; decide +kernel
      have hl : raw36401step0Labels = raw36401Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36401 raw36401Labels permutation682 permutation3
    mixedMoment B raw36401step0 raw36401step0Labels = mixedMoment B raw36401step1 raw36401step1Labels := by
      have ha : raw36401step1 = -raw36401step0 := by apply Matrix.ext; change ∀ i j, raw36401step1 i j = -(raw36401step0 i j); unfold raw36401step1 raw36401step0; decide +kernel
      have hl : raw36401step1Labels = raw36401step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36401step1 raw36401step1Labels = mixedMoment B raw36401step2 raw36401step2Labels := by
      have ha : raw36401step2 = raw36401step1 := by apply Matrix.ext; unfold raw36401step2 raw36401step1; decide +kernel
      have hl : raw36401step1Labels = labelEmbedding6 ∘ raw36401step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36401step1 raw36401step1Labels raw36401step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4795 node4795Labels := by rfl

def raw36402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw36402Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36402step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw36402step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36402step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36402step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36402step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36402step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36402 raw36402Labels = mixedMoment B node4795 node4795Labels := by
  calc
    mixedMoment B raw36402 raw36402Labels = mixedMoment B raw36402step0 raw36402step0Labels := by
      have ha : raw36402step0 = (fun i j => raw36402 (permutation658 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36402step0 raw36402; decide +kernel
      have hl : raw36402step0Labels = raw36402Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36402 raw36402Labels permutation658 permutation3
    mixedMoment B raw36402step0 raw36402step0Labels = mixedMoment B raw36402step1 raw36402step1Labels := by
      have ha : raw36402step1 = -raw36402step0 := by apply Matrix.ext; change ∀ i j, raw36402step1 i j = -(raw36402step0 i j); unfold raw36402step1 raw36402step0; decide +kernel
      have hl : raw36402step1Labels = raw36402step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36402step1 raw36402step1Labels = mixedMoment B raw36402step2 raw36402step2Labels := by
      have ha : raw36402step2 = raw36402step1 := by apply Matrix.ext; unfold raw36402step2 raw36402step1; decide +kernel
      have hl : raw36402step1Labels = labelEmbedding6 ∘ raw36402step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36402step1 raw36402step1Labels raw36402step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4795 node4795Labels := by rfl

def raw36403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36403Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36403step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw36403step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36403step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw36403step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36403step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw36403step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36403 raw36403Labels = mixedMoment B node3477 node3477Labels := by
  calc
    mixedMoment B raw36403 raw36403Labels = mixedMoment B raw36403step0 raw36403step0Labels := by
      have ha : raw36403step0 = (fun i j => raw36403 (permutation283 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36403step0 raw36403; decide +kernel
      have hl : raw36403step0Labels = raw36403Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36403 raw36403Labels permutation283 permutation7
    mixedMoment B raw36403step0 raw36403step0Labels = mixedMoment B raw36403step1 raw36403step1Labels := by
      have ha : raw36403step1 = -raw36403step0 := by apply Matrix.ext; change ∀ i j, raw36403step1 i j = -(raw36403step0 i j); unfold raw36403step1 raw36403step0; decide +kernel
      have hl : raw36403step1Labels = raw36403step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36403step1 raw36403step1Labels = mixedMoment B raw36403step2 raw36403step2Labels := by
      have ha : raw36403step2 = raw36403step1 := by apply Matrix.ext; unfold raw36403step2 raw36403step1; decide +kernel
      have hl : raw36403step1Labels = labelEmbedding1 ∘ raw36403step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36403step1 raw36403step1Labels raw36403step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3477 node3477Labels := by rfl

def raw36404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36404Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36404step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw36404step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36404step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw36404step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36404step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw36404step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36404 raw36404Labels = mixedMoment B node3810 node3810Labels := by
  calc
    mixedMoment B raw36404 raw36404Labels = mixedMoment B raw36404step0 raw36404step0Labels := by
      have ha : raw36404step0 = (fun i j => raw36404 (permutation283 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36404step0 raw36404; decide +kernel
      have hl : raw36404step0Labels = raw36404Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36404 raw36404Labels permutation283 permutation7
    mixedMoment B raw36404step0 raw36404step0Labels = mixedMoment B raw36404step1 raw36404step1Labels := by
      have ha : raw36404step1 = -raw36404step0 := by apply Matrix.ext; change ∀ i j, raw36404step1 i j = -(raw36404step0 i j); unfold raw36404step1 raw36404step0; decide +kernel
      have hl : raw36404step1Labels = raw36404step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36404step1 raw36404step1Labels = mixedMoment B raw36404step2 raw36404step2Labels := by
      have ha : raw36404step2 = raw36404step1 := by apply Matrix.ext; unfold raw36404step2 raw36404step1; decide +kernel
      have hl : raw36404step1Labels = labelEmbedding1 ∘ raw36404step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36404step1 raw36404step1Labels raw36404step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3810 node3810Labels := by rfl

def raw36405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36405Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36405step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw36405step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36405step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw36405step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36405step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw36405step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36405 raw36405Labels = mixedMoment B node3812 node3812Labels := by
  calc
    mixedMoment B raw36405 raw36405Labels = mixedMoment B raw36405step0 raw36405step0Labels := by
      have ha : raw36405step0 = (fun i j => raw36405 (permutation283 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36405step0 raw36405; decide +kernel
      have hl : raw36405step0Labels = raw36405Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36405 raw36405Labels permutation283 permutation7
    mixedMoment B raw36405step0 raw36405step0Labels = mixedMoment B raw36405step1 raw36405step1Labels := by
      have ha : raw36405step1 = -raw36405step0 := by apply Matrix.ext; change ∀ i j, raw36405step1 i j = -(raw36405step0 i j); unfold raw36405step1 raw36405step0; decide +kernel
      have hl : raw36405step1Labels = raw36405step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36405step1 raw36405step1Labels = mixedMoment B raw36405step2 raw36405step2Labels := by
      have ha : raw36405step2 = raw36405step1 := by apply Matrix.ext; unfold raw36405step2 raw36405step1; decide +kernel
      have hl : raw36405step1Labels = labelEmbedding1 ∘ raw36405step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36405step1 raw36405step1Labels raw36405step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3812 node3812Labels := by rfl

def raw36406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw36406Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36406step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw36406step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36406step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw36406step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36406step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw36406step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36406 raw36406Labels = mixedMoment B node3812 node3812Labels := by
  calc
    mixedMoment B raw36406 raw36406Labels = mixedMoment B raw36406step0 raw36406step0Labels := by
      have ha : raw36406step0 = (fun i j => raw36406 (permutation284 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36406step0 raw36406; decide +kernel
      have hl : raw36406step0Labels = raw36406Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36406 raw36406Labels permutation284 permutation7
    mixedMoment B raw36406step0 raw36406step0Labels = mixedMoment B raw36406step1 raw36406step1Labels := by
      have ha : raw36406step1 = -raw36406step0 := by apply Matrix.ext; change ∀ i j, raw36406step1 i j = -(raw36406step0 i j); unfold raw36406step1 raw36406step0; decide +kernel
      have hl : raw36406step1Labels = raw36406step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36406step1 raw36406step1Labels = mixedMoment B raw36406step2 raw36406step2Labels := by
      have ha : raw36406step2 = raw36406step1 := by apply Matrix.ext; unfold raw36406step2 raw36406step1; decide +kernel
      have hl : raw36406step1Labels = labelEmbedding1 ∘ raw36406step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36406step1 raw36406step1Labels raw36406step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3812 node3812Labels := by rfl

def raw36407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw36407Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36407step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw36407step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36407step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw36407step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36407step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw36407step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36407 raw36407Labels = mixedMoment B node3957 node3957Labels := by
  calc
    mixedMoment B raw36407 raw36407Labels = mixedMoment B raw36407step0 raw36407step0Labels := by
      have ha : raw36407step0 = (fun i j => raw36407 (permutation283 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36407step0 raw36407; decide +kernel
      have hl : raw36407step0Labels = raw36407Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36407 raw36407Labels permutation283 permutation7
    mixedMoment B raw36407step0 raw36407step0Labels = mixedMoment B raw36407step1 raw36407step1Labels := by
      have ha : raw36407step1 = -raw36407step0 := by apply Matrix.ext; change ∀ i j, raw36407step1 i j = -(raw36407step0 i j); unfold raw36407step1 raw36407step0; decide +kernel
      have hl : raw36407step1Labels = raw36407step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36407step1 raw36407step1Labels = mixedMoment B raw36407step2 raw36407step2Labels := by
      have ha : raw36407step2 = raw36407step1 := by apply Matrix.ext; unfold raw36407step2 raw36407step1; decide +kernel
      have hl : raw36407step1Labels = labelEmbedding1 ∘ raw36407step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36407step1 raw36407step1Labels raw36407step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3957 node3957Labels := by rfl

def raw36408 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36408Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36408step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw36408step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36408step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw36408step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36408step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw36408step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36408 raw36408Labels = mixedMoment B node3585 node3585Labels := by
  calc
    mixedMoment B raw36408 raw36408Labels = mixedMoment B raw36408step0 raw36408step0Labels := by
      have ha : raw36408step0 = (fun i j => raw36408 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36408step0 raw36408; decide +kernel
      have hl : raw36408step0Labels = raw36408Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36408 raw36408Labels permutation152 permutation5
    mixedMoment B raw36408step0 raw36408step0Labels = mixedMoment B raw36408step1 raw36408step1Labels := by
      have ha : raw36408step1 = -raw36408step0 := by apply Matrix.ext; change ∀ i j, raw36408step1 i j = -(raw36408step0 i j); unfold raw36408step1 raw36408step0; decide +kernel
      have hl : raw36408step1Labels = raw36408step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36408step1 raw36408step1Labels = mixedMoment B raw36408step2 raw36408step2Labels := by
      have ha : raw36408step2 = raw36408step1 := by apply Matrix.ext; unfold raw36408step2 raw36408step1; decide +kernel
      have hl : raw36408step1Labels = labelEmbedding1 ∘ raw36408step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36408step1 raw36408step1Labels raw36408step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3585 node3585Labels := by rfl

def raw36409 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36409Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36409step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw36409step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36409step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw36409step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36409step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw36409step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36409 raw36409Labels = mixedMoment B node3416 node3416Labels := by
  calc
    mixedMoment B raw36409 raw36409Labels = mixedMoment B raw36409step0 raw36409step0Labels := by
      have ha : raw36409step0 = (fun i j => raw36409 (permutation283 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36409step0 raw36409; decide +kernel
      have hl : raw36409step0Labels = raw36409Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36409 raw36409Labels permutation283 permutation7
    mixedMoment B raw36409step0 raw36409step0Labels = mixedMoment B raw36409step1 raw36409step1Labels := by
      have ha : raw36409step1 = -raw36409step0 := by apply Matrix.ext; change ∀ i j, raw36409step1 i j = -(raw36409step0 i j); unfold raw36409step1 raw36409step0; decide +kernel
      have hl : raw36409step1Labels = raw36409step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36409step1 raw36409step1Labels = mixedMoment B raw36409step2 raw36409step2Labels := by
      have ha : raw36409step2 = raw36409step1 := by apply Matrix.ext; unfold raw36409step2 raw36409step1; decide +kernel
      have hl : raw36409step1Labels = labelEmbedding1 ∘ raw36409step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36409step1 raw36409step1Labels raw36409step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3416 node3416Labels := by rfl

def raw36410 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36410Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36410step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw36410step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36410step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw36410step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36410step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw36410step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36410 raw36410Labels = mixedMoment B node3769 node3769Labels := by
  calc
    mixedMoment B raw36410 raw36410Labels = mixedMoment B raw36410step0 raw36410step0Labels := by
      have ha : raw36410step0 = (fun i j => raw36410 (permutation285 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36410step0 raw36410; decide +kernel
      have hl : raw36410step0Labels = raw36410Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36410 raw36410Labels permutation285 permutation7
    mixedMoment B raw36410step0 raw36410step0Labels = mixedMoment B raw36410step1 raw36410step1Labels := by
      have ha : raw36410step1 = -raw36410step0 := by apply Matrix.ext; change ∀ i j, raw36410step1 i j = -(raw36410step0 i j); unfold raw36410step1 raw36410step0; decide +kernel
      have hl : raw36410step1Labels = raw36410step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36410step1 raw36410step1Labels = mixedMoment B raw36410step2 raw36410step2Labels := by
      have ha : raw36410step2 = raw36410step1 := by apply Matrix.ext; unfold raw36410step2 raw36410step1; decide +kernel
      have hl : raw36410step1Labels = labelEmbedding1 ∘ raw36410step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36410step1 raw36410step1Labels raw36410step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3769 node3769Labels := by rfl

def raw36411 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw36411Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36411step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw36411step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36411step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw36411step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36411step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw36411step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36411 raw36411Labels = mixedMoment B node3769 node3769Labels := by
  calc
    mixedMoment B raw36411 raw36411Labels = mixedMoment B raw36411step0 raw36411step0Labels := by
      have ha : raw36411step0 = (fun i j => raw36411 (permutation287 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36411step0 raw36411; decide +kernel
      have hl : raw36411step0Labels = raw36411Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36411 raw36411Labels permutation287 permutation7
    mixedMoment B raw36411step0 raw36411step0Labels = mixedMoment B raw36411step1 raw36411step1Labels := by
      have ha : raw36411step1 = -raw36411step0 := by apply Matrix.ext; change ∀ i j, raw36411step1 i j = -(raw36411step0 i j); unfold raw36411step1 raw36411step0; decide +kernel
      have hl : raw36411step1Labels = raw36411step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36411step1 raw36411step1Labels = mixedMoment B raw36411step2 raw36411step2Labels := by
      have ha : raw36411step2 = raw36411step1 := by apply Matrix.ext; unfold raw36411step2 raw36411step1; decide +kernel
      have hl : raw36411step1Labels = labelEmbedding1 ∘ raw36411step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36411step1 raw36411step1Labels raw36411step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3769 node3769Labels := by rfl

def raw36412 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36412Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36412step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw36412step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36412step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36412step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36412step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36412step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36412 raw36412Labels = mixedMoment B node3508 node3508Labels := by
  calc
    mixedMoment B raw36412 raw36412Labels = mixedMoment B raw36412step0 raw36412step0Labels := by
      have ha : raw36412step0 = (fun i j => raw36412 (permutation178 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36412step0 raw36412; decide +kernel
      have hl : raw36412step0Labels = raw36412Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36412 raw36412Labels permutation178 permutation5
    mixedMoment B raw36412step0 raw36412step0Labels = mixedMoment B raw36412step1 raw36412step1Labels := by
      have ha : raw36412step1 = -raw36412step0 := by apply Matrix.ext; change ∀ i j, raw36412step1 i j = -(raw36412step0 i j); unfold raw36412step1 raw36412step0; decide +kernel
      have hl : raw36412step1Labels = raw36412step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36412step1 raw36412step1Labels = mixedMoment B raw36412step2 raw36412step2Labels := by
      have ha : raw36412step2 = raw36412step1 := by apply Matrix.ext; unfold raw36412step2 raw36412step1; decide +kernel
      have hl : raw36412step1Labels = labelEmbedding1 ∘ raw36412step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36412step1 raw36412step1Labels raw36412step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3508 node3508Labels := by rfl

def raw36413 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36413Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36413step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw36413step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36413step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36413step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36413step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36413step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36413 raw36413Labels = mixedMoment B node3414 node3414Labels := by
  calc
    mixedMoment B raw36413 raw36413Labels = mixedMoment B raw36413step0 raw36413step0Labels := by
      have ha : raw36413step0 = (fun i j => raw36413 (permutation284 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36413step0 raw36413; decide +kernel
      have hl : raw36413step0Labels = raw36413Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36413 raw36413Labels permutation284 permutation7
    mixedMoment B raw36413step0 raw36413step0Labels = mixedMoment B raw36413step1 raw36413step1Labels := by
      have ha : raw36413step1 = -raw36413step0 := by apply Matrix.ext; change ∀ i j, raw36413step1 i j = -(raw36413step0 i j); unfold raw36413step1 raw36413step0; decide +kernel
      have hl : raw36413step1Labels = raw36413step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36413step1 raw36413step1Labels = mixedMoment B raw36413step2 raw36413step2Labels := by
      have ha : raw36413step2 = raw36413step1 := by apply Matrix.ext; unfold raw36413step2 raw36413step1; decide +kernel
      have hl : raw36413step1Labels = labelEmbedding1 ∘ raw36413step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36413step1 raw36413step1Labels raw36413step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3414 node3414Labels := by rfl

def raw36414 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 2, -1], ![2, -1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36414Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36414step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw36414step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36414step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw36414step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36414 raw36414Labels = mixedMoment B node3755 node3755Labels := by
  calc
    mixedMoment B raw36414 raw36414Labels = mixedMoment B raw36414step0 raw36414step0Labels := by
      have ha : raw36414step0 = (fun i j => raw36414 (permutation661 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36414step0 raw36414; decide +kernel
      have hl : raw36414step0Labels = raw36414Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36414 raw36414Labels permutation661 permutation5
    mixedMoment B raw36414step0 raw36414step0Labels = mixedMoment B raw36414step1 raw36414step1Labels := by
      have ha : raw36414step1 = raw36414step0 := by apply Matrix.ext; unfold raw36414step1 raw36414step0; decide +kernel
      have hl : raw36414step0Labels = labelEmbedding1 ∘ raw36414step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36414step0 raw36414step0Labels raw36414step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3755 node3755Labels := by rfl

def raw36415 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw36415Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36415step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw36415step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36415step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw36415step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36415 raw36415Labels = mixedMoment B node3768 node3768Labels := by
  calc
    mixedMoment B raw36415 raw36415Labels = mixedMoment B raw36415step0 raw36415step0Labels := by
      have ha : raw36415step0 = (fun i j => raw36415 (permutation653 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36415step0 raw36415; decide +kernel
      have hl : raw36415step0Labels = raw36415Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36415 raw36415Labels permutation653 permutation5
    mixedMoment B raw36415step0 raw36415step0Labels = mixedMoment B raw36415step1 raw36415step1Labels := by
      have ha : raw36415step1 = raw36415step0 := by apply Matrix.ext; unfold raw36415step1 raw36415step0; decide +kernel
      have hl : raw36415step0Labels = labelEmbedding1 ∘ raw36415step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36415step0 raw36415step0Labels raw36415step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3768 node3768Labels := by rfl

def raw36416 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw36416Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36416step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw36416step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36416step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36416step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36416step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36416step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36416 raw36416Labels = mixedMoment B node3508 node3508Labels := by
  calc
    mixedMoment B raw36416 raw36416Labels = mixedMoment B raw36416step0 raw36416step0Labels := by
      have ha : raw36416step0 = (fun i j => raw36416 (permutation176 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36416step0 raw36416; decide +kernel
      have hl : raw36416step0Labels = raw36416Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36416 raw36416Labels permutation176 permutation5
    mixedMoment B raw36416step0 raw36416step0Labels = mixedMoment B raw36416step1 raw36416step1Labels := by
      have ha : raw36416step1 = -raw36416step0 := by apply Matrix.ext; change ∀ i j, raw36416step1 i j = -(raw36416step0 i j); unfold raw36416step1 raw36416step0; decide +kernel
      have hl : raw36416step1Labels = raw36416step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36416step1 raw36416step1Labels = mixedMoment B raw36416step2 raw36416step2Labels := by
      have ha : raw36416step2 = raw36416step1 := by apply Matrix.ext; unfold raw36416step2 raw36416step1; decide +kernel
      have hl : raw36416step1Labels = labelEmbedding1 ∘ raw36416step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36416step1 raw36416step1Labels raw36416step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3508 node3508Labels := by rfl

def raw36417 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw36417Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36417step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw36417step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36417step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36417step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36417step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36417step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36417 raw36417Labels = mixedMoment B node3414 node3414Labels := by
  calc
    mixedMoment B raw36417 raw36417Labels = mixedMoment B raw36417step0 raw36417step0Labels := by
      have ha : raw36417step0 = (fun i j => raw36417 (permutation283 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36417step0 raw36417; decide +kernel
      have hl : raw36417step0Labels = raw36417Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36417 raw36417Labels permutation283 permutation7
    mixedMoment B raw36417step0 raw36417step0Labels = mixedMoment B raw36417step1 raw36417step1Labels := by
      have ha : raw36417step1 = -raw36417step0 := by apply Matrix.ext; change ∀ i j, raw36417step1 i j = -(raw36417step0 i j); unfold raw36417step1 raw36417step0; decide +kernel
      have hl : raw36417step1Labels = raw36417step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36417step1 raw36417step1Labels = mixedMoment B raw36417step2 raw36417step2Labels := by
      have ha : raw36417step2 = raw36417step1 := by apply Matrix.ext; unfold raw36417step2 raw36417step1; decide +kernel
      have hl : raw36417step1Labels = labelEmbedding1 ∘ raw36417step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36417step1 raw36417step1Labels raw36417step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3414 node3414Labels := by rfl

def raw36418 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1], ![2, -2, 0]]
def raw36418Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36418step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw36418step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36418step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw36418step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36418 raw36418Labels = mixedMoment B node3755 node3755Labels := by
  calc
    mixedMoment B raw36418 raw36418Labels = mixedMoment B raw36418step0 raw36418step0Labels := by
      have ha : raw36418step0 = (fun i j => raw36418 (permutation685 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36418step0 raw36418; decide +kernel
      have hl : raw36418step0Labels = raw36418Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36418 raw36418Labels permutation685 permutation5
    mixedMoment B raw36418step0 raw36418step0Labels = mixedMoment B raw36418step1 raw36418step1Labels := by
      have ha : raw36418step1 = raw36418step0 := by apply Matrix.ext; unfold raw36418step1 raw36418step0; decide +kernel
      have hl : raw36418step0Labels = labelEmbedding1 ∘ raw36418step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36418step0 raw36418step0Labels raw36418step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3755 node3755Labels := by rfl

def raw36419 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![2, -1, -1], ![2, -2, 0]]
def raw36419Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36419step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw36419step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36419step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw36419step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36419 raw36419Labels = mixedMoment B node3768 node3768Labels := by
  calc
    mixedMoment B raw36419 raw36419Labels = mixedMoment B raw36419step0 raw36419step0Labels := by
      have ha : raw36419step0 = (fun i j => raw36419 (permutation674 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36419step0 raw36419; decide +kernel
      have hl : raw36419step0Labels = raw36419Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36419 raw36419Labels permutation674 permutation5
    mixedMoment B raw36419step0 raw36419step0Labels = mixedMoment B raw36419step1 raw36419step1Labels := by
      have ha : raw36419step1 = raw36419step0 := by apply Matrix.ext; unfold raw36419step1 raw36419step0; decide +kernel
      have hl : raw36419step0Labels = labelEmbedding1 ∘ raw36419step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36419step0 raw36419step0Labels raw36419step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3768 node3768Labels := by rfl

def raw36420 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw36420Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36420step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw36420step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36420step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 1, -3]]
def raw36420step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36420 raw36420Labels = mixedMoment B node2176 node2176Labels := by
  calc
    mixedMoment B raw36420 raw36420Labels = mixedMoment B raw36420step0 raw36420step0Labels := by
      have ha : raw36420step0 = (fun i j => raw36420 (permutation662 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36420step0 raw36420; decide +kernel
      have hl : raw36420step0Labels = raw36420Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36420 raw36420Labels permutation662 permutation5
    mixedMoment B raw36420step0 raw36420step0Labels = mixedMoment B raw36420step1 raw36420step1Labels := by
      have ha : raw36420step1 = raw36420step0 := by apply Matrix.ext; unfold raw36420step1 raw36420step0; decide +kernel
      have hl : raw36420step0Labels = labelEmbedding1 ∘ raw36420step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36420step0 raw36420step0Labels raw36420step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2176 node2176Labels := by rfl

def raw36421 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw36421Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36421step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw36421step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36421step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 2, -3]]
def raw36421step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36421 raw36421Labels = mixedMoment B node2181 node2181Labels := by
  calc
    mixedMoment B raw36421 raw36421Labels = mixedMoment B raw36421step0 raw36421step0Labels := by
      have ha : raw36421step0 = (fun i j => raw36421 (permutation663 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36421step0 raw36421; decide +kernel
      have hl : raw36421step0Labels = raw36421Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36421 raw36421Labels permutation663 permutation5
    mixedMoment B raw36421step0 raw36421step0Labels = mixedMoment B raw36421step1 raw36421step1Labels := by
      have ha : raw36421step1 = raw36421step0 := by apply Matrix.ext; unfold raw36421step1 raw36421step0; decide +kernel
      have hl : raw36421step0Labels = labelEmbedding1 ∘ raw36421step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36421step0 raw36421step0Labels raw36421step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2181 node2181Labels := by rfl

def raw36422 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, 0, -1], ![3, -3, 0]]
def raw36422Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36422step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw36422step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36422step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw36422step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36422 raw36422Labels = mixedMoment B node2178 node2178Labels := by
  calc
    mixedMoment B raw36422 raw36422Labels = mixedMoment B raw36422step0 raw36422step0Labels := by
      have ha : raw36422step0 = (fun i j => raw36422 (permutation661 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36422step0 raw36422; decide +kernel
      have hl : raw36422step0Labels = raw36422Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36422 raw36422Labels permutation661 permutation5
    mixedMoment B raw36422step0 raw36422step0Labels = mixedMoment B raw36422step1 raw36422step1Labels := by
      have ha : raw36422step1 = raw36422step0 := by apply Matrix.ext; unfold raw36422step1 raw36422step0; decide +kernel
      have hl : raw36422step0Labels = labelEmbedding1 ∘ raw36422step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36422step0 raw36422step0Labels raw36422step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2178 node2178Labels := by rfl

def raw36423 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw36423Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36423step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw36423step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36423step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw36423step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36423 raw36423Labels = mixedMoment B node2213 node2213Labels := by
  calc
    mixedMoment B raw36423 raw36423Labels = mixedMoment B raw36423step0 raw36423step0Labels := by
      have ha : raw36423step0 = (fun i j => raw36423 (permutation674 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36423step0 raw36423; decide +kernel
      have hl : raw36423step0Labels = raw36423Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36423 raw36423Labels permutation674 permutation5
    mixedMoment B raw36423step0 raw36423step0Labels = mixedMoment B raw36423step1 raw36423step1Labels := by
      have ha : raw36423step1 = raw36423step0 := by apply Matrix.ext; unfold raw36423step1 raw36423step0; decide +kernel
      have hl : raw36423step0Labels = labelEmbedding1 ∘ raw36423step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36423step0 raw36423step0Labels raw36423step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2213 node2213Labels := by rfl

def raw36424 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![0, 1, -1], ![3, -3, 0]]
def raw36424Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36424step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw36424step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36424step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw36424step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36424 raw36424Labels = mixedMoment B node2213 node2213Labels := by
  calc
    mixedMoment B raw36424 raw36424Labels = mixedMoment B raw36424step0 raw36424step0Labels := by
      have ha : raw36424step0 = (fun i j => raw36424 (permutation653 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36424step0 raw36424; decide +kernel
      have hl : raw36424step0Labels = raw36424Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36424 raw36424Labels permutation653 permutation5
    mixedMoment B raw36424step0 raw36424step0Labels = mixedMoment B raw36424step1 raw36424step1Labels := by
      have ha : raw36424step1 = raw36424step0 := by apply Matrix.ext; unfold raw36424step1 raw36424step0; decide +kernel
      have hl : raw36424step0Labels = labelEmbedding1 ∘ raw36424step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36424step0 raw36424step0Labels raw36424step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2213 node2213Labels := by rfl

def raw36425 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36425Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36425step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36425step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36425step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36425step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36425 raw36425Labels = mixedMoment B node4805 node4805Labels := by
  calc
    mixedMoment B raw36425 raw36425Labels = mixedMoment B raw36425step0 raw36425step0Labels := by
      have ha : raw36425step0 = (fun i j => raw36425 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36425step0 raw36425; decide +kernel
      have hl : raw36425step0Labels = raw36425Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36425 raw36425Labels permutation265 permutation3
    mixedMoment B raw36425step0 raw36425step0Labels = mixedMoment B raw36425step1 raw36425step1Labels := by
      have ha : raw36425step1 = raw36425step0 := by apply Matrix.ext; unfold raw36425step1 raw36425step0; decide +kernel
      have hl : raw36425step0Labels = labelEmbedding6 ∘ raw36425step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36425step0 raw36425step0Labels raw36425step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4805 node4805Labels := by rfl

def raw36426 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36426Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36426step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw36426step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36426step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36426step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36426 raw36426Labels = mixedMoment B node5417 node5417Labels := by
  calc
    mixedMoment B raw36426 raw36426Labels = mixedMoment B raw36426step0 raw36426step0Labels := by
      have ha : raw36426step0 = (fun i j => raw36426 (permutation660 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36426step0 raw36426; decide +kernel
      have hl : raw36426step0Labels = raw36426Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36426 raw36426Labels permutation660 permutation2
    mixedMoment B raw36426step0 raw36426step0Labels = mixedMoment B raw36426step1 raw36426step1Labels := by
      have ha : raw36426step1 = -raw36426step0 := by apply Matrix.ext; change ∀ i j, raw36426step1 i j = -(raw36426step0 i j); unfold raw36426step1 raw36426step0; decide +kernel
      have hl : raw36426step1Labels = raw36426step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5417 node5417Labels := by rfl

def raw36427 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36427Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36427step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw36427step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36427step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw36427step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36427step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36427step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36427 raw36427Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw36427 raw36427Labels = mixedMoment B raw36427step0 raw36427step0Labels := by
      have hz : ∀ j, raw36427 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw36427step0 = (fun i j => raw36427 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw36427step0 raw36427; decide +kernel
      have hl : raw36427step0Labels = raw36427Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36427 raw36427Labels permutation434 hz
    mixedMoment B raw36427step0 raw36427step0Labels = mixedMoment B raw36427step1 raw36427step1Labels := by
      have ha : raw36427step1 = (fun i j => raw36427step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36427step1 raw36427step0; decide +kernel
      have hl : raw36427step1Labels = raw36427step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36427step0 raw36427step0Labels permutation150 permutation2
    mixedMoment B raw36427step1 raw36427step1Labels = mixedMoment B raw36427step2 raw36427step2Labels := by
      have ha : raw36427step2 = -raw36427step1 := by apply Matrix.ext; change ∀ i j, raw36427step2 i j = -(raw36427step1 i j); unfold raw36427step2 raw36427step1; decide +kernel
      have hl : raw36427step2Labels = raw36427step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5435 node5435Labels := by rfl

def raw36428 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw36428Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36428step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, 0, -2]]
def raw36428step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36428step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw36428step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36428step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36428step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36428 raw36428Labels = mixedMoment B node5435 node5435Labels := by
  calc
    mixedMoment B raw36428 raw36428Labels = mixedMoment B raw36428step0 raw36428step0Labels := by
      have hz : ∀ j, raw36428 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36428step0 = (fun i j => raw36428 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36428step0 raw36428; decide +kernel
      have hl : raw36428step0Labels = raw36428Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36428 raw36428Labels permutation520 hz
    mixedMoment B raw36428step0 raw36428step0Labels = mixedMoment B raw36428step1 raw36428step1Labels := by
      have ha : raw36428step1 = (fun i j => raw36428step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36428step1 raw36428step0; decide +kernel
      have hl : raw36428step1Labels = raw36428step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36428step0 raw36428step0Labels permutation150 permutation2
    mixedMoment B raw36428step1 raw36428step1Labels = mixedMoment B raw36428step2 raw36428step2Labels := by
      have ha : raw36428step2 = -raw36428step1 := by apply Matrix.ext; change ∀ i j, raw36428step2 i j = -(raw36428step1 i j); unfold raw36428step2 raw36428step1; decide +kernel
      have hl : raw36428step2Labels = raw36428step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5435 node5435Labels := by rfl

def raw36429 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 3, 0], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36429Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36429step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36429step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36429step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36429step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36429 raw36429Labels = mixedMoment B node4648 node4648Labels := by
  calc
    mixedMoment B raw36429 raw36429Labels = mixedMoment B raw36429step0 raw36429step0Labels := by
      have ha : raw36429step0 = (fun i j => raw36429 (permutation273 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36429step0 raw36429; decide +kernel
      have hl : raw36429step0Labels = raw36429Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36429 raw36429Labels permutation273 permutation3
    mixedMoment B raw36429step0 raw36429step0Labels = mixedMoment B raw36429step1 raw36429step1Labels := by
      have ha : raw36429step1 = raw36429step0 := by apply Matrix.ext; unfold raw36429step1 raw36429step0; decide +kernel
      have hl : raw36429step0Labels = labelEmbedding6 ∘ raw36429step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36429step0 raw36429step0Labels raw36429step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4648 node4648Labels := by rfl

def raw36430 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![0, 0, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36430Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw36430step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36430step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36430step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36430step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36430step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36430 raw36430Labels = mixedMoment B node5370 node5370Labels := by
  calc
    mixedMoment B raw36430 raw36430Labels = mixedMoment B raw36430step0 raw36430step0Labels := by
      have hz : ∀ j, raw36430 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw36430step0 = (fun i j => raw36430 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw36430step0 raw36430; decide +kernel
      have hl : raw36430step0Labels = raw36430Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36430 raw36430Labels permutation434 hz
    mixedMoment B raw36430step0 raw36430step0Labels = mixedMoment B raw36430step1 raw36430step1Labels := by
      have ha : raw36430step1 = (fun i j => raw36430step0 (permutation58 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36430step1 raw36430step0; decide +kernel
      have hl : raw36430step1Labels = raw36430step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36430step0 raw36430step0Labels permutation58 permutation3
    mixedMoment B raw36430step1 raw36430step1Labels = mixedMoment B raw36430step2 raw36430step2Labels := by
      have ha : raw36430step2 = raw36430step1 := by apply Matrix.ext; unfold raw36430step2 raw36430step1; decide +kernel
      have hl : raw36430step1Labels = labelEmbedding6 ∘ raw36430step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36430step1 raw36430step1Labels raw36430step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5370 node5370Labels := by rfl

def raw36431 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw36431Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw36431step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36431step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36431step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36431step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw36431step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36431 raw36431Labels = mixedMoment B node5370 node5370Labels := by
  calc
    mixedMoment B raw36431 raw36431Labels = mixedMoment B raw36431step0 raw36431step0Labels := by
      have hz : ∀ j, raw36431 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36431step0 = (fun i j => raw36431 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36431step0 raw36431; decide +kernel
      have hl : raw36431step0Labels = raw36431Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36431 raw36431Labels permutation520 hz
    mixedMoment B raw36431step0 raw36431step0Labels = mixedMoment B raw36431step1 raw36431step1Labels := by
      have ha : raw36431step1 = (fun i j => raw36431step0 (permutation58 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36431step1 raw36431step0; decide +kernel
      have hl : raw36431step1Labels = raw36431step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36431step0 raw36431step0Labels permutation58 permutation3
    mixedMoment B raw36431step1 raw36431step1Labels = mixedMoment B raw36431step2 raw36431step2Labels := by
      have ha : raw36431step2 = raw36431step1 := by apply Matrix.ext; unfold raw36431step2 raw36431step1; decide +kernel
      have hl : raw36431step1Labels = labelEmbedding6 ∘ raw36431step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36431step1 raw36431step1Labels raw36431step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5370 node5370Labels := by rfl

def raw36432 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 3, 0], ![0, -1, 1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36432Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36432step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36432step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36432step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36432step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36432 raw36432Labels = mixedMoment B node4634 node4634Labels := by
  calc
    mixedMoment B raw36432 raw36432Labels = mixedMoment B raw36432step0 raw36432step0Labels := by
      have ha : raw36432step0 = (fun i j => raw36432 (permutation268 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36432step0 raw36432; decide +kernel
      have hl : raw36432step0Labels = raw36432Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36432 raw36432Labels permutation268 permutation3
    mixedMoment B raw36432step0 raw36432step0Labels = mixedMoment B raw36432step1 raw36432step1Labels := by
      have ha : raw36432step1 = raw36432step0 := by apply Matrix.ext; unfold raw36432step1 raw36432step0; decide +kernel
      have hl : raw36432step0Labels = labelEmbedding6 ∘ raw36432step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36432step0 raw36432step0Labels raw36432step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4634 node4634Labels := by rfl

def raw36433 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw36433Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36433step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36433step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36433step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36433step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36433 raw36433Labels = mixedMoment B node5336 node5336Labels := by
  calc
    mixedMoment B raw36433 raw36433Labels = mixedMoment B raw36433step0 raw36433step0Labels := by
      have ha : raw36433step0 = (fun i j => raw36433 (permutation268 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36433step0 raw36433; decide +kernel
      have hl : raw36433step0Labels = raw36433Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36433 raw36433Labels permutation268 permutation3
    mixedMoment B raw36433step0 raw36433step0Labels = mixedMoment B raw36433step1 raw36433step1Labels := by
      have ha : raw36433step1 = raw36433step0 := by apply Matrix.ext; unfold raw36433step1 raw36433step0; decide +kernel
      have hl : raw36433step0Labels = labelEmbedding6 ∘ raw36433step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36433step0 raw36433step0Labels raw36433step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5336 node5336Labels := by rfl

def raw36434 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw36434Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36434step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![2, -2, 0], ![2, 0, -2]]
def raw36434step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36434step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36434step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36434step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36434step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36434 raw36434Labels = mixedMoment B node5355 node5355Labels := by
  calc
    mixedMoment B raw36434 raw36434Labels = mixedMoment B raw36434step0 raw36434step0Labels := by
      have hz : ∀ j, raw36434 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36434step0 = (fun i j => raw36434 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36434step0 raw36434; decide +kernel
      have hl : raw36434step0Labels = raw36434Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36434 raw36434Labels permutation520 hz
    mixedMoment B raw36434step0 raw36434step0Labels = mixedMoment B raw36434step1 raw36434step1Labels := by
      have ha : raw36434step1 = (fun i j => raw36434step0 (permutation57 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36434step1 raw36434step0; decide +kernel
      have hl : raw36434step1Labels = raw36434step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36434step0 raw36434step0Labels permutation57 permutation3
    mixedMoment B raw36434step1 raw36434step1Labels = mixedMoment B raw36434step2 raw36434step2Labels := by
      have ha : raw36434step2 = raw36434step1 := by apply Matrix.ext; unfold raw36434step2 raw36434step1; decide +kernel
      have hl : raw36434step1Labels = labelEmbedding6 ∘ raw36434step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36434step1 raw36434step1Labels raw36434step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5355 node5355Labels := by rfl

def raw36435 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw36435Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36435step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36435step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36435step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36435step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36435 raw36435Labels = mixedMoment B node4634 node4634Labels := by
  calc
    mixedMoment B raw36435 raw36435Labels = mixedMoment B raw36435step0 raw36435step0Labels := by
      have ha : raw36435step0 = (fun i j => raw36435 (permutation266 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36435step0 raw36435; decide +kernel
      have hl : raw36435step0Labels = raw36435Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36435 raw36435Labels permutation266 permutation3
    mixedMoment B raw36435step0 raw36435step0Labels = mixedMoment B raw36435step1 raw36435step1Labels := by
      have ha : raw36435step1 = raw36435step0 := by apply Matrix.ext; unfold raw36435step1 raw36435step0; decide +kernel
      have hl : raw36435step0Labels = labelEmbedding6 ∘ raw36435step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36435step0 raw36435step0Labels raw36435step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4634 node4634Labels := by rfl

def raw36436 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw36436Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36436step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36436step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36436step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw36436step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36436 raw36436Labels = mixedMoment B node5336 node5336Labels := by
  calc
    mixedMoment B raw36436 raw36436Labels = mixedMoment B raw36436step0 raw36436step0Labels := by
      have ha : raw36436step0 = (fun i j => raw36436 (permutation266 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36436step0 raw36436; decide +kernel
      have hl : raw36436step0Labels = raw36436Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36436 raw36436Labels permutation266 permutation3
    mixedMoment B raw36436step0 raw36436step0Labels = mixedMoment B raw36436step1 raw36436step1Labels := by
      have ha : raw36436step1 = raw36436step0 := by apply Matrix.ext; unfold raw36436step1 raw36436step0; decide +kernel
      have hl : raw36436step0Labels = labelEmbedding6 ∘ raw36436step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36436step0 raw36436step0Labels raw36436step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5336 node5336Labels := by rfl

def raw36437 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 3, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw36437Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36437step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw36437step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36437step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw36437step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36437 raw36437Labels = mixedMoment B node4633 node4633Labels := by
  calc
    mixedMoment B raw36437 raw36437Labels = mixedMoment B raw36437step0 raw36437step0Labels := by
      have ha : raw36437step0 = (fun i j => raw36437 (permutation265 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36437step0 raw36437; decide +kernel
      have hl : raw36437step0Labels = raw36437Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36437 raw36437Labels permutation265 permutation3
    mixedMoment B raw36437step0 raw36437step0Labels = mixedMoment B raw36437step1 raw36437step1Labels := by
      have ha : raw36437step1 = raw36437step0 := by apply Matrix.ext; unfold raw36437step1 raw36437step0; decide +kernel
      have hl : raw36437step0Labels = labelEmbedding6 ∘ raw36437step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36437step0 raw36437step0Labels raw36437step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4633 node4633Labels := by rfl

def raw36438 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![3, -1, -2]]
def raw36438Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36438step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw36438step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36438step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36438step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36438 raw36438Labels = mixedMoment B node5117 node5117Labels := by
  calc
    mixedMoment B raw36438 raw36438Labels = mixedMoment B raw36438step0 raw36438step0Labels := by
      have ha : raw36438step0 = (fun i j => raw36438 (permutation664 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36438step0 raw36438; decide +kernel
      have hl : raw36438step0Labels = raw36438Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36438 raw36438Labels permutation664 permutation2
    mixedMoment B raw36438step0 raw36438step0Labels = mixedMoment B raw36438step1 raw36438step1Labels := by
      have ha : raw36438step1 = -raw36438step0 := by apply Matrix.ext; change ∀ i j, raw36438step1 i j = -(raw36438step0 i j); unfold raw36438step1 raw36438step0; decide +kernel
      have hl : raw36438step1Labels = raw36438step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5117 node5117Labels := by rfl

def raw36439 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![3, -1, -2]]
def raw36439Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36439step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw36439step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36439step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw36439step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36439step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36439step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36439 raw36439Labels = mixedMoment B node5152 node5152Labels := by
  calc
    mixedMoment B raw36439 raw36439Labels = mixedMoment B raw36439step0 raw36439step0Labels := by
      have hz : ∀ j, raw36439 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw36439step0 = (fun i j => raw36439 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw36439step0 raw36439; decide +kernel
      have hl : raw36439step0Labels = raw36439Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36439 raw36439Labels permutation434 hz
    mixedMoment B raw36439step0 raw36439step0Labels = mixedMoment B raw36439step1 raw36439step1Labels := by
      have ha : raw36439step1 = (fun i j => raw36439step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36439step1 raw36439step0; decide +kernel
      have hl : raw36439step1Labels = raw36439step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36439step0 raw36439step0Labels permutation151 permutation2
    mixedMoment B raw36439step1 raw36439step1Labels = mixedMoment B raw36439step2 raw36439step2Labels := by
      have ha : raw36439step2 = -raw36439step1 := by apply Matrix.ext; change ∀ i j, raw36439step2 i j = -(raw36439step1 i j); unfold raw36439step2 raw36439step1; decide +kernel
      have hl : raw36439step2Labels = raw36439step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5152 node5152Labels := by rfl

def raw36440 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![0, 0, 0], ![3, -1, -2]]
def raw36440Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![3, -1, -2]]
def raw36440step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36440step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw36440step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36440step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36440step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36440 raw36440Labels = mixedMoment B node5152 node5152Labels := by
  calc
    mixedMoment B raw36440 raw36440Labels = mixedMoment B raw36440step0 raw36440step0Labels := by
      have hz : ∀ j, raw36440 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36440step0 = (fun i j => raw36440 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36440step0 raw36440; decide +kernel
      have hl : raw36440step0Labels = raw36440Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36440 raw36440Labels permutation520 hz
    mixedMoment B raw36440step0 raw36440step0Labels = mixedMoment B raw36440step1 raw36440step1Labels := by
      have ha : raw36440step1 = (fun i j => raw36440step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36440step1 raw36440step0; decide +kernel
      have hl : raw36440step1Labels = raw36440step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36440step0 raw36440step0Labels permutation151 permutation2
    mixedMoment B raw36440step1 raw36440step1Labels = mixedMoment B raw36440step2 raw36440step2Labels := by
      have ha : raw36440step2 = -raw36440step1 := by apply Matrix.ext; change ∀ i j, raw36440step2 i j = -(raw36440step1 i j); unfold raw36440step2 raw36440step1; decide +kernel
      have hl : raw36440step2Labels = raw36440step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5152 node5152Labels := by rfl

def raw36441 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36441Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36441step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36441step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36441 raw36441Labels = mixedMoment B node5073 node5073Labels := by
  calc
    mixedMoment B raw36441 raw36441Labels = mixedMoment B raw36441step0 raw36441step0Labels := by
      have ha : raw36441step0 = (fun i j => raw36441 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36441step0 raw36441; decide +kernel
      have hl : raw36441step0Labels = raw36441Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36441 raw36441Labels permutation267 permutation2
    _ = mixedMoment B node5073 node5073Labels := by rfl

def raw36442 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36442Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36442step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36442step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36442 raw36442Labels = mixedMoment B node5401 node5401Labels := by
  calc
    mixedMoment B raw36442 raw36442Labels = mixedMoment B raw36442step0 raw36442step0Labels := by
      have ha : raw36442step0 = (fun i j => raw36442 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36442step0 raw36442; decide +kernel
      have hl : raw36442step0Labels = raw36442Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36442 raw36442Labels permutation267 permutation2
    _ = mixedMoment B node5401 node5401Labels := by rfl

def raw36443 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw36443Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36443step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36443step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36443step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36443 raw36443Labels = mixedMoment B node5410 node5410Labels := by
  calc
    mixedMoment B raw36443 raw36443Labels = mixedMoment B raw36443step0 raw36443step0Labels := by
      have hz : ∀ j, raw36443 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36443step0 = (fun i j => raw36443 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36443step0 raw36443; decide +kernel
      have hl : raw36443step0Labels = raw36443Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36443 raw36443Labels permutation520 hz
    mixedMoment B raw36443step0 raw36443step0Labels = mixedMoment B raw36443step1 raw36443step1Labels := by
      have ha : raw36443step1 = (fun i j => raw36443step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36443step1 raw36443step0; decide +kernel
      have hl : raw36443step1Labels = raw36443step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36443step0 raw36443step0Labels permutation56 permutation2
    _ = mixedMoment B node5410 node5410Labels := by rfl

def raw36444 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw36444Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36444step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw36444step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36444 raw36444Labels = mixedMoment B node5408 node5408Labels := by
  calc
    mixedMoment B raw36444 raw36444Labels = mixedMoment B raw36444step0 raw36444step0Labels := by
      have ha : raw36444step0 = (fun i j => raw36444 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36444step0 raw36444; decide +kernel
      have hl : raw36444step0Labels = raw36444Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36444 raw36444Labels permutation267 permutation2
    _ = mixedMoment B node5408 node5408Labels := by rfl

def raw36445 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36445Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36445 raw36445Labels = mixedMoment B node5471 node5471Labels := by
  calc
    _ = mixedMoment B node5471 node5471Labels := by rfl

def raw36446 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36446Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36446step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36446step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36446step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36446step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36446 raw36446Labels = mixedMoment B node4968 node4968Labels := by
  calc
    mixedMoment B raw36446 raw36446Labels = mixedMoment B raw36446step0 raw36446step0Labels := by
      have ha : raw36446step0 = (fun i j => raw36446 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36446step0 raw36446; decide +kernel
      have hl : raw36446step0Labels = raw36446Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36446 raw36446Labels permutation152 permutation3
    mixedMoment B raw36446step0 raw36446step0Labels = mixedMoment B raw36446step1 raw36446step1Labels := by
      have ha : raw36446step1 = raw36446step0 := by apply Matrix.ext; unfold raw36446step1 raw36446step0; decide +kernel
      have hl : raw36446step0Labels = labelEmbedding6 ∘ raw36446step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36446step0 raw36446step0Labels raw36446step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4968 node4968Labels := by rfl

def raw36447 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36447Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36447step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36447step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36447 raw36447Labels = mixedMoment B node4941 node4941Labels := by
  calc
    mixedMoment B raw36447 raw36447Labels = mixedMoment B raw36447step0 raw36447step0Labels := by
      have ha : raw36447step0 = (fun i j => raw36447 (permutation277 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36447step0 raw36447; decide +kernel
      have hl : raw36447step0Labels = raw36447Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36447 raw36447Labels permutation277 permutation2
    _ = mixedMoment B node4941 node4941Labels := by rfl

def raw36448 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw36448Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36448step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36448step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36448step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36448step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36448 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36448 raw36448Labels = mixedMoment B node5369 node5369Labels := by
  calc
    mixedMoment B raw36448 raw36448Labels = mixedMoment B raw36448step0 raw36448step0Labels := by
      have hz : ∀ j, raw36448 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36448step0 = (fun i j => raw36448 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36448step0 raw36448; decide +kernel
      have hl : raw36448step0Labels = raw36448Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36448 raw36448Labels permutation520 hz
    mixedMoment B raw36448step0 raw36448step0Labels = mixedMoment B raw36448step1 raw36448step1Labels := by
      have ha : raw36448step1 = (fun i j => raw36448step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36448step1 raw36448step0; decide +kernel
      have hl : raw36448step1Labels = raw36448step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36448step0 raw36448step0Labels permutation56 permutation2
    _ = mixedMoment B node5369 node5369Labels := by rfl

def raw36449 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw36449Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36449step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw36449step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36449 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36449 raw36449Labels = mixedMoment B node5366 node5366Labels := by
  calc
    mixedMoment B raw36449 raw36449Labels = mixedMoment B raw36449step0 raw36449step0Labels := by
      have ha : raw36449step0 = (fun i j => raw36449 (permutation277 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36449step0 raw36449; decide +kernel
      have hl : raw36449step0Labels = raw36449Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36449 raw36449Labels permutation277 permutation2
    _ = mixedMoment B node5366 node5366Labels := by rfl

def raw36450 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36450Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36450step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36450step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36450step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36450step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36450 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36450 raw36450Labels = mixedMoment B node4958 node4958Labels := by
  calc
    mixedMoment B raw36450 raw36450Labels = mixedMoment B raw36450step0 raw36450step0Labels := by
      have ha : raw36450step0 = (fun i j => raw36450 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36450step0 raw36450; decide +kernel
      have hl : raw36450step0Labels = raw36450Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36450 raw36450Labels permutation154 permutation3
    mixedMoment B raw36450step0 raw36450step0Labels = mixedMoment B raw36450step1 raw36450step1Labels := by
      have ha : raw36450step1 = raw36450step0 := by apply Matrix.ext; unfold raw36450step1 raw36450step0; decide +kernel
      have hl : raw36450step0Labels = labelEmbedding6 ∘ raw36450step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36450step0 raw36450step0Labels raw36450step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4958 node4958Labels := by rfl

def raw36451 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36451Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36451step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw36451step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36451 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36451 raw36451Labels = mixedMoment B node4932 node4932Labels := by
  calc
    mixedMoment B raw36451 raw36451Labels = mixedMoment B raw36451step0 raw36451step0Labels := by
      have ha : raw36451step0 = (fun i j => raw36451 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36451step0 raw36451; decide +kernel
      have hl : raw36451step0Labels = raw36451Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36451 raw36451Labels permutation267 permutation2
    _ = mixedMoment B node4932 node4932Labels := by rfl

def raw36452 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 2, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36452Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36452step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw36452step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36452 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36452 raw36452Labels = mixedMoment B node5340 node5340Labels := by
  calc
    mixedMoment B raw36452 raw36452Labels = mixedMoment B raw36452step0 raw36452step0Labels := by
      have ha : raw36452step0 = (fun i j => raw36452 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36452step0 raw36452; decide +kernel
      have hl : raw36452step0Labels = raw36452Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36452 raw36452Labels permutation267 permutation2
    _ = mixedMoment B node5340 node5340Labels := by rfl

def raw36453 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw36453Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36453step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36453step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36453step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36453step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36453 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36453 raw36453Labels = mixedMoment B node5356 node5356Labels := by
  calc
    mixedMoment B raw36453 raw36453Labels = mixedMoment B raw36453step0 raw36453step0Labels := by
      have hz : ∀ j, raw36453 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36453step0 = (fun i j => raw36453 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36453step0 raw36453; decide +kernel
      have hl : raw36453step0Labels = raw36453Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36453 raw36453Labels permutation520 hz
    mixedMoment B raw36453step0 raw36453step0Labels = mixedMoment B raw36453step1 raw36453step1Labels := by
      have ha : raw36453step1 = (fun i j => raw36453step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36453step1 raw36453step0; decide +kernel
      have hl : raw36453step1Labels = raw36453step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36453step0 raw36453step0Labels permutation56 permutation2
    _ = mixedMoment B node5356 node5356Labels := by rfl

def raw36454 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw36454Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36454step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw36454step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36454 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36454 raw36454Labels = mixedMoment B node5352 node5352Labels := by
  calc
    mixedMoment B raw36454 raw36454Labels = mixedMoment B raw36454step0 raw36454step0Labels := by
      have ha : raw36454step0 = (fun i j => raw36454 (permutation268 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36454step0 raw36454; decide +kernel
      have hl : raw36454step0Labels = raw36454Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36454 raw36454Labels permutation268 permutation2
    _ = mixedMoment B node5352 node5352Labels := by rfl

def raw36455 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36455Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36455step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36455step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36455step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw36455step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36455 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36455 raw36455Labels = mixedMoment B node4955 node4955Labels := by
  calc
    mixedMoment B raw36455 raw36455Labels = mixedMoment B raw36455step0 raw36455step0Labels := by
      have ha : raw36455step0 = (fun i j => raw36455 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36455step0 raw36455; decide +kernel
      have hl : raw36455step0Labels = raw36455Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36455 raw36455Labels permutation153 permutation3
    mixedMoment B raw36455step0 raw36455step0Labels = mixedMoment B raw36455step1 raw36455step1Labels := by
      have ha : raw36455step1 = raw36455step0 := by apply Matrix.ext; unfold raw36455step1 raw36455step0; decide +kernel
      have hl : raw36455step0Labels = labelEmbedding6 ∘ raw36455step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36455step0 raw36455step0Labels raw36455step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4955 node4955Labels := by rfl

def raw36456 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36456Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36456step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36456step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36456 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36456 raw36456Labels = mixedMoment B node4933 node4933Labels := by
  calc
    mixedMoment B raw36456 raw36456Labels = mixedMoment B raw36456step0 raw36456step0Labels := by
      have ha : raw36456step0 = (fun i j => raw36456 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36456step0 raw36456; decide +kernel
      have hl : raw36456step0Labels = raw36456Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36456 raw36456Labels permutation265 permutation2
    _ = mixedMoment B node4933 node4933Labels := by rfl

def raw36457 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36457Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36457step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![2, -1, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw36457step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36457step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36457step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36457step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36457step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36457 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36457 raw36457Labels = mixedMoment B node5338 node5338Labels := by
  calc
    mixedMoment B raw36457 raw36457Labels = mixedMoment B raw36457step0 raw36457step0Labels := by
      have ha : raw36457step0 = (fun i j => raw36457 (permutation589 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36457step0 raw36457; decide +kernel
      have hl : raw36457step0Labels = raw36457Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36457 raw36457Labels permutation589 permutation3
    mixedMoment B raw36457step0 raw36457step0Labels = mixedMoment B raw36457step1 raw36457step1Labels := by
      have ha : raw36457step1 = -raw36457step0 := by apply Matrix.ext; change ∀ i j, raw36457step1 i j = -(raw36457step0 i j); unfold raw36457step1 raw36457step0; decide +kernel
      have hl : raw36457step1Labels = raw36457step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36457step1 raw36457step1Labels = mixedMoment B raw36457step2 raw36457step2Labels := by
      have ha : raw36457step2 = raw36457step1 := by apply Matrix.ext; unfold raw36457step2 raw36457step1; decide +kernel
      have hl : raw36457step1Labels = labelEmbedding6 ∘ raw36457step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36457step1 raw36457step1Labels raw36457step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5338 node5338Labels := by rfl

def raw36458 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![1, 0, -1]]
def raw36458Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36458step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw36458step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36458 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36458 raw36458Labels = mixedMoment B node5354 node5354Labels := by
  calc
    mixedMoment B raw36458 raw36458Labels = mixedMoment B raw36458step0 raw36458step0Labels := by
      have ha : raw36458step0 = (fun i j => raw36458 (permutation266 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36458step0 raw36458; decide +kernel
      have hl : raw36458step0Labels = raw36458Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36458 raw36458Labels permutation266 permutation2
    _ = mixedMoment B node5354 node5354Labels := by rfl

def raw36459 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw36459Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36459step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw36459step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36459step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw36459step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36459 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36459 raw36459Labels = mixedMoment B node4954 node4954Labels := by
  calc
    mixedMoment B raw36459 raw36459Labels = mixedMoment B raw36459step0 raw36459step0Labels := by
      have ha : raw36459step0 = (fun i j => raw36459 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36459step0 raw36459; decide +kernel
      have hl : raw36459step0Labels = raw36459Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36459 raw36459Labels permutation152 permutation3
    mixedMoment B raw36459step0 raw36459step0Labels = mixedMoment B raw36459step1 raw36459step1Labels := by
      have ha : raw36459step1 = raw36459step0 := by apply Matrix.ext; unfold raw36459step1 raw36459step0; decide +kernel
      have hl : raw36459step0Labels = labelEmbedding6 ∘ raw36459step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36459step0 raw36459step0Labels raw36459step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4954 node4954Labels := by rfl

def raw36460 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw36460Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36460step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![3, -2, -1]]
def raw36460step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36460 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36460 raw36460Labels = mixedMoment B node4930 node4930Labels := by
  calc
    mixedMoment B raw36460 raw36460Labels = mixedMoment B raw36460step0 raw36460step0Labels := by
      have ha : raw36460step0 = (fun i j => raw36460 (permutation267 i) (permutation2 j)) := by apply Matrix.ext; unfold raw36460step0 raw36460; decide +kernel
      have hl : raw36460step0Labels = raw36460Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36460 raw36460Labels permutation267 permutation2
    _ = mixedMoment B node4930 node4930Labels := by rfl

def raw36461 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![3, -2, -1]]
def raw36461Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36461step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, 2, 0], ![-2, 1, 1]]
def raw36461step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36461step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36461step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36461step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw36461step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36461 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36461 raw36461Labels = mixedMoment B node5040 node5040Labels := by
  calc
    mixedMoment B raw36461 raw36461Labels = mixedMoment B raw36461step0 raw36461step0Labels := by
      have ha : raw36461step0 = (fun i j => raw36461 (permutation688 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36461step0 raw36461; decide +kernel
      have hl : raw36461step0Labels = raw36461Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36461 raw36461Labels permutation688 permutation3
    mixedMoment B raw36461step0 raw36461step0Labels = mixedMoment B raw36461step1 raw36461step1Labels := by
      have ha : raw36461step1 = -raw36461step0 := by apply Matrix.ext; change ∀ i j, raw36461step1 i j = -(raw36461step0 i j); unfold raw36461step1 raw36461step0; decide +kernel
      have hl : raw36461step1Labels = raw36461step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36461step1 raw36461step1Labels = mixedMoment B raw36461step2 raw36461step2Labels := by
      have ha : raw36461step2 = raw36461step1 := by apply Matrix.ext; unfold raw36461step2 raw36461step1; decide +kernel
      have hl : raw36461step1Labels = labelEmbedding6 ∘ raw36461step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36461step1 raw36461step1Labels raw36461step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5040 node5040Labels := by rfl

def raw36462 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![3, -2, -1]]
def raw36462Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36462step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw36462step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw36462step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 1, 1]]
def raw36462step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36462step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36462step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw36462step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36462step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical36462 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36462 raw36462Labels = mixedMoment B node5152 node5152Labels := by
  calc
    mixedMoment B raw36462 raw36462Labels = mixedMoment B raw36462step0 raw36462step0Labels := by
      have hz : ∀ j, raw36462 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36462step0 = (fun i j => raw36462 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36462step0 raw36462; decide +kernel
      have hl : raw36462step0Labels = raw36462Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36462 raw36462Labels permutation520 hz
    mixedMoment B raw36462step0 raw36462step0Labels = mixedMoment B raw36462step1 raw36462step1Labels := by
      have ha : raw36462step1 = (fun i j => raw36462step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw36462step1 raw36462step0; decide +kernel
      have hl : raw36462step1Labels = raw36462step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36462step0 raw36462step0Labels permutation151 permutation3
    mixedMoment B raw36462step1 raw36462step1Labels = mixedMoment B raw36462step2 raw36462step2Labels := by
      have ha : raw36462step2 = -raw36462step1 := by apply Matrix.ext; change ∀ i j, raw36462step2 i j = -(raw36462step1 i j); unfold raw36462step2 raw36462step1; decide +kernel
      have hl : raw36462step2Labels = raw36462step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36462step2 raw36462step2Labels = mixedMoment B raw36462step3 raw36462step3Labels := by
      have ha : raw36462step3 = raw36462step2 := by apply Matrix.ext; unfold raw36462step3 raw36462step2; decide +kernel
      have hl : raw36462step2Labels = labelEmbedding6 ∘ raw36462step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36462step2 raw36462step2Labels raw36462step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5152 node5152Labels := by rfl

def raw36463 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36463Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36463step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw36463step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36463step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36463step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36463step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36463step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36463 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36463 raw36463Labels = mixedMoment B node3467 node3467Labels := by
  calc
    mixedMoment B raw36463 raw36463Labels = mixedMoment B raw36463step0 raw36463step0Labels := by
      have ha : raw36463step0 = (fun i j => raw36463 (permutation277 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36463step0 raw36463; decide +kernel
      have hl : raw36463step0Labels = raw36463Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36463 raw36463Labels permutation277 permutation7
    mixedMoment B raw36463step0 raw36463step0Labels = mixedMoment B raw36463step1 raw36463step1Labels := by
      have ha : raw36463step1 = -raw36463step0 := by apply Matrix.ext; change ∀ i j, raw36463step1 i j = -(raw36463step0 i j); unfold raw36463step1 raw36463step0; decide +kernel
      have hl : raw36463step1Labels = raw36463step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36463step1 raw36463step1Labels = mixedMoment B raw36463step2 raw36463step2Labels := by
      have ha : raw36463step2 = raw36463step1 := by apply Matrix.ext; unfold raw36463step2 raw36463step1; decide +kernel
      have hl : raw36463step1Labels = labelEmbedding1 ∘ raw36463step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36463step1 raw36463step1Labels raw36463step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3467 node3467Labels := by rfl

def raw36464 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36464Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36464step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw36464step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36464step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw36464step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36464step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw36464step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36464 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36464 raw36464Labels = mixedMoment B node3804 node3804Labels := by
  calc
    mixedMoment B raw36464 raw36464Labels = mixedMoment B raw36464step0 raw36464step0Labels := by
      have ha : raw36464step0 = (fun i j => raw36464 (permutation277 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36464step0 raw36464; decide +kernel
      have hl : raw36464step0Labels = raw36464Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36464 raw36464Labels permutation277 permutation7
    mixedMoment B raw36464step0 raw36464step0Labels = mixedMoment B raw36464step1 raw36464step1Labels := by
      have ha : raw36464step1 = -raw36464step0 := by apply Matrix.ext; change ∀ i j, raw36464step1 i j = -(raw36464step0 i j); unfold raw36464step1 raw36464step0; decide +kernel
      have hl : raw36464step1Labels = raw36464step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36464step1 raw36464step1Labels = mixedMoment B raw36464step2 raw36464step2Labels := by
      have ha : raw36464step2 = raw36464step1 := by apply Matrix.ext; unfold raw36464step2 raw36464step1; decide +kernel
      have hl : raw36464step1Labels = labelEmbedding1 ∘ raw36464step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36464step1 raw36464step1Labels raw36464step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3804 node3804Labels := by rfl

def raw36465 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw36465Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36465step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36465step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36465step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw36465step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36465step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36465step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36465step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36465step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36465 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36465 raw36465Labels = mixedMoment B node3816 node3816Labels := by
  calc
    mixedMoment B raw36465 raw36465Labels = mixedMoment B raw36465step0 raw36465step0Labels := by
      have hz : ∀ j, raw36465 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36465step0 = (fun i j => raw36465 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36465step0 raw36465; decide +kernel
      have hl : raw36465step0Labels = raw36465Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36465 raw36465Labels permutation520 hz
    mixedMoment B raw36465step0 raw36465step0Labels = mixedMoment B raw36465step1 raw36465step1Labels := by
      have ha : raw36465step1 = (fun i j => raw36465step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36465step1 raw36465step0; decide +kernel
      have hl : raw36465step1Labels = raw36465step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36465step0 raw36465step0Labels permutation56 permutation7
    mixedMoment B raw36465step1 raw36465step1Labels = mixedMoment B raw36465step2 raw36465step2Labels := by
      have ha : raw36465step2 = -raw36465step1 := by apply Matrix.ext; change ∀ i j, raw36465step2 i j = -(raw36465step1 i j); unfold raw36465step2 raw36465step1; decide +kernel
      have hl : raw36465step2Labels = raw36465step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36465step2 raw36465step2Labels = mixedMoment B raw36465step3 raw36465step3Labels := by
      have ha : raw36465step3 = raw36465step2 := by apply Matrix.ext; unfold raw36465step3 raw36465step2; decide +kernel
      have hl : raw36465step2Labels = labelEmbedding1 ∘ raw36465step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36465step2 raw36465step2Labels raw36465step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3816 node3816Labels := by rfl

def raw36466 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw36466Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36466step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw36466step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36466step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw36466step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36466step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw36466step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36466 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36466 raw36466Labels = mixedMoment B node3806 node3806Labels := by
  calc
    mixedMoment B raw36466 raw36466Labels = mixedMoment B raw36466step0 raw36466step0Labels := by
      have ha : raw36466step0 = (fun i j => raw36466 (permutation277 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36466step0 raw36466; decide +kernel
      have hl : raw36466step0Labels = raw36466Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36466 raw36466Labels permutation277 permutation7
    mixedMoment B raw36466step0 raw36466step0Labels = mixedMoment B raw36466step1 raw36466step1Labels := by
      have ha : raw36466step1 = -raw36466step0 := by apply Matrix.ext; change ∀ i j, raw36466step1 i j = -(raw36466step0 i j); unfold raw36466step1 raw36466step0; decide +kernel
      have hl : raw36466step1Labels = raw36466step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36466step1 raw36466step1Labels = mixedMoment B raw36466step2 raw36466step2Labels := by
      have ha : raw36466step2 = raw36466step1 := by apply Matrix.ext; unfold raw36466step2 raw36466step1; decide +kernel
      have hl : raw36466step1Labels = labelEmbedding1 ∘ raw36466step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36466step1 raw36466step1Labels raw36466step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3806 node3806Labels := by rfl

def raw36467 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36467Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36467step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw36467step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36467step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw36467step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36467step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw36467step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36467 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36467 raw36467Labels = mixedMoment B node3956 node3956Labels := by
  calc
    mixedMoment B raw36467 raw36467Labels = mixedMoment B raw36467step0 raw36467step0Labels := by
      have ha : raw36467step0 = (fun i j => raw36467 (permutation277 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36467step0 raw36467; decide +kernel
      have hl : raw36467step0Labels = raw36467Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36467 raw36467Labels permutation277 permutation7
    mixedMoment B raw36467step0 raw36467step0Labels = mixedMoment B raw36467step1 raw36467step1Labels := by
      have ha : raw36467step1 = -raw36467step0 := by apply Matrix.ext; change ∀ i j, raw36467step1 i j = -(raw36467step0 i j); unfold raw36467step1 raw36467step0; decide +kernel
      have hl : raw36467step1Labels = raw36467step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36467step1 raw36467step1Labels = mixedMoment B raw36467step2 raw36467step2Labels := by
      have ha : raw36467step2 = raw36467step1 := by apply Matrix.ext; unfold raw36467step2 raw36467step1; decide +kernel
      have hl : raw36467step1Labels = labelEmbedding1 ∘ raw36467step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36467step1 raw36467step1Labels raw36467step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3956 node3956Labels := by rfl

def raw36468 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36468Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36468step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw36468step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36468step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw36468step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36468step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw36468step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36468 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36468 raw36468Labels = mixedMoment B node3587 node3587Labels := by
  calc
    mixedMoment B raw36468 raw36468Labels = mixedMoment B raw36468step0 raw36468step0Labels := by
      have ha : raw36468step0 = (fun i j => raw36468 (permutation152 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36468step0 raw36468; decide +kernel
      have hl : raw36468step0Labels = raw36468Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36468 raw36468Labels permutation152 permutation5
    mixedMoment B raw36468step0 raw36468step0Labels = mixedMoment B raw36468step1 raw36468step1Labels := by
      have ha : raw36468step1 = -raw36468step0 := by apply Matrix.ext; change ∀ i j, raw36468step1 i j = -(raw36468step0 i j); unfold raw36468step1 raw36468step0; decide +kernel
      have hl : raw36468step1Labels = raw36468step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36468step1 raw36468step1Labels = mixedMoment B raw36468step2 raw36468step2Labels := by
      have ha : raw36468step2 = raw36468step1 := by apply Matrix.ext; unfold raw36468step2 raw36468step1; decide +kernel
      have hl : raw36468step1Labels = labelEmbedding1 ∘ raw36468step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36468step1 raw36468step1Labels raw36468step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3587 node3587Labels := by rfl

def raw36469 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36469Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36469step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw36469step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36469step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw36469step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36469step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw36469step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36469 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36469 raw36469Labels = mixedMoment B node3410 node3410Labels := by
  calc
    mixedMoment B raw36469 raw36469Labels = mixedMoment B raw36469step0 raw36469step0Labels := by
      have ha : raw36469step0 = (fun i j => raw36469 (permutation277 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36469step0 raw36469; decide +kernel
      have hl : raw36469step0Labels = raw36469Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36469 raw36469Labels permutation277 permutation7
    mixedMoment B raw36469step0 raw36469step0Labels = mixedMoment B raw36469step1 raw36469step1Labels := by
      have ha : raw36469step1 = -raw36469step0 := by apply Matrix.ext; change ∀ i j, raw36469step1 i j = -(raw36469step0 i j); unfold raw36469step1 raw36469step0; decide +kernel
      have hl : raw36469step1Labels = raw36469step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36469step1 raw36469step1Labels = mixedMoment B raw36469step2 raw36469step2Labels := by
      have ha : raw36469step2 = raw36469step1 := by apply Matrix.ext; unfold raw36469step2 raw36469step1; decide +kernel
      have hl : raw36469step1Labels = labelEmbedding1 ∘ raw36469step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36469step1 raw36469step1Labels raw36469step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3410 node3410Labels := by rfl

def raw36470 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0], ![2, -1, -1]]
def raw36470Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36470step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw36470step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36470step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw36470step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36470step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw36470step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36470step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw36470step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36470 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36470 raw36470Labels = mixedMoment B node3774 node3774Labels := by
  calc
    mixedMoment B raw36470 raw36470Labels = mixedMoment B raw36470step0 raw36470step0Labels := by
      have hz : ∀ j, raw36470 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36470step0 = (fun i j => raw36470 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36470step0 raw36470; decide +kernel
      have hl : raw36470step0Labels = raw36470Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36470 raw36470Labels permutation520 hz
    mixedMoment B raw36470step0 raw36470step0Labels = mixedMoment B raw36470step1 raw36470step1Labels := by
      have ha : raw36470step1 = (fun i j => raw36470step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36470step1 raw36470step0; decide +kernel
      have hl : raw36470step1Labels = raw36470step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36470step0 raw36470step0Labels permutation56 permutation7
    mixedMoment B raw36470step1 raw36470step1Labels = mixedMoment B raw36470step2 raw36470step2Labels := by
      have ha : raw36470step2 = -raw36470step1 := by apply Matrix.ext; change ∀ i j, raw36470step2 i j = -(raw36470step1 i j); unfold raw36470step2 raw36470step1; decide +kernel
      have hl : raw36470step2Labels = raw36470step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36470step2 raw36470step2Labels = mixedMoment B raw36470step3 raw36470step3Labels := by
      have ha : raw36470step3 = raw36470step2 := by apply Matrix.ext; unfold raw36470step3 raw36470step2; decide +kernel
      have hl : raw36470step2Labels = labelEmbedding1 ∘ raw36470step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36470step2 raw36470step2Labels raw36470step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3774 node3774Labels := by rfl

def raw36471 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0], ![1, 0, -1]]
def raw36471Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36471step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw36471step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36471step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw36471step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36471step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw36471step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36471 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36471 raw36471Labels = mixedMoment B node3765 node3765Labels := by
  calc
    mixedMoment B raw36471 raw36471Labels = mixedMoment B raw36471step0 raw36471step0Labels := by
      have ha : raw36471step0 = (fun i j => raw36471 (permutation277 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36471step0 raw36471; decide +kernel
      have hl : raw36471step0Labels = raw36471Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36471 raw36471Labels permutation277 permutation7
    mixedMoment B raw36471step0 raw36471step0Labels = mixedMoment B raw36471step1 raw36471step1Labels := by
      have ha : raw36471step1 = -raw36471step0 := by apply Matrix.ext; change ∀ i j, raw36471step1 i j = -(raw36471step0 i j); unfold raw36471step1 raw36471step0; decide +kernel
      have hl : raw36471step1Labels = raw36471step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36471step1 raw36471step1Labels = mixedMoment B raw36471step2 raw36471step2Labels := by
      have ha : raw36471step2 = raw36471step1 := by apply Matrix.ext; unfold raw36471step2 raw36471step1; decide +kernel
      have hl : raw36471step1Labels = labelEmbedding1 ∘ raw36471step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36471step1 raw36471step1Labels raw36471step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3765 node3765Labels := by rfl

def raw36472 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36472Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36472step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw36472step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36472step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw36472step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36472step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw36472step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36472 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36472 raw36472Labels = mixedMoment B node3511 node3511Labels := by
  calc
    mixedMoment B raw36472 raw36472Labels = mixedMoment B raw36472step0 raw36472step0Labels := by
      have ha : raw36472step0 = (fun i j => raw36472 (permutation178 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36472step0 raw36472; decide +kernel
      have hl : raw36472step0Labels = raw36472Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36472 raw36472Labels permutation178 permutation5
    mixedMoment B raw36472step0 raw36472step0Labels = mixedMoment B raw36472step1 raw36472step1Labels := by
      have ha : raw36472step1 = -raw36472step0 := by apply Matrix.ext; change ∀ i j, raw36472step1 i j = -(raw36472step0 i j); unfold raw36472step1 raw36472step0; decide +kernel
      have hl : raw36472step1Labels = raw36472step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36472step1 raw36472step1Labels = mixedMoment B raw36472step2 raw36472step2Labels := by
      have ha : raw36472step2 = raw36472step1 := by apply Matrix.ext; unfold raw36472step2 raw36472step1; decide +kernel
      have hl : raw36472step1Labels = labelEmbedding1 ∘ raw36472step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36472step1 raw36472step1Labels raw36472step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3511 node3511Labels := by rfl

def raw36473 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36473Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36473step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw36473step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36473step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36473step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36473step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36473step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36473 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36473 raw36473Labels = mixedMoment B node3409 node3409Labels := by
  calc
    mixedMoment B raw36473 raw36473Labels = mixedMoment B raw36473step0 raw36473step0Labels := by
      have ha : raw36473step0 = (fun i j => raw36473 (permutation277 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36473step0 raw36473; decide +kernel
      have hl : raw36473step0Labels = raw36473Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36473 raw36473Labels permutation277 permutation7
    mixedMoment B raw36473step0 raw36473step0Labels = mixedMoment B raw36473step1 raw36473step1Labels := by
      have ha : raw36473step1 = -raw36473step0 := by apply Matrix.ext; change ∀ i j, raw36473step1 i j = -(raw36473step0 i j); unfold raw36473step1 raw36473step0; decide +kernel
      have hl : raw36473step1Labels = raw36473step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36473step1 raw36473step1Labels = mixedMoment B raw36473step2 raw36473step2Labels := by
      have ha : raw36473step2 = raw36473step1 := by apply Matrix.ext; unfold raw36473step2 raw36473step1; decide +kernel
      have hl : raw36473step1Labels = labelEmbedding1 ∘ raw36473step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36473step1 raw36473step1Labels raw36473step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3409 node3409Labels := by rfl

def raw36474 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 2, -1], ![2, -1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw36474Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36474step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 2, -1], ![-1, -1, 2], ![-1, -1, 2]]
def raw36474step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36474step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36474step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36474step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 1, -2], ![1, 1, -2]]
def raw36474step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36474 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36474 raw36474Labels = mixedMoment B node3763 node3763Labels := by
  calc
    mixedMoment B raw36474 raw36474Labels = mixedMoment B raw36474step0 raw36474step0Labels := by
      have ha : raw36474step0 = (fun i j => raw36474 (permutation277 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36474step0 raw36474; decide +kernel
      have hl : raw36474step0Labels = raw36474Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36474 raw36474Labels permutation277 permutation7
    mixedMoment B raw36474step0 raw36474step0Labels = mixedMoment B raw36474step1 raw36474step1Labels := by
      have ha : raw36474step1 = -raw36474step0 := by apply Matrix.ext; change ∀ i j, raw36474step1 i j = -(raw36474step0 i j); unfold raw36474step1 raw36474step0; decide +kernel
      have hl : raw36474step1Labels = raw36474step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36474step1 raw36474step1Labels = mixedMoment B raw36474step2 raw36474step2Labels := by
      have ha : raw36474step2 = raw36474step1 := by apply Matrix.ext; unfold raw36474step2 raw36474step1; decide +kernel
      have hl : raw36474step1Labels = labelEmbedding1 ∘ raw36474step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36474step1 raw36474step1Labels raw36474step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3763 node3763Labels := by rfl

def raw36475 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![0, 0, 0], ![2, -1, -1]]
def raw36475Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36475step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw36475step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36475step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw36475step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36475step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36475step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36475step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw36475step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36475 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36475 raw36475Labels = mixedMoment B node3773 node3773Labels := by
  calc
    mixedMoment B raw36475 raw36475Labels = mixedMoment B raw36475step0 raw36475step0Labels := by
      have hz : ∀ j, raw36475 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw36475step0 = (fun i j => raw36475 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw36475step0 raw36475; decide +kernel
      have hl : raw36475step0Labels = raw36475Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw36475 raw36475Labels permutation520 hz
    mixedMoment B raw36475step0 raw36475step0Labels = mixedMoment B raw36475step1 raw36475step1Labels := by
      have ha : raw36475step1 = (fun i j => raw36475step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36475step1 raw36475step0; decide +kernel
      have hl : raw36475step1Labels = raw36475step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36475step0 raw36475step0Labels permutation56 permutation7
    mixedMoment B raw36475step1 raw36475step1Labels = mixedMoment B raw36475step2 raw36475step2Labels := by
      have ha : raw36475step2 = -raw36475step1 := by apply Matrix.ext; change ∀ i j, raw36475step2 i j = -(raw36475step1 i j); unfold raw36475step2 raw36475step1; decide +kernel
      have hl : raw36475step2Labels = raw36475step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36475step2 raw36475step2Labels = mixedMoment B raw36475step3 raw36475step3Labels := by
      have ha : raw36475step3 = raw36475step2 := by apply Matrix.ext; unfold raw36475step3 raw36475step2; decide +kernel
      have hl : raw36475step2Labels = labelEmbedding1 ∘ raw36475step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36475step2 raw36475step2Labels raw36475step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3773 node3773Labels := by rfl

def raw36476 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0], ![1, 0, -1]]
def raw36476Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36476step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw36476step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36476step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36476step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36476step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36476step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36476 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36476 raw36476Labels = mixedMoment B node3764 node3764Labels := by
  calc
    mixedMoment B raw36476 raw36476Labels = mixedMoment B raw36476step0 raw36476step0Labels := by
      have ha : raw36476step0 = (fun i j => raw36476 (permutation278 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36476step0 raw36476; decide +kernel
      have hl : raw36476step0Labels = raw36476Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36476 raw36476Labels permutation278 permutation7
    mixedMoment B raw36476step0 raw36476step0Labels = mixedMoment B raw36476step1 raw36476step1Labels := by
      have ha : raw36476step1 = -raw36476step0 := by apply Matrix.ext; change ∀ i j, raw36476step1 i j = -(raw36476step0 i j); unfold raw36476step1 raw36476step0; decide +kernel
      have hl : raw36476step1Labels = raw36476step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36476step1 raw36476step1Labels = mixedMoment B raw36476step2 raw36476step2Labels := by
      have ha : raw36476step2 = raw36476step1 := by apply Matrix.ext; unfold raw36476step2 raw36476step1; decide +kernel
      have hl : raw36476step1Labels = labelEmbedding1 ∘ raw36476step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36476step1 raw36476step1Labels raw36476step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3764 node3764Labels := by rfl

def raw36477 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 0, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36477Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36477step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 2, -2], ![0, -1, 1], ![-1, -1, 2], ![-2, 0, 2]]
def raw36477step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36477step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36477step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36477step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![0, 1, -1], ![1, 1, -2], ![2, 0, -2]]
def raw36477step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36477 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36477 raw36477Labels = mixedMoment B node3508 node3508Labels := by
  calc
    mixedMoment B raw36477 raw36477Labels = mixedMoment B raw36477step0 raw36477step0Labels := by
      have ha : raw36477step0 = (fun i j => raw36477 (permutation177 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36477step0 raw36477; decide +kernel
      have hl : raw36477step0Labels = raw36477Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36477 raw36477Labels permutation177 permutation5
    mixedMoment B raw36477step0 raw36477step0Labels = mixedMoment B raw36477step1 raw36477step1Labels := by
      have ha : raw36477step1 = -raw36477step0 := by apply Matrix.ext; change ∀ i j, raw36477step1 i j = -(raw36477step0 i j); unfold raw36477step1 raw36477step0; decide +kernel
      have hl : raw36477step1Labels = raw36477step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36477step1 raw36477step1Labels = mixedMoment B raw36477step2 raw36477step2Labels := by
      have ha : raw36477step2 = raw36477step1 := by apply Matrix.ext; unfold raw36477step2 raw36477step1; decide +kernel
      have hl : raw36477step1Labels = labelEmbedding1 ∘ raw36477step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36477step1 raw36477step1Labels raw36477step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3508 node3508Labels := by rfl

def raw36478 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36478Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36478step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw36478step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36478step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36478step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36478step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw36478step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36478 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36478 raw36478Labels = mixedMoment B node3414 node3414Labels := by
  calc
    mixedMoment B raw36478 raw36478Labels = mixedMoment B raw36478step0 raw36478step0Labels := by
      have ha : raw36478step0 = (fun i j => raw36478 (permutation277 i) (permutation7 j)) := by apply Matrix.ext; unfold raw36478step0 raw36478; decide +kernel
      have hl : raw36478step0Labels = raw36478Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36478 raw36478Labels permutation277 permutation7
    mixedMoment B raw36478step0 raw36478step0Labels = mixedMoment B raw36478step1 raw36478step1Labels := by
      have ha : raw36478step1 = -raw36478step0 := by apply Matrix.ext; change ∀ i j, raw36478step1 i j = -(raw36478step0 i j); unfold raw36478step1 raw36478step0; decide +kernel
      have hl : raw36478step1Labels = raw36478step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw36478step1 raw36478step1Labels = mixedMoment B raw36478step2 raw36478step2Labels := by
      have ha : raw36478step2 = raw36478step1 := by apply Matrix.ext; unfold raw36478step2 raw36478step1; decide +kernel
      have hl : raw36478step1Labels = labelEmbedding1 ∘ raw36478step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36478step1 raw36478step1Labels raw36478step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3414 node3414Labels := by rfl

def raw36479 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 0, 2], ![-1, 2, -1], ![1, 0, -1], ![2, -2, 0], ![2, -1, -1]]
def raw36479Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw36479step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw36479step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw36479step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, -1, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw36479step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical36479 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw36479 raw36479Labels = mixedMoment B node3755 node3755Labels := by
  calc
    mixedMoment B raw36479 raw36479Labels = mixedMoment B raw36479step0 raw36479step0Labels := by
      have ha : raw36479step0 = (fun i j => raw36479 (permutation586 i) (permutation5 j)) := by apply Matrix.ext; unfold raw36479step0 raw36479; decide +kernel
      have hl : raw36479step0Labels = raw36479Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw36479 raw36479Labels permutation586 permutation5
    mixedMoment B raw36479step0 raw36479step0Labels = mixedMoment B raw36479step1 raw36479step1Labels := by
      have ha : raw36479step1 = raw36479step0 := by apply Matrix.ext; unfold raw36479step1 raw36479step0; decide +kernel
      have hl : raw36479step0Labels = labelEmbedding1 ∘ raw36479step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw36479step0 raw36479step0Labels raw36479step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3755 node3755Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
