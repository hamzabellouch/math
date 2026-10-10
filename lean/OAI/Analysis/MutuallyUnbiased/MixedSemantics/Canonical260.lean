import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes57
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw33280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw33280Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33280step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw33280step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33280step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw33280step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33280 raw33280Labels = mixedMoment B node5031 node5031Labels := by
  calc
    mixedMoment B raw33280 raw33280Labels = mixedMoment B raw33280step0 raw33280step0Labels := by
      have ha : raw33280step0 = (fun i j => raw33280 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33280step0 raw33280; decide +kernel
      have hl : raw33280step0Labels = raw33280Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33280 raw33280Labels permutation152 permutation3
    mixedMoment B raw33280step0 raw33280step0Labels = mixedMoment B raw33280step1 raw33280step1Labels := by
      have ha : raw33280step1 = raw33280step0 := by apply Matrix.ext; unfold raw33280step1 raw33280step0; decide +kernel
      have hl : raw33280step0Labels = labelEmbedding6 ∘ raw33280step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33280step0 raw33280step0Labels raw33280step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5031 node5031Labels := by rfl

def raw33281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1], ![1, 0, -1]]
def raw33281Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33281step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![1, 0, -1]]
def raw33281step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33281step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw33281step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33281step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw33281step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33281 raw33281Labels = mixedMoment B node5102 node5102Labels := by
  calc
    mixedMoment B raw33281 raw33281Labels = mixedMoment B raw33281step0 raw33281step0Labels := by
      have hz : ∀ j, raw33281 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33281step0 = (fun i j => raw33281 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33281step0 raw33281; decide +kernel
      have hl : raw33281step0Labels = raw33281Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33281 raw33281Labels permutation346 hz
    mixedMoment B raw33281step0 raw33281step0Labels = mixedMoment B raw33281step1 raw33281step1Labels := by
      have ha : raw33281step1 = (fun i j => raw33281step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33281step1 raw33281step0; decide +kernel
      have hl : raw33281step1Labels = raw33281step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33281step0 raw33281step0Labels permutation36 permutation3
    mixedMoment B raw33281step1 raw33281step1Labels = mixedMoment B raw33281step2 raw33281step2Labels := by
      have ha : raw33281step2 = raw33281step1 := by apply Matrix.ext; unfold raw33281step2 raw33281step1; decide +kernel
      have hl : raw33281step1Labels = labelEmbedding6 ∘ raw33281step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33281step1 raw33281step1Labels raw33281step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5102 node5102Labels := by rfl

def raw33282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw33282Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33282step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw33282step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33282step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw33282step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33282step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw33282step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33282 raw33282Labels = mixedMoment B node4913 node4913Labels := by
  calc
    mixedMoment B raw33282 raw33282Labels = mixedMoment B raw33282step0 raw33282step0Labels := by
      have hz : ∀ j, raw33282 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33282step0 = (fun i j => raw33282 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33282step0 raw33282; decide +kernel
      have hl : raw33282step0Labels = raw33282Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33282 raw33282Labels permutation346 hz
    mixedMoment B raw33282step0 raw33282step0Labels = mixedMoment B raw33282step1 raw33282step1Labels := by
      have ha : raw33282step1 = (fun i j => raw33282step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33282step1 raw33282step0; decide +kernel
      have hl : raw33282step1Labels = raw33282step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33282step0 raw33282step0Labels permutation34 permutation3
    mixedMoment B raw33282step1 raw33282step1Labels = mixedMoment B raw33282step2 raw33282step2Labels := by
      have ha : raw33282step2 = raw33282step1 := by apply Matrix.ext; unfold raw33282step2 raw33282step1; decide +kernel
      have hl : raw33282step1Labels = labelEmbedding6 ∘ raw33282step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33282step1 raw33282step1Labels raw33282step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4913 node4913Labels := by rfl

def raw33283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw33283Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33283step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw33283step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33283step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw33283step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33283step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw33283step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33283 raw33283Labels = mixedMoment B node4986 node4986Labels := by
  calc
    mixedMoment B raw33283 raw33283Labels = mixedMoment B raw33283step0 raw33283step0Labels := by
      have ha : raw33283step0 = (fun i j => raw33283 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33283step0 raw33283; decide +kernel
      have hl : raw33283step0Labels = raw33283Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33283 raw33283Labels permutation662 permutation3
    mixedMoment B raw33283step0 raw33283step0Labels = mixedMoment B raw33283step1 raw33283step1Labels := by
      have ha : raw33283step1 = -raw33283step0 := by apply Matrix.ext; change ∀ i j, raw33283step1 i j = -(raw33283step0 i j); unfold raw33283step1 raw33283step0; decide +kernel
      have hl : raw33283step1Labels = raw33283step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33283step1 raw33283step1Labels = mixedMoment B raw33283step2 raw33283step2Labels := by
      have ha : raw33283step2 = raw33283step1 := by apply Matrix.ext; unfold raw33283step2 raw33283step1; decide +kernel
      have hl : raw33283step1Labels = labelEmbedding6 ∘ raw33283step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33283step1 raw33283step1Labels raw33283step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4986 node4986Labels := by rfl

def raw33284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, -2, -1]]
def raw33284Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33284step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![3, -2, -1]]
def raw33284step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33284step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw33284step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33284step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw33284step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33284step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw33284step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33284 raw33284Labels = mixedMoment B node5000 node5000Labels := by
  calc
    mixedMoment B raw33284 raw33284Labels = mixedMoment B raw33284step0 raw33284step0Labels := by
      have hz : ∀ j, raw33284 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33284step0 = (fun i j => raw33284 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33284step0 raw33284; decide +kernel
      have hl : raw33284step0Labels = raw33284Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33284 raw33284Labels permutation346 hz
    mixedMoment B raw33284step0 raw33284step0Labels = mixedMoment B raw33284step1 raw33284step1Labels := by
      have ha : raw33284step1 = (fun i j => raw33284step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33284step1 raw33284step0; decide +kernel
      have hl : raw33284step1Labels = raw33284step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33284step0 raw33284step0Labels permutation145 permutation3
    mixedMoment B raw33284step1 raw33284step1Labels = mixedMoment B raw33284step2 raw33284step2Labels := by
      have ha : raw33284step2 = -raw33284step1 := by apply Matrix.ext; change ∀ i j, raw33284step2 i j = -(raw33284step1 i j); unfold raw33284step2 raw33284step1; decide +kernel
      have hl : raw33284step2Labels = raw33284step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33284step2 raw33284step2Labels = mixedMoment B raw33284step3 raw33284step3Labels := by
      have ha : raw33284step3 = raw33284step2 := by apply Matrix.ext; unfold raw33284step3 raw33284step2; decide +kernel
      have hl : raw33284step2Labels = labelEmbedding6 ∘ raw33284step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33284step2 raw33284step2Labels raw33284step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5000 node5000Labels := by rfl

def raw33285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw33285Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33285step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw33285step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33285step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw33285step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33285 raw33285Labels = mixedMoment B node3705 node3705Labels := by
  calc
    mixedMoment B raw33285 raw33285Labels = mixedMoment B raw33285step0 raw33285step0Labels := by
      have hz : ∀ j, raw33285 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33285step0 = (fun i j => raw33285 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33285step0 raw33285; decide +kernel
      have hl : raw33285step0Labels = raw33285Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33285 raw33285Labels permutation346 hz
    mixedMoment B raw33285step0 raw33285step0Labels = mixedMoment B raw33285step1 raw33285step1Labels := by
      have ha : raw33285step1 = (fun i j => raw33285step0 (permutation58 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33285step1 raw33285step0; decide +kernel
      have hl : raw33285step1Labels = raw33285step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33285step0 raw33285step0Labels permutation58 permutation3
    _ = mixedMoment B node3705 node3705Labels := by rfl

def raw33286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw33286Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33286step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw33286step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33286step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33286step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33286 raw33286Labels = mixedMoment B node3945 node3945Labels := by
  calc
    mixedMoment B raw33286 raw33286Labels = mixedMoment B raw33286step0 raw33286step0Labels := by
      have ha : raw33286step0 = (fun i j => raw33286 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33286step0 raw33286; decide +kernel
      have hl : raw33286step0Labels = raw33286Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33286 raw33286Labels permutation662 permutation3
    mixedMoment B raw33286step0 raw33286step0Labels = mixedMoment B raw33286step1 raw33286step1Labels := by
      have ha : raw33286step1 = -raw33286step0 := by apply Matrix.ext; change ∀ i j, raw33286step1 i j = -(raw33286step0 i j); unfold raw33286step1 raw33286step0; decide +kernel
      have hl : raw33286step1Labels = raw33286step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3945 node3945Labels := by rfl

def raw33287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw33287Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw33287step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33287step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw33287step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33287step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33287step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33287 raw33287Labels = mixedMoment B node3958 node3958Labels := by
  calc
    mixedMoment B raw33287 raw33287Labels = mixedMoment B raw33287step0 raw33287step0Labels := by
      have hz : ∀ j, raw33287 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33287step0 = (fun i j => raw33287 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33287step0 raw33287; decide +kernel
      have hl : raw33287step0Labels = raw33287Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33287 raw33287Labels permutation346 hz
    mixedMoment B raw33287step0 raw33287step0Labels = mixedMoment B raw33287step1 raw33287step1Labels := by
      have ha : raw33287step1 = (fun i j => raw33287step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33287step1 raw33287step0; decide +kernel
      have hl : raw33287step1Labels = raw33287step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33287step0 raw33287step0Labels permutation145 permutation3
    mixedMoment B raw33287step1 raw33287step1Labels = mixedMoment B raw33287step2 raw33287step2Labels := by
      have ha : raw33287step2 = -raw33287step1 := by apply Matrix.ext; change ∀ i j, raw33287step2 i j = -(raw33287step1 i j); unfold raw33287step2 raw33287step1; decide +kernel
      have hl : raw33287step2Labels = raw33287step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3958 node3958Labels := by rfl

def raw33288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33288Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33288step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33288step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33288step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw33288step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33288 raw33288Labels = mixedMoment B node3984 node3984Labels := by
  calc
    mixedMoment B raw33288 raw33288Labels = mixedMoment B raw33288step0 raw33288step0Labels := by
      have hz : ∀ j, raw33288 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33288step0 = (fun i j => raw33288 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33288step0 raw33288; decide +kernel
      have hl : raw33288step0Labels = raw33288Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33288 raw33288Labels permutation346 hz
    mixedMoment B raw33288step0 raw33288step0Labels = mixedMoment B raw33288step1 raw33288step1Labels := by
      have ha : raw33288step1 = (fun i j => raw33288step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33288step1 raw33288step0; decide +kernel
      have hl : raw33288step1Labels = raw33288step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33288step0 raw33288step0Labels permutation35 permutation3
    _ = mixedMoment B node3984 node3984Labels := by rfl

def raw33289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw33289Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33289step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw33289step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33289 raw33289Labels = mixedMoment B node2305 node2305Labels := by
  calc
    mixedMoment B raw33289 raw33289Labels = mixedMoment B raw33289step0 raw33289step0Labels := by
      have ha : raw33289step0 = (fun i j => raw33289 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33289step0 raw33289; decide +kernel
      have hl : raw33289step0Labels = raw33289Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33289 raw33289Labels permutation164 permutation3
    _ = mixedMoment B node2305 node2305Labels := by rfl

def raw33290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![0, 1, -1], ![2, -1, -1]]
def raw33290Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33290step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw33290step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33290 raw33290Labels = mixedMoment B node2462 node2462Labels := by
  calc
    mixedMoment B raw33290 raw33290Labels = mixedMoment B raw33290step0 raw33290step0Labels := by
      have ha : raw33290step0 = (fun i j => raw33290 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33290step0 raw33290; decide +kernel
      have hl : raw33290step0Labels = raw33290Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33290 raw33290Labels permutation164 permutation3
    _ = mixedMoment B node2462 node2462Labels := by rfl

def raw33291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33291Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33291step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw33291step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33291 raw33291Labels = mixedMoment B node2508 node2508Labels := by
  calc
    mixedMoment B raw33291 raw33291Labels = mixedMoment B raw33291step0 raw33291step0Labels := by
      have ha : raw33291step0 = (fun i j => raw33291 (permutation168 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33291step0 raw33291; decide +kernel
      have hl : raw33291step0Labels = raw33291Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33291 raw33291Labels permutation168 permutation3
    _ = mixedMoment B node2508 node2508Labels := by rfl

def raw33292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, 0, 0], ![2, -3, 1], ![1, 0, -1], ![2, -1, -1]]
def raw33292Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33292step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![2, -3, 1], ![1, 0, -1], ![2, -1, -1]]
def raw33292step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33292step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw33292step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33292 raw33292Labels = mixedMoment B node2307 node2307Labels := by
  calc
    mixedMoment B raw33292 raw33292Labels = mixedMoment B raw33292step0 raw33292step0Labels := by
      have hz : ∀ j, raw33292 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33292step0 = (fun i j => raw33292 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33292step0 raw33292; decide +kernel
      have hl : raw33292step0Labels = raw33292Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33292 raw33292Labels permutation346 hz
    mixedMoment B raw33292step0 raw33292step0Labels = mixedMoment B raw33292step1 raw33292step1Labels := by
      have ha : raw33292step1 = (fun i j => raw33292step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33292step1 raw33292step0; decide +kernel
      have hl : raw33292step1Labels = raw33292step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33292step0 raw33292step0Labels permutation35 permutation3
    _ = mixedMoment B node2307 node2307Labels := by rfl

def raw33293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 1, 0], ![2, -3, 1], ![1, 0, -1], ![2, -1, -1]]
def raw33293Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33293step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw33293step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33293 raw33293Labels = mixedMoment B node2413 node2413Labels := by
  calc
    mixedMoment B raw33293 raw33293Labels = mixedMoment B raw33293step0 raw33293step0Labels := by
      have ha : raw33293step0 = (fun i j => raw33293 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33293step0 raw33293; decide +kernel
      have hl : raw33293step0Labels = raw33293Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33293 raw33293Labels permutation155 permutation3
    _ = mixedMoment B node2413 node2413Labels := by rfl

def raw33294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![0, 1, -1], ![2, -1, -1]]
def raw33294Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -3, 1], ![0, 1, -1], ![2, -1, -1]]
def raw33294step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33294step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw33294step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33294 raw33294Labels = mixedMoment B node2467 node2467Labels := by
  calc
    mixedMoment B raw33294 raw33294Labels = mixedMoment B raw33294step0 raw33294step0Labels := by
      have hz : ∀ j, raw33294 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33294step0 = (fun i j => raw33294 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33294step0 raw33294; decide +kernel
      have hl : raw33294step0Labels = raw33294Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33294 raw33294Labels permutation346 hz
    mixedMoment B raw33294step0 raw33294step0Labels = mixedMoment B raw33294step1 raw33294step1Labels := by
      have ha : raw33294step1 = (fun i j => raw33294step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33294step1 raw33294step0; decide +kernel
      have hl : raw33294step1Labels = raw33294step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33294step0 raw33294step0Labels permutation35 permutation3
    _ = mixedMoment B node2467 node2467Labels := by rfl

def raw33295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -3, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33295Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33295step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -3, 1], ![1, 0, -1], ![1, 0, -1]]
def raw33295step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33295step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33295step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33295 raw33295Labels = mixedMoment B node2509 node2509Labels := by
  calc
    mixedMoment B raw33295 raw33295Labels = mixedMoment B raw33295step0 raw33295step0Labels := by
      have hz : ∀ j, raw33295 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33295step0 = (fun i j => raw33295 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33295step0 raw33295; decide +kernel
      have hl : raw33295step0Labels = raw33295Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33295 raw33295Labels permutation346 hz
    mixedMoment B raw33295step0 raw33295step0Labels = mixedMoment B raw33295step1 raw33295step1Labels := by
      have ha : raw33295step1 = (fun i j => raw33295step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33295step1 raw33295step0; decide +kernel
      have hl : raw33295step1Labels = raw33295step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33295step0 raw33295step0Labels permutation35 permutation3
    _ = mixedMoment B node2509 node2509Labels := by rfl

def raw33296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw33296Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33296step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw33296step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33296step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw33296step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33296 raw33296Labels = mixedMoment B node2314 node2314Labels := by
  calc
    mixedMoment B raw33296 raw33296Labels = mixedMoment B raw33296step0 raw33296step0Labels := by
      have hz : ∀ j, raw33296 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33296step0 = (fun i j => raw33296 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33296step0 raw33296; decide +kernel
      have hl : raw33296step0Labels = raw33296Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33296 raw33296Labels permutation346 hz
    mixedMoment B raw33296step0 raw33296step0Labels = mixedMoment B raw33296step1 raw33296step1Labels := by
      have ha : raw33296step1 = (fun i j => raw33296step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33296step1 raw33296step0; decide +kernel
      have hl : raw33296step1Labels = raw33296step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33296step0 raw33296step0Labels permutation32 permutation3
    _ = mixedMoment B node2314 node2314Labels := by rfl

def raw33297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![2, -1, -1]]
def raw33297Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33297step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw33297step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33297 raw33297Labels = mixedMoment B node2420 node2420Labels := by
  calc
    mixedMoment B raw33297 raw33297Labels = mixedMoment B raw33297step0 raw33297step0Labels := by
      have ha : raw33297step0 = (fun i j => raw33297 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33297step0 raw33297; decide +kernel
      have hl : raw33297step0Labels = raw33297Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33297 raw33297Labels permutation152 permutation3
    _ = mixedMoment B node2420 node2420Labels := by rfl

def raw33298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![2, -1, -1], ![1, 0, -1]]
def raw33298Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33298step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![2, -1, -1], ![1, 0, -1]]
def raw33298step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33298step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw33298step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33298 raw33298Labels = mixedMoment B node2512 node2512Labels := by
  calc
    mixedMoment B raw33298 raw33298Labels = mixedMoment B raw33298step0 raw33298step0Labels := by
      have hz : ∀ j, raw33298 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33298step0 = (fun i j => raw33298 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33298step0 raw33298; decide +kernel
      have hl : raw33298step0Labels = raw33298Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33298 raw33298Labels permutation346 hz
    mixedMoment B raw33298step0 raw33298step0Labels = mixedMoment B raw33298step1 raw33298step1Labels := by
      have ha : raw33298step1 = (fun i j => raw33298step0 (permutation36 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33298step1 raw33298step0; decide +kernel
      have hl : raw33298step1Labels = raw33298step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33298step0 raw33298step0Labels permutation36 permutation3
    _ = mixedMoment B node2512 node2512Labels := by rfl

def raw33299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw33299Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw33299step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33299step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw33299step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33299 raw33299Labels = mixedMoment B node2306 node2306Labels := by
  calc
    mixedMoment B raw33299 raw33299Labels = mixedMoment B raw33299step0 raw33299step0Labels := by
      have hz : ∀ j, raw33299 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33299step0 = (fun i j => raw33299 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33299step0 raw33299; decide +kernel
      have hl : raw33299step0Labels = raw33299Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33299 raw33299Labels permutation346 hz
    mixedMoment B raw33299step0 raw33299step0Labels = mixedMoment B raw33299step1 raw33299step1Labels := by
      have ha : raw33299step1 = (fun i j => raw33299step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33299step1 raw33299step0; decide +kernel
      have hl : raw33299step1Labels = raw33299step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33299step0 raw33299step0Labels permutation34 permutation3
    _ = mixedMoment B node2306 node2306Labels := by rfl

def raw33300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, -2, -1]]
def raw33300Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33300step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw33300step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33300step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw33300step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33300 raw33300Labels = mixedMoment B node2371 node2371Labels := by
  calc
    mixedMoment B raw33300 raw33300Labels = mixedMoment B raw33300step0 raw33300step0Labels := by
      have ha : raw33300step0 = (fun i j => raw33300 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33300step0 raw33300; decide +kernel
      have hl : raw33300step0Labels = raw33300Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33300 raw33300Labels permutation662 permutation3
    mixedMoment B raw33300step0 raw33300step0Labels = mixedMoment B raw33300step1 raw33300step1Labels := by
      have ha : raw33300step1 = -raw33300step0 := by apply Matrix.ext; change ∀ i j, raw33300step1 i j = -(raw33300step0 i j); unfold raw33300step1 raw33300step0; decide +kernel
      have hl : raw33300step1Labels = raw33300step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2371 node2371Labels := by rfl

def raw33301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, -2, -1]]
def raw33301Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![3, -2, -1]]
def raw33301step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33301step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw33301step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33301step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw33301step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33301 raw33301Labels = mixedMoment B node2385 node2385Labels := by
  calc
    mixedMoment B raw33301 raw33301Labels = mixedMoment B raw33301step0 raw33301step0Labels := by
      have hz : ∀ j, raw33301 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33301step0 = (fun i j => raw33301 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33301step0 raw33301; decide +kernel
      have hl : raw33301step0Labels = raw33301Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33301 raw33301Labels permutation346 hz
    mixedMoment B raw33301step0 raw33301step0Labels = mixedMoment B raw33301step1 raw33301step1Labels := by
      have ha : raw33301step1 = (fun i j => raw33301step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33301step1 raw33301step0; decide +kernel
      have hl : raw33301step1Labels = raw33301step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33301step0 raw33301step0Labels permutation145 permutation3
    mixedMoment B raw33301step1 raw33301step1Labels = mixedMoment B raw33301step2 raw33301step2Labels := by
      have ha : raw33301step2 = -raw33301step1 := by apply Matrix.ext; change ∀ i j, raw33301step2 i j = -(raw33301step1 i j); unfold raw33301step2 raw33301step1; decide +kernel
      have hl : raw33301step2Labels = raw33301step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2385 node2385Labels := by rfl

def raw33302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33302Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33302step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33302step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw33302step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33302step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw33302step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33302 raw33302Labels = mixedMoment B node5248 node5248Labels := by
  calc
    mixedMoment B raw33302 raw33302Labels = mixedMoment B raw33302step0 raw33302step0Labels := by
      have hz : ∀ j, raw33302 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33302step0 = (fun i j => raw33302 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33302step0 raw33302; decide +kernel
      have hl : raw33302step0Labels = raw33302Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33302 raw33302Labels permutation346 hz
    mixedMoment B raw33302step0 raw33302step0Labels = mixedMoment B raw33302step1 raw33302step1Labels := by
      have ha : raw33302step1 = (fun i j => raw33302step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33302step1 raw33302step0; decide +kernel
      have hl : raw33302step1Labels = raw33302step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33302step0 raw33302step0Labels permutation145 permutation7
    mixedMoment B raw33302step1 raw33302step1Labels = mixedMoment B raw33302step2 raw33302step2Labels := by
      have ha : raw33302step2 = raw33302step1 := by apply Matrix.ext; unfold raw33302step2 raw33302step1; decide +kernel
      have hl : raw33302step1Labels = labelEmbedding10 ∘ raw33302step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33302step1 raw33302step1Labels raw33302step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5248 node5248Labels := by rfl

def raw33303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33303Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33303step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw33303step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33303step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw33303step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33303 raw33303Labels = mixedMoment B node5241 node5241Labels := by
  calc
    mixedMoment B raw33303 raw33303Labels = mixedMoment B raw33303step0 raw33303step0Labels := by
      have ha : raw33303step0 = (fun i j => raw33303 (permutation664 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33303step0 raw33303; decide +kernel
      have hl : raw33303step0Labels = raw33303Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33303 raw33303Labels permutation664 permutation7
    mixedMoment B raw33303step0 raw33303step0Labels = mixedMoment B raw33303step1 raw33303step1Labels := by
      have ha : raw33303step1 = raw33303step0 := by apply Matrix.ext; unfold raw33303step1 raw33303step0; decide +kernel
      have hl : raw33303step0Labels = labelEmbedding10 ∘ raw33303step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33303step0 raw33303step0Labels raw33303step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5241 node5241Labels := by rfl

def raw33304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw33304Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33304step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33304step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw33304step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33304step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw33304step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33304step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw33304step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33304 raw33304Labels = mixedMoment B node5274 node5274Labels := by
  calc
    mixedMoment B raw33304 raw33304Labels = mixedMoment B raw33304step0 raw33304step0Labels := by
      have hz : ∀ j, raw33304 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33304step0 = (fun i j => raw33304 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33304step0 raw33304; decide +kernel
      have hl : raw33304step0Labels = raw33304Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33304 raw33304Labels permutation520 hz
    mixedMoment B raw33304step0 raw33304step0Labels = mixedMoment B raw33304step1 raw33304step1Labels := by
      have hz : ∀ j, raw33304step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33304step1 = (fun i j => raw33304step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33304step1 raw33304step0; decide +kernel
      have hl : raw33304step1Labels = raw33304step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33304step0 raw33304step0Labels permutation80 hz
    mixedMoment B raw33304step1 raw33304step1Labels = mixedMoment B raw33304step2 raw33304step2Labels := by
      have ha : raw33304step2 = (fun i j => raw33304step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33304step2 raw33304step1; decide +kernel
      have hl : raw33304step2Labels = raw33304step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33304step1 raw33304step1Labels permutation31 permutation7
    mixedMoment B raw33304step2 raw33304step2Labels = mixedMoment B raw33304step3 raw33304step3Labels := by
      have ha : raw33304step3 = raw33304step2 := by apply Matrix.ext; unfold raw33304step3 raw33304step2; decide +kernel
      have hl : raw33304step2Labels = labelEmbedding10 ∘ raw33304step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33304step2 raw33304step2Labels raw33304step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5274 node5274Labels := by rfl

def raw33305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw33305Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33305step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw33305step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33305step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw33305step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw33305step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw33305step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33305 raw33305Labels = mixedMoment B node5284 node5284Labels := by
  calc
    mixedMoment B raw33305 raw33305Labels = mixedMoment B raw33305step0 raw33305step0Labels := by
      have hz : ∀ j, raw33305 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33305step0 = (fun i j => raw33305 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33305step0 raw33305; decide +kernel
      have hl : raw33305step0Labels = raw33305Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33305 raw33305Labels permutation346 hz
    mixedMoment B raw33305step0 raw33305step0Labels = mixedMoment B raw33305step1 raw33305step1Labels := by
      have ha : raw33305step1 = (fun i j => raw33305step0 (permutation145 i) (permutation6 j)) := by apply Matrix.ext; unfold raw33305step1 raw33305step0; decide +kernel
      have hl : raw33305step1Labels = raw33305step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33305step0 raw33305step0Labels permutation145 permutation6
    mixedMoment B raw33305step1 raw33305step1Labels = mixedMoment B raw33305step2 raw33305step2Labels := by
      have ha : raw33305step2 = raw33305step1 := by apply Matrix.ext; unfold raw33305step2 raw33305step1; decide +kernel
      have hl : raw33305step1Labels = labelEmbedding9 ∘ raw33305step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33305step1 raw33305step1Labels raw33305step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5284 node5284Labels := by rfl

def raw33306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33306Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33306step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33306step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33306 raw33306Labels = mixedMoment B node4600 node4600Labels := by
  calc
    mixedMoment B raw33306 raw33306Labels = mixedMoment B raw33306step0 raw33306step0Labels := by
      have hz : ∀ j, raw33306 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33306step0 = (fun i j => raw33306 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33306step0 raw33306; decide +kernel
      have hl : raw33306step0Labels = raw33306Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33306 raw33306Labels permutation346 hz
    _ = mixedMoment B node4600 node4600Labels := by rfl

def raw33307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33307Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33307step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33307step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33307 raw33307Labels = mixedMoment B node5133 node5133Labels := by
  calc
    mixedMoment B raw33307 raw33307Labels = mixedMoment B raw33307step0 raw33307step0Labels := by
      have ha : raw33307step0 = (fun i j => raw33307 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33307step0 raw33307; decide +kernel
      have hl : raw33307step0Labels = raw33307Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33307 raw33307Labels permutation176 permutation2
    _ = mixedMoment B node5133 node5133Labels := by rfl

def raw33308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw33308Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33308step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33308step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw33308step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33308 raw33308Labels = mixedMoment B node5272 node5272Labels := by
  calc
    mixedMoment B raw33308 raw33308Labels = mixedMoment B raw33308step0 raw33308step0Labels := by
      have hz : ∀ j, raw33308 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33308step0 = (fun i j => raw33308 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33308step0 raw33308; decide +kernel
      have hl : raw33308step0Labels = raw33308Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33308 raw33308Labels permutation520 hz
    mixedMoment B raw33308step0 raw33308step0Labels = mixedMoment B raw33308step1 raw33308step1Labels := by
      have hz : ∀ j, raw33308step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33308step1 = (fun i j => raw33308step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33308step1 raw33308step0; decide +kernel
      have hl : raw33308step1Labels = raw33308step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33308step0 raw33308step0Labels permutation80 hz
    _ = mixedMoment B node5272 node5272Labels := by rfl

def raw33309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw33309Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw33309step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33309 raw33309Labels = mixedMoment B node5270 node5270Labels := by
  calc
    mixedMoment B raw33309 raw33309Labels = mixedMoment B raw33309step0 raw33309step0Labels := by
      have hz : ∀ j, raw33309 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33309step0 = (fun i j => raw33309 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33309step0 raw33309; decide +kernel
      have hl : raw33309step0Labels = raw33309Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33309 raw33309Labels permutation346 hz
    _ = mixedMoment B node5270 node5270Labels := by rfl

def raw33310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33310Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33310 raw33310Labels = mixedMoment B node4540 node4540Labels := by
  calc
    _ = mixedMoment B node4540 node4540Labels := by rfl

def raw33311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33311Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33311 raw33311Labels = mixedMoment B node4938 node4938Labels := by
  calc
    _ = mixedMoment B node4938 node4938Labels := by rfl

def raw33312 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw33312Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33312step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33312step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33312 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33312 raw33312Labels = mixedMoment B node5099 node5099Labels := by
  calc
    mixedMoment B raw33312 raw33312Labels = mixedMoment B raw33312step0 raw33312step0Labels := by
      have hz : ∀ j, raw33312 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33312step0 = (fun i j => raw33312 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33312step0 raw33312; decide +kernel
      have hl : raw33312step0Labels = raw33312Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33312 raw33312Labels permutation520 hz
    _ = mixedMoment B node5099 node5099Labels := by rfl

def raw33313 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw33313Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33313 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33313 raw33313Labels = mixedMoment B node5097 node5097Labels := by
  calc
    _ = mixedMoment B node5097 node5097Labels := by rfl

def raw33314 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33314Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33314step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33314step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33314step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw33314step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33314 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33314 raw33314Labels = mixedMoment B node4548 node4548Labels := by
  calc
    mixedMoment B raw33314 raw33314Labels = mixedMoment B raw33314step0 raw33314step0Labels := by
      have hz : ∀ j, raw33314 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33314step0 = (fun i j => raw33314 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33314step0 raw33314; decide +kernel
      have hl : raw33314step0Labels = raw33314Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33314 raw33314Labels permutation346 hz
    mixedMoment B raw33314step0 raw33314step0Labels = mixedMoment B raw33314step1 raw33314step1Labels := by
      have ha : raw33314step1 = (fun i j => raw33314step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33314step1 raw33314step0; decide +kernel
      have hl : raw33314step1Labels = raw33314step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33314step0 raw33314step0Labels permutation34 permutation2
    _ = mixedMoment B node4548 node4548Labels := by rfl

def raw33315 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33315Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33315step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33315step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33315step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw33315step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33315 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33315 raw33315Labels = mixedMoment B node4945 node4945Labels := by
  calc
    mixedMoment B raw33315 raw33315Labels = mixedMoment B raw33315step0 raw33315step0Labels := by
      have hz : ∀ j, raw33315 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33315step0 = (fun i j => raw33315 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33315step0 raw33315; decide +kernel
      have hl : raw33315step0Labels = raw33315Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33315 raw33315Labels permutation346 hz
    mixedMoment B raw33315step0 raw33315step0Labels = mixedMoment B raw33315step1 raw33315step1Labels := by
      have ha : raw33315step1 = (fun i j => raw33315step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33315step1 raw33315step0; decide +kernel
      have hl : raw33315step1Labels = raw33315step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33315step0 raw33315step0Labels permutation34 permutation2
    _ = mixedMoment B node4945 node4945Labels := by rfl

def raw33316 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33316Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33316step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw33316step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33316 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33316 raw33316Labels = mixedMoment B node5035 node5035Labels := by
  calc
    mixedMoment B raw33316 raw33316Labels = mixedMoment B raw33316step0 raw33316step0Labels := by
      have ha : raw33316step0 = (fun i j => raw33316 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33316step0 raw33316; decide +kernel
      have hl : raw33316step0Labels = raw33316Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33316 raw33316Labels permutation154 permutation2
    _ = mixedMoment B node5035 node5035Labels := by rfl

def raw33317 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 1, -3]]
def raw33317Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33317step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw33317step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33317step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw33317step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33317 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33317 raw33317Labels = mixedMoment B node5110 node5110Labels := by
  calc
    mixedMoment B raw33317 raw33317Labels = mixedMoment B raw33317step0 raw33317step0Labels := by
      have hz : ∀ j, raw33317 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33317step0 = (fun i j => raw33317 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33317step0 raw33317; decide +kernel
      have hl : raw33317step0Labels = raw33317Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33317 raw33317Labels permutation520 hz
    mixedMoment B raw33317step0 raw33317step0Labels = mixedMoment B raw33317step1 raw33317step1Labels := by
      have hz : ∀ j, raw33317step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33317step1 = (fun i j => raw33317step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33317step1 raw33317step0; decide +kernel
      have hl : raw33317step1Labels = raw33317step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33317step0 raw33317step0Labels permutation80 hz
    _ = mixedMoment B node5110 node5110Labels := by rfl

def raw33318 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw33318Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33318step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw33318step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33318step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw33318step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33318 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33318 raw33318Labels = mixedMoment B node5103 node5103Labels := by
  calc
    mixedMoment B raw33318 raw33318Labels = mixedMoment B raw33318step0 raw33318step0Labels := by
      have hz : ∀ j, raw33318 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33318step0 = (fun i j => raw33318 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33318step0 raw33318; decide +kernel
      have hl : raw33318step0Labels = raw33318Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33318 raw33318Labels permutation346 hz
    mixedMoment B raw33318step0 raw33318step0Labels = mixedMoment B raw33318step1 raw33318step1Labels := by
      have ha : raw33318step1 = (fun i j => raw33318step0 (permutation35 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33318step1 raw33318step0; decide +kernel
      have hl : raw33318step1Labels = raw33318step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33318step0 raw33318step0Labels permutation35 permutation2
    _ = mixedMoment B node5103 node5103Labels := by rfl

def raw33319 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw33319Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33319step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw33319step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33319 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33319 raw33319Labels = mixedMoment B node4548 node4548Labels := by
  calc
    mixedMoment B raw33319 raw33319Labels = mixedMoment B raw33319step0 raw33319step0Labels := by
      have hz : ∀ j, raw33319 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33319step0 = (fun i j => raw33319 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33319step0 raw33319; decide +kernel
      have hl : raw33319step0Labels = raw33319Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33319 raw33319Labels permutation346 hz
    _ = mixedMoment B node4548 node4548Labels := by rfl

def raw33320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw33320Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33320step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw33320step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33320 raw33320Labels = mixedMoment B node4945 node4945Labels := by
  calc
    mixedMoment B raw33320 raw33320Labels = mixedMoment B raw33320step0 raw33320step0Labels := by
      have hz : ∀ j, raw33320 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33320step0 = (fun i j => raw33320 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33320step0 raw33320; decide +kernel
      have hl : raw33320step0Labels = raw33320Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33320 raw33320Labels permutation346 hz
    _ = mixedMoment B node4945 node4945Labels := by rfl

def raw33321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw33321Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33321 raw33321Labels = mixedMoment B node5035 node5035Labels := by
  calc
    _ = mixedMoment B node5035 node5035Labels := by rfl

def raw33322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw33322Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33322step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw33322step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33322step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw33322step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33322 raw33322Labels = mixedMoment B node5103 node5103Labels := by
  calc
    mixedMoment B raw33322 raw33322Labels = mixedMoment B raw33322step0 raw33322step0Labels := by
      have hz : ∀ j, raw33322 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33322step0 = (fun i j => raw33322 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33322step0 raw33322; decide +kernel
      have hl : raw33322step0Labels = raw33322Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33322 raw33322Labels permutation346 hz
    mixedMoment B raw33322step0 raw33322step0Labels = mixedMoment B raw33322step1 raw33322step1Labels := by
      have ha : raw33322step1 = (fun i j => raw33322step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33322step1 raw33322step0; decide +kernel
      have hl : raw33322step1Labels = raw33322step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33322step0 raw33322step0Labels permutation33 permutation2
    _ = mixedMoment B node5103 node5103Labels := by rfl

def raw33323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw33323Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33323step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw33323step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33323step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw33323step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33323step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 0, 1], ![-3, 1, 2]]
def raw33323step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33323step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![3, -1, -2]]
def raw33323step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33323 raw33323Labels = mixedMoment B node4841 node4841Labels := by
  calc
    mixedMoment B raw33323 raw33323Labels = mixedMoment B raw33323step0 raw33323step0Labels := by
      have hz : ∀ j, raw33323 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw33323step0 = (fun i j => raw33323 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw33323step0 raw33323; decide +kernel
      have hl : raw33323step0Labels = raw33323Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33323 raw33323Labels permutation434 hz
    mixedMoment B raw33323step0 raw33323step0Labels = mixedMoment B raw33323step1 raw33323step1Labels := by
      have hz : ∀ j, raw33323step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33323step1 = (fun i j => raw33323step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33323step1 raw33323step0; decide +kernel
      have hl : raw33323step1Labels = raw33323step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33323step0 raw33323step0Labels permutation80 hz
    mixedMoment B raw33323step1 raw33323step1Labels = mixedMoment B raw33323step2 raw33323step2Labels := by
      have ha : raw33323step2 = (fun i j => raw33323step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33323step2 raw33323step1; decide +kernel
      have hl : raw33323step2Labels = raw33323step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33323step1 raw33323step1Labels permutation31 permutation2
    mixedMoment B raw33323step2 raw33323step2Labels = mixedMoment B raw33323step3 raw33323step3Labels := by
      have ha : raw33323step3 = -raw33323step2 := by apply Matrix.ext; change ∀ i j, raw33323step3 i j = -(raw33323step2 i j); unfold raw33323step3 raw33323step2; decide +kernel
      have hl : raw33323step3Labels = raw33323step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4841 node4841Labels := by rfl

def raw33324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33324Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33324step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33324step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw33324step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33324step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw33324step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33324 raw33324Labels = mixedMoment B node2705 node2705Labels := by
  calc
    mixedMoment B raw33324 raw33324Labels = mixedMoment B raw33324step0 raw33324step0Labels := by
      have hz : ∀ j, raw33324 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33324step0 = (fun i j => raw33324 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33324step0 raw33324; decide +kernel
      have hl : raw33324step0Labels = raw33324Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33324 raw33324Labels permutation346 hz
    mixedMoment B raw33324step0 raw33324step0Labels = mixedMoment B raw33324step1 raw33324step1Labels := by
      have ha : raw33324step1 = (fun i j => raw33324step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33324step1 raw33324step0; decide +kernel
      have hl : raw33324step1Labels = raw33324step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33324step0 raw33324step0Labels permutation145 permutation7
    mixedMoment B raw33324step1 raw33324step1Labels = mixedMoment B raw33324step2 raw33324step2Labels := by
      have ha : raw33324step2 = raw33324step1 := by apply Matrix.ext; unfold raw33324step2 raw33324step1; decide +kernel
      have hl : raw33324step1Labels = labelEmbedding1 ∘ raw33324step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33324step1 raw33324step1Labels raw33324step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2705 node2705Labels := by rfl

def raw33325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33325Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33325step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw33325step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33325step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw33325step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33325 raw33325Labels = mixedMoment B node2694 node2694Labels := by
  calc
    mixedMoment B raw33325 raw33325Labels = mixedMoment B raw33325step0 raw33325step0Labels := by
      have ha : raw33325step0 = (fun i j => raw33325 (permutation664 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33325step0 raw33325; decide +kernel
      have hl : raw33325step0Labels = raw33325Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33325 raw33325Labels permutation664 permutation7
    mixedMoment B raw33325step0 raw33325step0Labels = mixedMoment B raw33325step1 raw33325step1Labels := by
      have ha : raw33325step1 = raw33325step0 := by apply Matrix.ext; unfold raw33325step1 raw33325step0; decide +kernel
      have hl : raw33325step0Labels = labelEmbedding1 ∘ raw33325step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33325step0 raw33325step0Labels raw33325step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2694 node2694Labels := by rfl

def raw33326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw33326Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33326step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33326step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![2, 1, -3]]
def raw33326step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33326step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw33326step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33326step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw33326step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33326 raw33326Labels = mixedMoment B node2742 node2742Labels := by
  calc
    mixedMoment B raw33326 raw33326Labels = mixedMoment B raw33326step0 raw33326step0Labels := by
      have hz : ∀ j, raw33326 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33326step0 = (fun i j => raw33326 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33326step0 raw33326; decide +kernel
      have hl : raw33326step0Labels = raw33326Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33326 raw33326Labels permutation520 hz
    mixedMoment B raw33326step0 raw33326step0Labels = mixedMoment B raw33326step1 raw33326step1Labels := by
      have hz : ∀ j, raw33326step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33326step1 = (fun i j => raw33326step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33326step1 raw33326step0; decide +kernel
      have hl : raw33326step1Labels = raw33326step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33326step0 raw33326step0Labels permutation80 hz
    mixedMoment B raw33326step1 raw33326step1Labels = mixedMoment B raw33326step2 raw33326step2Labels := by
      have ha : raw33326step2 = (fun i j => raw33326step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33326step2 raw33326step1; decide +kernel
      have hl : raw33326step2Labels = raw33326step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33326step1 raw33326step1Labels permutation31 permutation7
    mixedMoment B raw33326step2 raw33326step2Labels = mixedMoment B raw33326step3 raw33326step3Labels := by
      have ha : raw33326step3 = raw33326step2 := by apply Matrix.ext; unfold raw33326step3 raw33326step2; decide +kernel
      have hl : raw33326step2Labels = labelEmbedding1 ∘ raw33326step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33326step2 raw33326step2Labels raw33326step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2742 node2742Labels := by rfl

def raw33327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw33327Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw33327step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33327step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw33327step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33327step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw33327step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33327 raw33327Labels = mixedMoment B node3077 node3077Labels := by
  calc
    mixedMoment B raw33327 raw33327Labels = mixedMoment B raw33327step0 raw33327step0Labels := by
      have hz : ∀ j, raw33327 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33327step0 = (fun i j => raw33327 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33327step0 raw33327; decide +kernel
      have hl : raw33327step0Labels = raw33327Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33327 raw33327Labels permutation346 hz
    mixedMoment B raw33327step0 raw33327step0Labels = mixedMoment B raw33327step1 raw33327step1Labels := by
      have ha : raw33327step1 = (fun i j => raw33327step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33327step1 raw33327step0; decide +kernel
      have hl : raw33327step1Labels = raw33327step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33327step0 raw33327step0Labels permutation145 permutation7
    mixedMoment B raw33327step1 raw33327step1Labels = mixedMoment B raw33327step2 raw33327step2Labels := by
      have ha : raw33327step2 = raw33327step1 := by apply Matrix.ext; unfold raw33327step2 raw33327step1; decide +kernel
      have hl : raw33327step1Labels = labelEmbedding1 ∘ raw33327step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33327step1 raw33327step1Labels raw33327step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3077 node3077Labels := by rfl

def raw33328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33328Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33328step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33328step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33328step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw33328step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33328step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 2, -4]]
def raw33328step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33328 raw33328Labels = mixedMoment B node2702 node2702Labels := by
  calc
    mixedMoment B raw33328 raw33328Labels = mixedMoment B raw33328step0 raw33328step0Labels := by
      have hz : ∀ j, raw33328 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33328step0 = (fun i j => raw33328 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33328step0 raw33328; decide +kernel
      have hl : raw33328step0Labels = raw33328Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33328 raw33328Labels permutation346 hz
    mixedMoment B raw33328step0 raw33328step0Labels = mixedMoment B raw33328step1 raw33328step1Labels := by
      have ha : raw33328step1 = (fun i j => raw33328step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33328step1 raw33328step0; decide +kernel
      have hl : raw33328step1Labels = raw33328step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33328step0 raw33328step0Labels permutation145 permutation7
    mixedMoment B raw33328step1 raw33328step1Labels = mixedMoment B raw33328step2 raw33328step2Labels := by
      have ha : raw33328step2 = raw33328step1 := by apply Matrix.ext; unfold raw33328step2 raw33328step1; decide +kernel
      have hl : raw33328step1Labels = labelEmbedding1 ∘ raw33328step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33328step1 raw33328step1Labels raw33328step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2702 node2702Labels := by rfl

def raw33329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33329Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33329step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw33329step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33329step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw33329step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33329 raw33329Labels = mixedMoment B node2693 node2693Labels := by
  calc
    mixedMoment B raw33329 raw33329Labels = mixedMoment B raw33329step0 raw33329step0Labels := by
      have ha : raw33329step0 = (fun i j => raw33329 (permutation664 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33329step0 raw33329; decide +kernel
      have hl : raw33329step0Labels = raw33329Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33329 raw33329Labels permutation664 permutation7
    mixedMoment B raw33329step0 raw33329step0Labels = mixedMoment B raw33329step1 raw33329step1Labels := by
      have ha : raw33329step1 = raw33329step0 := by apply Matrix.ext; unfold raw33329step1 raw33329step0; decide +kernel
      have hl : raw33329step0Labels = labelEmbedding1 ∘ raw33329step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33329step0 raw33329step0Labels raw33329step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2693 node2693Labels := by rfl

def raw33330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw33330Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33330step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33330step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw33330step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33330step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw33330step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33330step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw33330step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33330 raw33330Labels = mixedMoment B node2740 node2740Labels := by
  calc
    mixedMoment B raw33330 raw33330Labels = mixedMoment B raw33330step0 raw33330step0Labels := by
      have hz : ∀ j, raw33330 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33330step0 = (fun i j => raw33330 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33330step0 raw33330; decide +kernel
      have hl : raw33330step0Labels = raw33330Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33330 raw33330Labels permutation520 hz
    mixedMoment B raw33330step0 raw33330step0Labels = mixedMoment B raw33330step1 raw33330step1Labels := by
      have hz : ∀ j, raw33330step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33330step1 = (fun i j => raw33330step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33330step1 raw33330step0; decide +kernel
      have hl : raw33330step1Labels = raw33330step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33330step0 raw33330step0Labels permutation80 hz
    mixedMoment B raw33330step1 raw33330step1Labels = mixedMoment B raw33330step2 raw33330step2Labels := by
      have ha : raw33330step2 = (fun i j => raw33330step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33330step2 raw33330step1; decide +kernel
      have hl : raw33330step2Labels = raw33330step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33330step1 raw33330step1Labels permutation31 permutation7
    mixedMoment B raw33330step2 raw33330step2Labels = mixedMoment B raw33330step3 raw33330step3Labels := by
      have ha : raw33330step3 = raw33330step2 := by apply Matrix.ext; unfold raw33330step3 raw33330step2; decide +kernel
      have hl : raw33330step2Labels = labelEmbedding1 ∘ raw33330step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33330step2 raw33330step2Labels raw33330step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2740 node2740Labels := by rfl

def raw33331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw33331Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw33331step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33331step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw33331step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33331step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw33331step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33331 raw33331Labels = mixedMoment B node3075 node3075Labels := by
  calc
    mixedMoment B raw33331 raw33331Labels = mixedMoment B raw33331step0 raw33331step0Labels := by
      have hz : ∀ j, raw33331 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33331step0 = (fun i j => raw33331 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33331step0 raw33331; decide +kernel
      have hl : raw33331step0Labels = raw33331Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33331 raw33331Labels permutation346 hz
    mixedMoment B raw33331step0 raw33331step0Labels = mixedMoment B raw33331step1 raw33331step1Labels := by
      have ha : raw33331step1 = (fun i j => raw33331step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33331step1 raw33331step0; decide +kernel
      have hl : raw33331step1Labels = raw33331step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33331step0 raw33331step0Labels permutation145 permutation7
    mixedMoment B raw33331step1 raw33331step1Labels = mixedMoment B raw33331step2 raw33331step2Labels := by
      have ha : raw33331step2 = raw33331step1 := by apply Matrix.ext; unfold raw33331step2 raw33331step1; decide +kernel
      have hl : raw33331step1Labels = labelEmbedding1 ∘ raw33331step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33331step1 raw33331step1Labels raw33331step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3075 node3075Labels := by rfl

def raw33332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33332Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33332step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw33332step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33332step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw33332step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33332 raw33332Labels = mixedMoment B node2688 node2688Labels := by
  calc
    mixedMoment B raw33332 raw33332Labels = mixedMoment B raw33332step0 raw33332step0Labels := by
      have ha : raw33332step0 = (fun i j => raw33332 (permutation640 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33332step0 raw33332; decide +kernel
      have hl : raw33332step0Labels = raw33332Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33332 raw33332Labels permutation640 permutation7
    mixedMoment B raw33332step0 raw33332step0Labels = mixedMoment B raw33332step1 raw33332step1Labels := by
      have ha : raw33332step1 = raw33332step0 := by apply Matrix.ext; unfold raw33332step1 raw33332step0; decide +kernel
      have hl : raw33332step0Labels = labelEmbedding1 ∘ raw33332step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33332step0 raw33332step0Labels raw33332step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2688 node2688Labels := by rfl

def raw33333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33333Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33333step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw33333step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33333step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw33333step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33333 raw33333Labels = mixedMoment B node2689 node2689Labels := by
  calc
    mixedMoment B raw33333 raw33333Labels = mixedMoment B raw33333step0 raw33333step0Labels := by
      have ha : raw33333step0 = (fun i j => raw33333 (permutation640 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33333step0 raw33333; decide +kernel
      have hl : raw33333step0Labels = raw33333Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33333 raw33333Labels permutation640 permutation7
    mixedMoment B raw33333step0 raw33333step0Labels = mixedMoment B raw33333step1 raw33333step1Labels := by
      have ha : raw33333step1 = raw33333step0 := by apply Matrix.ext; unfold raw33333step1 raw33333step0; decide +kernel
      have hl : raw33333step0Labels = labelEmbedding1 ∘ raw33333step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33333step0 raw33333step0Labels raw33333step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2689 node2689Labels := by rfl

def raw33334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 1, -3]]
def raw33334Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33334step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33334step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33334step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw33334step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33334step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw33334step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33334 raw33334Labels = mixedMoment B node2704 node2704Labels := by
  calc
    mixedMoment B raw33334 raw33334Labels = mixedMoment B raw33334step0 raw33334step0Labels := by
      have hz : ∀ j, raw33334 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33334step0 = (fun i j => raw33334 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33334step0 raw33334; decide +kernel
      have hl : raw33334step0Labels = raw33334Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33334 raw33334Labels permutation520 hz
    mixedMoment B raw33334step0 raw33334step0Labels = mixedMoment B raw33334step1 raw33334step1Labels := by
      have ha : raw33334step1 = (fun i j => raw33334step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33334step1 raw33334step0; decide +kernel
      have hl : raw33334step1Labels = raw33334step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33334step0 raw33334step0Labels permutation145 permutation7
    mixedMoment B raw33334step1 raw33334step1Labels = mixedMoment B raw33334step2 raw33334step2Labels := by
      have ha : raw33334step2 = raw33334step1 := by apply Matrix.ext; unfold raw33334step2 raw33334step1; decide +kernel
      have hl : raw33334step1Labels = labelEmbedding1 ∘ raw33334step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33334step1 raw33334step1Labels raw33334step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2704 node2704Labels := by rfl

def raw33335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw33335Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33335step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw33335step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33335step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw33335step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33335 raw33335Labels = mixedMoment B node3058 node3058Labels := by
  calc
    mixedMoment B raw33335 raw33335Labels = mixedMoment B raw33335step0 raw33335step0Labels := by
      have ha : raw33335step0 = (fun i j => raw33335 (permutation640 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33335step0 raw33335; decide +kernel
      have hl : raw33335step0Labels = raw33335Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33335 raw33335Labels permutation640 permutation7
    mixedMoment B raw33335step0 raw33335step0Labels = mixedMoment B raw33335step1 raw33335step1Labels := by
      have ha : raw33335step1 = raw33335step0 := by apply Matrix.ext; unfold raw33335step1 raw33335step0; decide +kernel
      have hl : raw33335step0Labels = labelEmbedding1 ∘ raw33335step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33335step0 raw33335step0Labels raw33335step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3058 node3058Labels := by rfl

def raw33336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33336Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33336step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33336step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33336step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw33336step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33336step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw33336step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33336 raw33336Labels = mixedMoment B node2657 node2657Labels := by
  calc
    mixedMoment B raw33336 raw33336Labels = mixedMoment B raw33336step0 raw33336step0Labels := by
      have hz : ∀ j, raw33336 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33336step0 = (fun i j => raw33336 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33336step0 raw33336; decide +kernel
      have hl : raw33336step0Labels = raw33336Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33336 raw33336Labels permutation346 hz
    mixedMoment B raw33336step0 raw33336step0Labels = mixedMoment B raw33336step1 raw33336step1Labels := by
      have ha : raw33336step1 = (fun i j => raw33336step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33336step1 raw33336step0; decide +kernel
      have hl : raw33336step1Labels = raw33336step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33336step0 raw33336step0Labels permutation145 permutation7
    mixedMoment B raw33336step1 raw33336step1Labels = mixedMoment B raw33336step2 raw33336step2Labels := by
      have ha : raw33336step2 = raw33336step1 := by apply Matrix.ext; unfold raw33336step2 raw33336step1; decide +kernel
      have hl : raw33336step1Labels = labelEmbedding1 ∘ raw33336step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33336step1 raw33336step1Labels raw33336step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2657 node2657Labels := by rfl

def raw33337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33337Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33337step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33337step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw33337step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33337step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw33337step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33337 raw33337Labels = mixedMoment B node2658 node2658Labels := by
  calc
    mixedMoment B raw33337 raw33337Labels = mixedMoment B raw33337step0 raw33337step0Labels := by
      have hz : ∀ j, raw33337 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33337step0 = (fun i j => raw33337 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33337step0 raw33337; decide +kernel
      have hl : raw33337step0Labels = raw33337Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33337 raw33337Labels permutation346 hz
    mixedMoment B raw33337step0 raw33337step0Labels = mixedMoment B raw33337step1 raw33337step1Labels := by
      have ha : raw33337step1 = (fun i j => raw33337step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33337step1 raw33337step0; decide +kernel
      have hl : raw33337step1Labels = raw33337step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33337step0 raw33337step0Labels permutation145 permutation7
    mixedMoment B raw33337step1 raw33337step1Labels = mixedMoment B raw33337step2 raw33337step2Labels := by
      have ha : raw33337step2 = raw33337step1 := by apply Matrix.ext; unfold raw33337step2 raw33337step1; decide +kernel
      have hl : raw33337step1Labels = labelEmbedding1 ∘ raw33337step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33337step1 raw33337step1Labels raw33337step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2658 node2658Labels := by rfl

def raw33338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![2, -2, 0], ![1, -1, 0], ![2, 1, -3]]
def raw33338Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33338step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw33338step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33338step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw33338step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33338 raw33338Labels = mixedMoment B node2652 node2652Labels := by
  calc
    mixedMoment B raw33338 raw33338Labels = mixedMoment B raw33338step0 raw33338step0Labels := by
      have ha : raw33338step0 = (fun i j => raw33338 (permutation664 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33338step0 raw33338; decide +kernel
      have hl : raw33338step0Labels = raw33338Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33338 raw33338Labels permutation664 permutation7
    mixedMoment B raw33338step0 raw33338step0Labels = mixedMoment B raw33338step1 raw33338step1Labels := by
      have ha : raw33338step1 = raw33338step0 := by apply Matrix.ext; unfold raw33338step1 raw33338step0; decide +kernel
      have hl : raw33338step0Labels = labelEmbedding1 ∘ raw33338step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33338step0 raw33338step0Labels raw33338step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2652 node2652Labels := by rfl

def raw33339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![0, 0, 0], ![2, 1, -3]]
def raw33339Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw33339step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33339step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![2, 1, -3]]
def raw33339step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33339step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw33339step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33339step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![2, 1, -3]]
def raw33339step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33339 raw33339Labels = mixedMoment B node2685 node2685Labels := by
  calc
    mixedMoment B raw33339 raw33339Labels = mixedMoment B raw33339step0 raw33339step0Labels := by
      have hz : ∀ j, raw33339 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw33339step0 = (fun i j => raw33339 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw33339step0 raw33339; decide +kernel
      have hl : raw33339step0Labels = raw33339Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33339 raw33339Labels permutation520 hz
    mixedMoment B raw33339step0 raw33339step0Labels = mixedMoment B raw33339step1 raw33339step1Labels := by
      have hz : ∀ j, raw33339step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33339step1 = (fun i j => raw33339step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33339step1 raw33339step0; decide +kernel
      have hl : raw33339step1Labels = raw33339step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33339step0 raw33339step0Labels permutation80 hz
    mixedMoment B raw33339step1 raw33339step1Labels = mixedMoment B raw33339step2 raw33339step2Labels := by
      have ha : raw33339step2 = (fun i j => raw33339step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33339step2 raw33339step1; decide +kernel
      have hl : raw33339step2Labels = raw33339step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33339step1 raw33339step1Labels permutation31 permutation7
    mixedMoment B raw33339step2 raw33339step2Labels = mixedMoment B raw33339step3 raw33339step3Labels := by
      have ha : raw33339step3 = raw33339step2 := by apply Matrix.ext; unfold raw33339step3 raw33339step2; decide +kernel
      have hl : raw33339step2Labels = labelEmbedding1 ∘ raw33339step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33339step2 raw33339step2Labels raw33339step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2685 node2685Labels := by rfl

def raw33340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw33340Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33340step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![2, -2, 0], ![1, -1, 0], ![1, 2, -3]]
def raw33340step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33340step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw33340step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33340step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw33340step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33340 raw33340Labels = mixedMoment B node3024 node3024Labels := by
  calc
    mixedMoment B raw33340 raw33340Labels = mixedMoment B raw33340step0 raw33340step0Labels := by
      have hz : ∀ j, raw33340 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33340step0 = (fun i j => raw33340 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33340step0 raw33340; decide +kernel
      have hl : raw33340step0Labels = raw33340Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33340 raw33340Labels permutation346 hz
    mixedMoment B raw33340step0 raw33340step0Labels = mixedMoment B raw33340step1 raw33340step1Labels := by
      have ha : raw33340step1 = (fun i j => raw33340step0 (permutation145 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33340step1 raw33340step0; decide +kernel
      have hl : raw33340step1Labels = raw33340step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33340step0 raw33340step0Labels permutation145 permutation7
    mixedMoment B raw33340step1 raw33340step1Labels = mixedMoment B raw33340step2 raw33340step2Labels := by
      have ha : raw33340step2 = raw33340step1 := by apply Matrix.ext; unfold raw33340step2 raw33340step1; decide +kernel
      have hl : raw33340step1Labels = labelEmbedding1 ∘ raw33340step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33340step1 raw33340step1Labels raw33340step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3024 node3024Labels := by rfl

def raw33341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw33341Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33341step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw33341step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33341step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw33341step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33341step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw33341step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33341 raw33341Labels = mixedMoment B node2657 node2657Labels := by
  calc
    mixedMoment B raw33341 raw33341Labels = mixedMoment B raw33341step0 raw33341step0Labels := by
      have hz : ∀ j, raw33341 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33341step0 = (fun i j => raw33341 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33341step0 raw33341; decide +kernel
      have hl : raw33341step0Labels = raw33341Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33341 raw33341Labels permutation346 hz
    mixedMoment B raw33341step0 raw33341step0Labels = mixedMoment B raw33341step1 raw33341step1Labels := by
      have ha : raw33341step1 = (fun i j => raw33341step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33341step1 raw33341step0; decide +kernel
      have hl : raw33341step1Labels = raw33341step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33341step0 raw33341step0Labels permutation151 permutation7
    mixedMoment B raw33341step1 raw33341step1Labels = mixedMoment B raw33341step2 raw33341step2Labels := by
      have ha : raw33341step2 = raw33341step1 := by apply Matrix.ext; unfold raw33341step2 raw33341step1; decide +kernel
      have hl : raw33341step1Labels = labelEmbedding1 ∘ raw33341step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33341step1 raw33341step1Labels raw33341step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2657 node2657Labels := by rfl

def raw33342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw33342Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33342step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw33342step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33342step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw33342step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33342step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 1, -2], ![2, 1, -3]]
def raw33342step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33342 raw33342Labels = mixedMoment B node2658 node2658Labels := by
  calc
    mixedMoment B raw33342 raw33342Labels = mixedMoment B raw33342step0 raw33342step0Labels := by
      have hz : ∀ j, raw33342 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33342step0 = (fun i j => raw33342 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33342step0 raw33342; decide +kernel
      have hl : raw33342step0Labels = raw33342Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33342 raw33342Labels permutation346 hz
    mixedMoment B raw33342step0 raw33342step0Labels = mixedMoment B raw33342step1 raw33342step1Labels := by
      have ha : raw33342step1 = (fun i j => raw33342step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33342step1 raw33342step0; decide +kernel
      have hl : raw33342step1Labels = raw33342step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33342step0 raw33342step0Labels permutation151 permutation7
    mixedMoment B raw33342step1 raw33342step1Labels = mixedMoment B raw33342step2 raw33342step2Labels := by
      have ha : raw33342step2 = raw33342step1 := by apply Matrix.ext; unfold raw33342step2 raw33342step1; decide +kernel
      have hl : raw33342step1Labels = labelEmbedding1 ∘ raw33342step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33342step1 raw33342step1Labels raw33342step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2658 node2658Labels := by rfl

def raw33343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw33343Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33343step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw33343step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33343step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 1, -3]]
def raw33343step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33343 raw33343Labels = mixedMoment B node2652 node2652Labels := by
  calc
    mixedMoment B raw33343 raw33343Labels = mixedMoment B raw33343step0 raw33343step0Labels := by
      have ha : raw33343step0 = (fun i j => raw33343 (permutation688 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33343step0 raw33343; decide +kernel
      have hl : raw33343step0Labels = raw33343Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33343 raw33343Labels permutation688 permutation7
    mixedMoment B raw33343step0 raw33343step0Labels = mixedMoment B raw33343step1 raw33343step1Labels := by
      have ha : raw33343step1 = raw33343step0 := by apply Matrix.ext; unfold raw33343step1 raw33343step0; decide +kernel
      have hl : raw33343step0Labels = labelEmbedding1 ∘ raw33343step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33343step0 raw33343step0Labels raw33343step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2652 node2652Labels := by rfl

def raw33344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw33344Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![1, 2, -3]]
def raw33344step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33344step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw33344step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33344step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw33344step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33344 raw33344Labels = mixedMoment B node3024 node3024Labels := by
  calc
    mixedMoment B raw33344 raw33344Labels = mixedMoment B raw33344step0 raw33344step0Labels := by
      have hz : ∀ j, raw33344 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33344step0 = (fun i j => raw33344 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33344step0 raw33344; decide +kernel
      have hl : raw33344step0Labels = raw33344Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33344 raw33344Labels permutation346 hz
    mixedMoment B raw33344step0 raw33344step0Labels = mixedMoment B raw33344step1 raw33344step1Labels := by
      have ha : raw33344step1 = (fun i j => raw33344step0 (permutation151 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33344step1 raw33344step0; decide +kernel
      have hl : raw33344step1Labels = raw33344step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33344step0 raw33344step0Labels permutation151 permutation7
    mixedMoment B raw33344step1 raw33344step1Labels = mixedMoment B raw33344step2 raw33344step2Labels := by
      have ha : raw33344step2 = raw33344step1 := by apply Matrix.ext; unfold raw33344step2 raw33344step1; decide +kernel
      have hl : raw33344step1Labels = labelEmbedding1 ∘ raw33344step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33344step1 raw33344step1Labels raw33344step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3024 node3024Labels := by rfl

def raw33345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw33345Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33345step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw33345step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33345step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![3, 0, -3]]
def raw33345step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw33345step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw33345step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw33345step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw33345step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33345 raw33345Labels = mixedMoment B node2228 node2228Labels := by
  calc
    mixedMoment B raw33345 raw33345Labels = mixedMoment B raw33345step0 raw33345step0Labels := by
      have hz : ∀ j, raw33345 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw33345step0 = (fun i j => raw33345 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw33345step0 raw33345; decide +kernel
      have hl : raw33345step0Labels = raw33345Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33345 raw33345Labels permutation434 hz
    mixedMoment B raw33345step0 raw33345step0Labels = mixedMoment B raw33345step1 raw33345step1Labels := by
      have hz : ∀ j, raw33345step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw33345step1 = (fun i j => raw33345step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw33345step1 raw33345step0; decide +kernel
      have hl : raw33345step1Labels = raw33345step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33345step0 raw33345step0Labels permutation80 hz
    mixedMoment B raw33345step1 raw33345step1Labels = mixedMoment B raw33345step2 raw33345step2Labels := by
      have ha : raw33345step2 = (fun i j => raw33345step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33345step2 raw33345step1; decide +kernel
      have hl : raw33345step2Labels = raw33345step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33345step1 raw33345step1Labels permutation31 permutation7
    mixedMoment B raw33345step2 raw33345step2Labels = mixedMoment B raw33345step3 raw33345step3Labels := by
      have ha : raw33345step3 = raw33345step2 := by apply Matrix.ext; unfold raw33345step3 raw33345step2; decide +kernel
      have hl : raw33345step2Labels = labelEmbedding1 ∘ raw33345step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33345step2 raw33345step2Labels raw33345step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2228 node2228Labels := by rfl

def raw33346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw33346Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33346step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw33346step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33346step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw33346step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33346 raw33346Labels = mixedMoment B node4909 node4909Labels := by
  calc
    mixedMoment B raw33346 raw33346Labels = mixedMoment B raw33346step0 raw33346step0Labels := by
      have ha : raw33346step0 = (fun i j => raw33346 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33346step0 raw33346; decide +kernel
      have hl : raw33346step0Labels = raw33346Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33346 raw33346Labels permutation160 permutation3
    mixedMoment B raw33346step0 raw33346step0Labels = mixedMoment B raw33346step1 raw33346step1Labels := by
      have ha : raw33346step1 = raw33346step0 := by apply Matrix.ext; unfold raw33346step1 raw33346step0; decide +kernel
      have hl : raw33346step0Labels = labelEmbedding6 ∘ raw33346step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33346step0 raw33346step0Labels raw33346step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4909 node4909Labels := by rfl

def raw33347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw33347Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33347step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw33347step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33347step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw33347step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33347 raw33347Labels = mixedMoment B node5055 node5055Labels := by
  calc
    mixedMoment B raw33347 raw33347Labels = mixedMoment B raw33347step0 raw33347step0Labels := by
      have ha : raw33347step0 = (fun i j => raw33347 (permutation166 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33347step0 raw33347; decide +kernel
      have hl : raw33347step0Labels = raw33347Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33347 raw33347Labels permutation166 permutation3
    mixedMoment B raw33347step0 raw33347step0Labels = mixedMoment B raw33347step1 raw33347step1Labels := by
      have ha : raw33347step1 = raw33347step0 := by apply Matrix.ext; unfold raw33347step1 raw33347step0; decide +kernel
      have hl : raw33347step0Labels = labelEmbedding6 ∘ raw33347step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33347step0 raw33347step0Labels raw33347step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5055 node5055Labels := by rfl

def raw33348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw33348Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33348step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![2, -1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw33348step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33348step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw33348step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33348step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw33348step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33348 raw33348Labels = mixedMoment B node4914 node4914Labels := by
  calc
    mixedMoment B raw33348 raw33348Labels = mixedMoment B raw33348step0 raw33348step0Labels := by
      have hz : ∀ j, raw33348 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33348step0 = (fun i j => raw33348 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33348step0 raw33348; decide +kernel
      have hl : raw33348step0Labels = raw33348Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33348 raw33348Labels permutation346 hz
    mixedMoment B raw33348step0 raw33348step0Labels = mixedMoment B raw33348step1 raw33348step1Labels := by
      have ha : raw33348step1 = (fun i j => raw33348step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33348step1 raw33348step0; decide +kernel
      have hl : raw33348step1Labels = raw33348step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33348step0 raw33348step0Labels permutation34 permutation3
    mixedMoment B raw33348step1 raw33348step1Labels = mixedMoment B raw33348step2 raw33348step2Labels := by
      have ha : raw33348step2 = raw33348step1 := by apply Matrix.ext; unfold raw33348step2 raw33348step1; decide +kernel
      have hl : raw33348step1Labels = labelEmbedding6 ∘ raw33348step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33348step1 raw33348step1Labels raw33348step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4914 node4914Labels := by rfl

def raw33349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw33349Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33349step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw33349step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33349step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw33349step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33349 raw33349Labels = mixedMoment B node4989 node4989Labels := by
  calc
    mixedMoment B raw33349 raw33349Labels = mixedMoment B raw33349step0 raw33349step0Labels := by
      have ha : raw33349step0 = (fun i j => raw33349 (permutation662 i) (permutation5 j)) := by apply Matrix.ext; unfold raw33349step0 raw33349; decide +kernel
      have hl : raw33349step0Labels = raw33349Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33349 raw33349Labels permutation662 permutation5
    mixedMoment B raw33349step0 raw33349step0Labels = mixedMoment B raw33349step1 raw33349step1Labels := by
      have ha : raw33349step1 = raw33349step0 := by apply Matrix.ext; unfold raw33349step1 raw33349step0; decide +kernel
      have hl : raw33349step0Labels = labelEmbedding8 ∘ raw33349step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33349step0 raw33349step0Labels raw33349step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4989 node4989Labels := by rfl

def raw33350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw33350Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw33350step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33350step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw33350step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33350step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw33350step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33350 raw33350Labels = mixedMoment B node5014 node5014Labels := by
  calc
    mixedMoment B raw33350 raw33350Labels = mixedMoment B raw33350step0 raw33350step0Labels := by
      have hz : ∀ j, raw33350 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33350step0 = (fun i j => raw33350 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33350step0 raw33350; decide +kernel
      have hl : raw33350step0Labels = raw33350Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33350 raw33350Labels permutation346 hz
    mixedMoment B raw33350step0 raw33350step0Labels = mixedMoment B raw33350step1 raw33350step1Labels := by
      have ha : raw33350step1 = (fun i j => raw33350step0 (permutation145 i) (permutation5 j)) := by apply Matrix.ext; unfold raw33350step1 raw33350step0; decide +kernel
      have hl : raw33350step1Labels = raw33350step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33350step0 raw33350step0Labels permutation145 permutation5
    mixedMoment B raw33350step1 raw33350step1Labels = mixedMoment B raw33350step2 raw33350step2Labels := by
      have ha : raw33350step2 = raw33350step1 := by apply Matrix.ext; unfold raw33350step2 raw33350step1; decide +kernel
      have hl : raw33350step1Labels = labelEmbedding8 ∘ raw33350step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33350step1 raw33350step1Labels raw33350step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5014 node5014Labels := by rfl

def raw33351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -3, 1]]
def raw33351Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33351step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -3, 1]]
def raw33351step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33351step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw33351step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw33351step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw33351step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33351 raw33351Labels = mixedMoment B node4914 node4914Labels := by
  calc
    mixedMoment B raw33351 raw33351Labels = mixedMoment B raw33351step0 raw33351step0Labels := by
      have hz : ∀ j, raw33351 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33351step0 = (fun i j => raw33351 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33351step0 raw33351; decide +kernel
      have hl : raw33351step0Labels = raw33351Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33351 raw33351Labels permutation346 hz
    mixedMoment B raw33351step0 raw33351step0Labels = mixedMoment B raw33351step1 raw33351step1Labels := by
      have ha : raw33351step1 = (fun i j => raw33351step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33351step1 raw33351step0; decide +kernel
      have hl : raw33351step1Labels = raw33351step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33351step0 raw33351step0Labels permutation32 permutation3
    mixedMoment B raw33351step1 raw33351step1Labels = mixedMoment B raw33351step2 raw33351step2Labels := by
      have ha : raw33351step2 = raw33351step1 := by apply Matrix.ext; unfold raw33351step2 raw33351step1; decide +kernel
      have hl : raw33351step1Labels = labelEmbedding6 ∘ raw33351step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33351step1 raw33351step1Labels raw33351step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4914 node4914Labels := by rfl

def raw33352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -3, 1]]
def raw33352Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33352step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw33352step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33352step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw33352step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33352 raw33352Labels = mixedMoment B node4989 node4989Labels := by
  calc
    mixedMoment B raw33352 raw33352Labels = mixedMoment B raw33352step0 raw33352step0Labels := by
      have ha : raw33352step0 = (fun i j => raw33352 (permutation686 i) (permutation5 j)) := by apply Matrix.ext; unfold raw33352step0 raw33352; decide +kernel
      have hl : raw33352step0Labels = raw33352Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33352 raw33352Labels permutation686 permutation5
    mixedMoment B raw33352step0 raw33352step0Labels = mixedMoment B raw33352step1 raw33352step1Labels := by
      have ha : raw33352step1 = raw33352step0 := by apply Matrix.ext; unfold raw33352step1 raw33352step0; decide +kernel
      have hl : raw33352step0Labels = labelEmbedding8 ∘ raw33352step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33352step0 raw33352step0Labels raw33352step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4989 node4989Labels := by rfl

def raw33353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -4, 1]]
def raw33353Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33353step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -4, 1]]
def raw33353step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33353step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw33353step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33353step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![2, 0, -2], ![2, 1, -3]]
def raw33353step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33353 raw33353Labels = mixedMoment B node4389 node4389Labels := by
  calc
    mixedMoment B raw33353 raw33353Labels = mixedMoment B raw33353step0 raw33353step0Labels := by
      have hz : ∀ j, raw33353 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33353step0 = (fun i j => raw33353 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33353step0 raw33353; decide +kernel
      have hl : raw33353step0Labels = raw33353Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33353 raw33353Labels permutation346 hz
    mixedMoment B raw33353step0 raw33353step0Labels = mixedMoment B raw33353step1 raw33353step1Labels := by
      have ha : raw33353step1 = (fun i j => raw33353step0 (permutation145 i) (permutation5 j)) := by apply Matrix.ext; unfold raw33353step1 raw33353step0; decide +kernel
      have hl : raw33353step1Labels = raw33353step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33353step0 raw33353step0Labels permutation145 permutation5
    mixedMoment B raw33353step1 raw33353step1Labels = mixedMoment B raw33353step2 raw33353step2Labels := by
      have ha : raw33353step2 = raw33353step1 := by apply Matrix.ext; unfold raw33353step2 raw33353step1; decide +kernel
      have hl : raw33353step1Labels = labelEmbedding8 ∘ raw33353step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33353step1 raw33353step1Labels raw33353step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4389 node4389Labels := by rfl

def raw33354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -4, 1]]
def raw33354Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33354step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw33354step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33354step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 1, -3]]
def raw33354step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33354 raw33354Labels = mixedMoment B node4386 node4386Labels := by
  calc
    mixedMoment B raw33354 raw33354Labels = mixedMoment B raw33354step0 raw33354step0Labels := by
      have ha : raw33354step0 = (fun i j => raw33354 (permutation662 i) (permutation5 j)) := by apply Matrix.ext; unfold raw33354step0 raw33354; decide +kernel
      have hl : raw33354step0Labels = raw33354Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33354 raw33354Labels permutation662 permutation5
    mixedMoment B raw33354step0 raw33354step0Labels = mixedMoment B raw33354step1 raw33354step1Labels := by
      have ha : raw33354step1 = raw33354step0 := by apply Matrix.ext; unfold raw33354step1 raw33354step0; decide +kernel
      have hl : raw33354step0Labels = labelEmbedding8 ∘ raw33354step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33354step0 raw33354step0Labels raw33354step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4386 node4386Labels := by rfl

def raw33355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -4, 1]]
def raw33355Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![3, -4, 1]]
def raw33355step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33355step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw33355step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw33355step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw33355step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33355 raw33355Labels = mixedMoment B node4418 node4418Labels := by
  calc
    mixedMoment B raw33355 raw33355Labels = mixedMoment B raw33355step0 raw33355step0Labels := by
      have hz : ∀ j, raw33355 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33355step0 = (fun i j => raw33355 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33355step0 raw33355; decide +kernel
      have hl : raw33355step0Labels = raw33355Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33355 raw33355Labels permutation346 hz
    mixedMoment B raw33355step0 raw33355step0Labels = mixedMoment B raw33355step1 raw33355step1Labels := by
      have ha : raw33355step1 = (fun i j => raw33355step0 (permutation145 i) (permutation5 j)) := by apply Matrix.ext; unfold raw33355step1 raw33355step0; decide +kernel
      have hl : raw33355step1Labels = raw33355step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33355step0 raw33355step0Labels permutation145 permutation5
    mixedMoment B raw33355step1 raw33355step1Labels = mixedMoment B raw33355step2 raw33355step2Labels := by
      have ha : raw33355step2 = raw33355step1 := by apply Matrix.ext; unfold raw33355step2 raw33355step1; decide +kernel
      have hl : raw33355step1Labels = labelEmbedding8 ∘ raw33355step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33355step1 raw33355step1Labels raw33355step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4418 node4418Labels := by rfl

def raw33356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw33356Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33356step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw33356step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33356step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 0, 2]]
def raw33356step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33356step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw33356step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33356 raw33356Labels = mixedMoment B node3498 node3498Labels := by
  calc
    mixedMoment B raw33356 raw33356Labels = mixedMoment B raw33356step0 raw33356step0Labels := by
      have hz : ∀ j, raw33356 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33356step0 = (fun i j => raw33356 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33356step0 raw33356; decide +kernel
      have hl : raw33356step0Labels = raw33356Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33356 raw33356Labels permutation346 hz
    mixedMoment B raw33356step0 raw33356step0Labels = mixedMoment B raw33356step1 raw33356step1Labels := by
      have ha : raw33356step1 = (fun i j => raw33356step0 (permutation144 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33356step1 raw33356step0; decide +kernel
      have hl : raw33356step1Labels = raw33356step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33356step0 raw33356step0Labels permutation144 permutation3
    mixedMoment B raw33356step1 raw33356step1Labels = mixedMoment B raw33356step2 raw33356step2Labels := by
      have ha : raw33356step2 = -raw33356step1 := by apply Matrix.ext; change ∀ i j, raw33356step2 i j = -(raw33356step1 i j); unfold raw33356step2 raw33356step1; decide +kernel
      have hl : raw33356step2Labels = raw33356step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3498 node3498Labels := by rfl

def raw33357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw33357Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33357step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw33357step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33357step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33357step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33357 raw33357Labels = mixedMoment B node3496 node3496Labels := by
  calc
    mixedMoment B raw33357 raw33357Labels = mixedMoment B raw33357step0 raw33357step0Labels := by
      have ha : raw33357step0 = (fun i j => raw33357 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33357step0 raw33357; decide +kernel
      have hl : raw33357step0Labels = raw33357Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33357 raw33357Labels permutation662 permutation3
    mixedMoment B raw33357step0 raw33357step0Labels = mixedMoment B raw33357step1 raw33357step1Labels := by
      have ha : raw33357step1 = -raw33357step0 := by apply Matrix.ext; change ∀ i j, raw33357step1 i j = -(raw33357step0 i j); unfold raw33357step1 raw33357step0; decide +kernel
      have hl : raw33357step1Labels = raw33357step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3496 node3496Labels := by rfl

def raw33358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw33358Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw33358step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33358step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw33358step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33358step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33358step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33358 raw33358Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw33358 raw33358Labels = mixedMoment B raw33358step0 raw33358step0Labels := by
      have hz : ∀ j, raw33358 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33358step0 = (fun i j => raw33358 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33358step0 raw33358; decide +kernel
      have hl : raw33358step0Labels = raw33358Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33358 raw33358Labels permutation346 hz
    mixedMoment B raw33358step0 raw33358step0Labels = mixedMoment B raw33358step1 raw33358step1Labels := by
      have ha : raw33358step1 = (fun i j => raw33358step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33358step1 raw33358step0; decide +kernel
      have hl : raw33358step1Labels = raw33358step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33358step0 raw33358step0Labels permutation151 permutation3
    mixedMoment B raw33358step1 raw33358step1Labels = mixedMoment B raw33358step2 raw33358step2Labels := by
      have ha : raw33358step2 = -raw33358step1 := by apply Matrix.ext; change ∀ i j, raw33358step2 i j = -(raw33358step1 i j); unfold raw33358step2 raw33358step1; decide +kernel
      have hl : raw33358step2Labels = raw33358step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3534 node3534Labels := by rfl

def raw33359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw33359Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33359step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw33359step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33359step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw33359step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33359step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33359step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33359 raw33359Labels = mixedMoment B node3534 node3534Labels := by
  calc
    mixedMoment B raw33359 raw33359Labels = mixedMoment B raw33359step0 raw33359step0Labels := by
      have hz : ∀ j, raw33359 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33359step0 = (fun i j => raw33359 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33359step0 raw33359; decide +kernel
      have hl : raw33359step0Labels = raw33359Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33359 raw33359Labels permutation346 hz
    mixedMoment B raw33359step0 raw33359step0Labels = mixedMoment B raw33359step1 raw33359step1Labels := by
      have ha : raw33359step1 = (fun i j => raw33359step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33359step1 raw33359step0; decide +kernel
      have hl : raw33359step1Labels = raw33359step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33359step0 raw33359step0Labels permutation145 permutation3
    mixedMoment B raw33359step1 raw33359step1Labels = mixedMoment B raw33359step2 raw33359step2Labels := by
      have ha : raw33359step2 = -raw33359step1 := by apply Matrix.ext; change ∀ i j, raw33359step2 i j = -(raw33359step1 i j); unfold raw33359step2 raw33359step1; decide +kernel
      have hl : raw33359step2Labels = raw33359step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3534 node3534Labels := by rfl

def raw33360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw33360Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33360step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw33360step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33360 raw33360Labels = mixedMoment B node2302 node2302Labels := by
  calc
    mixedMoment B raw33360 raw33360Labels = mixedMoment B raw33360step0 raw33360step0Labels := by
      have ha : raw33360step0 = (fun i j => raw33360 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33360step0 raw33360; decide +kernel
      have hl : raw33360step0Labels = raw33360Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33360 raw33360Labels permutation160 permutation3
    _ = mixedMoment B node2302 node2302Labels := by rfl

def raw33361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw33361Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33361step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw33361step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33361 raw33361Labels = mixedMoment B node2458 node2458Labels := by
  calc
    mixedMoment B raw33361 raw33361Labels = mixedMoment B raw33361step0 raw33361step0Labels := by
      have ha : raw33361step0 = (fun i j => raw33361 (permutation160 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33361step0 raw33361; decide +kernel
      have hl : raw33361step0Labels = raw33361Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33361 raw33361Labels permutation160 permutation3
    _ = mixedMoment B node2458 node2458Labels := by rfl

def raw33362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![2, -3, 1]]
def raw33362Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33362step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw33362step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33362 raw33362Labels = mixedMoment B node2458 node2458Labels := by
  calc
    mixedMoment B raw33362 raw33362Labels = mixedMoment B raw33362step0 raw33362step0Labels := by
      have ha : raw33362step0 = (fun i j => raw33362 (permutation166 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33362step0 raw33362; decide +kernel
      have hl : raw33362step0Labels = raw33362Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33362 raw33362Labels permutation166 permutation3
    _ = mixedMoment B node2458 node2458Labels := by rfl

def raw33363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw33363Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![2, -1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw33363step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33363step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw33363step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33363 raw33363Labels = mixedMoment B node2307 node2307Labels := by
  calc
    mixedMoment B raw33363 raw33363Labels = mixedMoment B raw33363step0 raw33363step0Labels := by
      have hz : ∀ j, raw33363 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33363step0 = (fun i j => raw33363 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33363step0 raw33363; decide +kernel
      have hl : raw33363step0Labels = raw33363Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33363 raw33363Labels permutation346 hz
    mixedMoment B raw33363step0 raw33363step0Labels = mixedMoment B raw33363step1 raw33363step1Labels := by
      have ha : raw33363step1 = (fun i j => raw33363step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33363step1 raw33363step0; decide +kernel
      have hl : raw33363step1Labels = raw33363step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33363step0 raw33363step0Labels permutation34 permutation3
    _ = mixedMoment B node2307 node2307Labels := by rfl

def raw33364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw33364Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33364step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw33364step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33364 raw33364Labels = mixedMoment B node2413 node2413Labels := by
  calc
    mixedMoment B raw33364 raw33364Labels = mixedMoment B raw33364step0 raw33364step0Labels := by
      have ha : raw33364step0 = (fun i j => raw33364 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33364step0 raw33364; decide +kernel
      have hl : raw33364step0Labels = raw33364Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33364 raw33364Labels permutation154 permutation3
    _ = mixedMoment B node2413 node2413Labels := by rfl

def raw33365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw33365Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![2, -1, -1], ![0, 1, -1], ![2, -3, 1]]
def raw33365step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33365step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw33365step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33365 raw33365Labels = mixedMoment B node2467 node2467Labels := by
  calc
    mixedMoment B raw33365 raw33365Labels = mixedMoment B raw33365step0 raw33365step0Labels := by
      have hz : ∀ j, raw33365 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33365step0 = (fun i j => raw33365 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33365step0 raw33365; decide +kernel
      have hl : raw33365step0Labels = raw33365Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33365 raw33365Labels permutation346 hz
    mixedMoment B raw33365step0 raw33365step0Labels = mixedMoment B raw33365step1 raw33365step1Labels := by
      have ha : raw33365step1 = (fun i j => raw33365step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33365step1 raw33365step0; decide +kernel
      have hl : raw33365step1Labels = raw33365step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33365step0 raw33365step0Labels permutation34 permutation3
    _ = mixedMoment B node2467 node2467Labels := by rfl

def raw33366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![2, -1, -1], ![2, -3, 1]]
def raw33366Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![1, 0, -1], ![2, -1, -1], ![2, -3, 1]]
def raw33366step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33366step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw33366step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33366 raw33366Labels = mixedMoment B node2307 node2307Labels := by
  calc
    mixedMoment B raw33366 raw33366Labels = mixedMoment B raw33366step0 raw33366step0Labels := by
      have hz : ∀ j, raw33366 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33366step0 = (fun i j => raw33366 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33366step0 raw33366; decide +kernel
      have hl : raw33366step0Labels = raw33366Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33366 raw33366Labels permutation346 hz
    mixedMoment B raw33366step0 raw33366step0Labels = mixedMoment B raw33366step1 raw33366step1Labels := by
      have ha : raw33366step1 = (fun i j => raw33366step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33366step1 raw33366step0; decide +kernel
      have hl : raw33366step1Labels = raw33366step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33366step0 raw33366step0Labels permutation32 permutation3
    _ = mixedMoment B node2307 node2307Labels := by rfl

def raw33367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -3, 1]]
def raw33367Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33367step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw33367step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33367 raw33367Labels = mixedMoment B node2413 node2413Labels := by
  calc
    mixedMoment B raw33367 raw33367Labels = mixedMoment B raw33367step0 raw33367step0Labels := by
      have ha : raw33367step0 = (fun i j => raw33367 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33367step0 raw33367; decide +kernel
      have hl : raw33367step0Labels = raw33367Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33367 raw33367Labels permutation152 permutation3
    _ = mixedMoment B node2413 node2413Labels := by rfl

def raw33368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -1, -1], ![2, -3, 1]]
def raw33368Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -3, 1]]
def raw33368step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33368step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw33368step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33368 raw33368Labels = mixedMoment B node2467 node2467Labels := by
  calc
    mixedMoment B raw33368 raw33368Labels = mixedMoment B raw33368step0 raw33368step0Labels := by
      have hz : ∀ j, raw33368 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33368step0 = (fun i j => raw33368 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33368step0 raw33368; decide +kernel
      have hl : raw33368step0Labels = raw33368Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33368 raw33368Labels permutation346 hz
    mixedMoment B raw33368step0 raw33368step0Labels = mixedMoment B raw33368step1 raw33368step1Labels := by
      have ha : raw33368step1 = (fun i j => raw33368step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33368step1 raw33368step0; decide +kernel
      have hl : raw33368step1Labels = raw33368step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33368step0 raw33368step0Labels permutation32 permutation3
    _ = mixedMoment B node2467 node2467Labels := by rfl

def raw33369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1], ![3, -4, 1]]
def raw33369Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33369step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![3, -4, 1]]
def raw33369step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33369step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![1, -1, 0], ![-2, 0, 2], ![-3, 1, 2]]
def raw33369step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33369step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![-1, 1, 0], ![2, 0, -2], ![3, -1, -2]]
def raw33369step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33369 raw33369Labels = mixedMoment B node1585 node1585Labels := by
  calc
    mixedMoment B raw33369 raw33369Labels = mixedMoment B raw33369step0 raw33369step0Labels := by
      have hz : ∀ j, raw33369 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33369step0 = (fun i j => raw33369 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33369step0 raw33369; decide +kernel
      have hl : raw33369step0Labels = raw33369Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33369 raw33369Labels permutation346 hz
    mixedMoment B raw33369step0 raw33369step0Labels = mixedMoment B raw33369step1 raw33369step1Labels := by
      have ha : raw33369step1 = (fun i j => raw33369step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33369step1 raw33369step0; decide +kernel
      have hl : raw33369step1Labels = raw33369step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33369step0 raw33369step0Labels permutation145 permutation3
    mixedMoment B raw33369step1 raw33369step1Labels = mixedMoment B raw33369step2 raw33369step2Labels := by
      have ha : raw33369step2 = -raw33369step1 := by apply Matrix.ext; change ∀ i j, raw33369step2 i j = -(raw33369step1 i j); unfold raw33369step2 raw33369step1; decide +kernel
      have hl : raw33369step2Labels = raw33369step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1585 node1585Labels := by rfl

def raw33370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -4, 1]]
def raw33370Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33370step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw33370step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33370step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw33370step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33370 raw33370Labels = mixedMoment B node1582 node1582Labels := by
  calc
    mixedMoment B raw33370 raw33370Labels = mixedMoment B raw33370step0 raw33370step0Labels := by
      have ha : raw33370step0 = (fun i j => raw33370 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33370step0 raw33370; decide +kernel
      have hl : raw33370step0Labels = raw33370Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33370 raw33370Labels permutation662 permutation3
    mixedMoment B raw33370step0 raw33370step0Labels = mixedMoment B raw33370step1 raw33370step1Labels := by
      have ha : raw33370step1 = -raw33370step0 := by apply Matrix.ext; change ∀ i j, raw33370step1 i j = -(raw33370step0 i j); unfold raw33370step1 raw33370step0; decide +kernel
      have hl : raw33370step1Labels = raw33370step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1582 node1582Labels := by rfl

def raw33371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw33371Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -4, 1]]
def raw33371step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33371step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw33371step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33371step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw33371step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33371 raw33371Labels = mixedMoment B node1602 node1602Labels := by
  calc
    mixedMoment B raw33371 raw33371Labels = mixedMoment B raw33371step0 raw33371step0Labels := by
      have hz : ∀ j, raw33371 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33371step0 = (fun i j => raw33371 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33371step0 raw33371; decide +kernel
      have hl : raw33371step0Labels = raw33371Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33371 raw33371Labels permutation346 hz
    mixedMoment B raw33371step0 raw33371step0Labels = mixedMoment B raw33371step1 raw33371step1Labels := by
      have ha : raw33371step1 = (fun i j => raw33371step0 (permutation151 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33371step1 raw33371step0; decide +kernel
      have hl : raw33371step1Labels = raw33371step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33371step0 raw33371step0Labels permutation151 permutation3
    mixedMoment B raw33371step1 raw33371step1Labels = mixedMoment B raw33371step2 raw33371step2Labels := by
      have ha : raw33371step2 = -raw33371step1 := by apply Matrix.ext; change ∀ i j, raw33371step2 i j = -(raw33371step1 i j); unfold raw33371step2 raw33371step1; decide +kernel
      have hl : raw33371step2Labels = raw33371step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1602 node1602Labels := by rfl

def raw33372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, 1, -1], ![3, -4, 1]]
def raw33372Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, 0, -1], ![0, 1, -1], ![3, -4, 1]]
def raw33372step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw33372step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw33372step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33372step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw33372step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33372 raw33372Labels = mixedMoment B node1602 node1602Labels := by
  calc
    mixedMoment B raw33372 raw33372Labels = mixedMoment B raw33372step0 raw33372step0Labels := by
      have hz : ∀ j, raw33372 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33372step0 = (fun i j => raw33372 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33372step0 raw33372; decide +kernel
      have hl : raw33372step0Labels = raw33372Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33372 raw33372Labels permutation346 hz
    mixedMoment B raw33372step0 raw33372step0Labels = mixedMoment B raw33372step1 raw33372step1Labels := by
      have ha : raw33372step1 = (fun i j => raw33372step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw33372step1 raw33372step0; decide +kernel
      have hl : raw33372step1Labels = raw33372step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33372step0 raw33372step0Labels permutation145 permutation3
    mixedMoment B raw33372step1 raw33372step1Labels = mixedMoment B raw33372step2 raw33372step2Labels := by
      have ha : raw33372step2 = -raw33372step1 := by apply Matrix.ext; change ∀ i j, raw33372step2 i j = -(raw33372step1 i j); unfold raw33372step2 raw33372step1; decide +kernel
      have hl : raw33372step2Labels = raw33372step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1602 node1602Labels := by rfl

def raw33373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![2, -1, -1]]
def raw33373Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33373step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw33373step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33373 raw33373Labels = mixedMoment B node3777 node3777Labels := by
  calc
    mixedMoment B raw33373 raw33373Labels = mixedMoment B raw33373step0 raw33373step0Labels := by
      have ha : raw33373step0 = (fun i j => raw33373 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33373step0 raw33373; decide +kernel
      have hl : raw33373step0Labels = raw33373Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33373 raw33373Labels permutation154 permutation2
    _ = mixedMoment B node3777 node3777Labels := by rfl

def raw33374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![2, 0, -2], ![1, 0, -1], ![2, -1, -1]]
def raw33374Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33374step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw33374step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33374 raw33374Labels = mixedMoment B node2418 node2418Labels := by
  calc
    mixedMoment B raw33374 raw33374Labels = mixedMoment B raw33374step0 raw33374step0Labels := by
      have ha : raw33374step0 = (fun i j => raw33374 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33374step0 raw33374; decide +kernel
      have hl : raw33374step0Labels = raw33374Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33374 raw33374Labels permutation155 permutation2
    _ = mixedMoment B node2418 node2418Labels := by rfl

def raw33375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw33375Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33375 raw33375Labels = mixedMoment B node2420 node2420Labels := by
  calc
    _ = mixedMoment B node2420 node2420Labels := by rfl

def raw33376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![1, 0, -1], ![3, -2, -1]]
def raw33376Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33376step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw33376step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33376 raw33376Labels = mixedMoment B node2416 node2416Labels := by
  calc
    mixedMoment B raw33376 raw33376Labels = mixedMoment B raw33376step0 raw33376step0Labels := by
      have ha : raw33376step0 = (fun i j => raw33376 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33376step0 raw33376; decide +kernel
      have hl : raw33376step0Labels = raw33376Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33376 raw33376Labels permutation154 permutation2
    _ = mixedMoment B node2416 node2416Labels := by rfl

def raw33377 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw33377Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33377step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw33377step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33377step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw33377step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33377 raw33377Labels = mixedMoment B node3436 node3436Labels := by
  calc
    mixedMoment B raw33377 raw33377Labels = mixedMoment B raw33377step0 raw33377step0Labels := by
      have ha : raw33377step0 = (fun i j => raw33377 (permutation155 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33377step0 raw33377; decide +kernel
      have hl : raw33377step0Labels = raw33377Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33377 raw33377Labels permutation155 permutation4
    mixedMoment B raw33377step0 raw33377step0Labels = mixedMoment B raw33377step1 raw33377step1Labels := by
      have ha : raw33377step1 = -raw33377step0 := by apply Matrix.ext; change ∀ i j, raw33377step1 i j = -(raw33377step0 i j); unfold raw33377step1 raw33377step0; decide +kernel
      have hl : raw33377step1Labels = raw33377step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3436 node3436Labels := by rfl

def raw33378 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw33378Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33378step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw33378step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33378step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw33378step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33378 raw33378Labels = mixedMoment B node2000 node2000Labels := by
  calc
    mixedMoment B raw33378 raw33378Labels = mixedMoment B raw33378step0 raw33378step0Labels := by
      have ha : raw33378step0 = (fun i j => raw33378 (permutation179 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33378step0 raw33378; decide +kernel
      have hl : raw33378step0Labels = raw33378Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33378 raw33378Labels permutation179 permutation4
    mixedMoment B raw33378step0 raw33378step0Labels = mixedMoment B raw33378step1 raw33378step1Labels := by
      have ha : raw33378step1 = -raw33378step0 := by apply Matrix.ext; change ∀ i j, raw33378step1 i j = -(raw33378step0 i j); unfold raw33378step1 raw33378step0; decide +kernel
      have hl : raw33378step1Labels = raw33378step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2000 node2000Labels := by rfl

def raw33379 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw33379Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33379step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![1, -2, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw33379step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33379step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw33379step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33379step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw33379step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33379 raw33379Labels = mixedMoment B node1947 node1947Labels := by
  calc
    mixedMoment B raw33379 raw33379Labels = mixedMoment B raw33379step0 raw33379step0Labels := by
      have hz : ∀ j, raw33379 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw33379step0 = (fun i j => raw33379 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw33379step0 raw33379; decide +kernel
      have hl : raw33379step0Labels = raw33379Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw33379 raw33379Labels permutation346 hz
    mixedMoment B raw33379step0 raw33379step0Labels = mixedMoment B raw33379step1 raw33379step1Labels := by
      have ha : raw33379step1 = (fun i j => raw33379step0 (permutation35 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33379step1 raw33379step0; decide +kernel
      have hl : raw33379step1Labels = raw33379step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33379step0 raw33379step0Labels permutation35 permutation4
    mixedMoment B raw33379step1 raw33379step1Labels = mixedMoment B raw33379step2 raw33379step2Labels := by
      have ha : raw33379step2 = -raw33379step1 := by apply Matrix.ext; change ∀ i j, raw33379step2 i j = -(raw33379step1 i j); unfold raw33379step2 raw33379step1; decide +kernel
      have hl : raw33379step2Labels = raw33379step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1947 node1947Labels := by rfl

def raw33380 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![-1, 1, 0], ![2, -3, 1], ![0, -1, 1], ![-1, -1, 2]]
def raw33380Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33380step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw33380step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33380step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![3, -2, -1]]
def raw33380step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33380 raw33380Labels = mixedMoment B node1867 node1867Labels := by
  calc
    mixedMoment B raw33380 raw33380Labels = mixedMoment B raw33380step0 raw33380step0Labels := by
      have ha : raw33380step0 = (fun i j => raw33380 (permutation155 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33380step0 raw33380; decide +kernel
      have hl : raw33380step0Labels = raw33380Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33380 raw33380Labels permutation155 permutation4
    mixedMoment B raw33380step0 raw33380step0Labels = mixedMoment B raw33380step1 raw33380step1Labels := by
      have ha : raw33380step1 = -raw33380step0 := by apply Matrix.ext; change ∀ i j, raw33380step1 i j = -(raw33380step0 i j); unfold raw33380step1 raw33380step0; decide +kernel
      have hl : raw33380step1Labels = raw33380step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1867 node1867Labels := by rfl

def raw33381 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw33381Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33381step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-1, -1, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw33381step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33381step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 1, -2], ![2, -1, -1], ![2, -1, -1]]
def raw33381step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33381 raw33381Labels = mixedMoment B node1871 node1871Labels := by
  calc
    mixedMoment B raw33381 raw33381Labels = mixedMoment B raw33381step0 raw33381step0Labels := by
      have ha : raw33381step0 = (fun i j => raw33381 (permutation156 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33381step0 raw33381; decide +kernel
      have hl : raw33381step0Labels = raw33381Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33381 raw33381Labels permutation156 permutation4
    mixedMoment B raw33381step0 raw33381step0Labels = mixedMoment B raw33381step1 raw33381step1Labels := by
      have ha : raw33381step1 = -raw33381step0 := by apply Matrix.ext; change ∀ i j, raw33381step1 i j = -(raw33381step0 i j); unfold raw33381step1 raw33381step0; decide +kernel
      have hl : raw33381step1Labels = raw33381step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1871 node1871Labels := by rfl

def raw33382 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![0, -1, 1], ![0, -2, 2]]
def raw33382Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33382step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw33382step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33382step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw33382step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33382 raw33382Labels = mixedMoment B node1869 node1869Labels := by
  calc
    mixedMoment B raw33382 raw33382Labels = mixedMoment B raw33382step0 raw33382step0Labels := by
      have ha : raw33382step0 = (fun i j => raw33382 (permutation154 i) (permutation4 j)) := by apply Matrix.ext; unfold raw33382step0 raw33382; decide +kernel
      have hl : raw33382step0Labels = raw33382Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33382 raw33382Labels permutation154 permutation4
    mixedMoment B raw33382step0 raw33382step0Labels = mixedMoment B raw33382step1 raw33382step1Labels := by
      have ha : raw33382step1 = -raw33382step0 := by apply Matrix.ext; change ∀ i j, raw33382step1 i j = -(raw33382step0 i j); unfold raw33382step1 raw33382step0; decide +kernel
      have hl : raw33382step1Labels = raw33382step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1869 node1869Labels := by rfl

def raw33383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![2, 0, -2]]
def raw33383Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33383step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw33383step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33383step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw33383step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33383 raw33383Labels = mixedMoment B node3745 node3745Labels := by
  calc
    mixedMoment B raw33383 raw33383Labels = mixedMoment B raw33383step0 raw33383step0Labels := by
      have ha : raw33383step0 = (fun i j => raw33383 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33383step0 raw33383; decide +kernel
      have hl : raw33383step0Labels = raw33383Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33383 raw33383Labels permutation662 permutation2
    mixedMoment B raw33383step0 raw33383step0Labels = mixedMoment B raw33383step1 raw33383step1Labels := by
      have ha : raw33383step1 = -raw33383step0 := by apply Matrix.ext; change ∀ i j, raw33383step1 i j = -(raw33383step0 i j); unfold raw33383step1 raw33383step0; decide +kernel
      have hl : raw33383step1Labels = raw33383step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3745 node3745Labels := by rfl

def raw33384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![2, 0, -2], ![1, -1, 0], ![2, 0, -2]]
def raw33384Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33384step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, -1, 0], ![2, 0, -2], ![2, 0, -2]]
def raw33384step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33384 raw33384Labels = mixedMoment B node2414 node2414Labels := by
  calc
    mixedMoment B raw33384 raw33384Labels = mixedMoment B raw33384step0 raw33384step0Labels := by
      have ha : raw33384step0 = (fun i j => raw33384 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33384step0 raw33384; decide +kernel
      have hl : raw33384step0Labels = raw33384Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33384 raw33384Labels permutation154 permutation2
    _ = mixedMoment B node2414 node2414Labels := by rfl

def raw33385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, 0, -2]]
def raw33385Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33385 raw33385Labels = mixedMoment B node2419 node2419Labels := by
  calc
    _ = mixedMoment B node2419 node2419Labels := by rfl

def raw33386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 1, -2], ![1, -1, 0], ![3, -1, -2]]
def raw33386Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33386step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, 1, -2], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw33386step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw33386step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw33386step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical33386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33386 raw33386Labels = mixedMoment B node2371 node2371Labels := by
  calc
    mixedMoment B raw33386 raw33386Labels = mixedMoment B raw33386step0 raw33386step0Labels := by
      have ha : raw33386step0 = (fun i j => raw33386 (permutation662 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33386step0 raw33386; decide +kernel
      have hl : raw33386step0Labels = raw33386Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33386 raw33386Labels permutation662 permutation2
    mixedMoment B raw33386step0 raw33386step0Labels = mixedMoment B raw33386step1 raw33386step1Labels := by
      have ha : raw33386step1 = -raw33386step0 := by apply Matrix.ext; change ∀ i j, raw33386step1 i j = -(raw33386step0 i j); unfold raw33386step1 raw33386step0; decide +kernel
      have hl : raw33386step1Labels = raw33386step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2371 node2371Labels := by rfl

def raw33387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw33387Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33387 raw33387Labels = mixedMoment B node5345 node5345Labels := by
  calc
    _ = mixedMoment B node5345 node5345Labels := by rfl

def raw33388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw33388Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33388step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw33388step0Labels : Fin 2 → Fin 3 := ![0, 2]

def raw33388step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![2, -2]]
def raw33388step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical33388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33388 raw33388Labels = mixedMoment B node4090 node4090Labels := by
  calc
    mixedMoment B raw33388 raw33388Labels = mixedMoment B raw33388step0 raw33388step0Labels := by
      have hz : ∀ i, raw33388 i (permutation4 0) = 0 := by decide +kernel
      have ha : raw33388step0 = (fun i j => raw33388 i (permutation4 j.succ)) := by apply Matrix.ext; unfold raw33388step0 raw33388; decide +kernel
      have hl : raw33388step0Labels = (fun j => raw33388Labels (permutation4 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw33388 raw33388Labels permutation4 hz
    mixedMoment B raw33388step0 raw33388step0Labels = mixedMoment B raw33388step1 raw33388step1Labels := by
      have ha : raw33388step1 = raw33388step0 := by apply Matrix.ext; unfold raw33388step1 raw33388step0; decide +kernel
      have hl : raw33388step0Labels = labelEmbedding2 ∘ raw33388step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33388step0 raw33388step0Labels raw33388step1Labels labelEmbedding2 hl
    _ = mixedMoment B node4090 node4090Labels := by rfl

def raw33389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw33389Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33389step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33389step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33389step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33389step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33389 raw33389Labels = mixedMoment B node5394 node5394Labels := by
  calc
    mixedMoment B raw33389 raw33389Labels = mixedMoment B raw33389step0 raw33389step0Labels := by
      have ha : raw33389step0 = (fun i j => raw33389 (permutation688 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33389step0 raw33389; decide +kernel
      have hl : raw33389step0Labels = raw33389Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33389 raw33389Labels permutation688 permutation7
    mixedMoment B raw33389step0 raw33389step0Labels = mixedMoment B raw33389step1 raw33389step1Labels := by
      have ha : raw33389step1 = raw33389step0 := by apply Matrix.ext; unfold raw33389step1 raw33389step0; decide +kernel
      have hl : raw33389step0Labels = labelEmbedding10 ∘ raw33389step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33389step0 raw33389step0Labels raw33389step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5394 node5394Labels := by rfl

def raw33390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, 0, -2]]
def raw33390Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33390step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33390step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33390step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw33390step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33390 raw33390Labels = mixedMoment B node5394 node5394Labels := by
  calc
    mixedMoment B raw33390 raw33390Labels = mixedMoment B raw33390step0 raw33390step0Labels := by
      have ha : raw33390step0 = (fun i j => raw33390 (permutation664 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33390step0 raw33390; decide +kernel
      have hl : raw33390step0Labels = raw33390Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33390 raw33390Labels permutation664 permutation7
    mixedMoment B raw33390step0 raw33390step0Labels = mixedMoment B raw33390step1 raw33390step1Labels := by
      have ha : raw33390step1 = raw33390step0 := by apply Matrix.ext; unfold raw33390step1 raw33390step0; decide +kernel
      have hl : raw33390step0Labels = labelEmbedding10 ∘ raw33390step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33390step0 raw33390step0Labels raw33390step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5394 node5394Labels := by rfl

def raw33391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33391Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33391step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw33391step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33391step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33391step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw33391step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw33391step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33391 raw33391Labels = mixedMoment B node5396 node5396Labels := by
  calc
    mixedMoment B raw33391 raw33391Labels = mixedMoment B raw33391step0 raw33391step0Labels := by
      have ha : raw33391step0 = (fun i j => raw33391 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw33391step0 raw33391; decide +kernel
      have hl : raw33391step0Labels = raw33391Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33391 raw33391Labels permutation152 permutation7
    mixedMoment B raw33391step0 raw33391step0Labels = mixedMoment B raw33391step1 raw33391step1Labels := by
      have ha : raw33391step1 = -raw33391step0 := by apply Matrix.ext; change ∀ i j, raw33391step1 i j = -(raw33391step0 i j); unfold raw33391step1 raw33391step0; decide +kernel
      have hl : raw33391step1Labels = raw33391step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw33391step1 raw33391step1Labels = mixedMoment B raw33391step2 raw33391step2Labels := by
      have ha : raw33391step2 = raw33391step1 := by apply Matrix.ext; unfold raw33391step2 raw33391step1; decide +kernel
      have hl : raw33391step1Labels = labelEmbedding10 ∘ raw33391step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw33391step1 raw33391step1Labels raw33391step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5396 node5396Labels := by rfl

def raw33392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw33392Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33392 raw33392Labels = mixedMoment B node4581 node4581Labels := by
  calc
    _ = mixedMoment B node4581 node4581Labels := by rfl

def raw33393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw33393Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33393step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw33393step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33393 raw33393Labels = mixedMoment B node5058 node5058Labels := by
  calc
    mixedMoment B raw33393 raw33393Labels = mixedMoment B raw33393step0 raw33393step0Labels := by
      have ha : raw33393step0 = (fun i j => raw33393 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33393step0 raw33393; decide +kernel
      have hl : raw33393step0Labels = raw33393Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33393 raw33393Labels permutation176 permutation2
    _ = mixedMoment B node5058 node5058Labels := by rfl

def raw33394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw33394Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33394 raw33394Labels = mixedMoment B node5241 node5241Labels := by
  calc
    _ = mixedMoment B node5241 node5241Labels := by rfl

def raw33395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, 0, -2]]
def raw33395Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33395step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw33395step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33395 raw33395Labels = mixedMoment B node5241 node5241Labels := by
  calc
    mixedMoment B raw33395 raw33395Labels = mixedMoment B raw33395step0 raw33395step0Labels := by
      have ha : raw33395step0 = (fun i j => raw33395 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33395step0 raw33395; decide +kernel
      have hl : raw33395step0Labels = raw33395Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33395 raw33395Labels permutation154 permutation2
    _ = mixedMoment B node5241 node5241Labels := by rfl

def raw33396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33396Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33396 raw33396Labels = mixedMoment B node5247 node5247Labels := by
  calc
    _ = mixedMoment B node5247 node5247Labels := by rfl

def raw33397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw33397Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33397 raw33397Labels = mixedMoment B node4537 node4537Labels := by
  calc
    _ = mixedMoment B node4537 node4537Labels := by rfl

def raw33398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw33398Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33398 raw33398Labels = mixedMoment B node4936 node4936Labels := by
  calc
    _ = mixedMoment B node4936 node4936Labels := by rfl

def raw33399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw33399Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33399step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw33399step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33399 raw33399Labels = mixedMoment B node5070 node5070Labels := by
  calc
    mixedMoment B raw33399 raw33399Labels = mixedMoment B raw33399step0 raw33399step0Labels := by
      have ha : raw33399step0 = (fun i j => raw33399 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33399step0 raw33399; decide +kernel
      have hl : raw33399step0Labels = raw33399Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33399 raw33399Labels permutation158 permutation2
    _ = mixedMoment B node5070 node5070Labels := by rfl

def raw33400 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![2, 0, -2]]
def raw33400Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33400step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw33400step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33400 raw33400Labels = mixedMoment B node5070 node5070Labels := by
  calc
    mixedMoment B raw33400 raw33400Labels = mixedMoment B raw33400step0 raw33400step0Labels := by
      have ha : raw33400step0 = (fun i j => raw33400 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33400step0 raw33400; decide +kernel
      have hl : raw33400step0Labels = raw33400Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33400 raw33400Labels permutation164 permutation2
    _ = mixedMoment B node5070 node5070Labels := by rfl

def raw33401 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33401Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33401 raw33401Labels = mixedMoment B node5093 node5093Labels := by
  calc
    _ = mixedMoment B node5093 node5093Labels := by rfl

def raw33402 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw33402Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33402step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw33402step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33402 raw33402Labels = mixedMoment B node4524 node4524Labels := by
  calc
    mixedMoment B raw33402 raw33402Labels = mixedMoment B raw33402step0 raw33402step0Labels := by
      have ha : raw33402step0 = (fun i j => raw33402 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33402step0 raw33402; decide +kernel
      have hl : raw33402step0Labels = raw33402Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33402 raw33402Labels permutation154 permutation2
    _ = mixedMoment B node4524 node4524Labels := by rfl

def raw33403 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw33403Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33403step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw33403step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33403 raw33403Labels = mixedMoment B node4928 node4928Labels := by
  calc
    mixedMoment B raw33403 raw33403Labels = mixedMoment B raw33403step0 raw33403step0Labels := by
      have ha : raw33403step0 = (fun i j => raw33403 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33403step0 raw33403; decide +kernel
      have hl : raw33403step0Labels = raw33403Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33403 raw33403Labels permutation154 permutation2
    _ = mixedMoment B node4928 node4928Labels := by rfl

def raw33404 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw33404Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33404step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw33404step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33404 raw33404Labels = mixedMoment B node5029 node5029Labels := by
  calc
    mixedMoment B raw33404 raw33404Labels = mixedMoment B raw33404step0 raw33404step0Labels := by
      have ha : raw33404step0 = (fun i j => raw33404 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33404step0 raw33404; decide +kernel
      have hl : raw33404step0Labels = raw33404Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33404 raw33404Labels permutation154 permutation2
    _ = mixedMoment B node5029 node5029Labels := by rfl

def raw33405 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![2, 0, -2]]
def raw33405Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33405step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw33405step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33405 raw33405Labels = mixedMoment B node5050 node5050Labels := by
  calc
    mixedMoment B raw33405 raw33405Labels = mixedMoment B raw33405step0 raw33405step0Labels := by
      have ha : raw33405step0 = (fun i j => raw33405 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33405step0 raw33405; decide +kernel
      have hl : raw33405step0Labels = raw33405Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33405 raw33405Labels permutation154 permutation2
    _ = mixedMoment B node5050 node5050Labels := by rfl

def raw33406 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 1, -2]]
def raw33406Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw33406step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw33406step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33406 raw33406Labels = mixedMoment B node5059 node5059Labels := by
  calc
    mixedMoment B raw33406 raw33406Labels = mixedMoment B raw33406step0 raw33406step0Labels := by
      have ha : raw33406step0 = (fun i j => raw33406 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw33406step0 raw33406; decide +kernel
      have hl : raw33406step0Labels = raw33406Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw33406 raw33406Labels permutation155 permutation2
    _ = mixedMoment B node5059 node5059Labels := by rfl

def raw33407 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw33407Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical33407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw33407 raw33407Labels = mixedMoment B node4524 node4524Labels := by
  calc
    _ = mixedMoment B node4524 node4524Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
