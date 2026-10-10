import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes9
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes10
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes20
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes23
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes65
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes70
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw24320 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24320Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24320step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24320step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24320step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw24320step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24320step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw24320step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24320 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24320 raw24320Labels = mixedMoment B node4556 node4556Labels := by
  calc
    mixedMoment B raw24320 raw24320Labels = mixedMoment B raw24320step0 raw24320step0Labels := by
      have hz : ∀ j, raw24320 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24320step0 = (fun i j => raw24320 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24320step0 raw24320; decide +kernel
      have hl : raw24320step0Labels = raw24320Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24320 raw24320Labels permutation346 hz
    mixedMoment B raw24320step0 raw24320step0Labels = mixedMoment B raw24320step1 raw24320step1Labels := by
      have ha : raw24320step1 = (fun i j => raw24320step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24320step1 raw24320step0; decide +kernel
      have hl : raw24320step1Labels = raw24320step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24320step0 raw24320step0Labels permutation35 permutation3
    mixedMoment B raw24320step1 raw24320step1Labels = mixedMoment B raw24320step2 raw24320step2Labels := by
      have ha : raw24320step2 = raw24320step1 := by apply Matrix.ext; unfold raw24320step2 raw24320step1; decide +kernel
      have hl : raw24320step1Labels = labelEmbedding6 ∘ raw24320step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24320step1 raw24320step1Labels raw24320step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4556 node4556Labels := by rfl

def raw24321 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24321Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24321step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24321step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24321step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw24321step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24321step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw24321step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24321 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24321 raw24321Labels = mixedMoment B node4556 node4556Labels := by
  calc
    mixedMoment B raw24321 raw24321Labels = mixedMoment B raw24321step0 raw24321step0Labels := by
      have hz : ∀ j, raw24321 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24321step0 = (fun i j => raw24321 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24321step0 raw24321; decide +kernel
      have hl : raw24321step0Labels = raw24321Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24321 raw24321Labels permutation265 hz
    mixedMoment B raw24321step0 raw24321step0Labels = mixedMoment B raw24321step1 raw24321step1Labels := by
      have ha : raw24321step1 = (fun i j => raw24321step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24321step1 raw24321step0; decide +kernel
      have hl : raw24321step1Labels = raw24321step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24321step0 raw24321step0Labels permutation35 permutation3
    mixedMoment B raw24321step1 raw24321step1Labels = mixedMoment B raw24321step2 raw24321step2Labels := by
      have ha : raw24321step2 = raw24321step1 := by apply Matrix.ext; unfold raw24321step2 raw24321step1; decide +kernel
      have hl : raw24321step1Labels = labelEmbedding6 ∘ raw24321step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24321step1 raw24321step1Labels raw24321step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4556 node4556Labels := by rfl

def raw24322 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24322Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24322step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24322step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24322step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24322step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24322step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw24322step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24322 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24322 raw24322Labels = mixedMoment B node4612 node4612Labels := by
  calc
    mixedMoment B raw24322 raw24322Labels = mixedMoment B raw24322step0 raw24322step0Labels := by
      have hz : ∀ j, raw24322 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24322step0 = (fun i j => raw24322 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24322step0 raw24322; decide +kernel
      have hl : raw24322step0Labels = raw24322Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24322 raw24322Labels permutation346 hz
    mixedMoment B raw24322step0 raw24322step0Labels = mixedMoment B raw24322step1 raw24322step1Labels := by
      have hz : ∀ j, raw24322step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24322step1 = (fun i j => raw24322step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24322step1 raw24322step0; decide +kernel
      have hl : raw24322step1Labels = raw24322step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24322step0 raw24322step0Labels permutation56 hz
    mixedMoment B raw24322step1 raw24322step1Labels = mixedMoment B raw24322step2 raw24322step2Labels := by
      have ha : raw24322step2 = (fun i j => raw24322step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24322step2 raw24322step1; decide +kernel
      have hl : raw24322step2Labels = raw24322step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24322step1 raw24322step1Labels permutation10 permutation2
    _ = mixedMoment B node4612 node4612Labels := by rfl

def raw24323 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24323Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24323step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24323step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24323step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24323step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24323step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw24323step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24323 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24323 raw24323Labels = mixedMoment B node4620 node4620Labels := by
  calc
    mixedMoment B raw24323 raw24323Labels = mixedMoment B raw24323step0 raw24323step0Labels := by
      have hz : ∀ j, raw24323 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24323step0 = (fun i j => raw24323 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24323step0 raw24323; decide +kernel
      have hl : raw24323step0Labels = raw24323Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24323 raw24323Labels permutation346 hz
    mixedMoment B raw24323step0 raw24323step0Labels = mixedMoment B raw24323step1 raw24323step1Labels := by
      have hz : ∀ j, raw24323step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24323step1 = (fun i j => raw24323step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24323step1 raw24323step0; decide +kernel
      have hl : raw24323step1Labels = raw24323step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24323step0 raw24323step0Labels permutation56 hz
    mixedMoment B raw24323step1 raw24323step1Labels = mixedMoment B raw24323step2 raw24323step2Labels := by
      have ha : raw24323step2 = (fun i j => raw24323step1 (permutation11 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24323step2 raw24323step1; decide +kernel
      have hl : raw24323step2Labels = raw24323step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24323step1 raw24323step1Labels permutation11 permutation2
    _ = mixedMoment B node4620 node4620Labels := by rfl

def raw24324 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24324Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24324step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24324step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24324step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24324step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24324step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw24324step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24324step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw24324step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24324 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24324 raw24324Labels = mixedMoment B node4179 node4179Labels := by
  calc
    mixedMoment B raw24324 raw24324Labels = mixedMoment B raw24324step0 raw24324step0Labels := by
      have hz : ∀ j, raw24324 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24324step0 = (fun i j => raw24324 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24324step0 raw24324; decide +kernel
      have hl : raw24324step0Labels = raw24324Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24324 raw24324Labels permutation346 hz
    mixedMoment B raw24324step0 raw24324step0Labels = mixedMoment B raw24324step1 raw24324step1Labels := by
      have hz : ∀ j, raw24324step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24324step1 = (fun i j => raw24324step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24324step1 raw24324step0; decide +kernel
      have hl : raw24324step1Labels = raw24324step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24324step0 raw24324step0Labels permutation56 hz
    mixedMoment B raw24324step1 raw24324step1Labels = mixedMoment B raw24324step2 raw24324step2Labels := by
      have ha : raw24324step2 = (fun i j => raw24324step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24324step2 raw24324step1; decide +kernel
      have hl : raw24324step2Labels = raw24324step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24324step1 raw24324step1Labels permutation9 permutation3
    mixedMoment B raw24324step2 raw24324step2Labels = mixedMoment B raw24324step3 raw24324step3Labels := by
      have ha : raw24324step3 = raw24324step2 := by apply Matrix.ext; unfold raw24324step3 raw24324step2; decide +kernel
      have hl : raw24324step2Labels = labelEmbedding6 ∘ raw24324step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24324step2 raw24324step2Labels raw24324step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4179 node4179Labels := by rfl

def raw24325 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24325Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24325step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24325step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24325step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw24325step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24325step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw24325step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24325 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24325 raw24325Labels = mixedMoment B node4548 node4548Labels := by
  calc
    mixedMoment B raw24325 raw24325Labels = mixedMoment B raw24325step0 raw24325step0Labels := by
      have hz : ∀ j, raw24325 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24325step0 = (fun i j => raw24325 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24325step0 raw24325; decide +kernel
      have hl : raw24325step0Labels = raw24325Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24325 raw24325Labels permutation346 hz
    mixedMoment B raw24325step0 raw24325step0Labels = mixedMoment B raw24325step1 raw24325step1Labels := by
      have ha : raw24325step1 = (fun i j => raw24325step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24325step1 raw24325step0; decide +kernel
      have hl : raw24325step1Labels = raw24325step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24325step0 raw24325step0Labels permutation33 permutation3
    mixedMoment B raw24325step1 raw24325step1Labels = mixedMoment B raw24325step2 raw24325step2Labels := by
      have ha : raw24325step2 = raw24325step1 := by apply Matrix.ext; unfold raw24325step2 raw24325step1; decide +kernel
      have hl : raw24325step1Labels = labelEmbedding6 ∘ raw24325step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24325step1 raw24325step1Labels raw24325step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4548 node4548Labels := by rfl

def raw24326 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24326Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24326step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24326step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24326step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw24326step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24326step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw24326step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24326 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24326 raw24326Labels = mixedMoment B node4548 node4548Labels := by
  calc
    mixedMoment B raw24326 raw24326Labels = mixedMoment B raw24326step0 raw24326step0Labels := by
      have hz : ∀ j, raw24326 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24326step0 = (fun i j => raw24326 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24326step0 raw24326; decide +kernel
      have hl : raw24326step0Labels = raw24326Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24326 raw24326Labels permutation265 hz
    mixedMoment B raw24326step0 raw24326step0Labels = mixedMoment B raw24326step1 raw24326step1Labels := by
      have ha : raw24326step1 = (fun i j => raw24326step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24326step1 raw24326step0; decide +kernel
      have hl : raw24326step1Labels = raw24326step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24326step0 raw24326step0Labels permutation33 permutation3
    mixedMoment B raw24326step1 raw24326step1Labels = mixedMoment B raw24326step2 raw24326step2Labels := by
      have ha : raw24326step2 = raw24326step1 := by apply Matrix.ext; unfold raw24326step2 raw24326step1; decide +kernel
      have hl : raw24326step1Labels = labelEmbedding6 ∘ raw24326step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24326step1 raw24326step1Labels raw24326step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4548 node4548Labels := by rfl

def raw24327 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24327Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24327step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24327step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24327step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24327step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24327step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw24327step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24327step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw24327step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24327 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24327 raw24327Labels = mixedMoment B node4611 node4611Labels := by
  calc
    mixedMoment B raw24327 raw24327Labels = mixedMoment B raw24327step0 raw24327step0Labels := by
      have hz : ∀ j, raw24327 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24327step0 = (fun i j => raw24327 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24327step0 raw24327; decide +kernel
      have hl : raw24327step0Labels = raw24327Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24327 raw24327Labels permutation346 hz
    mixedMoment B raw24327step0 raw24327step0Labels = mixedMoment B raw24327step1 raw24327step1Labels := by
      have hz : ∀ j, raw24327step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24327step1 = (fun i j => raw24327step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24327step1 raw24327step0; decide +kernel
      have hl : raw24327step1Labels = raw24327step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24327step0 raw24327step0Labels permutation56 hz
    mixedMoment B raw24327step1 raw24327step1Labels = mixedMoment B raw24327step2 raw24327step2Labels := by
      have ha : raw24327step2 = (fun i j => raw24327step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24327step2 raw24327step1; decide +kernel
      have hl : raw24327step2Labels = raw24327step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24327step1 raw24327step1Labels permutation9 permutation3
    mixedMoment B raw24327step2 raw24327step2Labels = mixedMoment B raw24327step3 raw24327step3Labels := by
      have ha : raw24327step3 = raw24327step2 := by apply Matrix.ext; unfold raw24327step3 raw24327step2; decide +kernel
      have hl : raw24327step2Labels = labelEmbedding6 ∘ raw24327step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24327step2 raw24327step2Labels raw24327step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4611 node4611Labels := by rfl

def raw24328 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw24328Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24328step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw24328step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24328step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw24328step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24328step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw24328step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24328step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw24328step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24328 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24328 raw24328Labels = mixedMoment B node4617 node4617Labels := by
  calc
    mixedMoment B raw24328 raw24328Labels = mixedMoment B raw24328step0 raw24328step0Labels := by
      have hz : ∀ j, raw24328 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24328step0 = (fun i j => raw24328 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24328step0 raw24328; decide +kernel
      have hl : raw24328step0Labels = raw24328Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24328 raw24328Labels permutation346 hz
    mixedMoment B raw24328step0 raw24328step0Labels = mixedMoment B raw24328step1 raw24328step1Labels := by
      have hz : ∀ j, raw24328step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24328step1 = (fun i j => raw24328step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24328step1 raw24328step0; decide +kernel
      have hl : raw24328step1Labels = raw24328step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24328step0 raw24328step0Labels permutation56 hz
    mixedMoment B raw24328step1 raw24328step1Labels = mixedMoment B raw24328step2 raw24328step2Labels := by
      have ha : raw24328step2 = (fun i j => raw24328step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24328step2 raw24328step1; decide +kernel
      have hl : raw24328step2Labels = raw24328step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24328step1 raw24328step1Labels permutation12 permutation3
    mixedMoment B raw24328step2 raw24328step2Labels = mixedMoment B raw24328step3 raw24328step3Labels := by
      have ha : raw24328step3 = raw24328step2 := by apply Matrix.ext; unfold raw24328step3 raw24328step2; decide +kernel
      have hl : raw24328step2Labels = labelEmbedding6 ∘ raw24328step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24328step2 raw24328step2Labels raw24328step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4617 node4617Labels := by rfl

def raw24329 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24329Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24329step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24329step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24329step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24329step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24329step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw24329step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24329step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw24329step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24329 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24329 raw24329Labels = mixedMoment B node4178 node4178Labels := by
  calc
    mixedMoment B raw24329 raw24329Labels = mixedMoment B raw24329step0 raw24329step0Labels := by
      have hz : ∀ j, raw24329 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24329step0 = (fun i j => raw24329 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24329step0 raw24329; decide +kernel
      have hl : raw24329step0Labels = raw24329Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24329 raw24329Labels permutation346 hz
    mixedMoment B raw24329step0 raw24329step0Labels = mixedMoment B raw24329step1 raw24329step1Labels := by
      have hz : ∀ j, raw24329step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24329step1 = (fun i j => raw24329step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24329step1 raw24329step0; decide +kernel
      have hl : raw24329step1Labels = raw24329step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24329step0 raw24329step0Labels permutation56 hz
    mixedMoment B raw24329step1 raw24329step1Labels = mixedMoment B raw24329step2 raw24329step2Labels := by
      have ha : raw24329step2 = (fun i j => raw24329step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24329step2 raw24329step1; decide +kernel
      have hl : raw24329step2Labels = raw24329step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24329step1 raw24329step1Labels permutation8 permutation3
    mixedMoment B raw24329step2 raw24329step2Labels = mixedMoment B raw24329step3 raw24329step3Labels := by
      have ha : raw24329step3 = raw24329step2 := by apply Matrix.ext; unfold raw24329step3 raw24329step2; decide +kernel
      have hl : raw24329step2Labels = labelEmbedding6 ∘ raw24329step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24329step2 raw24329step2Labels raw24329step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4178 node4178Labels := by rfl

def raw24330 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24330Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24330step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24330step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24330step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw24330step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24330step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw24330step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24330 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24330 raw24330Labels = mixedMoment B node4547 node4547Labels := by
  calc
    mixedMoment B raw24330 raw24330Labels = mixedMoment B raw24330step0 raw24330step0Labels := by
      have hz : ∀ j, raw24330 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24330step0 = (fun i j => raw24330 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24330step0 raw24330; decide +kernel
      have hl : raw24330step0Labels = raw24330Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24330 raw24330Labels permutation346 hz
    mixedMoment B raw24330step0 raw24330step0Labels = mixedMoment B raw24330step1 raw24330step1Labels := by
      have ha : raw24330step1 = (fun i j => raw24330step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24330step1 raw24330step0; decide +kernel
      have hl : raw24330step1Labels = raw24330step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24330step0 raw24330step0Labels permutation32 permutation3
    mixedMoment B raw24330step1 raw24330step1Labels = mixedMoment B raw24330step2 raw24330step2Labels := by
      have ha : raw24330step2 = raw24330step1 := by apply Matrix.ext; unfold raw24330step2 raw24330step1; decide +kernel
      have hl : raw24330step1Labels = labelEmbedding6 ∘ raw24330step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24330step1 raw24330step1Labels raw24330step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4547 node4547Labels := by rfl

def raw24331 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24331Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24331step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24331step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24331step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw24331step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24331step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw24331step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24331 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24331 raw24331Labels = mixedMoment B node4547 node4547Labels := by
  calc
    mixedMoment B raw24331 raw24331Labels = mixedMoment B raw24331step0 raw24331step0Labels := by
      have hz : ∀ j, raw24331 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24331step0 = (fun i j => raw24331 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24331step0 raw24331; decide +kernel
      have hl : raw24331step0Labels = raw24331Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24331 raw24331Labels permutation265 hz
    mixedMoment B raw24331step0 raw24331step0Labels = mixedMoment B raw24331step1 raw24331step1Labels := by
      have ha : raw24331step1 = (fun i j => raw24331step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24331step1 raw24331step0; decide +kernel
      have hl : raw24331step1Labels = raw24331step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24331step0 raw24331step0Labels permutation32 permutation3
    mixedMoment B raw24331step1 raw24331step1Labels = mixedMoment B raw24331step2 raw24331step2Labels := by
      have ha : raw24331step2 = raw24331step1 := by apply Matrix.ext; unfold raw24331step2 raw24331step1; decide +kernel
      have hl : raw24331step1Labels = labelEmbedding6 ∘ raw24331step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24331step1 raw24331step1Labels raw24331step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4547 node4547Labels := by rfl

def raw24332 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24332Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24332step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24332step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24332step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24332step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24332step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw24332step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw24332step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw24332step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24332 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24332 raw24332Labels = mixedMoment B node4609 node4609Labels := by
  calc
    mixedMoment B raw24332 raw24332Labels = mixedMoment B raw24332step0 raw24332step0Labels := by
      have hz : ∀ j, raw24332 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24332step0 = (fun i j => raw24332 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24332step0 raw24332; decide +kernel
      have hl : raw24332step0Labels = raw24332Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24332 raw24332Labels permutation346 hz
    mixedMoment B raw24332step0 raw24332step0Labels = mixedMoment B raw24332step1 raw24332step1Labels := by
      have hz : ∀ j, raw24332step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24332step1 = (fun i j => raw24332step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24332step1 raw24332step0; decide +kernel
      have hl : raw24332step1Labels = raw24332step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24332step0 raw24332step0Labels permutation56 hz
    mixedMoment B raw24332step1 raw24332step1Labels = mixedMoment B raw24332step2 raw24332step2Labels := by
      have ha : raw24332step2 = (fun i j => raw24332step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24332step2 raw24332step1; decide +kernel
      have hl : raw24332step2Labels = raw24332step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24332step1 raw24332step1Labels permutation8 permutation3
    mixedMoment B raw24332step2 raw24332step2Labels = mixedMoment B raw24332step3 raw24332step3Labels := by
      have ha : raw24332step3 = raw24332step2 := by apply Matrix.ext; unfold raw24332step3 raw24332step2; decide +kernel
      have hl : raw24332step2Labels = labelEmbedding6 ∘ raw24332step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24332step2 raw24332step2Labels raw24332step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4609 node4609Labels := by rfl

def raw24333 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw24333Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24333step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw24333step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24333step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw24333step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24333step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![3, -1, -2]]
def raw24333step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24333 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24333 raw24333Labels = mixedMoment B node4608 node4608Labels := by
  calc
    mixedMoment B raw24333 raw24333Labels = mixedMoment B raw24333step0 raw24333step0Labels := by
      have hz : ∀ j, raw24333 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24333step0 = (fun i j => raw24333 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24333step0 raw24333; decide +kernel
      have hl : raw24333step0Labels = raw24333Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24333 raw24333Labels permutation346 hz
    mixedMoment B raw24333step0 raw24333step0Labels = mixedMoment B raw24333step1 raw24333step1Labels := by
      have hz : ∀ j, raw24333step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24333step1 = (fun i j => raw24333step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24333step1 raw24333step0; decide +kernel
      have hl : raw24333step1Labels = raw24333step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24333step0 raw24333step0Labels permutation56 hz
    mixedMoment B raw24333step1 raw24333step1Labels = mixedMoment B raw24333step2 raw24333step2Labels := by
      have ha : raw24333step2 = (fun i j => raw24333step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24333step2 raw24333step1; decide +kernel
      have hl : raw24333step2Labels = raw24333step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24333step1 raw24333step1Labels permutation10 permutation2
    _ = mixedMoment B node4608 node4608Labels := by rfl

def raw24334 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24334Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24334step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24334step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24334step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24334step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24334 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24334 raw24334Labels = mixedMoment B node2961 node2961Labels := by
  calc
    mixedMoment B raw24334 raw24334Labels = mixedMoment B raw24334step0 raw24334step0Labels := by
      have hz : ∀ j, raw24334 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24334step0 = (fun i j => raw24334 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24334step0 raw24334; decide +kernel
      have hl : raw24334step0Labels = raw24334Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24334 raw24334Labels permutation346 hz
    mixedMoment B raw24334step0 raw24334step0Labels = mixedMoment B raw24334step1 raw24334step1Labels := by
      have ha : raw24334step1 = (fun i j => raw24334step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24334step1 raw24334step0; decide +kernel
      have hl : raw24334step1Labels = raw24334step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24334step0 raw24334step0Labels permutation32 permutation3
    _ = mixedMoment B node2961 node2961Labels := by rfl

def raw24335 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24335Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24335step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24335step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24335step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24335step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24335 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24335 raw24335Labels = mixedMoment B node2961 node2961Labels := by
  calc
    mixedMoment B raw24335 raw24335Labels = mixedMoment B raw24335step0 raw24335step0Labels := by
      have hz : ∀ j, raw24335 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24335step0 = (fun i j => raw24335 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24335step0 raw24335; decide +kernel
      have hl : raw24335step0Labels = raw24335Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24335 raw24335Labels permutation265 hz
    mixedMoment B raw24335step0 raw24335step0Labels = mixedMoment B raw24335step1 raw24335step1Labels := by
      have ha : raw24335step1 = (fun i j => raw24335step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24335step1 raw24335step0; decide +kernel
      have hl : raw24335step1Labels = raw24335step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24335step0 raw24335step0Labels permutation32 permutation3
    _ = mixedMoment B node2961 node2961Labels := by rfl

def raw24336 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24336Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24336step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24336step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24336step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24336step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24336step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, 1, -2], ![2, -2, 0]]
def raw24336step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24336 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24336 raw24336Labels = mixedMoment B node3103 node3103Labels := by
  calc
    mixedMoment B raw24336 raw24336Labels = mixedMoment B raw24336step0 raw24336step0Labels := by
      have hz : ∀ j, raw24336 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24336step0 = (fun i j => raw24336 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24336step0 raw24336; decide +kernel
      have hl : raw24336step0Labels = raw24336Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24336 raw24336Labels permutation346 hz
    mixedMoment B raw24336step0 raw24336step0Labels = mixedMoment B raw24336step1 raw24336step1Labels := by
      have hz : ∀ j, raw24336step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24336step1 = (fun i j => raw24336step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24336step1 raw24336step0; decide +kernel
      have hl : raw24336step1Labels = raw24336step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24336step0 raw24336step0Labels permutation56 hz
    mixedMoment B raw24336step1 raw24336step1Labels = mixedMoment B raw24336step2 raw24336step2Labels := by
      have ha : raw24336step2 = (fun i j => raw24336step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24336step2 raw24336step1; decide +kernel
      have hl : raw24336step2Labels = raw24336step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24336step1 raw24336step1Labels permutation8 permutation3
    _ = mixedMoment B node3103 node3103Labels := by rfl

def raw24337 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24337Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24337step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24337step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24337step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24337step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24337step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw24337step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24337 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24337 raw24337Labels = mixedMoment B node3112 node3112Labels := by
  calc
    mixedMoment B raw24337 raw24337Labels = mixedMoment B raw24337step0 raw24337step0Labels := by
      have hz : ∀ j, raw24337 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24337step0 = (fun i j => raw24337 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24337step0 raw24337; decide +kernel
      have hl : raw24337step0Labels = raw24337Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24337 raw24337Labels permutation346 hz
    mixedMoment B raw24337step0 raw24337step0Labels = mixedMoment B raw24337step1 raw24337step1Labels := by
      have hz : ∀ j, raw24337step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24337step1 = (fun i j => raw24337step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24337step1 raw24337step0; decide +kernel
      have hl : raw24337step1Labels = raw24337step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24337step0 raw24337step0Labels permutation56 hz
    mixedMoment B raw24337step1 raw24337step1Labels = mixedMoment B raw24337step2 raw24337step2Labels := by
      have ha : raw24337step2 = (fun i j => raw24337step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24337step2 raw24337step1; decide +kernel
      have hl : raw24337step2Labels = raw24337step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24337step1 raw24337step1Labels permutation10 permutation3
    _ = mixedMoment B node3112 node3112Labels := by rfl

def raw24338 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24338Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24338step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24338step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24338step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24338step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24338step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 2, 1], ![1, -2, 1], ![1, -1, 0], ![1, 1, -2]]
def raw24338step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24338 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24338 raw24338Labels = mixedMoment B node3119 node3119Labels := by
  calc
    mixedMoment B raw24338 raw24338Labels = mixedMoment B raw24338step0 raw24338step0Labels := by
      have hz : ∀ j, raw24338 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24338step0 = (fun i j => raw24338 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24338step0 raw24338; decide +kernel
      have hl : raw24338step0Labels = raw24338Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24338 raw24338Labels permutation346 hz
    mixedMoment B raw24338step0 raw24338step0Labels = mixedMoment B raw24338step1 raw24338step1Labels := by
      have hz : ∀ j, raw24338step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24338step1 = (fun i j => raw24338step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24338step1 raw24338step0; decide +kernel
      have hl : raw24338step1Labels = raw24338step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24338step0 raw24338step0Labels permutation56 hz
    mixedMoment B raw24338step1 raw24338step1Labels = mixedMoment B raw24338step2 raw24338step2Labels := by
      have ha : raw24338step2 = (fun i j => raw24338step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24338step2 raw24338step1; decide +kernel
      have hl : raw24338step2Labels = raw24338step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24338step1 raw24338step1Labels permutation12 permutation3
    _ = mixedMoment B node3119 node3119Labels := by rfl

def raw24339 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24339Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24339step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24339step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24339step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24339step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24339 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24339 raw24339Labels = mixedMoment B node604 node604Labels := by
  calc
    mixedMoment B raw24339 raw24339Labels = mixedMoment B raw24339step0 raw24339step0Labels := by
      have hz : ∀ j, raw24339 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24339step0 = (fun i j => raw24339 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24339step0 raw24339; decide +kernel
      have hl : raw24339step0Labels = raw24339Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24339 raw24339Labels permutation346 hz
    mixedMoment B raw24339step0 raw24339step0Labels = mixedMoment B raw24339step1 raw24339step1Labels := by
      have ha : raw24339step1 = (fun i j => raw24339step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24339step1 raw24339step0; decide +kernel
      have hl : raw24339step1Labels = raw24339step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24339step0 raw24339step0Labels permutation38 permutation3
    _ = mixedMoment B node604 node604Labels := by rfl

def raw24340 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24340Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24340step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24340step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24340 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24340 raw24340Labels = mixedMoment B node1130 node1130Labels := by
  calc
    mixedMoment B raw24340 raw24340Labels = mixedMoment B raw24340step0 raw24340step0Labels := by
      have ha : raw24340step0 = (fun i j => raw24340 (permutation182 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24340step0 raw24340; decide +kernel
      have hl : raw24340step0Labels = raw24340Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24340 raw24340Labels permutation182 permutation3
    _ = mixedMoment B node1130 node1130Labels := by rfl

def raw24341 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24341Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24341step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24341step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24341step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24341step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24341 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24341 raw24341Labels = mixedMoment B node1241 node1241Labels := by
  calc
    mixedMoment B raw24341 raw24341Labels = mixedMoment B raw24341step0 raw24341step0Labels := by
      have hz : ∀ j, raw24341 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24341step0 = (fun i j => raw24341 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24341step0 raw24341; decide +kernel
      have hl : raw24341step0Labels = raw24341Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24341 raw24341Labels permutation346 hz
    mixedMoment B raw24341step0 raw24341step0Labels = mixedMoment B raw24341step1 raw24341step1Labels := by
      have ha : raw24341step1 = (fun i j => raw24341step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24341step1 raw24341step0; decide +kernel
      have hl : raw24341step1Labels = raw24341step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24341step0 raw24341step0Labels permutation38 permutation3
    _ = mixedMoment B node1241 node1241Labels := by rfl

def raw24342 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24342Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24342step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24342step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24342step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24342step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24342 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24342 raw24342Labels = mixedMoment B node1267 node1267Labels := by
  calc
    mixedMoment B raw24342 raw24342Labels = mixedMoment B raw24342step0 raw24342step0Labels := by
      have hz : ∀ j, raw24342 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24342step0 = (fun i j => raw24342 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24342step0 raw24342; decide +kernel
      have hl : raw24342step0Labels = raw24342Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24342 raw24342Labels permutation346 hz
    mixedMoment B raw24342step0 raw24342step0Labels = mixedMoment B raw24342step1 raw24342step1Labels := by
      have ha : raw24342step1 = (fun i j => raw24342step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24342step1 raw24342step0; decide +kernel
      have hl : raw24342step1Labels = raw24342step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24342step0 raw24342step0Labels permutation46 permutation3
    _ = mixedMoment B node1267 node1267Labels := by rfl

def raw24343 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24343Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24343step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24343step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24343step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24343step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24343 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24343 raw24343Labels = mixedMoment B node1291 node1291Labels := by
  calc
    mixedMoment B raw24343 raw24343Labels = mixedMoment B raw24343step0 raw24343step0Labels := by
      have hz : ∀ j, raw24343 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24343step0 = (fun i j => raw24343 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24343step0 raw24343; decide +kernel
      have hl : raw24343step0Labels = raw24343Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24343 raw24343Labels permutation346 hz
    mixedMoment B raw24343step0 raw24343step0Labels = mixedMoment B raw24343step1 raw24343step1Labels := by
      have ha : raw24343step1 = (fun i j => raw24343step0 (permutation52 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24343step1 raw24343step0; decide +kernel
      have hl : raw24343step1Labels = raw24343step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24343step0 raw24343step0Labels permutation52 permutation3
    _ = mixedMoment B node1291 node1291Labels := by rfl

def raw24344 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24344Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24344step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24344step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24344step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24344step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24344 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24344 raw24344Labels = mixedMoment B node604 node604Labels := by
  calc
    mixedMoment B raw24344 raw24344Labels = mixedMoment B raw24344step0 raw24344step0Labels := by
      have hz : ∀ j, raw24344 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24344step0 = (fun i j => raw24344 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24344step0 raw24344; decide +kernel
      have hl : raw24344step0Labels = raw24344Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24344 raw24344Labels permutation265 hz
    mixedMoment B raw24344step0 raw24344step0Labels = mixedMoment B raw24344step1 raw24344step1Labels := by
      have ha : raw24344step1 = (fun i j => raw24344step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24344step1 raw24344step0; decide +kernel
      have hl : raw24344step1Labels = raw24344step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24344step0 raw24344step0Labels permutation38 permutation3
    _ = mixedMoment B node604 node604Labels := by rfl

def raw24345 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24345Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24345step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24345step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24345 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24345 raw24345Labels = mixedMoment B node1130 node1130Labels := by
  calc
    mixedMoment B raw24345 raw24345Labels = mixedMoment B raw24345step0 raw24345step0Labels := by
      have ha : raw24345step0 = (fun i j => raw24345 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24345step0 raw24345; decide +kernel
      have hl : raw24345step0Labels = raw24345Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24345 raw24345Labels permutation158 permutation3
    _ = mixedMoment B node1130 node1130Labels := by rfl

def raw24346 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24346Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24346step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24346step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24346step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24346step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24346 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24346 raw24346Labels = mixedMoment B node1241 node1241Labels := by
  calc
    mixedMoment B raw24346 raw24346Labels = mixedMoment B raw24346step0 raw24346step0Labels := by
      have hz : ∀ j, raw24346 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24346step0 = (fun i j => raw24346 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24346step0 raw24346; decide +kernel
      have hl : raw24346step0Labels = raw24346Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24346 raw24346Labels permutation265 hz
    mixedMoment B raw24346step0 raw24346step0Labels = mixedMoment B raw24346step1 raw24346step1Labels := by
      have ha : raw24346step1 = (fun i j => raw24346step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24346step1 raw24346step0; decide +kernel
      have hl : raw24346step1Labels = raw24346step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24346step0 raw24346step0Labels permutation38 permutation3
    _ = mixedMoment B node1241 node1241Labels := by rfl

def raw24347 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24347Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24347step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24347step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24347step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -2, 0]]
def raw24347step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24347 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24347 raw24347Labels = mixedMoment B node1267 node1267Labels := by
  calc
    mixedMoment B raw24347 raw24347Labels = mixedMoment B raw24347step0 raw24347step0Labels := by
      have hz : ∀ j, raw24347 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24347step0 = (fun i j => raw24347 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24347step0 raw24347; decide +kernel
      have hl : raw24347step0Labels = raw24347Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24347 raw24347Labels permutation265 hz
    mixedMoment B raw24347step0 raw24347step0Labels = mixedMoment B raw24347step1 raw24347step1Labels := by
      have ha : raw24347step1 = (fun i j => raw24347step0 (permutation46 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24347step1 raw24347step0; decide +kernel
      have hl : raw24347step1Labels = raw24347step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24347step0 raw24347step0Labels permutation46 permutation3
    _ = mixedMoment B node1267 node1267Labels := by rfl

def raw24348 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24348Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24348step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24348step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24348step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw24348step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24348 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24348 raw24348Labels = mixedMoment B node1291 node1291Labels := by
  calc
    mixedMoment B raw24348 raw24348Labels = mixedMoment B raw24348step0 raw24348step0Labels := by
      have hz : ∀ j, raw24348 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24348step0 = (fun i j => raw24348 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24348step0 raw24348; decide +kernel
      have hl : raw24348step0Labels = raw24348Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24348 raw24348Labels permutation265 hz
    mixedMoment B raw24348step0 raw24348step0Labels = mixedMoment B raw24348step1 raw24348step1Labels := by
      have ha : raw24348step1 = (fun i j => raw24348step0 (permutation52 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24348step1 raw24348step0; decide +kernel
      have hl : raw24348step1Labels = raw24348step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24348step0 raw24348step0Labels permutation52 permutation3
    _ = mixedMoment B node1291 node1291Labels := by rfl

def raw24349 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24349Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24349step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24349step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24349step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24349step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24349step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw24349step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24349 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24349 raw24349Labels = mixedMoment B node616 node616Labels := by
  calc
    mixedMoment B raw24349 raw24349Labels = mixedMoment B raw24349step0 raw24349step0Labels := by
      have hz : ∀ j, raw24349 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24349step0 = (fun i j => raw24349 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24349step0 raw24349; decide +kernel
      have hl : raw24349step0Labels = raw24349Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24349 raw24349Labels permutation346 hz
    mixedMoment B raw24349step0 raw24349step0Labels = mixedMoment B raw24349step1 raw24349step1Labels := by
      have hz : ∀ j, raw24349step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24349step1 = (fun i j => raw24349step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24349step1 raw24349step0; decide +kernel
      have hl : raw24349step1Labels = raw24349step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24349step0 raw24349step0Labels permutation56 hz
    mixedMoment B raw24349step1 raw24349step1Labels = mixedMoment B raw24349step2 raw24349step2Labels := by
      have ha : raw24349step2 = (fun i j => raw24349step1 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24349step2 raw24349step1; decide +kernel
      have hl : raw24349step2Labels = raw24349step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24349step1 raw24349step1Labels permutation11 permutation3
    _ = mixedMoment B node616 node616Labels := by rfl

def raw24350 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24350Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24350step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24350step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24350step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw24350step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24350 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24350 raw24350Labels = mixedMoment B node1141 node1141Labels := by
  calc
    mixedMoment B raw24350 raw24350Labels = mixedMoment B raw24350step0 raw24350step0Labels := by
      have hz : ∀ j, raw24350 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24350step0 = (fun i j => raw24350 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24350step0 raw24350; decide +kernel
      have hl : raw24350step0Labels = raw24350Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24350 raw24350Labels permutation346 hz
    mixedMoment B raw24350step0 raw24350step0Labels = mixedMoment B raw24350step1 raw24350step1Labels := by
      have ha : raw24350step1 = (fun i j => raw24350step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24350step1 raw24350step0; decide +kernel
      have hl : raw24350step1Labels = raw24350step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24350step0 raw24350step0Labels permutation35 permutation3
    _ = mixedMoment B node1141 node1141Labels := by rfl

def raw24351 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24351Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24351step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24351step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24351step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw24351step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24351 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24351 raw24351Labels = mixedMoment B node1141 node1141Labels := by
  calc
    mixedMoment B raw24351 raw24351Labels = mixedMoment B raw24351step0 raw24351step0Labels := by
      have hz : ∀ j, raw24351 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24351step0 = (fun i j => raw24351 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24351step0 raw24351; decide +kernel
      have hl : raw24351step0Labels = raw24351Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24351 raw24351Labels permutation265 hz
    mixedMoment B raw24351step0 raw24351step0Labels = mixedMoment B raw24351step1 raw24351step1Labels := by
      have ha : raw24351step1 = (fun i j => raw24351step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24351step1 raw24351step0; decide +kernel
      have hl : raw24351step1Labels = raw24351step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24351step0 raw24351step0Labels permutation35 permutation3
    _ = mixedMoment B node1141 node1141Labels := by rfl

def raw24352 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24352Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24352step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24352step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24352step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24352step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24352step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw24352step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24352 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24352 raw24352Labels = mixedMoment B node1274 node1274Labels := by
  calc
    mixedMoment B raw24352 raw24352Labels = mixedMoment B raw24352step0 raw24352step0Labels := by
      have hz : ∀ j, raw24352 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24352step0 = (fun i j => raw24352 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24352step0 raw24352; decide +kernel
      have hl : raw24352step0Labels = raw24352Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24352 raw24352Labels permutation346 hz
    mixedMoment B raw24352step0 raw24352step0Labels = mixedMoment B raw24352step1 raw24352step1Labels := by
      have hz : ∀ j, raw24352step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24352step1 = (fun i j => raw24352step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24352step1 raw24352step0; decide +kernel
      have hl : raw24352step1Labels = raw24352step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24352step0 raw24352step0Labels permutation56 hz
    mixedMoment B raw24352step1 raw24352step1Labels = mixedMoment B raw24352step2 raw24352step2Labels := by
      have ha : raw24352step2 = (fun i j => raw24352step1 (permutation11 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24352step2 raw24352step1; decide +kernel
      have hl : raw24352step2Labels = raw24352step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24352step1 raw24352step1Labels permutation11 permutation3
    _ = mixedMoment B node1274 node1274Labels := by rfl

def raw24353 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24353Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24353step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24353step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24353step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24353step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24353step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw24353step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24353 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24353 raw24353Labels = mixedMoment B node1295 node1295Labels := by
  calc
    mixedMoment B raw24353 raw24353Labels = mixedMoment B raw24353step0 raw24353step0Labels := by
      have hz : ∀ j, raw24353 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24353step0 = (fun i j => raw24353 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24353step0 raw24353; decide +kernel
      have hl : raw24353step0Labels = raw24353Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24353 raw24353Labels permutation346 hz
    mixedMoment B raw24353step0 raw24353step0Labels = mixedMoment B raw24353step1 raw24353step1Labels := by
      have hz : ∀ j, raw24353step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24353step1 = (fun i j => raw24353step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24353step1 raw24353step0; decide +kernel
      have hl : raw24353step1Labels = raw24353step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24353step0 raw24353step0Labels permutation56 hz
    mixedMoment B raw24353step1 raw24353step1Labels = mixedMoment B raw24353step2 raw24353step2Labels := by
      have ha : raw24353step2 = (fun i j => raw24353step1 (permutation13 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24353step2 raw24353step1; decide +kernel
      have hl : raw24353step2Labels = raw24353step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24353step1 raw24353step1Labels permutation13 permutation3
    _ = mixedMoment B node1295 node1295Labels := by rfl

def raw24354 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24354Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24354step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24354step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24354step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24354step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24354step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw24354step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24354 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24354 raw24354Labels = mixedMoment B node607 node607Labels := by
  calc
    mixedMoment B raw24354 raw24354Labels = mixedMoment B raw24354step0 raw24354step0Labels := by
      have hz : ∀ j, raw24354 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24354step0 = (fun i j => raw24354 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24354step0 raw24354; decide +kernel
      have hl : raw24354step0Labels = raw24354Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24354 raw24354Labels permutation346 hz
    mixedMoment B raw24354step0 raw24354step0Labels = mixedMoment B raw24354step1 raw24354step1Labels := by
      have hz : ∀ j, raw24354step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24354step1 = (fun i j => raw24354step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24354step1 raw24354step0; decide +kernel
      have hl : raw24354step1Labels = raw24354step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24354step0 raw24354step0Labels permutation56 hz
    mixedMoment B raw24354step1 raw24354step1Labels = mixedMoment B raw24354step2 raw24354step2Labels := by
      have ha : raw24354step2 = (fun i j => raw24354step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24354step2 raw24354step1; decide +kernel
      have hl : raw24354step2Labels = raw24354step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24354step1 raw24354step1Labels permutation9 permutation3
    _ = mixedMoment B node607 node607Labels := by rfl

def raw24355 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24355Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24355step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24355step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24355step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw24355step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24355 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24355 raw24355Labels = mixedMoment B node1133 node1133Labels := by
  calc
    mixedMoment B raw24355 raw24355Labels = mixedMoment B raw24355step0 raw24355step0Labels := by
      have hz : ∀ j, raw24355 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24355step0 = (fun i j => raw24355 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24355step0 raw24355; decide +kernel
      have hl : raw24355step0Labels = raw24355Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24355 raw24355Labels permutation346 hz
    mixedMoment B raw24355step0 raw24355step0Labels = mixedMoment B raw24355step1 raw24355step1Labels := by
      have ha : raw24355step1 = (fun i j => raw24355step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24355step1 raw24355step0; decide +kernel
      have hl : raw24355step1Labels = raw24355step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24355step0 raw24355step0Labels permutation33 permutation3
    _ = mixedMoment B node1133 node1133Labels := by rfl

def raw24356 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24356Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24356step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24356step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24356step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw24356step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24356 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24356 raw24356Labels = mixedMoment B node1133 node1133Labels := by
  calc
    mixedMoment B raw24356 raw24356Labels = mixedMoment B raw24356step0 raw24356step0Labels := by
      have hz : ∀ j, raw24356 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24356step0 = (fun i j => raw24356 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24356step0 raw24356; decide +kernel
      have hl : raw24356step0Labels = raw24356Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24356 raw24356Labels permutation265 hz
    mixedMoment B raw24356step0 raw24356step0Labels = mixedMoment B raw24356step1 raw24356step1Labels := by
      have ha : raw24356step1 = (fun i j => raw24356step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24356step1 raw24356step0; decide +kernel
      have hl : raw24356step1Labels = raw24356step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24356step0 raw24356step0Labels permutation33 permutation3
    _ = mixedMoment B node1133 node1133Labels := by rfl

def raw24357 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24357Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24357step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24357step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24357step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24357step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24357step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![2, -2, 0], ![2, 1, -3]]
def raw24357step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24357 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24357 raw24357Labels = mixedMoment B node1245 node1245Labels := by
  calc
    mixedMoment B raw24357 raw24357Labels = mixedMoment B raw24357step0 raw24357step0Labels := by
      have hz : ∀ j, raw24357 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24357step0 = (fun i j => raw24357 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24357step0 raw24357; decide +kernel
      have hl : raw24357step0Labels = raw24357Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24357 raw24357Labels permutation346 hz
    mixedMoment B raw24357step0 raw24357step0Labels = mixedMoment B raw24357step1 raw24357step1Labels := by
      have hz : ∀ j, raw24357step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24357step1 = (fun i j => raw24357step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24357step1 raw24357step0; decide +kernel
      have hl : raw24357step1Labels = raw24357step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24357step0 raw24357step0Labels permutation56 hz
    mixedMoment B raw24357step1 raw24357step1Labels = mixedMoment B raw24357step2 raw24357step2Labels := by
      have ha : raw24357step2 = (fun i j => raw24357step1 (permutation9 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24357step2 raw24357step1; decide +kernel
      have hl : raw24357step2Labels = raw24357step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24357step1 raw24357step1Labels permutation9 permutation3
    _ = mixedMoment B node1245 node1245Labels := by rfl

def raw24358 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw24358Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24358step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw24358step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24358step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw24358step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24358step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw24358step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24358 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24358 raw24358Labels = mixedMoment B node1292 node1292Labels := by
  calc
    mixedMoment B raw24358 raw24358Labels = mixedMoment B raw24358step0 raw24358step0Labels := by
      have hz : ∀ j, raw24358 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24358step0 = (fun i j => raw24358 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24358step0 raw24358; decide +kernel
      have hl : raw24358step0Labels = raw24358Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24358 raw24358Labels permutation346 hz
    mixedMoment B raw24358step0 raw24358step0Labels = mixedMoment B raw24358step1 raw24358step1Labels := by
      have hz : ∀ j, raw24358step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24358step1 = (fun i j => raw24358step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24358step1 raw24358step0; decide +kernel
      have hl : raw24358step1Labels = raw24358step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24358step0 raw24358step0Labels permutation56 hz
    mixedMoment B raw24358step1 raw24358step1Labels = mixedMoment B raw24358step2 raw24358step2Labels := by
      have ha : raw24358step2 = (fun i j => raw24358step1 (permutation12 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24358step2 raw24358step1; decide +kernel
      have hl : raw24358step2Labels = raw24358step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24358step1 raw24358step1Labels permutation12 permutation3
    _ = mixedMoment B node1292 node1292Labels := by rfl

def raw24359 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24359Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24359step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24359step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24359step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24359step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24359step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 2, 3], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw24359step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24359 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24359 raw24359Labels = mixedMoment B node606 node606Labels := by
  calc
    mixedMoment B raw24359 raw24359Labels = mixedMoment B raw24359step0 raw24359step0Labels := by
      have hz : ∀ j, raw24359 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24359step0 = (fun i j => raw24359 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24359step0 raw24359; decide +kernel
      have hl : raw24359step0Labels = raw24359Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24359 raw24359Labels permutation346 hz
    mixedMoment B raw24359step0 raw24359step0Labels = mixedMoment B raw24359step1 raw24359step1Labels := by
      have hz : ∀ j, raw24359step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24359step1 = (fun i j => raw24359step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24359step1 raw24359step0; decide +kernel
      have hl : raw24359step1Labels = raw24359step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24359step0 raw24359step0Labels permutation56 hz
    mixedMoment B raw24359step1 raw24359step1Labels = mixedMoment B raw24359step2 raw24359step2Labels := by
      have ha : raw24359step2 = (fun i j => raw24359step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24359step2 raw24359step1; decide +kernel
      have hl : raw24359step2Labels = raw24359step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24359step1 raw24359step1Labels permutation8 permutation3
    _ = mixedMoment B node606 node606Labels := by rfl

def raw24360 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24360Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24360step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24360step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24360step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw24360step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24360 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24360 raw24360Labels = mixedMoment B node1132 node1132Labels := by
  calc
    mixedMoment B raw24360 raw24360Labels = mixedMoment B raw24360step0 raw24360step0Labels := by
      have hz : ∀ j, raw24360 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24360step0 = (fun i j => raw24360 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24360step0 raw24360; decide +kernel
      have hl : raw24360step0Labels = raw24360Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24360 raw24360Labels permutation346 hz
    mixedMoment B raw24360step0 raw24360step0Labels = mixedMoment B raw24360step1 raw24360step1Labels := by
      have ha : raw24360step1 = (fun i j => raw24360step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24360step1 raw24360step0; decide +kernel
      have hl : raw24360step1Labels = raw24360step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24360step0 raw24360step0Labels permutation32 permutation3
    _ = mixedMoment B node1132 node1132Labels := by rfl

def raw24361 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24361Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24361step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24361step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24361step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw24361step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24361 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24361 raw24361Labels = mixedMoment B node1132 node1132Labels := by
  calc
    mixedMoment B raw24361 raw24361Labels = mixedMoment B raw24361step0 raw24361step0Labels := by
      have hz : ∀ j, raw24361 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24361step0 = (fun i j => raw24361 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24361step0 raw24361; decide +kernel
      have hl : raw24361step0Labels = raw24361Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24361 raw24361Labels permutation265 hz
    mixedMoment B raw24361step0 raw24361step0Labels = mixedMoment B raw24361step1 raw24361step1Labels := by
      have ha : raw24361step1 = (fun i j => raw24361step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24361step1 raw24361step0; decide +kernel
      have hl : raw24361step1Labels = raw24361step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24361step0 raw24361step0Labels permutation32 permutation3
    _ = mixedMoment B node1132 node1132Labels := by rfl

def raw24362 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24362Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24362step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24362step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24362step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24362step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24362step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 1, -2], ![3, -2, -1]]
def raw24362step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24362 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24362 raw24362Labels = mixedMoment B node1243 node1243Labels := by
  calc
    mixedMoment B raw24362 raw24362Labels = mixedMoment B raw24362step0 raw24362step0Labels := by
      have hz : ∀ j, raw24362 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24362step0 = (fun i j => raw24362 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24362step0 raw24362; decide +kernel
      have hl : raw24362step0Labels = raw24362Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24362 raw24362Labels permutation346 hz
    mixedMoment B raw24362step0 raw24362step0Labels = mixedMoment B raw24362step1 raw24362step1Labels := by
      have hz : ∀ j, raw24362step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24362step1 = (fun i j => raw24362step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24362step1 raw24362step0; decide +kernel
      have hl : raw24362step1Labels = raw24362step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24362step0 raw24362step0Labels permutation56 hz
    mixedMoment B raw24362step1 raw24362step1Labels = mixedMoment B raw24362step2 raw24362step2Labels := by
      have ha : raw24362step2 = (fun i j => raw24362step1 (permutation8 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24362step2 raw24362step1; decide +kernel
      have hl : raw24362step2Labels = raw24362step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24362step1 raw24362step1Labels permutation8 permutation3
    _ = mixedMoment B node1243 node1243Labels := by rfl

def raw24363 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw24363Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24363step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw24363step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24363step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw24363step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw24363step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -1, 0], ![3, -2, -1]]
def raw24363step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24363 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24363 raw24363Labels = mixedMoment B node1269 node1269Labels := by
  calc
    mixedMoment B raw24363 raw24363Labels = mixedMoment B raw24363step0 raw24363step0Labels := by
      have hz : ∀ j, raw24363 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24363step0 = (fun i j => raw24363 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24363step0 raw24363; decide +kernel
      have hl : raw24363step0Labels = raw24363Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24363 raw24363Labels permutation346 hz
    mixedMoment B raw24363step0 raw24363step0Labels = mixedMoment B raw24363step1 raw24363step1Labels := by
      have hz : ∀ j, raw24363step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24363step1 = (fun i j => raw24363step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24363step1 raw24363step0; decide +kernel
      have hl : raw24363step1Labels = raw24363step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24363step0 raw24363step0Labels permutation56 hz
    mixedMoment B raw24363step1 raw24363step1Labels = mixedMoment B raw24363step2 raw24363step2Labels := by
      have ha : raw24363step2 = (fun i j => raw24363step1 (permutation10 i) (permutation3 j)) := by apply Matrix.ext; unfold raw24363step2 raw24363step1; decide +kernel
      have hl : raw24363step2Labels = raw24363step1Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24363step1 raw24363step1Labels permutation10 permutation3
    _ = mixedMoment B node1269 node1269Labels := by rfl

def raw24364 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24364Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24364step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24364step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24364step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw24364step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24364step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24364step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24364step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24364step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24364 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24364 raw24364Labels = mixedMoment B node3564 node3564Labels := by
  calc
    mixedMoment B raw24364 raw24364Labels = mixedMoment B raw24364step0 raw24364step0Labels := by
      have hz : ∀ j, raw24364 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24364step0 = (fun i j => raw24364 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24364step0 raw24364; decide +kernel
      have hl : raw24364step0Labels = raw24364Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24364 raw24364Labels permutation346 hz
    mixedMoment B raw24364step0 raw24364step0Labels = mixedMoment B raw24364step1 raw24364step1Labels := by
      have ha : raw24364step1 = (fun i j => raw24364step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24364step1 raw24364step0; decide +kernel
      have hl : raw24364step1Labels = raw24364step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24364step0 raw24364step0Labels permutation44 permutation7
    mixedMoment B raw24364step1 raw24364step1Labels = mixedMoment B raw24364step2 raw24364step2Labels := by
      have ha : raw24364step2 = -raw24364step1 := by apply Matrix.ext; change ∀ i j, raw24364step2 i j = -(raw24364step1 i j); unfold raw24364step2 raw24364step1; decide +kernel
      have hl : raw24364step2Labels = raw24364step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24364step2 raw24364step2Labels = mixedMoment B raw24364step3 raw24364step3Labels := by
      have ha : raw24364step3 = raw24364step2 := by apply Matrix.ext; unfold raw24364step3 raw24364step2; decide +kernel
      have hl : raw24364step2Labels = labelEmbedding1 ∘ raw24364step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24364step2 raw24364step2Labels raw24364step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3564 node3564Labels := by rfl

def raw24365 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24365Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24365step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24365step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24365step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw24365step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24365step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24365step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24365step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24365step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24365 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24365 raw24365Labels = mixedMoment B node3564 node3564Labels := by
  calc
    mixedMoment B raw24365 raw24365Labels = mixedMoment B raw24365step0 raw24365step0Labels := by
      have hz : ∀ j, raw24365 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24365step0 = (fun i j => raw24365 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24365step0 raw24365; decide +kernel
      have hl : raw24365step0Labels = raw24365Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24365 raw24365Labels permutation265 hz
    mixedMoment B raw24365step0 raw24365step0Labels = mixedMoment B raw24365step1 raw24365step1Labels := by
      have ha : raw24365step1 = (fun i j => raw24365step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24365step1 raw24365step0; decide +kernel
      have hl : raw24365step1Labels = raw24365step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24365step0 raw24365step0Labels permutation44 permutation7
    mixedMoment B raw24365step1 raw24365step1Labels = mixedMoment B raw24365step2 raw24365step2Labels := by
      have ha : raw24365step2 = -raw24365step1 := by apply Matrix.ext; change ∀ i j, raw24365step2 i j = -(raw24365step1 i j); unfold raw24365step2 raw24365step1; decide +kernel
      have hl : raw24365step2Labels = raw24365step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24365step2 raw24365step2Labels = mixedMoment B raw24365step3 raw24365step3Labels := by
      have ha : raw24365step3 = raw24365step2 := by apply Matrix.ext; unfold raw24365step3 raw24365step2; decide +kernel
      have hl : raw24365step2Labels = labelEmbedding1 ∘ raw24365step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24365step2 raw24365step2Labels raw24365step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3564 node3564Labels := by rfl

def raw24366 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24366Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24366step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24366step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24366step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24366step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24366step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw24366step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24366step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24366step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24366step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![2, 0, -2]]
def raw24366step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24366 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24366 raw24366Labels = mixedMoment B node3582 node3582Labels := by
  calc
    mixedMoment B raw24366 raw24366Labels = mixedMoment B raw24366step0 raw24366step0Labels := by
      have hz : ∀ j, raw24366 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24366step0 = (fun i j => raw24366 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24366step0 raw24366; decide +kernel
      have hl : raw24366step0Labels = raw24366Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24366 raw24366Labels permutation346 hz
    mixedMoment B raw24366step0 raw24366step0Labels = mixedMoment B raw24366step1 raw24366step1Labels := by
      have hz : ∀ j, raw24366step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24366step1 = (fun i j => raw24366step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24366step1 raw24366step0; decide +kernel
      have hl : raw24366step1Labels = raw24366step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24366step0 raw24366step0Labels permutation56 hz
    mixedMoment B raw24366step1 raw24366step1Labels = mixedMoment B raw24366step2 raw24366step2Labels := by
      have ha : raw24366step2 = (fun i j => raw24366step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24366step2 raw24366step1; decide +kernel
      have hl : raw24366step2Labels = raw24366step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24366step1 raw24366step1Labels permutation10 permutation7
    mixedMoment B raw24366step2 raw24366step2Labels = mixedMoment B raw24366step3 raw24366step3Labels := by
      have ha : raw24366step3 = -raw24366step2 := by apply Matrix.ext; change ∀ i j, raw24366step3 i j = -(raw24366step2 i j); unfold raw24366step3 raw24366step2; decide +kernel
      have hl : raw24366step3Labels = raw24366step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24366step3 raw24366step3Labels = mixedMoment B raw24366step4 raw24366step4Labels := by
      have ha : raw24366step4 = raw24366step3 := by apply Matrix.ext; unfold raw24366step4 raw24366step3; decide +kernel
      have hl : raw24366step3Labels = labelEmbedding1 ∘ raw24366step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24366step3 raw24366step3Labels raw24366step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3582 node3582Labels := by rfl

def raw24367 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24367Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24367step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24367step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24367step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24367step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24367step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-2, 0, 2]]
def raw24367step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24367step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24367step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24367step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24367step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24367 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24367 raw24367Labels = mixedMoment B node3547 node3547Labels := by
  calc
    mixedMoment B raw24367 raw24367Labels = mixedMoment B raw24367step0 raw24367step0Labels := by
      have hz : ∀ j, raw24367 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24367step0 = (fun i j => raw24367 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24367step0 raw24367; decide +kernel
      have hl : raw24367step0Labels = raw24367Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24367 raw24367Labels permutation346 hz
    mixedMoment B raw24367step0 raw24367step0Labels = mixedMoment B raw24367step1 raw24367step1Labels := by
      have hz : ∀ j, raw24367step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24367step1 = (fun i j => raw24367step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24367step1 raw24367step0; decide +kernel
      have hl : raw24367step1Labels = raw24367step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24367step0 raw24367step0Labels permutation56 hz
    mixedMoment B raw24367step1 raw24367step1Labels = mixedMoment B raw24367step2 raw24367step2Labels := by
      have ha : raw24367step2 = (fun i j => raw24367step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24367step2 raw24367step1; decide +kernel
      have hl : raw24367step2Labels = raw24367step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24367step1 raw24367step1Labels permutation10 permutation7
    mixedMoment B raw24367step2 raw24367step2Labels = mixedMoment B raw24367step3 raw24367step3Labels := by
      have ha : raw24367step3 = -raw24367step2 := by apply Matrix.ext; change ∀ i j, raw24367step3 i j = -(raw24367step2 i j); unfold raw24367step3 raw24367step2; decide +kernel
      have hl : raw24367step3Labels = raw24367step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24367step3 raw24367step3Labels = mixedMoment B raw24367step4 raw24367step4Labels := by
      have ha : raw24367step4 = raw24367step3 := by apply Matrix.ext; unfold raw24367step4 raw24367step3; decide +kernel
      have hl : raw24367step3Labels = labelEmbedding1 ∘ raw24367step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24367step3 raw24367step3Labels raw24367step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3547 node3547Labels := by rfl

def raw24368 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24368Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24368step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24368step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24368step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24368step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24368step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw24368step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24368step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24368step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24368step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24368step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24368 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24368 raw24368Labels = mixedMoment B node3583 node3583Labels := by
  calc
    mixedMoment B raw24368 raw24368Labels = mixedMoment B raw24368step0 raw24368step0Labels := by
      have hz : ∀ j, raw24368 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24368step0 = (fun i j => raw24368 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24368step0 raw24368; decide +kernel
      have hl : raw24368step0Labels = raw24368Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24368 raw24368Labels permutation346 hz
    mixedMoment B raw24368step0 raw24368step0Labels = mixedMoment B raw24368step1 raw24368step1Labels := by
      have hz : ∀ j, raw24368step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24368step1 = (fun i j => raw24368step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24368step1 raw24368step0; decide +kernel
      have hl : raw24368step1Labels = raw24368step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24368step0 raw24368step0Labels permutation56 hz
    mixedMoment B raw24368step1 raw24368step1Labels = mixedMoment B raw24368step2 raw24368step2Labels := by
      have ha : raw24368step2 = (fun i j => raw24368step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24368step2 raw24368step1; decide +kernel
      have hl : raw24368step2Labels = raw24368step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24368step1 raw24368step1Labels permutation10 permutation7
    mixedMoment B raw24368step2 raw24368step2Labels = mixedMoment B raw24368step3 raw24368step3Labels := by
      have ha : raw24368step3 = -raw24368step2 := by apply Matrix.ext; change ∀ i j, raw24368step3 i j = -(raw24368step2 i j); unfold raw24368step3 raw24368step2; decide +kernel
      have hl : raw24368step3Labels = raw24368step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24368step3 raw24368step3Labels = mixedMoment B raw24368step4 raw24368step4Labels := by
      have ha : raw24368step4 = raw24368step3 := by apply Matrix.ext; unfold raw24368step4 raw24368step3; decide +kernel
      have hl : raw24368step3Labels = labelEmbedding1 ∘ raw24368step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24368step3 raw24368step3Labels raw24368step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3583 node3583Labels := by rfl

def raw24369 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24369Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24369step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24369step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24369step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw24369step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24369step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24369step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24369step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24369step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24369 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24369 raw24369Labels = mixedMoment B node1512 node1512Labels := by
  calc
    mixedMoment B raw24369 raw24369Labels = mixedMoment B raw24369step0 raw24369step0Labels := by
      have hz : ∀ j, raw24369 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24369step0 = (fun i j => raw24369 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24369step0 raw24369; decide +kernel
      have hl : raw24369step0Labels = raw24369Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24369 raw24369Labels permutation346 hz
    mixedMoment B raw24369step0 raw24369step0Labels = mixedMoment B raw24369step1 raw24369step1Labels := by
      have ha : raw24369step1 = (fun i j => raw24369step0 (permutation42 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24369step1 raw24369step0; decide +kernel
      have hl : raw24369step1Labels = raw24369step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24369step0 raw24369step0Labels permutation42 permutation5
    mixedMoment B raw24369step1 raw24369step1Labels = mixedMoment B raw24369step2 raw24369step2Labels := by
      have ha : raw24369step2 = -raw24369step1 := by apply Matrix.ext; change ∀ i j, raw24369step2 i j = -(raw24369step1 i j); unfold raw24369step2 raw24369step1; decide +kernel
      have hl : raw24369step2Labels = raw24369step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24369step2 raw24369step2Labels = mixedMoment B raw24369step3 raw24369step3Labels := by
      have ha : raw24369step3 = raw24369step2 := by apply Matrix.ext; unfold raw24369step3 raw24369step2; decide +kernel
      have hl : raw24369step2Labels = labelEmbedding1 ∘ raw24369step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24369step2 raw24369step2Labels raw24369step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1512 node1512Labels := by rfl

def raw24370 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24370Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24370step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw24370step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24370step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24370step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24370step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24370step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24370 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24370 raw24370Labels = mixedMoment B node3259 node3259Labels := by
  calc
    mixedMoment B raw24370 raw24370Labels = mixedMoment B raw24370step0 raw24370step0Labels := by
      have ha : raw24370step0 = (fun i j => raw24370 (permutation186 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24370step0 raw24370; decide +kernel
      have hl : raw24370step0Labels = raw24370Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24370 raw24370Labels permutation186 permutation5
    mixedMoment B raw24370step0 raw24370step0Labels = mixedMoment B raw24370step1 raw24370step1Labels := by
      have ha : raw24370step1 = -raw24370step0 := by apply Matrix.ext; change ∀ i j, raw24370step1 i j = -(raw24370step0 i j); unfold raw24370step1 raw24370step0; decide +kernel
      have hl : raw24370step1Labels = raw24370step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24370step1 raw24370step1Labels = mixedMoment B raw24370step2 raw24370step2Labels := by
      have ha : raw24370step2 = raw24370step1 := by apply Matrix.ext; unfold raw24370step2 raw24370step1; decide +kernel
      have hl : raw24370step1Labels = labelEmbedding1 ∘ raw24370step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24370step1 raw24370step1Labels raw24370step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3259 node3259Labels := by rfl

def raw24371 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24371Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24371step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24371step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24371step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw24371step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24371step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24371step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24371step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24371step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24371 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24371 raw24371Labels = mixedMoment B node3296 node3296Labels := by
  calc
    mixedMoment B raw24371 raw24371Labels = mixedMoment B raw24371step0 raw24371step0Labels := by
      have hz : ∀ j, raw24371 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24371step0 = (fun i j => raw24371 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24371step0 raw24371; decide +kernel
      have hl : raw24371step0Labels = raw24371Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24371 raw24371Labels permutation346 hz
    mixedMoment B raw24371step0 raw24371step0Labels = mixedMoment B raw24371step1 raw24371step1Labels := by
      have ha : raw24371step1 = (fun i j => raw24371step0 (permutation42 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24371step1 raw24371step0; decide +kernel
      have hl : raw24371step1Labels = raw24371step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24371step0 raw24371step0Labels permutation42 permutation5
    mixedMoment B raw24371step1 raw24371step1Labels = mixedMoment B raw24371step2 raw24371step2Labels := by
      have ha : raw24371step2 = -raw24371step1 := by apply Matrix.ext; change ∀ i j, raw24371step2 i j = -(raw24371step1 i j); unfold raw24371step2 raw24371step1; decide +kernel
      have hl : raw24371step2Labels = raw24371step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24371step2 raw24371step2Labels = mixedMoment B raw24371step3 raw24371step3Labels := by
      have ha : raw24371step3 = raw24371step2 := by apply Matrix.ext; unfold raw24371step3 raw24371step2; decide +kernel
      have hl : raw24371step2Labels = labelEmbedding1 ∘ raw24371step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24371step2 raw24371step2Labels raw24371step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3296 node3296Labels := by rfl

def raw24372 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24372Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24372step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24372step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24372step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw24372step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24372step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24372step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24372step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24372step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24372 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24372 raw24372Labels = mixedMoment B node3293 node3293Labels := by
  calc
    mixedMoment B raw24372 raw24372Labels = mixedMoment B raw24372step0 raw24372step0Labels := by
      have hz : ∀ j, raw24372 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24372step0 = (fun i j => raw24372 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24372step0 raw24372; decide +kernel
      have hl : raw24372step0Labels = raw24372Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24372 raw24372Labels permutation346 hz
    mixedMoment B raw24372step0 raw24372step0Labels = mixedMoment B raw24372step1 raw24372step1Labels := by
      have ha : raw24372step1 = (fun i j => raw24372step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24372step1 raw24372step0; decide +kernel
      have hl : raw24372step1Labels = raw24372step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24372step0 raw24372step0Labels permutation44 permutation7
    mixedMoment B raw24372step1 raw24372step1Labels = mixedMoment B raw24372step2 raw24372step2Labels := by
      have ha : raw24372step2 = -raw24372step1 := by apply Matrix.ext; change ∀ i j, raw24372step2 i j = -(raw24372step1 i j); unfold raw24372step2 raw24372step1; decide +kernel
      have hl : raw24372step2Labels = raw24372step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24372step2 raw24372step2Labels = mixedMoment B raw24372step3 raw24372step3Labels := by
      have ha : raw24372step3 = raw24372step2 := by apply Matrix.ext; unfold raw24372step3 raw24372step2; decide +kernel
      have hl : raw24372step2Labels = labelEmbedding1 ∘ raw24372step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24372step2 raw24372step2Labels raw24372step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3293 node3293Labels := by rfl

def raw24373 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24373Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24373step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24373step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24373step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw24373step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24373step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24373step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24373step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24373step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24373 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24373 raw24373Labels = mixedMoment B node3303 node3303Labels := by
  calc
    mixedMoment B raw24373 raw24373Labels = mixedMoment B raw24373step0 raw24373step0Labels := by
      have hz : ∀ j, raw24373 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24373step0 = (fun i j => raw24373 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24373step0 raw24373; decide +kernel
      have hl : raw24373step0Labels = raw24373Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24373 raw24373Labels permutation346 hz
    mixedMoment B raw24373step0 raw24373step0Labels = mixedMoment B raw24373step1 raw24373step1Labels := by
      have ha : raw24373step1 = (fun i j => raw24373step0 (permutation52 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24373step1 raw24373step0; decide +kernel
      have hl : raw24373step1Labels = raw24373step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24373step0 raw24373step0Labels permutation52 permutation5
    mixedMoment B raw24373step1 raw24373step1Labels = mixedMoment B raw24373step2 raw24373step2Labels := by
      have ha : raw24373step2 = -raw24373step1 := by apply Matrix.ext; change ∀ i j, raw24373step2 i j = -(raw24373step1 i j); unfold raw24373step2 raw24373step1; decide +kernel
      have hl : raw24373step2Labels = raw24373step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24373step2 raw24373step2Labels = mixedMoment B raw24373step3 raw24373step3Labels := by
      have ha : raw24373step3 = raw24373step2 := by apply Matrix.ext; unfold raw24373step3 raw24373step2; decide +kernel
      have hl : raw24373step2Labels = labelEmbedding1 ∘ raw24373step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24373step2 raw24373step2Labels raw24373step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3303 node3303Labels := by rfl

def raw24374 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24374Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24374step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24374step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24374step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw24374step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24374step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24374step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24374step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24374step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24374 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24374 raw24374Labels = mixedMoment B node1512 node1512Labels := by
  calc
    mixedMoment B raw24374 raw24374Labels = mixedMoment B raw24374step0 raw24374step0Labels := by
      have hz : ∀ j, raw24374 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24374step0 = (fun i j => raw24374 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24374step0 raw24374; decide +kernel
      have hl : raw24374step0Labels = raw24374Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24374 raw24374Labels permutation265 hz
    mixedMoment B raw24374step0 raw24374step0Labels = mixedMoment B raw24374step1 raw24374step1Labels := by
      have ha : raw24374step1 = (fun i j => raw24374step0 (permutation42 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24374step1 raw24374step0; decide +kernel
      have hl : raw24374step1Labels = raw24374step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24374step0 raw24374step0Labels permutation42 permutation5
    mixedMoment B raw24374step1 raw24374step1Labels = mixedMoment B raw24374step2 raw24374step2Labels := by
      have ha : raw24374step2 = -raw24374step1 := by apply Matrix.ext; change ∀ i j, raw24374step2 i j = -(raw24374step1 i j); unfold raw24374step2 raw24374step1; decide +kernel
      have hl : raw24374step2Labels = raw24374step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24374step2 raw24374step2Labels = mixedMoment B raw24374step3 raw24374step3Labels := by
      have ha : raw24374step3 = raw24374step2 := by apply Matrix.ext; unfold raw24374step3 raw24374step2; decide +kernel
      have hl : raw24374step2Labels = labelEmbedding1 ∘ raw24374step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24374step2 raw24374step2Labels raw24374step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1512 node1512Labels := by rfl

def raw24375 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24375Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24375step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw24375step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24375step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24375step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24375step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24375step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24375 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24375 raw24375Labels = mixedMoment B node3259 node3259Labels := by
  calc
    mixedMoment B raw24375 raw24375Labels = mixedMoment B raw24375step0 raw24375step0Labels := by
      have ha : raw24375step0 = (fun i j => raw24375 (permutation162 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24375step0 raw24375; decide +kernel
      have hl : raw24375step0Labels = raw24375Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24375 raw24375Labels permutation162 permutation5
    mixedMoment B raw24375step0 raw24375step0Labels = mixedMoment B raw24375step1 raw24375step1Labels := by
      have ha : raw24375step1 = -raw24375step0 := by apply Matrix.ext; change ∀ i j, raw24375step1 i j = -(raw24375step0 i j); unfold raw24375step1 raw24375step0; decide +kernel
      have hl : raw24375step1Labels = raw24375step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24375step1 raw24375step1Labels = mixedMoment B raw24375step2 raw24375step2Labels := by
      have ha : raw24375step2 = raw24375step1 := by apply Matrix.ext; unfold raw24375step2 raw24375step1; decide +kernel
      have hl : raw24375step1Labels = labelEmbedding1 ∘ raw24375step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24375step1 raw24375step1Labels raw24375step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3259 node3259Labels := by rfl

def raw24376 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24376Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24376step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24376step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24376step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -2, 2], ![-1, 0, 1], ![-2, 1, 1]]
def raw24376step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24376step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24376step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24376step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw24376step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24376 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24376 raw24376Labels = mixedMoment B node3296 node3296Labels := by
  calc
    mixedMoment B raw24376 raw24376Labels = mixedMoment B raw24376step0 raw24376step0Labels := by
      have hz : ∀ j, raw24376 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24376step0 = (fun i j => raw24376 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24376step0 raw24376; decide +kernel
      have hl : raw24376step0Labels = raw24376Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24376 raw24376Labels permutation265 hz
    mixedMoment B raw24376step0 raw24376step0Labels = mixedMoment B raw24376step1 raw24376step1Labels := by
      have ha : raw24376step1 = (fun i j => raw24376step0 (permutation42 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24376step1 raw24376step0; decide +kernel
      have hl : raw24376step1Labels = raw24376step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24376step0 raw24376step0Labels permutation42 permutation5
    mixedMoment B raw24376step1 raw24376step1Labels = mixedMoment B raw24376step2 raw24376step2Labels := by
      have ha : raw24376step2 = -raw24376step1 := by apply Matrix.ext; change ∀ i j, raw24376step2 i j = -(raw24376step1 i j); unfold raw24376step2 raw24376step1; decide +kernel
      have hl : raw24376step2Labels = raw24376step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24376step2 raw24376step2Labels = mixedMoment B raw24376step3 raw24376step3Labels := by
      have ha : raw24376step3 = raw24376step2 := by apply Matrix.ext; unfold raw24376step3 raw24376step2; decide +kernel
      have hl : raw24376step2Labels = labelEmbedding1 ∘ raw24376step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24376step2 raw24376step2Labels raw24376step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3296 node3296Labels := by rfl

def raw24377 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24377Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24377step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24377step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24377step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw24377step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24377step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24377step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24377step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw24377step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24377 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24377 raw24377Labels = mixedMoment B node3293 node3293Labels := by
  calc
    mixedMoment B raw24377 raw24377Labels = mixedMoment B raw24377step0 raw24377step0Labels := by
      have hz : ∀ j, raw24377 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24377step0 = (fun i j => raw24377 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24377step0 raw24377; decide +kernel
      have hl : raw24377step0Labels = raw24377Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24377 raw24377Labels permutation265 hz
    mixedMoment B raw24377step0 raw24377step0Labels = mixedMoment B raw24377step1 raw24377step1Labels := by
      have ha : raw24377step1 = (fun i j => raw24377step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24377step1 raw24377step0; decide +kernel
      have hl : raw24377step1Labels = raw24377step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24377step0 raw24377step0Labels permutation44 permutation7
    mixedMoment B raw24377step1 raw24377step1Labels = mixedMoment B raw24377step2 raw24377step2Labels := by
      have ha : raw24377step2 = -raw24377step1 := by apply Matrix.ext; change ∀ i j, raw24377step2 i j = -(raw24377step1 i j); unfold raw24377step2 raw24377step1; decide +kernel
      have hl : raw24377step2Labels = raw24377step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24377step2 raw24377step2Labels = mixedMoment B raw24377step3 raw24377step3Labels := by
      have ha : raw24377step3 = raw24377step2 := by apply Matrix.ext; unfold raw24377step3 raw24377step2; decide +kernel
      have hl : raw24377step2Labels = labelEmbedding1 ∘ raw24377step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24377step2 raw24377step2Labels raw24377step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3293 node3293Labels := by rfl

def raw24378 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24378Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24378step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24378step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24378step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw24378step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24378step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24378step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24378step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw24378step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24378 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24378 raw24378Labels = mixedMoment B node3303 node3303Labels := by
  calc
    mixedMoment B raw24378 raw24378Labels = mixedMoment B raw24378step0 raw24378step0Labels := by
      have hz : ∀ j, raw24378 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24378step0 = (fun i j => raw24378 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24378step0 raw24378; decide +kernel
      have hl : raw24378step0Labels = raw24378Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24378 raw24378Labels permutation265 hz
    mixedMoment B raw24378step0 raw24378step0Labels = mixedMoment B raw24378step1 raw24378step1Labels := by
      have ha : raw24378step1 = (fun i j => raw24378step0 (permutation52 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24378step1 raw24378step0; decide +kernel
      have hl : raw24378step1Labels = raw24378step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24378step0 raw24378step0Labels permutation52 permutation5
    mixedMoment B raw24378step1 raw24378step1Labels = mixedMoment B raw24378step2 raw24378step2Labels := by
      have ha : raw24378step2 = -raw24378step1 := by apply Matrix.ext; change ∀ i j, raw24378step2 i j = -(raw24378step1 i j); unfold raw24378step2 raw24378step1; decide +kernel
      have hl : raw24378step2Labels = raw24378step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24378step2 raw24378step2Labels = mixedMoment B raw24378step3 raw24378step3Labels := by
      have ha : raw24378step3 = raw24378step2 := by apply Matrix.ext; unfold raw24378step3 raw24378step2; decide +kernel
      have hl : raw24378step2Labels = labelEmbedding1 ∘ raw24378step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24378step2 raw24378step2Labels raw24378step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3303 node3303Labels := by rfl

def raw24379 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24379Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24379step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24379step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24379step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24379step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24379step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw24379step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24379step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw24379step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24379step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw24379step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24379 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24379 raw24379Labels = mixedMoment B node1526 node1526Labels := by
  calc
    mixedMoment B raw24379 raw24379Labels = mixedMoment B raw24379step0 raw24379step0Labels := by
      have hz : ∀ j, raw24379 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24379step0 = (fun i j => raw24379 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24379step0 raw24379; decide +kernel
      have hl : raw24379step0Labels = raw24379Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24379 raw24379Labels permutation346 hz
    mixedMoment B raw24379step0 raw24379step0Labels = mixedMoment B raw24379step1 raw24379step1Labels := by
      have hz : ∀ j, raw24379step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24379step1 = (fun i j => raw24379step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24379step1 raw24379step0; decide +kernel
      have hl : raw24379step1Labels = raw24379step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24379step0 raw24379step0Labels permutation56 hz
    mixedMoment B raw24379step1 raw24379step1Labels = mixedMoment B raw24379step2 raw24379step2Labels := by
      have ha : raw24379step2 = (fun i j => raw24379step1 (permutation12 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24379step2 raw24379step1; decide +kernel
      have hl : raw24379step2Labels = raw24379step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24379step1 raw24379step1Labels permutation12 permutation5
    mixedMoment B raw24379step2 raw24379step2Labels = mixedMoment B raw24379step3 raw24379step3Labels := by
      have ha : raw24379step3 = -raw24379step2 := by apply Matrix.ext; change ∀ i j, raw24379step3 i j = -(raw24379step2 i j); unfold raw24379step3 raw24379step2; decide +kernel
      have hl : raw24379step3Labels = raw24379step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24379step3 raw24379step3Labels = mixedMoment B raw24379step4 raw24379step4Labels := by
      have ha : raw24379step4 = raw24379step3 := by apply Matrix.ext; unfold raw24379step4 raw24379step3; decide +kernel
      have hl : raw24379step3Labels = labelEmbedding1 ∘ raw24379step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24379step3 raw24379step3Labels raw24379step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1526 node1526Labels := by rfl

def raw24380 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24380Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24380step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24380step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24380step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw24380step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24380step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw24380step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24380step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw24380step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24380 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24380 raw24380Labels = mixedMoment B node3271 node3271Labels := by
  calc
    mixedMoment B raw24380 raw24380Labels = mixedMoment B raw24380step0 raw24380step0Labels := by
      have hz : ∀ j, raw24380 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24380step0 = (fun i j => raw24380 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24380step0 raw24380; decide +kernel
      have hl : raw24380step0Labels = raw24380Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24380 raw24380Labels permutation346 hz
    mixedMoment B raw24380step0 raw24380step0Labels = mixedMoment B raw24380step1 raw24380step1Labels := by
      have ha : raw24380step1 = (fun i j => raw24380step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24380step1 raw24380step0; decide +kernel
      have hl : raw24380step1Labels = raw24380step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24380step0 raw24380step0Labels permutation36 permutation5
    mixedMoment B raw24380step1 raw24380step1Labels = mixedMoment B raw24380step2 raw24380step2Labels := by
      have ha : raw24380step2 = -raw24380step1 := by apply Matrix.ext; change ∀ i j, raw24380step2 i j = -(raw24380step1 i j); unfold raw24380step2 raw24380step1; decide +kernel
      have hl : raw24380step2Labels = raw24380step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24380step2 raw24380step2Labels = mixedMoment B raw24380step3 raw24380step3Labels := by
      have ha : raw24380step3 = raw24380step2 := by apply Matrix.ext; unfold raw24380step3 raw24380step2; decide +kernel
      have hl : raw24380step2Labels = labelEmbedding1 ∘ raw24380step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24380step2 raw24380step2Labels raw24380step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3271 node3271Labels := by rfl

def raw24381 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24381Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24381step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24381step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24381step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -2, 2], ![-1, -1, 2], ![-2, 1, 1]]
def raw24381step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24381step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw24381step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24381step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 2, -2], ![1, 1, -2], ![2, -1, -1]]
def raw24381step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24381 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24381 raw24381Labels = mixedMoment B node3271 node3271Labels := by
  calc
    mixedMoment B raw24381 raw24381Labels = mixedMoment B raw24381step0 raw24381step0Labels := by
      have hz : ∀ j, raw24381 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24381step0 = (fun i j => raw24381 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24381step0 raw24381; decide +kernel
      have hl : raw24381step0Labels = raw24381Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24381 raw24381Labels permutation265 hz
    mixedMoment B raw24381step0 raw24381step0Labels = mixedMoment B raw24381step1 raw24381step1Labels := by
      have ha : raw24381step1 = (fun i j => raw24381step0 (permutation36 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24381step1 raw24381step0; decide +kernel
      have hl : raw24381step1Labels = raw24381step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24381step0 raw24381step0Labels permutation36 permutation5
    mixedMoment B raw24381step1 raw24381step1Labels = mixedMoment B raw24381step2 raw24381step2Labels := by
      have ha : raw24381step2 = -raw24381step1 := by apply Matrix.ext; change ∀ i j, raw24381step2 i j = -(raw24381step1 i j); unfold raw24381step2 raw24381step1; decide +kernel
      have hl : raw24381step2Labels = raw24381step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24381step2 raw24381step2Labels = mixedMoment B raw24381step3 raw24381step3Labels := by
      have ha : raw24381step3 = raw24381step2 := by apply Matrix.ext; unfold raw24381step3 raw24381step2; decide +kernel
      have hl : raw24381step2Labels = labelEmbedding1 ∘ raw24381step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24381step2 raw24381step2Labels raw24381step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3271 node3271Labels := by rfl

def raw24382 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24382Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24382step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24382step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24382step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw24382step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24382step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -1, 2], ![-2, 0, 2]]
def raw24382step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24382step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw24382step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24382step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw24382step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24382 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24382 raw24382Labels = mixedMoment B node3301 node3301Labels := by
  calc
    mixedMoment B raw24382 raw24382Labels = mixedMoment B raw24382step0 raw24382step0Labels := by
      have hz : ∀ j, raw24382 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24382step0 = (fun i j => raw24382 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24382step0 raw24382; decide +kernel
      have hl : raw24382step0Labels = raw24382Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24382 raw24382Labels permutation346 hz
    mixedMoment B raw24382step0 raw24382step0Labels = mixedMoment B raw24382step1 raw24382step1Labels := by
      have hz : ∀ j, raw24382step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24382step1 = (fun i j => raw24382step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24382step1 raw24382step0; decide +kernel
      have hl : raw24382step1Labels = raw24382step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24382step0 raw24382step0Labels permutation56 hz
    mixedMoment B raw24382step1 raw24382step1Labels = mixedMoment B raw24382step2 raw24382step2Labels := by
      have ha : raw24382step2 = (fun i j => raw24382step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24382step2 raw24382step1; decide +kernel
      have hl : raw24382step2Labels = raw24382step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24382step1 raw24382step1Labels permutation10 permutation7
    mixedMoment B raw24382step2 raw24382step2Labels = mixedMoment B raw24382step3 raw24382step3Labels := by
      have ha : raw24382step3 = -raw24382step2 := by apply Matrix.ext; change ∀ i j, raw24382step3 i j = -(raw24382step2 i j); unfold raw24382step3 raw24382step2; decide +kernel
      have hl : raw24382step3Labels = raw24382step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24382step3 raw24382step3Labels = mixedMoment B raw24382step4 raw24382step4Labels := by
      have ha : raw24382step4 = raw24382step3 := by apply Matrix.ext; unfold raw24382step4 raw24382step3; decide +kernel
      have hl : raw24382step3Labels = labelEmbedding1 ∘ raw24382step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24382step3 raw24382step3Labels raw24382step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3301 node3301Labels := by rfl

def raw24383 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24383Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24383step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24383step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24383step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw24383step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24383step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, -1, 2], ![-2, 1, 1]]
def raw24383step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24383step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24383step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24383step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 1, -2], ![2, -1, -1]]
def raw24383step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24383 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24383 raw24383Labels = mixedMoment B node3306 node3306Labels := by
  calc
    mixedMoment B raw24383 raw24383Labels = mixedMoment B raw24383step0 raw24383step0Labels := by
      have hz : ∀ j, raw24383 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24383step0 = (fun i j => raw24383 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24383step0 raw24383; decide +kernel
      have hl : raw24383step0Labels = raw24383Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24383 raw24383Labels permutation346 hz
    mixedMoment B raw24383step0 raw24383step0Labels = mixedMoment B raw24383step1 raw24383step1Labels := by
      have hz : ∀ j, raw24383step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24383step1 = (fun i j => raw24383step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24383step1 raw24383step0; decide +kernel
      have hl : raw24383step1Labels = raw24383step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24383step0 raw24383step0Labels permutation56 hz
    mixedMoment B raw24383step1 raw24383step1Labels = mixedMoment B raw24383step2 raw24383step2Labels := by
      have ha : raw24383step2 = (fun i j => raw24383step1 (permutation12 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24383step2 raw24383step1; decide +kernel
      have hl : raw24383step2Labels = raw24383step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24383step1 raw24383step1Labels permutation12 permutation5
    mixedMoment B raw24383step2 raw24383step2Labels = mixedMoment B raw24383step3 raw24383step3Labels := by
      have ha : raw24383step3 = -raw24383step2 := by apply Matrix.ext; change ∀ i j, raw24383step3 i j = -(raw24383step2 i j); unfold raw24383step3 raw24383step2; decide +kernel
      have hl : raw24383step3Labels = raw24383step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24383step3 raw24383step3Labels = mixedMoment B raw24383step4 raw24383step4Labels := by
      have ha : raw24383step4 = raw24383step3 := by apply Matrix.ext; unfold raw24383step4 raw24383step3; decide +kernel
      have hl : raw24383step3Labels = labelEmbedding1 ∘ raw24383step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24383step3 raw24383step3Labels raw24383step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3306 node3306Labels := by rfl

def raw24384 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24384Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24384step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24384step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24384step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24384step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24384step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![0, -2, 2], ![-3, 1, 2]]
def raw24384step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24384step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw24384step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24384step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![0, 2, -2], ![3, -1, -2]]
def raw24384step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24384 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24384 raw24384Labels = mixedMoment B node1513 node1513Labels := by
  calc
    mixedMoment B raw24384 raw24384Labels = mixedMoment B raw24384step0 raw24384step0Labels := by
      have hz : ∀ j, raw24384 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24384step0 = (fun i j => raw24384 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24384step0 raw24384; decide +kernel
      have hl : raw24384step0Labels = raw24384Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24384 raw24384Labels permutation346 hz
    mixedMoment B raw24384step0 raw24384step0Labels = mixedMoment B raw24384step1 raw24384step1Labels := by
      have hz : ∀ j, raw24384step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24384step1 = (fun i j => raw24384step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24384step1 raw24384step0; decide +kernel
      have hl : raw24384step1Labels = raw24384step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24384step0 raw24384step0Labels permutation56 hz
    mixedMoment B raw24384step1 raw24384step1Labels = mixedMoment B raw24384step2 raw24384step2Labels := by
      have ha : raw24384step2 = (fun i j => raw24384step1 (permutation9 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24384step2 raw24384step1; decide +kernel
      have hl : raw24384step2Labels = raw24384step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24384step1 raw24384step1Labels permutation9 permutation5
    mixedMoment B raw24384step2 raw24384step2Labels = mixedMoment B raw24384step3 raw24384step3Labels := by
      have ha : raw24384step3 = -raw24384step2 := by apply Matrix.ext; change ∀ i j, raw24384step3 i j = -(raw24384step2 i j); unfold raw24384step3 raw24384step2; decide +kernel
      have hl : raw24384step3Labels = raw24384step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24384step3 raw24384step3Labels = mixedMoment B raw24384step4 raw24384step4Labels := by
      have ha : raw24384step4 = raw24384step3 := by apply Matrix.ext; unfold raw24384step4 raw24384step3; decide +kernel
      have hl : raw24384step3Labels = labelEmbedding1 ∘ raw24384step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24384step3 raw24384step3Labels raw24384step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1513 node1513Labels := by rfl

def raw24385 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24385Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24385step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24385step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24385step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw24385step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24385step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw24385step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24385 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24385 raw24385Labels = mixedMoment B node2657 node2657Labels := by
  calc
    mixedMoment B raw24385 raw24385Labels = mixedMoment B raw24385step0 raw24385step0Labels := by
      have hz : ∀ j, raw24385 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24385step0 = (fun i j => raw24385 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24385step0 raw24385; decide +kernel
      have hl : raw24385step0Labels = raw24385Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24385 raw24385Labels permutation346 hz
    mixedMoment B raw24385step0 raw24385step0Labels = mixedMoment B raw24385step1 raw24385step1Labels := by
      have ha : raw24385step1 = (fun i j => raw24385step0 (permutation127 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24385step1 raw24385step0; decide +kernel
      have hl : raw24385step1Labels = raw24385step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24385step0 raw24385step0Labels permutation127 permutation5
    mixedMoment B raw24385step1 raw24385step1Labels = mixedMoment B raw24385step2 raw24385step2Labels := by
      have ha : raw24385step2 = raw24385step1 := by apply Matrix.ext; unfold raw24385step2 raw24385step1; decide +kernel
      have hl : raw24385step1Labels = labelEmbedding1 ∘ raw24385step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24385step1 raw24385step1Labels raw24385step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2657 node2657Labels := by rfl

def raw24386 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24386Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24386step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24386step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24386step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw24386step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24386step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![2, 2, -4]]
def raw24386step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24386 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24386 raw24386Labels = mixedMoment B node2657 node2657Labels := by
  calc
    mixedMoment B raw24386 raw24386Labels = mixedMoment B raw24386step0 raw24386step0Labels := by
      have hz : ∀ j, raw24386 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24386step0 = (fun i j => raw24386 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24386step0 raw24386; decide +kernel
      have hl : raw24386step0Labels = raw24386Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24386 raw24386Labels permutation265 hz
    mixedMoment B raw24386step0 raw24386step0Labels = mixedMoment B raw24386step1 raw24386step1Labels := by
      have ha : raw24386step1 = (fun i j => raw24386step0 (permutation127 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24386step1 raw24386step0; decide +kernel
      have hl : raw24386step1Labels = raw24386step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24386step0 raw24386step0Labels permutation127 permutation5
    mixedMoment B raw24386step1 raw24386step1Labels = mixedMoment B raw24386step2 raw24386step2Labels := by
      have ha : raw24386step2 = raw24386step1 := by apply Matrix.ext; unfold raw24386step2 raw24386step1; decide +kernel
      have hl : raw24386step1Labels = labelEmbedding1 ∘ raw24386step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24386step1 raw24386step1Labels raw24386step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2657 node2657Labels := by rfl

def raw24387 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24387Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24387step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24387step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24387step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24387step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24387step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw24387step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24387step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![2, 2, -4]]
def raw24387step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24387 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24387 raw24387Labels = mixedMoment B node2683 node2683Labels := by
  calc
    mixedMoment B raw24387 raw24387Labels = mixedMoment B raw24387step0 raw24387step0Labels := by
      have hz : ∀ j, raw24387 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24387step0 = (fun i j => raw24387 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24387step0 raw24387; decide +kernel
      have hl : raw24387step0Labels = raw24387Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24387 raw24387Labels permutation346 hz
    mixedMoment B raw24387step0 raw24387step0Labels = mixedMoment B raw24387step1 raw24387step1Labels := by
      have hz : ∀ j, raw24387step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24387step1 = (fun i j => raw24387step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24387step1 raw24387step0; decide +kernel
      have hl : raw24387step1Labels = raw24387step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24387step0 raw24387step0Labels permutation56 hz
    mixedMoment B raw24387step1 raw24387step1Labels = mixedMoment B raw24387step2 raw24387step2Labels := by
      have ha : raw24387step2 = (fun i j => raw24387step1 (permutation25 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24387step2 raw24387step1; decide +kernel
      have hl : raw24387step2Labels = raw24387step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24387step1 raw24387step1Labels permutation25 permutation5
    mixedMoment B raw24387step2 raw24387step2Labels = mixedMoment B raw24387step3 raw24387step3Labels := by
      have ha : raw24387step3 = raw24387step2 := by apply Matrix.ext; unfold raw24387step3 raw24387step2; decide +kernel
      have hl : raw24387step2Labels = labelEmbedding1 ∘ raw24387step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24387step2 raw24387step2Labels raw24387step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2683 node2683Labels := by rfl

def raw24388 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw24388Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24388step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw24388step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24388step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw24388step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24388step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw24388step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24388step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![2, 2, -4]]
def raw24388step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24388 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24388 raw24388Labels = mixedMoment B node2737 node2737Labels := by
  calc
    mixedMoment B raw24388 raw24388Labels = mixedMoment B raw24388step0 raw24388step0Labels := by
      have hz : ∀ j, raw24388 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24388step0 = (fun i j => raw24388 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24388step0 raw24388; decide +kernel
      have hl : raw24388step0Labels = raw24388Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24388 raw24388Labels permutation346 hz
    mixedMoment B raw24388step0 raw24388step0Labels = mixedMoment B raw24388step1 raw24388step1Labels := by
      have hz : ∀ j, raw24388step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24388step1 = (fun i j => raw24388step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24388step1 raw24388step0; decide +kernel
      have hl : raw24388step1Labels = raw24388step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24388step0 raw24388step0Labels permutation56 hz
    mixedMoment B raw24388step1 raw24388step1Labels = mixedMoment B raw24388step2 raw24388step2Labels := by
      have ha : raw24388step2 = (fun i j => raw24388step1 (permutation23 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24388step2 raw24388step1; decide +kernel
      have hl : raw24388step2Labels = raw24388step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24388step1 raw24388step1Labels permutation23 permutation5
    mixedMoment B raw24388step2 raw24388step2Labels = mixedMoment B raw24388step3 raw24388step3Labels := by
      have ha : raw24388step3 = raw24388step2 := by apply Matrix.ext; unfold raw24388step3 raw24388step2; decide +kernel
      have hl : raw24388step2Labels = labelEmbedding1 ∘ raw24388step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24388step2 raw24388step2Labels raw24388step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2737 node2737Labels := by rfl

def raw24389 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24389Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24389step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24389step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24389step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24389step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24389step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 2, -5], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw24389step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24389step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw24389step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24389step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -2, 5], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw24389step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24389 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24389 raw24389Labels = mixedMoment B node1520 node1520Labels := by
  calc
    mixedMoment B raw24389 raw24389Labels = mixedMoment B raw24389step0 raw24389step0Labels := by
      have hz : ∀ j, raw24389 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24389step0 = (fun i j => raw24389 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24389step0 raw24389; decide +kernel
      have hl : raw24389step0Labels = raw24389Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24389 raw24389Labels permutation346 hz
    mixedMoment B raw24389step0 raw24389step0Labels = mixedMoment B raw24389step1 raw24389step1Labels := by
      have hz : ∀ j, raw24389step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24389step1 = (fun i j => raw24389step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24389step1 raw24389step0; decide +kernel
      have hl : raw24389step1Labels = raw24389step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24389step0 raw24389step0Labels permutation56 hz
    mixedMoment B raw24389step1 raw24389step1Labels = mixedMoment B raw24389step2 raw24389step2Labels := by
      have ha : raw24389step2 = (fun i j => raw24389step1 (permutation9 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24389step2 raw24389step1; decide +kernel
      have hl : raw24389step2Labels = raw24389step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24389step1 raw24389step1Labels permutation9 permutation5
    mixedMoment B raw24389step2 raw24389step2Labels = mixedMoment B raw24389step3 raw24389step3Labels := by
      have ha : raw24389step3 = -raw24389step2 := by apply Matrix.ext; change ∀ i j, raw24389step3 i j = -(raw24389step2 i j); unfold raw24389step3 raw24389step2; decide +kernel
      have hl : raw24389step3Labels = raw24389step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24389step3 raw24389step3Labels = mixedMoment B raw24389step4 raw24389step4Labels := by
      have ha : raw24389step4 = raw24389step3 := by apply Matrix.ext; unfold raw24389step4 raw24389step3; decide +kernel
      have hl : raw24389step3Labels = labelEmbedding1 ∘ raw24389step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24389step3 raw24389step3Labels raw24389step4Labels labelEmbedding1 hl
    _ = mixedMoment B node1520 node1520Labels := by rfl

def raw24390 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24390Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24390step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24390step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24390step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw24390step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24390step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw24390step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24390step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw24390step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24390 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24390 raw24390Labels = mixedMoment B node3266 node3266Labels := by
  calc
    mixedMoment B raw24390 raw24390Labels = mixedMoment B raw24390step0 raw24390step0Labels := by
      have hz : ∀ j, raw24390 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24390step0 = (fun i j => raw24390 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24390step0 raw24390; decide +kernel
      have hl : raw24390step0Labels = raw24390Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24390 raw24390Labels permutation346 hz
    mixedMoment B raw24390step0 raw24390step0Labels = mixedMoment B raw24390step1 raw24390step1Labels := by
      have ha : raw24390step1 = (fun i j => raw24390step0 (permutation33 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24390step1 raw24390step0; decide +kernel
      have hl : raw24390step1Labels = raw24390step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24390step0 raw24390step0Labels permutation33 permutation5
    mixedMoment B raw24390step1 raw24390step1Labels = mixedMoment B raw24390step2 raw24390step2Labels := by
      have ha : raw24390step2 = -raw24390step1 := by apply Matrix.ext; change ∀ i j, raw24390step2 i j = -(raw24390step1 i j); unfold raw24390step2 raw24390step1; decide +kernel
      have hl : raw24390step2Labels = raw24390step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24390step2 raw24390step2Labels = mixedMoment B raw24390step3 raw24390step3Labels := by
      have ha : raw24390step3 = raw24390step2 := by apply Matrix.ext; unfold raw24390step3 raw24390step2; decide +kernel
      have hl : raw24390step2Labels = labelEmbedding1 ∘ raw24390step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24390step2 raw24390step2Labels raw24390step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3266 node3266Labels := by rfl

def raw24391 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24391Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24391step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24391step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24391step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, 0, -1], ![0, -1, 1], ![-1, -2, 3], ![-2, 1, 1]]
def raw24391step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24391step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw24391step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24391step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 0, 1], ![0, 1, -1], ![1, 2, -3], ![2, -1, -1]]
def raw24391step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24391 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24391 raw24391Labels = mixedMoment B node3266 node3266Labels := by
  calc
    mixedMoment B raw24391 raw24391Labels = mixedMoment B raw24391step0 raw24391step0Labels := by
      have hz : ∀ j, raw24391 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24391step0 = (fun i j => raw24391 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24391step0 raw24391; decide +kernel
      have hl : raw24391step0Labels = raw24391Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24391 raw24391Labels permutation265 hz
    mixedMoment B raw24391step0 raw24391step0Labels = mixedMoment B raw24391step1 raw24391step1Labels := by
      have ha : raw24391step1 = (fun i j => raw24391step0 (permutation33 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24391step1 raw24391step0; decide +kernel
      have hl : raw24391step1Labels = raw24391step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24391step0 raw24391step0Labels permutation33 permutation5
    mixedMoment B raw24391step1 raw24391step1Labels = mixedMoment B raw24391step2 raw24391step2Labels := by
      have ha : raw24391step2 = -raw24391step1 := by apply Matrix.ext; change ∀ i j, raw24391step2 i j = -(raw24391step1 i j); unfold raw24391step2 raw24391step1; decide +kernel
      have hl : raw24391step2Labels = raw24391step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24391step2 raw24391step2Labels = mixedMoment B raw24391step3 raw24391step3Labels := by
      have ha : raw24391step3 = raw24391step2 := by apply Matrix.ext; unfold raw24391step3 raw24391step2; decide +kernel
      have hl : raw24391step2Labels = labelEmbedding1 ∘ raw24391step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24391step2 raw24391step2Labels raw24391step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3266 node3266Labels := by rfl

def raw24392 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24392Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24392step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24392step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24392step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24392step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24392step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, -2, 3], ![-2, 1, 1]]
def raw24392step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24392step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw24392step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24392step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw24392step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24392 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24392 raw24392Labels = mixedMoment B node3302 node3302Labels := by
  calc
    mixedMoment B raw24392 raw24392Labels = mixedMoment B raw24392step0 raw24392step0Labels := by
      have hz : ∀ j, raw24392 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24392step0 = (fun i j => raw24392 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24392step0 raw24392; decide +kernel
      have hl : raw24392step0Labels = raw24392Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24392 raw24392Labels permutation346 hz
    mixedMoment B raw24392step0 raw24392step0Labels = mixedMoment B raw24392step1 raw24392step1Labels := by
      have hz : ∀ j, raw24392step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24392step1 = (fun i j => raw24392step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24392step1 raw24392step0; decide +kernel
      have hl : raw24392step1Labels = raw24392step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24392step0 raw24392step0Labels permutation56 hz
    mixedMoment B raw24392step1 raw24392step1Labels = mixedMoment B raw24392step2 raw24392step2Labels := by
      have ha : raw24392step2 = (fun i j => raw24392step1 (permutation9 i) (permutation5 j)) := by apply Matrix.ext; unfold raw24392step2 raw24392step1; decide +kernel
      have hl : raw24392step2Labels = raw24392step1Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24392step1 raw24392step1Labels permutation9 permutation5
    mixedMoment B raw24392step2 raw24392step2Labels = mixedMoment B raw24392step3 raw24392step3Labels := by
      have ha : raw24392step3 = -raw24392step2 := by apply Matrix.ext; change ∀ i j, raw24392step3 i j = -(raw24392step2 i j); unfold raw24392step3 raw24392step2; decide +kernel
      have hl : raw24392step3Labels = raw24392step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24392step3 raw24392step3Labels = mixedMoment B raw24392step4 raw24392step4Labels := by
      have ha : raw24392step4 = raw24392step3 := by apply Matrix.ext; unfold raw24392step4 raw24392step3; decide +kernel
      have hl : raw24392step3Labels = labelEmbedding1 ∘ raw24392step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24392step3 raw24392step3Labels raw24392step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3302 node3302Labels := by rfl

def raw24393 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw24393Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24393step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw24393step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24393step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw24393step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24393step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-2, -1, 3]]
def raw24393step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24393step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw24393step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24393step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw24393step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24393 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24393 raw24393Labels = mixedMoment B node3300 node3300Labels := by
  calc
    mixedMoment B raw24393 raw24393Labels = mixedMoment B raw24393step0 raw24393step0Labels := by
      have hz : ∀ j, raw24393 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24393step0 = (fun i j => raw24393 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24393step0 raw24393; decide +kernel
      have hl : raw24393step0Labels = raw24393Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24393 raw24393Labels permutation346 hz
    mixedMoment B raw24393step0 raw24393step0Labels = mixedMoment B raw24393step1 raw24393step1Labels := by
      have hz : ∀ j, raw24393step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24393step1 = (fun i j => raw24393step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24393step1 raw24393step0; decide +kernel
      have hl : raw24393step1Labels = raw24393step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24393step0 raw24393step0Labels permutation56 hz
    mixedMoment B raw24393step1 raw24393step1Labels = mixedMoment B raw24393step2 raw24393step2Labels := by
      have ha : raw24393step2 = (fun i j => raw24393step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24393step2 raw24393step1; decide +kernel
      have hl : raw24393step2Labels = raw24393step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24393step1 raw24393step1Labels permutation10 permutation7
    mixedMoment B raw24393step2 raw24393step2Labels = mixedMoment B raw24393step3 raw24393step3Labels := by
      have ha : raw24393step3 = -raw24393step2 := by apply Matrix.ext; change ∀ i j, raw24393step3 i j = -(raw24393step2 i j); unfold raw24393step3 raw24393step2; decide +kernel
      have hl : raw24393step3Labels = raw24393step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw24393step3 raw24393step3Labels = mixedMoment B raw24393step4 raw24393step4Labels := by
      have ha : raw24393step4 = raw24393step3 := by apply Matrix.ext; unfold raw24393step4 raw24393step3; decide +kernel
      have hl : raw24393step3Labels = labelEmbedding1 ∘ raw24393step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24393step3 raw24393step3Labels raw24393step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3300 node3300Labels := by rfl

def raw24394 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24394Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24394step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24394step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24394step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24394step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24394step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24394step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24394 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24394 raw24394Labels = mixedMoment B node1294 node1294Labels := by
  calc
    mixedMoment B raw24394 raw24394Labels = mixedMoment B raw24394step0 raw24394step0Labels := by
      have hz : ∀ j, raw24394 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24394step0 = (fun i j => raw24394 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24394step0 raw24394; decide +kernel
      have hl : raw24394step0Labels = raw24394Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24394 raw24394Labels permutation346 hz
    mixedMoment B raw24394step0 raw24394step0Labels = mixedMoment B raw24394step1 raw24394step1Labels := by
      have hz : ∀ j, raw24394step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24394step1 = (fun i j => raw24394step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24394step1 raw24394step0; decide +kernel
      have hl : raw24394step1Labels = raw24394step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24394step0 raw24394step0Labels permutation56 hz
    mixedMoment B raw24394step1 raw24394step1Labels = mixedMoment B raw24394step2 raw24394step2Labels := by
      have ha : raw24394step2 = (fun i j => raw24394step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24394step2 raw24394step1; decide +kernel
      have hl : raw24394step2Labels = raw24394step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24394step1 raw24394step1Labels permutation10 permutation2
    _ = mixedMoment B node1294 node1294Labels := by rfl

def raw24395 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24395Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24395step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24395step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24395step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24395step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24395 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24395 raw24395Labels = mixedMoment B node638 node638Labels := by
  calc
    mixedMoment B raw24395 raw24395Labels = mixedMoment B raw24395step0 raw24395step0Labels := by
      have hz : ∀ j, raw24395 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24395step0 = (fun i j => raw24395 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24395step0 raw24395; decide +kernel
      have hl : raw24395step0Labels = raw24395Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24395 raw24395Labels permutation346 hz
    mixedMoment B raw24395step0 raw24395step0Labels = mixedMoment B raw24395step1 raw24395step1Labels := by
      have ha : raw24395step1 = (fun i j => raw24395step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24395step1 raw24395step0; decide +kernel
      have hl : raw24395step1Labels = raw24395step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24395step0 raw24395step0Labels permutation44 permutation2
    _ = mixedMoment B node638 node638Labels := by rfl

def raw24396 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24396Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24396step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24396step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24396step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24396step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24396 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24396 raw24396Labels = mixedMoment B node638 node638Labels := by
  calc
    mixedMoment B raw24396 raw24396Labels = mixedMoment B raw24396step0 raw24396step0Labels := by
      have hz : ∀ j, raw24396 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24396step0 = (fun i j => raw24396 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24396step0 raw24396; decide +kernel
      have hl : raw24396step0Labels = raw24396Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24396 raw24396Labels permutation265 hz
    mixedMoment B raw24396step0 raw24396step0Labels = mixedMoment B raw24396step1 raw24396step1Labels := by
      have ha : raw24396step1 = (fun i j => raw24396step0 (permutation44 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24396step1 raw24396step0; decide +kernel
      have hl : raw24396step1Labels = raw24396step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24396step0 raw24396step0Labels permutation44 permutation2
    _ = mixedMoment B node638 node638Labels := by rfl

def raw24397 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24397Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24397step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24397step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24397step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw24397step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24397step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw24397step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24397 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24397 raw24397Labels = mixedMoment B node642 node642Labels := by
  calc
    mixedMoment B raw24397 raw24397Labels = mixedMoment B raw24397step0 raw24397step0Labels := by
      have hz : ∀ j, raw24397 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24397step0 = (fun i j => raw24397 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24397step0 raw24397; decide +kernel
      have hl : raw24397step0Labels = raw24397Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24397 raw24397Labels permutation346 hz
    mixedMoment B raw24397step0 raw24397step0Labels = mixedMoment B raw24397step1 raw24397step1Labels := by
      have hz : ∀ j, raw24397step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24397step1 = (fun i j => raw24397step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24397step1 raw24397step0; decide +kernel
      have hl : raw24397step1Labels = raw24397step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24397step0 raw24397step0Labels permutation56 hz
    mixedMoment B raw24397step1 raw24397step1Labels = mixedMoment B raw24397step2 raw24397step2Labels := by
      have ha : raw24397step2 = (fun i j => raw24397step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24397step2 raw24397step1; decide +kernel
      have hl : raw24397step2Labels = raw24397step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24397step1 raw24397step1Labels permutation10 permutation2
    _ = mixedMoment B node642 node642Labels := by rfl

def raw24398 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24398Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24398step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24398step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24398step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw24398step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24398 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24398 raw24398Labels = mixedMoment B node653 node653Labels := by
  calc
    mixedMoment B raw24398 raw24398Labels = mixedMoment B raw24398step0 raw24398step0Labels := by
      have hz : ∀ j, raw24398 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24398step0 = (fun i j => raw24398 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24398step0 raw24398; decide +kernel
      have hl : raw24398step0Labels = raw24398Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24398 raw24398Labels permutation346 hz
    mixedMoment B raw24398step0 raw24398step0Labels = mixedMoment B raw24398step1 raw24398step1Labels := by
      have hz : ∀ j, raw24398step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24398step1 = (fun i j => raw24398step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24398step1 raw24398step0; decide +kernel
      have hl : raw24398step1Labels = raw24398step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24398step0 raw24398step0Labels permutation56 hz
    _ = mixedMoment B node653 node653Labels := by rfl

def raw24399 : Matrix (Fin 6) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24399Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24399step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-5, 3, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24399step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24399step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw24399step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw24399step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-5, 3, 2], ![1, -2, 1], ![1, 0, -1], ![3, -1, -2]]
def raw24399step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24399 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24399 raw24399Labels = mixedMoment B node641 node641Labels := by
  calc
    mixedMoment B raw24399 raw24399Labels = mixedMoment B raw24399step0 raw24399step0Labels := by
      have hz : ∀ j, raw24399 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24399step0 = (fun i j => raw24399 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24399step0 raw24399; decide +kernel
      have hl : raw24399step0Labels = raw24399Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24399 raw24399Labels permutation346 hz
    mixedMoment B raw24399step0 raw24399step0Labels = mixedMoment B raw24399step1 raw24399step1Labels := by
      have hz : ∀ j, raw24399step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24399step1 = (fun i j => raw24399step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24399step1 raw24399step0; decide +kernel
      have hl : raw24399step1Labels = raw24399step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24399step0 raw24399step0Labels permutation56 hz
    mixedMoment B raw24399step1 raw24399step1Labels = mixedMoment B raw24399step2 raw24399step2Labels := by
      have ha : raw24399step2 = (fun i j => raw24399step1 (permutation10 i) (permutation2 j)) := by apply Matrix.ext; unfold raw24399step2 raw24399step1; decide +kernel
      have hl : raw24399step2Labels = raw24399step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24399step1 raw24399step1Labels permutation10 permutation2
    _ = mixedMoment B node641 node641Labels := by rfl

def raw24400 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![0, 0], ![1, -1], ![-1, 1], ![2, -2]]
def raw24400Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24400step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![0, 0], ![1, -1], ![-1, 1], ![2, -2]]
def raw24400step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24400step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![1, -1], ![-1, 1], ![2, -2]]
def raw24400step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw24400step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![2, -2]]
def raw24400step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical24400 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24400 raw24400Labels = mixedMoment B node4092 node4092Labels := by
  calc
    mixedMoment B raw24400 raw24400Labels = mixedMoment B raw24400step0 raw24400step0Labels := by
      have hz : ∀ j, raw24400 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24400step0 = (fun i j => raw24400 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24400step0 raw24400; decide +kernel
      have hl : raw24400step0Labels = raw24400Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24400 raw24400Labels permutation346 hz
    mixedMoment B raw24400step0 raw24400step0Labels = mixedMoment B raw24400step1 raw24400step1Labels := by
      have hz : ∀ j, raw24400step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24400step1 = (fun i j => raw24400step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24400step1 raw24400step0; decide +kernel
      have hl : raw24400step1Labels = raw24400step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24400step0 raw24400step0Labels permutation56 hz
    mixedMoment B raw24400step1 raw24400step1Labels = mixedMoment B raw24400step2 raw24400step2Labels := by
      have ha : raw24400step2 = (fun i j => raw24400step1 (permutation10 i) (permutation0 j)) := by apply Matrix.ext; unfold raw24400step2 raw24400step1; decide +kernel
      have hl : raw24400step2Labels = raw24400step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24400step1 raw24400step1Labels permutation10 permutation0
    _ = mixedMoment B node4092 node4092Labels := by rfl

def raw24401 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24401Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24401step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24401step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24401step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24401step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24401step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24401step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24401 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24401 raw24401Labels = mixedMoment B node4452 node4452Labels := by
  calc
    mixedMoment B raw24401 raw24401Labels = mixedMoment B raw24401step0 raw24401step0Labels := by
      have hz : ∀ j, raw24401 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24401step0 = (fun i j => raw24401 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24401step0 raw24401; decide +kernel
      have hl : raw24401step0Labels = raw24401Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24401 raw24401Labels permutation346 hz
    mixedMoment B raw24401step0 raw24401step0Labels = mixedMoment B raw24401step1 raw24401step1Labels := by
      have ha : raw24401step1 = (fun i j => raw24401step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24401step1 raw24401step0; decide +kernel
      have hl : raw24401step1Labels = raw24401step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24401step0 raw24401step0Labels permutation34 permutation7
    mixedMoment B raw24401step1 raw24401step1Labels = mixedMoment B raw24401step2 raw24401step2Labels := by
      have ha : raw24401step2 = raw24401step1 := by apply Matrix.ext; unfold raw24401step2 raw24401step1; decide +kernel
      have hl : raw24401step1Labels = labelEmbedding10 ∘ raw24401step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24401step1 raw24401step1Labels raw24401step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4452 node4452Labels := by rfl

def raw24402 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24402Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24402step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24402step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24402step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24402step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24402step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24402step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24402 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24402 raw24402Labels = mixedMoment B node4452 node4452Labels := by
  calc
    mixedMoment B raw24402 raw24402Labels = mixedMoment B raw24402step0 raw24402step0Labels := by
      have hz : ∀ j, raw24402 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24402step0 = (fun i j => raw24402 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24402step0 raw24402; decide +kernel
      have hl : raw24402step0Labels = raw24402Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24402 raw24402Labels permutation265 hz
    mixedMoment B raw24402step0 raw24402step0Labels = mixedMoment B raw24402step1 raw24402step1Labels := by
      have ha : raw24402step1 = (fun i j => raw24402step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24402step1 raw24402step0; decide +kernel
      have hl : raw24402step1Labels = raw24402step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24402step0 raw24402step0Labels permutation34 permutation7
    mixedMoment B raw24402step1 raw24402step1Labels = mixedMoment B raw24402step2 raw24402step2Labels := by
      have ha : raw24402step2 = raw24402step1 := by apply Matrix.ext; unfold raw24402step2 raw24402step1; decide +kernel
      have hl : raw24402step1Labels = labelEmbedding10 ∘ raw24402step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24402step1 raw24402step1Labels raw24402step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4452 node4452Labels := by rfl

def raw24403 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24403Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24403step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24403step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24403step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24403step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24403step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw24403step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24403step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw24403step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24403 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24403 raw24403Labels = mixedMoment B node4491 node4491Labels := by
  calc
    mixedMoment B raw24403 raw24403Labels = mixedMoment B raw24403step0 raw24403step0Labels := by
      have hz : ∀ j, raw24403 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24403step0 = (fun i j => raw24403 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24403step0 raw24403; decide +kernel
      have hl : raw24403step0Labels = raw24403Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24403 raw24403Labels permutation346 hz
    mixedMoment B raw24403step0 raw24403step0Labels = mixedMoment B raw24403step1 raw24403step1Labels := by
      have hz : ∀ j, raw24403step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24403step1 = (fun i j => raw24403step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24403step1 raw24403step0; decide +kernel
      have hl : raw24403step1Labels = raw24403step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24403step0 raw24403step0Labels permutation56 hz
    mixedMoment B raw24403step1 raw24403step1Labels = mixedMoment B raw24403step2 raw24403step2Labels := by
      have ha : raw24403step2 = (fun i j => raw24403step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24403step2 raw24403step1; decide +kernel
      have hl : raw24403step2Labels = raw24403step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24403step1 raw24403step1Labels permutation10 permutation7
    mixedMoment B raw24403step2 raw24403step2Labels = mixedMoment B raw24403step3 raw24403step3Labels := by
      have ha : raw24403step3 = raw24403step2 := by apply Matrix.ext; unfold raw24403step3 raw24403step2; decide +kernel
      have hl : raw24403step2Labels = labelEmbedding10 ∘ raw24403step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24403step2 raw24403step2Labels raw24403step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4491 node4491Labels := by rfl

def raw24404 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw24404Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24404step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw24404step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24404step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw24404step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24404step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw24404step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24404step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw24404step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24404 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24404 raw24404Labels = mixedMoment B node4490 node4490Labels := by
  calc
    mixedMoment B raw24404 raw24404Labels = mixedMoment B raw24404step0 raw24404step0Labels := by
      have hz : ∀ j, raw24404 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24404step0 = (fun i j => raw24404 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24404step0 raw24404; decide +kernel
      have hl : raw24404step0Labels = raw24404Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24404 raw24404Labels permutation346 hz
    mixedMoment B raw24404step0 raw24404step0Labels = mixedMoment B raw24404step1 raw24404step1Labels := by
      have hz : ∀ j, raw24404step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24404step1 = (fun i j => raw24404step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24404step1 raw24404step0; decide +kernel
      have hl : raw24404step1Labels = raw24404step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24404step0 raw24404step0Labels permutation56 hz
    mixedMoment B raw24404step1 raw24404step1Labels = mixedMoment B raw24404step2 raw24404step2Labels := by
      have ha : raw24404step2 = (fun i j => raw24404step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24404step2 raw24404step1; decide +kernel
      have hl : raw24404step2Labels = raw24404step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24404step1 raw24404step1Labels permutation10 permutation7
    mixedMoment B raw24404step2 raw24404step2Labels = mixedMoment B raw24404step3 raw24404step3Labels := by
      have ha : raw24404step3 = raw24404step2 := by apply Matrix.ext; unfold raw24404step3 raw24404step2; decide +kernel
      have hl : raw24404step2Labels = labelEmbedding10 ∘ raw24404step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24404step2 raw24404step2Labels raw24404step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4490 node4490Labels := by rfl

def raw24405 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24405Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24405step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24405step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24405step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24405step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24405step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24405step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24405 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24405 raw24405Labels = mixedMoment B node4459 node4459Labels := by
  calc
    mixedMoment B raw24405 raw24405Labels = mixedMoment B raw24405step0 raw24405step0Labels := by
      have hz : ∀ j, raw24405 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24405step0 = (fun i j => raw24405 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24405step0 raw24405; decide +kernel
      have hl : raw24405step0Labels = raw24405Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24405 raw24405Labels permutation346 hz
    mixedMoment B raw24405step0 raw24405step0Labels = mixedMoment B raw24405step1 raw24405step1Labels := by
      have ha : raw24405step1 = (fun i j => raw24405step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24405step1 raw24405step0; decide +kernel
      have hl : raw24405step1Labels = raw24405step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24405step0 raw24405step0Labels permutation32 permutation6
    mixedMoment B raw24405step1 raw24405step1Labels = mixedMoment B raw24405step2 raw24405step2Labels := by
      have ha : raw24405step2 = raw24405step1 := by apply Matrix.ext; unfold raw24405step2 raw24405step1; decide +kernel
      have hl : raw24405step1Labels = labelEmbedding9 ∘ raw24405step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24405step1 raw24405step1Labels raw24405step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4459 node4459Labels := by rfl

def raw24406 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24406Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24406step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24406step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24406step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24406step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24406 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24406 raw24406Labels = mixedMoment B node4587 node4587Labels := by
  calc
    mixedMoment B raw24406 raw24406Labels = mixedMoment B raw24406step0 raw24406step0Labels := by
      have ha : raw24406step0 = (fun i j => raw24406 (permutation154 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24406step0 raw24406; decide +kernel
      have hl : raw24406step0Labels = raw24406Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24406 raw24406Labels permutation154 permutation7
    mixedMoment B raw24406step0 raw24406step0Labels = mixedMoment B raw24406step1 raw24406step1Labels := by
      have ha : raw24406step1 = raw24406step0 := by apply Matrix.ext; unfold raw24406step1 raw24406step0; decide +kernel
      have hl : raw24406step0Labels = labelEmbedding10 ∘ raw24406step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24406step0 raw24406step0Labels raw24406step1Labels labelEmbedding10 hl
    _ = mixedMoment B node4587 node4587Labels := by rfl

def raw24407 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24407Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24407step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24407step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24407step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw24407step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24407step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw24407step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24407 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24407 raw24407Labels = mixedMoment B node4597 node4597Labels := by
  calc
    mixedMoment B raw24407 raw24407Labels = mixedMoment B raw24407step0 raw24407step0Labels := by
      have hz : ∀ j, raw24407 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24407step0 = (fun i j => raw24407 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24407step0 raw24407; decide +kernel
      have hl : raw24407step0Labels = raw24407Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24407 raw24407Labels permutation346 hz
    mixedMoment B raw24407step0 raw24407step0Labels = mixedMoment B raw24407step1 raw24407step1Labels := by
      have ha : raw24407step1 = (fun i j => raw24407step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24407step1 raw24407step0; decide +kernel
      have hl : raw24407step1Labels = raw24407step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24407step0 raw24407step0Labels permutation34 permutation7
    mixedMoment B raw24407step1 raw24407step1Labels = mixedMoment B raw24407step2 raw24407step2Labels := by
      have ha : raw24407step2 = raw24407step1 := by apply Matrix.ext; unfold raw24407step2 raw24407step1; decide +kernel
      have hl : raw24407step1Labels = labelEmbedding10 ∘ raw24407step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24407step1 raw24407step1Labels raw24407step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4597 node4597Labels := by rfl

def raw24408 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw24408Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24408step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw24408step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24408step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw24408step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24408step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw24408step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24408 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24408 raw24408Labels = mixedMoment B node4596 node4596Labels := by
  calc
    mixedMoment B raw24408 raw24408Labels = mixedMoment B raw24408step0 raw24408step0Labels := by
      have hz : ∀ j, raw24408 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24408step0 = (fun i j => raw24408 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24408step0 raw24408; decide +kernel
      have hl : raw24408step0Labels = raw24408Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24408 raw24408Labels permutation346 hz
    mixedMoment B raw24408step0 raw24408step0Labels = mixedMoment B raw24408step1 raw24408step1Labels := by
      have ha : raw24408step1 = (fun i j => raw24408step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24408step1 raw24408step0; decide +kernel
      have hl : raw24408step1Labels = raw24408step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24408step0 raw24408step0Labels permutation34 permutation7
    mixedMoment B raw24408step1 raw24408step1Labels = mixedMoment B raw24408step2 raw24408step2Labels := by
      have ha : raw24408step2 = raw24408step1 := by apply Matrix.ext; unfold raw24408step2 raw24408step1; decide +kernel
      have hl : raw24408step1Labels = labelEmbedding10 ∘ raw24408step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24408step1 raw24408step1Labels raw24408step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4596 node4596Labels := by rfl

def raw24409 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24409Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24409step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24409step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24409step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24409step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24409step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw24409step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24409 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24409 raw24409Labels = mixedMoment B node4459 node4459Labels := by
  calc
    mixedMoment B raw24409 raw24409Labels = mixedMoment B raw24409step0 raw24409step0Labels := by
      have hz : ∀ j, raw24409 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24409step0 = (fun i j => raw24409 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24409step0 raw24409; decide +kernel
      have hl : raw24409step0Labels = raw24409Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24409 raw24409Labels permutation265 hz
    mixedMoment B raw24409step0 raw24409step0Labels = mixedMoment B raw24409step1 raw24409step1Labels := by
      have ha : raw24409step1 = (fun i j => raw24409step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24409step1 raw24409step0; decide +kernel
      have hl : raw24409step1Labels = raw24409step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24409step0 raw24409step0Labels permutation32 permutation6
    mixedMoment B raw24409step1 raw24409step1Labels = mixedMoment B raw24409step2 raw24409step2Labels := by
      have ha : raw24409step2 = raw24409step1 := by apply Matrix.ext; unfold raw24409step2 raw24409step1; decide +kernel
      have hl : raw24409step1Labels = labelEmbedding9 ∘ raw24409step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24409step1 raw24409step1Labels raw24409step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4459 node4459Labels := by rfl

def raw24410 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24410Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24410step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24410step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24410step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24410step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24410 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24410 raw24410Labels = mixedMoment B node4587 node4587Labels := by
  calc
    mixedMoment B raw24410 raw24410Labels = mixedMoment B raw24410step0 raw24410step0Labels := by
      have ha : raw24410step0 = (fun i j => raw24410 (permutation178 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24410step0 raw24410; decide +kernel
      have hl : raw24410step0Labels = raw24410Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24410 raw24410Labels permutation178 permutation7
    mixedMoment B raw24410step0 raw24410step0Labels = mixedMoment B raw24410step1 raw24410step1Labels := by
      have ha : raw24410step1 = raw24410step0 := by apply Matrix.ext; unfold raw24410step1 raw24410step0; decide +kernel
      have hl : raw24410step0Labels = labelEmbedding10 ∘ raw24410step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24410step0 raw24410step0Labels raw24410step1Labels labelEmbedding10 hl
    _ = mixedMoment B node4587 node4587Labels := by rfl

def raw24411 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24411Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24411step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24411step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24411step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw24411step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24411step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw24411step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24411 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24411 raw24411Labels = mixedMoment B node4597 node4597Labels := by
  calc
    mixedMoment B raw24411 raw24411Labels = mixedMoment B raw24411step0 raw24411step0Labels := by
      have hz : ∀ j, raw24411 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24411step0 = (fun i j => raw24411 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24411step0 raw24411; decide +kernel
      have hl : raw24411step0Labels = raw24411Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24411 raw24411Labels permutation265 hz
    mixedMoment B raw24411step0 raw24411step0Labels = mixedMoment B raw24411step1 raw24411step1Labels := by
      have ha : raw24411step1 = (fun i j => raw24411step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24411step1 raw24411step0; decide +kernel
      have hl : raw24411step1Labels = raw24411step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24411step0 raw24411step0Labels permutation34 permutation7
    mixedMoment B raw24411step1 raw24411step1Labels = mixedMoment B raw24411step2 raw24411step2Labels := by
      have ha : raw24411step2 = raw24411step1 := by apply Matrix.ext; unfold raw24411step2 raw24411step1; decide +kernel
      have hl : raw24411step1Labels = labelEmbedding10 ∘ raw24411step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24411step1 raw24411step1Labels raw24411step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4597 node4597Labels := by rfl

def raw24412 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw24412Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24412step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw24412step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24412step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw24412step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24412step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw24412step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24412 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24412 raw24412Labels = mixedMoment B node4596 node4596Labels := by
  calc
    mixedMoment B raw24412 raw24412Labels = mixedMoment B raw24412step0 raw24412step0Labels := by
      have hz : ∀ j, raw24412 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24412step0 = (fun i j => raw24412 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24412step0 raw24412; decide +kernel
      have hl : raw24412step0Labels = raw24412Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24412 raw24412Labels permutation265 hz
    mixedMoment B raw24412step0 raw24412step0Labels = mixedMoment B raw24412step1 raw24412step1Labels := by
      have ha : raw24412step1 = (fun i j => raw24412step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24412step1 raw24412step0; decide +kernel
      have hl : raw24412step1Labels = raw24412step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24412step0 raw24412step0Labels permutation34 permutation7
    mixedMoment B raw24412step1 raw24412step1Labels = mixedMoment B raw24412step2 raw24412step2Labels := by
      have ha : raw24412step2 = raw24412step1 := by apply Matrix.ext; unfold raw24412step2 raw24412step1; decide +kernel
      have hl : raw24412step1Labels = labelEmbedding10 ∘ raw24412step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24412step1 raw24412step1Labels raw24412step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4596 node4596Labels := by rfl

def raw24413 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24413Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24413step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24413step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24413step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24413step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24413step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24413step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24413step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24413step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24413 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24413 raw24413Labels = mixedMoment B node4503 node4503Labels := by
  calc
    mixedMoment B raw24413 raw24413Labels = mixedMoment B raw24413step0 raw24413step0Labels := by
      have hz : ∀ j, raw24413 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24413step0 = (fun i j => raw24413 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24413step0 raw24413; decide +kernel
      have hl : raw24413step0Labels = raw24413Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24413 raw24413Labels permutation346 hz
    mixedMoment B raw24413step0 raw24413step0Labels = mixedMoment B raw24413step1 raw24413step1Labels := by
      have hz : ∀ j, raw24413step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24413step1 = (fun i j => raw24413step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24413step1 raw24413step0; decide +kernel
      have hl : raw24413step1Labels = raw24413step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24413step0 raw24413step0Labels permutation56 hz
    mixedMoment B raw24413step1 raw24413step1Labels = mixedMoment B raw24413step2 raw24413step2Labels := by
      have ha : raw24413step2 = (fun i j => raw24413step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24413step2 raw24413step1; decide +kernel
      have hl : raw24413step2Labels = raw24413step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24413step1 raw24413step1Labels permutation8 permutation6
    mixedMoment B raw24413step2 raw24413step2Labels = mixedMoment B raw24413step3 raw24413step3Labels := by
      have ha : raw24413step3 = raw24413step2 := by apply Matrix.ext; unfold raw24413step3 raw24413step2; decide +kernel
      have hl : raw24413step2Labels = labelEmbedding9 ∘ raw24413step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24413step2 raw24413step2Labels raw24413step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4503 node4503Labels := by rfl

def raw24414 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24414Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24414step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24414step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24414step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24414step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24414step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24414step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24414 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24414 raw24414Labels = mixedMoment B node4607 node4607Labels := by
  calc
    mixedMoment B raw24414 raw24414Labels = mixedMoment B raw24414step0 raw24414step0Labels := by
      have hz : ∀ j, raw24414 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24414step0 = (fun i j => raw24414 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24414step0 raw24414; decide +kernel
      have hl : raw24414step0Labels = raw24414Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24414 raw24414Labels permutation346 hz
    mixedMoment B raw24414step0 raw24414step0Labels = mixedMoment B raw24414step1 raw24414step1Labels := by
      have ha : raw24414step1 = (fun i j => raw24414step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24414step1 raw24414step0; decide +kernel
      have hl : raw24414step1Labels = raw24414step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24414step0 raw24414step0Labels permutation32 permutation6
    mixedMoment B raw24414step1 raw24414step1Labels = mixedMoment B raw24414step2 raw24414step2Labels := by
      have ha : raw24414step2 = raw24414step1 := by apply Matrix.ext; unfold raw24414step2 raw24414step1; decide +kernel
      have hl : raw24414step1Labels = labelEmbedding9 ∘ raw24414step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24414step1 raw24414step1Labels raw24414step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4607 node4607Labels := by rfl

def raw24415 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24415Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24415step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24415step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24415step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24415step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24415step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw24415step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24415 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24415 raw24415Labels = mixedMoment B node4607 node4607Labels := by
  calc
    mixedMoment B raw24415 raw24415Labels = mixedMoment B raw24415step0 raw24415step0Labels := by
      have hz : ∀ j, raw24415 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24415step0 = (fun i j => raw24415 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24415step0 raw24415; decide +kernel
      have hl : raw24415step0Labels = raw24415Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24415 raw24415Labels permutation265 hz
    mixedMoment B raw24415step0 raw24415step0Labels = mixedMoment B raw24415step1 raw24415step1Labels := by
      have ha : raw24415step1 = (fun i j => raw24415step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24415step1 raw24415step0; decide +kernel
      have hl : raw24415step1Labels = raw24415step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24415step0 raw24415step0Labels permutation32 permutation6
    mixedMoment B raw24415step1 raw24415step1Labels = mixedMoment B raw24415step2 raw24415step2Labels := by
      have ha : raw24415step2 = raw24415step1 := by apply Matrix.ext; unfold raw24415step2 raw24415step1; decide +kernel
      have hl : raw24415step1Labels = labelEmbedding9 ∘ raw24415step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24415step1 raw24415step1Labels raw24415step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4607 node4607Labels := by rfl

def raw24416 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw24416Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24416step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw24416step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24416step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw24416step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24416step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw24416step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24416step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw24416step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24416 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24416 raw24416Labels = mixedMoment B node4617 node4617Labels := by
  calc
    mixedMoment B raw24416 raw24416Labels = mixedMoment B raw24416step0 raw24416step0Labels := by
      have hz : ∀ j, raw24416 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24416step0 = (fun i j => raw24416 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24416step0 raw24416; decide +kernel
      have hl : raw24416step0Labels = raw24416Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24416 raw24416Labels permutation346 hz
    mixedMoment B raw24416step0 raw24416step0Labels = mixedMoment B raw24416step1 raw24416step1Labels := by
      have hz : ∀ j, raw24416step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24416step1 = (fun i j => raw24416step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24416step1 raw24416step0; decide +kernel
      have hl : raw24416step1Labels = raw24416step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24416step0 raw24416step0Labels permutation56 hz
    mixedMoment B raw24416step1 raw24416step1Labels = mixedMoment B raw24416step2 raw24416step2Labels := by
      have ha : raw24416step2 = (fun i j => raw24416step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24416step2 raw24416step1; decide +kernel
      have hl : raw24416step2Labels = raw24416step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24416step1 raw24416step1Labels permutation10 permutation7
    mixedMoment B raw24416step2 raw24416step2Labels = mixedMoment B raw24416step3 raw24416step3Labels := by
      have ha : raw24416step3 = raw24416step2 := by apply Matrix.ext; unfold raw24416step3 raw24416step2; decide +kernel
      have hl : raw24416step2Labels = labelEmbedding10 ∘ raw24416step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24416step2 raw24416step2Labels raw24416step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4617 node4617Labels := by rfl

def raw24417 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw24417Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24417step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw24417step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24417step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw24417step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24417step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw24417step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24417step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw24417step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24417 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24417 raw24417Labels = mixedMoment B node4500 node4500Labels := by
  calc
    mixedMoment B raw24417 raw24417Labels = mixedMoment B raw24417step0 raw24417step0Labels := by
      have hz : ∀ j, raw24417 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24417step0 = (fun i j => raw24417 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24417step0 raw24417; decide +kernel
      have hl : raw24417step0Labels = raw24417Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24417 raw24417Labels permutation346 hz
    mixedMoment B raw24417step0 raw24417step0Labels = mixedMoment B raw24417step1 raw24417step1Labels := by
      have hz : ∀ j, raw24417step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24417step1 = (fun i j => raw24417step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24417step1 raw24417step0; decide +kernel
      have hl : raw24417step1Labels = raw24417step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24417step0 raw24417step0Labels permutation56 hz
    mixedMoment B raw24417step1 raw24417step1Labels = mixedMoment B raw24417step2 raw24417step2Labels := by
      have ha : raw24417step2 = (fun i j => raw24417step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24417step2 raw24417step1; decide +kernel
      have hl : raw24417step2Labels = raw24417step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24417step1 raw24417step1Labels permutation8 permutation6
    mixedMoment B raw24417step2 raw24417step2Labels = mixedMoment B raw24417step3 raw24417step3Labels := by
      have ha : raw24417step3 = raw24417step2 := by apply Matrix.ext; unfold raw24417step3 raw24417step2; decide +kernel
      have hl : raw24417step2Labels = labelEmbedding9 ∘ raw24417step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24417step2 raw24417step2Labels raw24417step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4500 node4500Labels := by rfl

def raw24418 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw24418Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24418step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw24418step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24418step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw24418step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24418step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw24418step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24418 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24418 raw24418Labels = mixedMoment B node4604 node4604Labels := by
  calc
    mixedMoment B raw24418 raw24418Labels = mixedMoment B raw24418step0 raw24418step0Labels := by
      have hz : ∀ j, raw24418 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24418step0 = (fun i j => raw24418 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24418step0 raw24418; decide +kernel
      have hl : raw24418step0Labels = raw24418Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24418 raw24418Labels permutation346 hz
    mixedMoment B raw24418step0 raw24418step0Labels = mixedMoment B raw24418step1 raw24418step1Labels := by
      have ha : raw24418step1 = (fun i j => raw24418step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24418step1 raw24418step0; decide +kernel
      have hl : raw24418step1Labels = raw24418step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24418step0 raw24418step0Labels permutation32 permutation6
    mixedMoment B raw24418step1 raw24418step1Labels = mixedMoment B raw24418step2 raw24418step2Labels := by
      have ha : raw24418step2 = raw24418step1 := by apply Matrix.ext; unfold raw24418step2 raw24418step1; decide +kernel
      have hl : raw24418step1Labels = labelEmbedding9 ∘ raw24418step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24418step1 raw24418step1Labels raw24418step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4604 node4604Labels := by rfl

def raw24419 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw24419Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24419step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw24419step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24419step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw24419step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw24419step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw24419step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24419 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24419 raw24419Labels = mixedMoment B node4604 node4604Labels := by
  calc
    mixedMoment B raw24419 raw24419Labels = mixedMoment B raw24419step0 raw24419step0Labels := by
      have hz : ∀ j, raw24419 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24419step0 = (fun i j => raw24419 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24419step0 raw24419; decide +kernel
      have hl : raw24419step0Labels = raw24419Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24419 raw24419Labels permutation265 hz
    mixedMoment B raw24419step0 raw24419step0Labels = mixedMoment B raw24419step1 raw24419step1Labels := by
      have ha : raw24419step1 = (fun i j => raw24419step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw24419step1 raw24419step0; decide +kernel
      have hl : raw24419step1Labels = raw24419step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24419step0 raw24419step0Labels permutation32 permutation6
    mixedMoment B raw24419step1 raw24419step1Labels = mixedMoment B raw24419step2 raw24419step2Labels := by
      have ha : raw24419step2 = raw24419step1 := by apply Matrix.ext; unfold raw24419step2 raw24419step1; decide +kernel
      have hl : raw24419step1Labels = labelEmbedding9 ∘ raw24419step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24419step1 raw24419step1Labels raw24419step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4604 node4604Labels := by rfl

def raw24420 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw24420Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24420step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 1, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw24420step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24420step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 1, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw24420step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24420step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 1, -2], ![2, 0, -2]]
def raw24420step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24420step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 1, -2], ![2, 0, -2]]
def raw24420step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24420 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24420 raw24420Labels = mixedMoment B node4615 node4615Labels := by
  calc
    mixedMoment B raw24420 raw24420Labels = mixedMoment B raw24420step0 raw24420step0Labels := by
      have hz : ∀ j, raw24420 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24420step0 = (fun i j => raw24420 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24420step0 raw24420; decide +kernel
      have hl : raw24420step0Labels = raw24420Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24420 raw24420Labels permutation346 hz
    mixedMoment B raw24420step0 raw24420step0Labels = mixedMoment B raw24420step1 raw24420step1Labels := by
      have hz : ∀ j, raw24420step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24420step1 = (fun i j => raw24420step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24420step1 raw24420step0; decide +kernel
      have hl : raw24420step1Labels = raw24420step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24420step0 raw24420step0Labels permutation56 hz
    mixedMoment B raw24420step1 raw24420step1Labels = mixedMoment B raw24420step2 raw24420step2Labels := by
      have ha : raw24420step2 = (fun i j => raw24420step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24420step2 raw24420step1; decide +kernel
      have hl : raw24420step2Labels = raw24420step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24420step1 raw24420step1Labels permutation10 permutation7
    mixedMoment B raw24420step2 raw24420step2Labels = mixedMoment B raw24420step3 raw24420step3Labels := by
      have ha : raw24420step3 = raw24420step2 := by apply Matrix.ext; unfold raw24420step3 raw24420step2; decide +kernel
      have hl : raw24420step2Labels = labelEmbedding10 ∘ raw24420step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24420step2 raw24420step2Labels raw24420step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4615 node4615Labels := by rfl

def raw24421 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![-3, 1, 2]]
def raw24421Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24421step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![-3, 1, 2]]
def raw24421step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24421step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![2, -3, 1], ![-3, 1, 2]]
def raw24421step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw24421step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def raw24421step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw24421step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def raw24421step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical24421 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24421 raw24421Labels = mixedMoment B node4614 node4614Labels := by
  calc
    mixedMoment B raw24421 raw24421Labels = mixedMoment B raw24421step0 raw24421step0Labels := by
      have hz : ∀ j, raw24421 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24421step0 = (fun i j => raw24421 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24421step0 raw24421; decide +kernel
      have hl : raw24421step0Labels = raw24421Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24421 raw24421Labels permutation346 hz
    mixedMoment B raw24421step0 raw24421step0Labels = mixedMoment B raw24421step1 raw24421step1Labels := by
      have hz : ∀ j, raw24421step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24421step1 = (fun i j => raw24421step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24421step1 raw24421step0; decide +kernel
      have hl : raw24421step1Labels = raw24421step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24421step0 raw24421step0Labels permutation56 hz
    mixedMoment B raw24421step1 raw24421step1Labels = mixedMoment B raw24421step2 raw24421step2Labels := by
      have ha : raw24421step2 = (fun i j => raw24421step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24421step2 raw24421step1; decide +kernel
      have hl : raw24421step2Labels = raw24421step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24421step1 raw24421step1Labels permutation10 permutation7
    mixedMoment B raw24421step2 raw24421step2Labels = mixedMoment B raw24421step3 raw24421step3Labels := by
      have ha : raw24421step3 = raw24421step2 := by apply Matrix.ext; unfold raw24421step3 raw24421step2; decide +kernel
      have hl : raw24421step2Labels = labelEmbedding10 ∘ raw24421step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24421step2 raw24421step2Labels raw24421step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4614 node4614Labels := by rfl

def raw24422 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24422Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24422step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24422step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24422step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24422step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24422step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24422step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24422 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24422 raw24422Labels = mixedMoment B node1035 node1035Labels := by
  calc
    mixedMoment B raw24422 raw24422Labels = mixedMoment B raw24422step0 raw24422step0Labels := by
      have hz : ∀ j, raw24422 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24422step0 = (fun i j => raw24422 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24422step0 raw24422; decide +kernel
      have hl : raw24422step0Labels = raw24422Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24422 raw24422Labels permutation346 hz
    mixedMoment B raw24422step0 raw24422step0Labels = mixedMoment B raw24422step1 raw24422step1Labels := by
      have ha : raw24422step1 = (fun i j => raw24422step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24422step1 raw24422step0; decide +kernel
      have hl : raw24422step1Labels = raw24422step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24422step0 raw24422step0Labels permutation34 permutation7
    mixedMoment B raw24422step1 raw24422step1Labels = mixedMoment B raw24422step2 raw24422step2Labels := by
      have ha : raw24422step2 = raw24422step1 := by apply Matrix.ext; unfold raw24422step2 raw24422step1; decide +kernel
      have hl : raw24422step1Labels = labelEmbedding1 ∘ raw24422step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24422step1 raw24422step1Labels raw24422step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1035 node1035Labels := by rfl

def raw24423 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24423Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24423step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24423step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24423step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24423step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24423step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24423step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24423 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24423 raw24423Labels = mixedMoment B node1035 node1035Labels := by
  calc
    mixedMoment B raw24423 raw24423Labels = mixedMoment B raw24423step0 raw24423step0Labels := by
      have hz : ∀ j, raw24423 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24423step0 = (fun i j => raw24423 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24423step0 raw24423; decide +kernel
      have hl : raw24423step0Labels = raw24423Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24423 raw24423Labels permutation265 hz
    mixedMoment B raw24423step0 raw24423step0Labels = mixedMoment B raw24423step1 raw24423step1Labels := by
      have ha : raw24423step1 = (fun i j => raw24423step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24423step1 raw24423step0; decide +kernel
      have hl : raw24423step1Labels = raw24423step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24423step0 raw24423step0Labels permutation34 permutation7
    mixedMoment B raw24423step1 raw24423step1Labels = mixedMoment B raw24423step2 raw24423step2Labels := by
      have ha : raw24423step2 = raw24423step1 := by apply Matrix.ext; unfold raw24423step2 raw24423step1; decide +kernel
      have hl : raw24423step1Labels = labelEmbedding1 ∘ raw24423step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24423step1 raw24423step1Labels raw24423step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1035 node1035Labels := by rfl

def raw24424 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24424Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24424step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-2, 1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24424step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24424step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-2, 1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24424step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24424step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw24424step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24424step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw24424step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24424 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24424 raw24424Labels = mixedMoment B node1075 node1075Labels := by
  calc
    mixedMoment B raw24424 raw24424Labels = mixedMoment B raw24424step0 raw24424step0Labels := by
      have hz : ∀ j, raw24424 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24424step0 = (fun i j => raw24424 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24424step0 raw24424; decide +kernel
      have hl : raw24424step0Labels = raw24424Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24424 raw24424Labels permutation346 hz
    mixedMoment B raw24424step0 raw24424step0Labels = mixedMoment B raw24424step1 raw24424step1Labels := by
      have hz : ∀ j, raw24424step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24424step1 = (fun i j => raw24424step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24424step1 raw24424step0; decide +kernel
      have hl : raw24424step1Labels = raw24424step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24424step0 raw24424step0Labels permutation56 hz
    mixedMoment B raw24424step1 raw24424step1Labels = mixedMoment B raw24424step2 raw24424step2Labels := by
      have ha : raw24424step2 = (fun i j => raw24424step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24424step2 raw24424step1; decide +kernel
      have hl : raw24424step2Labels = raw24424step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24424step1 raw24424step1Labels permutation10 permutation7
    mixedMoment B raw24424step2 raw24424step2Labels = mixedMoment B raw24424step3 raw24424step3Labels := by
      have ha : raw24424step3 = raw24424step2 := by apply Matrix.ext; unfold raw24424step3 raw24424step2; decide +kernel
      have hl : raw24424step2Labels = labelEmbedding1 ∘ raw24424step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24424step2 raw24424step2Labels raw24424step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1075 node1075Labels := by rfl

def raw24425 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24425Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24425step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24425step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24425step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24425step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24425step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24425step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24425step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24425step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24425 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24425 raw24425Labels = mixedMoment B node1082 node1082Labels := by
  calc
    mixedMoment B raw24425 raw24425Labels = mixedMoment B raw24425step0 raw24425step0Labels := by
      have hz : ∀ j, raw24425 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24425step0 = (fun i j => raw24425 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24425step0 raw24425; decide +kernel
      have hl : raw24425step0Labels = raw24425Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24425 raw24425Labels permutation346 hz
    mixedMoment B raw24425step0 raw24425step0Labels = mixedMoment B raw24425step1 raw24425step1Labels := by
      have hz : ∀ j, raw24425step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24425step1 = (fun i j => raw24425step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24425step1 raw24425step0; decide +kernel
      have hl : raw24425step1Labels = raw24425step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24425step0 raw24425step0Labels permutation56 hz
    mixedMoment B raw24425step1 raw24425step1Labels = mixedMoment B raw24425step2 raw24425step2Labels := by
      have ha : raw24425step2 = (fun i j => raw24425step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24425step2 raw24425step1; decide +kernel
      have hl : raw24425step2Labels = raw24425step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24425step1 raw24425step1Labels permutation10 permutation7
    mixedMoment B raw24425step2 raw24425step2Labels = mixedMoment B raw24425step3 raw24425step3Labels := by
      have ha : raw24425step3 = raw24425step2 := by apply Matrix.ext; unfold raw24425step3 raw24425step2; decide +kernel
      have hl : raw24425step2Labels = labelEmbedding1 ∘ raw24425step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24425step2 raw24425step2Labels raw24425step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1082 node1082Labels := by rfl

def raw24426 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw24426Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24426step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 1, -4], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw24426step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24426step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 1, -4], ![-1, 0, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw24426step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24426step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw24426step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24426step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw24426step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24426 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24426 raw24426Labels = mixedMoment B node1074 node1074Labels := by
  calc
    mixedMoment B raw24426 raw24426Labels = mixedMoment B raw24426step0 raw24426step0Labels := by
      have hz : ∀ j, raw24426 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24426step0 = (fun i j => raw24426 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24426step0 raw24426; decide +kernel
      have hl : raw24426step0Labels = raw24426Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24426 raw24426Labels permutation346 hz
    mixedMoment B raw24426step0 raw24426step0Labels = mixedMoment B raw24426step1 raw24426step1Labels := by
      have hz : ∀ j, raw24426step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24426step1 = (fun i j => raw24426step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24426step1 raw24426step0; decide +kernel
      have hl : raw24426step1Labels = raw24426step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24426step0 raw24426step0Labels permutation56 hz
    mixedMoment B raw24426step1 raw24426step1Labels = mixedMoment B raw24426step2 raw24426step2Labels := by
      have ha : raw24426step2 = (fun i j => raw24426step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24426step2 raw24426step1; decide +kernel
      have hl : raw24426step2Labels = raw24426step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24426step1 raw24426step1Labels permutation10 permutation7
    mixedMoment B raw24426step2 raw24426step2Labels = mixedMoment B raw24426step3 raw24426step3Labels := by
      have ha : raw24426step3 = raw24426step2 := by apply Matrix.ext; unfold raw24426step3 raw24426step2; decide +kernel
      have hl : raw24426step2Labels = labelEmbedding1 ∘ raw24426step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24426step2 raw24426step2Labels raw24426step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1074 node1074Labels := by rfl

def raw24427 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24427Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24427step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24427step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24427step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24427step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24427step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24427step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24427 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24427 raw24427Labels = mixedMoment B node1406 node1406Labels := by
  calc
    mixedMoment B raw24427 raw24427Labels = mixedMoment B raw24427step0 raw24427step0Labels := by
      have hz : ∀ j, raw24427 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24427step0 = (fun i j => raw24427 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24427step0 raw24427; decide +kernel
      have hl : raw24427step0Labels = raw24427Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24427 raw24427Labels permutation346 hz
    mixedMoment B raw24427step0 raw24427step0Labels = mixedMoment B raw24427step1 raw24427step1Labels := by
      have ha : raw24427step1 = (fun i j => raw24427step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24427step1 raw24427step0; decide +kernel
      have hl : raw24427step1Labels = raw24427step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24427step0 raw24427step0Labels permutation34 permutation7
    mixedMoment B raw24427step1 raw24427step1Labels = mixedMoment B raw24427step2 raw24427step2Labels := by
      have ha : raw24427step2 = raw24427step1 := by apply Matrix.ext; unfold raw24427step2 raw24427step1; decide +kernel
      have hl : raw24427step1Labels = labelEmbedding1 ∘ raw24427step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24427step1 raw24427step1Labels raw24427step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1406 node1406Labels := by rfl

def raw24428 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24428Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24428step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24428step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24428step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24428step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24428 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24428 raw24428Labels = mixedMoment B node1210 node1210Labels := by
  calc
    mixedMoment B raw24428 raw24428Labels = mixedMoment B raw24428step0 raw24428step0Labels := by
      have ha : raw24428step0 = (fun i j => raw24428 (permutation154 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24428step0 raw24428; decide +kernel
      have hl : raw24428step0Labels = raw24428Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24428 raw24428Labels permutation154 permutation7
    mixedMoment B raw24428step0 raw24428step0Labels = mixedMoment B raw24428step1 raw24428step1Labels := by
      have ha : raw24428step1 = raw24428step0 := by apply Matrix.ext; unfold raw24428step1 raw24428step0; decide +kernel
      have hl : raw24428step0Labels = labelEmbedding1 ∘ raw24428step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24428step0 raw24428step0Labels raw24428step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1210 node1210Labels := by rfl

def raw24429 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-2, 1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24429Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24429step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24429step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24429step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw24429step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24429step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw24429step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24429 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24429 raw24429Labels = mixedMoment B node1230 node1230Labels := by
  calc
    mixedMoment B raw24429 raw24429Labels = mixedMoment B raw24429step0 raw24429step0Labels := by
      have hz : ∀ j, raw24429 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24429step0 = (fun i j => raw24429 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24429step0 raw24429; decide +kernel
      have hl : raw24429step0Labels = raw24429Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24429 raw24429Labels permutation346 hz
    mixedMoment B raw24429step0 raw24429step0Labels = mixedMoment B raw24429step1 raw24429step1Labels := by
      have ha : raw24429step1 = (fun i j => raw24429step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24429step1 raw24429step0; decide +kernel
      have hl : raw24429step1Labels = raw24429step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24429step0 raw24429step0Labels permutation34 permutation7
    mixedMoment B raw24429step1 raw24429step1Labels = mixedMoment B raw24429step2 raw24429step2Labels := by
      have ha : raw24429step2 = raw24429step1 := by apply Matrix.ext; unfold raw24429step2 raw24429step1; decide +kernel
      have hl : raw24429step1Labels = labelEmbedding1 ∘ raw24429step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24429step1 raw24429step1Labels raw24429step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1230 node1230Labels := by rfl

def raw24430 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24430Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24430step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24430step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24430step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24430step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24430step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24430step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24430 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24430 raw24430Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw24430 raw24430Labels = mixedMoment B raw24430step0 raw24430step0Labels := by
      have hz : ∀ j, raw24430 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24430step0 = (fun i j => raw24430 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24430step0 raw24430; decide +kernel
      have hl : raw24430step0Labels = raw24430Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24430 raw24430Labels permutation346 hz
    mixedMoment B raw24430step0 raw24430step0Labels = mixedMoment B raw24430step1 raw24430step1Labels := by
      have ha : raw24430step1 = (fun i j => raw24430step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24430step1 raw24430step0; decide +kernel
      have hl : raw24430step1Labels = raw24430step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24430step0 raw24430step0Labels permutation34 permutation7
    mixedMoment B raw24430step1 raw24430step1Labels = mixedMoment B raw24430step2 raw24430step2Labels := by
      have ha : raw24430step2 = raw24430step1 := by apply Matrix.ext; unfold raw24430step2 raw24430step1; decide +kernel
      have hl : raw24430step1Labels = labelEmbedding1 ∘ raw24430step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24430step1 raw24430step1Labels raw24430step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1236 node1236Labels := by rfl

def raw24431 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw24431Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24431step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw24431step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24431step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw24431step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24431step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw24431step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24431 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24431 raw24431Labels = mixedMoment B node1229 node1229Labels := by
  calc
    mixedMoment B raw24431 raw24431Labels = mixedMoment B raw24431step0 raw24431step0Labels := by
      have hz : ∀ j, raw24431 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24431step0 = (fun i j => raw24431 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24431step0 raw24431; decide +kernel
      have hl : raw24431step0Labels = raw24431Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24431 raw24431Labels permutation346 hz
    mixedMoment B raw24431step0 raw24431step0Labels = mixedMoment B raw24431step1 raw24431step1Labels := by
      have ha : raw24431step1 = (fun i j => raw24431step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24431step1 raw24431step0; decide +kernel
      have hl : raw24431step1Labels = raw24431step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24431step0 raw24431step0Labels permutation34 permutation7
    mixedMoment B raw24431step1 raw24431step1Labels = mixedMoment B raw24431step2 raw24431step2Labels := by
      have ha : raw24431step2 = raw24431step1 := by apply Matrix.ext; unfold raw24431step2 raw24431step1; decide +kernel
      have hl : raw24431step1Labels = labelEmbedding1 ∘ raw24431step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24431step1 raw24431step1Labels raw24431step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1229 node1229Labels := by rfl

def raw24432 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24432Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24432step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24432step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24432step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24432step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24432step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24432step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24432 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24432 raw24432Labels = mixedMoment B node1406 node1406Labels := by
  calc
    mixedMoment B raw24432 raw24432Labels = mixedMoment B raw24432step0 raw24432step0Labels := by
      have hz : ∀ j, raw24432 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24432step0 = (fun i j => raw24432 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24432step0 raw24432; decide +kernel
      have hl : raw24432step0Labels = raw24432Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24432 raw24432Labels permutation265 hz
    mixedMoment B raw24432step0 raw24432step0Labels = mixedMoment B raw24432step1 raw24432step1Labels := by
      have ha : raw24432step1 = (fun i j => raw24432step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24432step1 raw24432step0; decide +kernel
      have hl : raw24432step1Labels = raw24432step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24432step0 raw24432step0Labels permutation34 permutation7
    mixedMoment B raw24432step1 raw24432step1Labels = mixedMoment B raw24432step2 raw24432step2Labels := by
      have ha : raw24432step2 = raw24432step1 := by apply Matrix.ext; unfold raw24432step2 raw24432step1; decide +kernel
      have hl : raw24432step1Labels = labelEmbedding1 ∘ raw24432step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24432step1 raw24432step1Labels raw24432step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1406 node1406Labels := by rfl

def raw24433 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24433Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24433step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24433step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24433step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw24433step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24433 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24433 raw24433Labels = mixedMoment B node1210 node1210Labels := by
  calc
    mixedMoment B raw24433 raw24433Labels = mixedMoment B raw24433step0 raw24433step0Labels := by
      have ha : raw24433step0 = (fun i j => raw24433 (permutation178 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24433step0 raw24433; decide +kernel
      have hl : raw24433step0Labels = raw24433Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24433 raw24433Labels permutation178 permutation7
    mixedMoment B raw24433step0 raw24433step0Labels = mixedMoment B raw24433step1 raw24433step1Labels := by
      have ha : raw24433step1 = raw24433step0 := by apply Matrix.ext; unfold raw24433step1 raw24433step0; decide +kernel
      have hl : raw24433step0Labels = labelEmbedding1 ∘ raw24433step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24433step0 raw24433step0Labels raw24433step1Labels labelEmbedding1 hl
    _ = mixedMoment B node1210 node1210Labels := by rfl

def raw24434 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-2, 1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24434Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24434step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-2, 1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24434step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24434step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw24434step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24434step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw24434step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24434 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24434 raw24434Labels = mixedMoment B node1230 node1230Labels := by
  calc
    mixedMoment B raw24434 raw24434Labels = mixedMoment B raw24434step0 raw24434step0Labels := by
      have hz : ∀ j, raw24434 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24434step0 = (fun i j => raw24434 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24434step0 raw24434; decide +kernel
      have hl : raw24434step0Labels = raw24434Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24434 raw24434Labels permutation265 hz
    mixedMoment B raw24434step0 raw24434step0Labels = mixedMoment B raw24434step1 raw24434step1Labels := by
      have ha : raw24434step1 = (fun i j => raw24434step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24434step1 raw24434step0; decide +kernel
      have hl : raw24434step1Labels = raw24434step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24434step0 raw24434step0Labels permutation34 permutation7
    mixedMoment B raw24434step1 raw24434step1Labels = mixedMoment B raw24434step2 raw24434step2Labels := by
      have ha : raw24434step2 = raw24434step1 := by apply Matrix.ext; unfold raw24434step2 raw24434step1; decide +kernel
      have hl : raw24434step1Labels = labelEmbedding1 ∘ raw24434step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24434step1 raw24434step1Labels raw24434step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1230 node1230Labels := by rfl

def raw24435 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24435Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24435step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24435step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24435step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24435step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24435step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw24435step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24435 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24435 raw24435Labels = mixedMoment B node1236 node1236Labels := by
  calc
    mixedMoment B raw24435 raw24435Labels = mixedMoment B raw24435step0 raw24435step0Labels := by
      have hz : ∀ j, raw24435 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24435step0 = (fun i j => raw24435 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24435step0 raw24435; decide +kernel
      have hl : raw24435step0Labels = raw24435Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24435 raw24435Labels permutation265 hz
    mixedMoment B raw24435step0 raw24435step0Labels = mixedMoment B raw24435step1 raw24435step1Labels := by
      have ha : raw24435step1 = (fun i j => raw24435step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24435step1 raw24435step0; decide +kernel
      have hl : raw24435step1Labels = raw24435step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24435step0 raw24435step0Labels permutation34 permutation7
    mixedMoment B raw24435step1 raw24435step1Labels = mixedMoment B raw24435step2 raw24435step2Labels := by
      have ha : raw24435step2 = raw24435step1 := by apply Matrix.ext; unfold raw24435step2 raw24435step1; decide +kernel
      have hl : raw24435step1Labels = labelEmbedding1 ∘ raw24435step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24435step1 raw24435step1Labels raw24435step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1236 node1236Labels := by rfl

def raw24436 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw24436Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24436step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw24436step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24436step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw24436step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24436step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw24436step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24436 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24436 raw24436Labels = mixedMoment B node1229 node1229Labels := by
  calc
    mixedMoment B raw24436 raw24436Labels = mixedMoment B raw24436step0 raw24436step0Labels := by
      have hz : ∀ j, raw24436 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24436step0 = (fun i j => raw24436 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24436step0 raw24436; decide +kernel
      have hl : raw24436step0Labels = raw24436Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24436 raw24436Labels permutation265 hz
    mixedMoment B raw24436step0 raw24436step0Labels = mixedMoment B raw24436step1 raw24436step1Labels := by
      have ha : raw24436step1 = (fun i j => raw24436step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24436step1 raw24436step0; decide +kernel
      have hl : raw24436step1Labels = raw24436step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24436step0 raw24436step0Labels permutation34 permutation7
    mixedMoment B raw24436step1 raw24436step1Labels = mixedMoment B raw24436step2 raw24436step2Labels := by
      have ha : raw24436step2 = raw24436step1 := by apply Matrix.ext; unfold raw24436step2 raw24436step1; decide +kernel
      have hl : raw24436step1Labels = labelEmbedding1 ∘ raw24436step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24436step1 raw24436step1Labels raw24436step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1229 node1229Labels := by rfl

def raw24437 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24437Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24437step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24437step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24437step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24437step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24437step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw24437step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24437step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw24437step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24437 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24437 raw24437Labels = mixedMoment B node1442 node1442Labels := by
  calc
    mixedMoment B raw24437 raw24437Labels = mixedMoment B raw24437step0 raw24437step0Labels := by
      have hz : ∀ j, raw24437 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24437step0 = (fun i j => raw24437 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24437step0 raw24437; decide +kernel
      have hl : raw24437step0Labels = raw24437Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24437 raw24437Labels permutation346 hz
    mixedMoment B raw24437step0 raw24437step0Labels = mixedMoment B raw24437step1 raw24437step1Labels := by
      have hz : ∀ j, raw24437step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24437step1 = (fun i j => raw24437step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24437step1 raw24437step0; decide +kernel
      have hl : raw24437step1Labels = raw24437step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24437step0 raw24437step0Labels permutation56 hz
    mixedMoment B raw24437step1 raw24437step1Labels = mixedMoment B raw24437step2 raw24437step2Labels := by
      have ha : raw24437step2 = (fun i j => raw24437step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24437step2 raw24437step1; decide +kernel
      have hl : raw24437step2Labels = raw24437step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24437step1 raw24437step1Labels permutation10 permutation7
    mixedMoment B raw24437step2 raw24437step2Labels = mixedMoment B raw24437step3 raw24437step3Labels := by
      have ha : raw24437step3 = raw24437step2 := by apply Matrix.ext; unfold raw24437step3 raw24437step2; decide +kernel
      have hl : raw24437step2Labels = labelEmbedding1 ∘ raw24437step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24437step2 raw24437step2Labels raw24437step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1442 node1442Labels := by rfl

def raw24438 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24438Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24438step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24438step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24438step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw24438step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24438step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw24438step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24438 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24438 raw24438Labels = mixedMoment B node1261 node1261Labels := by
  calc
    mixedMoment B raw24438 raw24438Labels = mixedMoment B raw24438step0 raw24438step0Labels := by
      have hz : ∀ j, raw24438 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24438step0 = (fun i j => raw24438 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24438step0 raw24438; decide +kernel
      have hl : raw24438step0Labels = raw24438Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24438 raw24438Labels permutation346 hz
    mixedMoment B raw24438step0 raw24438step0Labels = mixedMoment B raw24438step1 raw24438step1Labels := by
      have ha : raw24438step1 = (fun i j => raw24438step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24438step1 raw24438step0; decide +kernel
      have hl : raw24438step1Labels = raw24438step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24438step0 raw24438step0Labels permutation34 permutation7
    mixedMoment B raw24438step1 raw24438step1Labels = mixedMoment B raw24438step2 raw24438step2Labels := by
      have ha : raw24438step2 = raw24438step1 := by apply Matrix.ext; unfold raw24438step2 raw24438step1; decide +kernel
      have hl : raw24438step1Labels = labelEmbedding1 ∘ raw24438step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24438step1 raw24438step1Labels raw24438step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1261 node1261Labels := by rfl

def raw24439 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24439Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24439step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![-2, 0, 2]]
def raw24439step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24439step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw24439step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24439step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw24439step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24439 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24439 raw24439Labels = mixedMoment B node1261 node1261Labels := by
  calc
    mixedMoment B raw24439 raw24439Labels = mixedMoment B raw24439step0 raw24439step0Labels := by
      have hz : ∀ j, raw24439 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24439step0 = (fun i j => raw24439 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24439step0 raw24439; decide +kernel
      have hl : raw24439step0Labels = raw24439Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24439 raw24439Labels permutation265 hz
    mixedMoment B raw24439step0 raw24439step0Labels = mixedMoment B raw24439step1 raw24439step1Labels := by
      have ha : raw24439step1 = (fun i j => raw24439step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24439step1 raw24439step0; decide +kernel
      have hl : raw24439step1Labels = raw24439step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24439step0 raw24439step0Labels permutation34 permutation7
    mixedMoment B raw24439step1 raw24439step1Labels = mixedMoment B raw24439step2 raw24439step2Labels := by
      have ha : raw24439step2 = raw24439step1 := by apply Matrix.ext; unfold raw24439step2 raw24439step1; decide +kernel
      have hl : raw24439step1Labels = labelEmbedding1 ∘ raw24439step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24439step1 raw24439step1Labels raw24439step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1261 node1261Labels := by rfl

def raw24440 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24440Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24440step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24440step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24440step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![0, -1, 1], ![-2, 0, 2]]
def raw24440step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24440step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24440step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24440step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw24440step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24440 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24440 raw24440Labels = mixedMoment B node1300 node1300Labels := by
  calc
    mixedMoment B raw24440 raw24440Labels = mixedMoment B raw24440step0 raw24440step0Labels := by
      have hz : ∀ j, raw24440 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24440step0 = (fun i j => raw24440 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24440step0 raw24440; decide +kernel
      have hl : raw24440step0Labels = raw24440Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24440 raw24440Labels permutation346 hz
    mixedMoment B raw24440step0 raw24440step0Labels = mixedMoment B raw24440step1 raw24440step1Labels := by
      have hz : ∀ j, raw24440step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24440step1 = (fun i j => raw24440step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24440step1 raw24440step0; decide +kernel
      have hl : raw24440step1Labels = raw24440step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24440step0 raw24440step0Labels permutation56 hz
    mixedMoment B raw24440step1 raw24440step1Labels = mixedMoment B raw24440step2 raw24440step2Labels := by
      have ha : raw24440step2 = (fun i j => raw24440step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24440step2 raw24440step1; decide +kernel
      have hl : raw24440step2Labels = raw24440step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24440step1 raw24440step1Labels permutation8 permutation7
    mixedMoment B raw24440step2 raw24440step2Labels = mixedMoment B raw24440step3 raw24440step3Labels := by
      have ha : raw24440step3 = raw24440step2 := by apply Matrix.ext; unfold raw24440step3 raw24440step2; decide +kernel
      have hl : raw24440step2Labels = labelEmbedding1 ∘ raw24440step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24440step2 raw24440step2Labels raw24440step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1300 node1300Labels := by rfl

def raw24441 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw24441Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24441step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, -1, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw24441step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24441step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![0, -1, 1], ![1, -2, 1], ![-3, 1, 2]]
def raw24441step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24441step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw24441step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24441step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw24441step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24441 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24441 raw24441Labels = mixedMoment B node1292 node1292Labels := by
  calc
    mixedMoment B raw24441 raw24441Labels = mixedMoment B raw24441step0 raw24441step0Labels := by
      have hz : ∀ j, raw24441 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24441step0 = (fun i j => raw24441 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24441step0 raw24441; decide +kernel
      have hl : raw24441step0Labels = raw24441Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24441 raw24441Labels permutation346 hz
    mixedMoment B raw24441step0 raw24441step0Labels = mixedMoment B raw24441step1 raw24441step1Labels := by
      have hz : ∀ j, raw24441step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24441step1 = (fun i j => raw24441step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24441step1 raw24441step0; decide +kernel
      have hl : raw24441step1Labels = raw24441step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24441step0 raw24441step0Labels permutation56 hz
    mixedMoment B raw24441step1 raw24441step1Labels = mixedMoment B raw24441step2 raw24441step2Labels := by
      have ha : raw24441step2 = (fun i j => raw24441step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24441step2 raw24441step1; decide +kernel
      have hl : raw24441step2Labels = raw24441step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24441step1 raw24441step1Labels permutation10 permutation7
    mixedMoment B raw24441step2 raw24441step2Labels = mixedMoment B raw24441step3 raw24441step3Labels := by
      have ha : raw24441step3 = raw24441step2 := by apply Matrix.ext; unfold raw24441step3 raw24441step2; decide +kernel
      have hl : raw24441step2Labels = labelEmbedding1 ∘ raw24441step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24441step2 raw24441step2Labels raw24441step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1292 node1292Labels := by rfl

def raw24442 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw24442Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24442step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw24442step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24442step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw24442step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24442step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw24442step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24442step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw24442step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24442 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24442 raw24442Labels = mixedMoment B node1436 node1436Labels := by
  calc
    mixedMoment B raw24442 raw24442Labels = mixedMoment B raw24442step0 raw24442step0Labels := by
      have hz : ∀ j, raw24442 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24442step0 = (fun i j => raw24442 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24442step0 raw24442; decide +kernel
      have hl : raw24442step0Labels = raw24442Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24442 raw24442Labels permutation346 hz
    mixedMoment B raw24442step0 raw24442step0Labels = mixedMoment B raw24442step1 raw24442step1Labels := by
      have hz : ∀ j, raw24442step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24442step1 = (fun i j => raw24442step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24442step1 raw24442step0; decide +kernel
      have hl : raw24442step1Labels = raw24442step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24442step0 raw24442step0Labels permutation56 hz
    mixedMoment B raw24442step1 raw24442step1Labels = mixedMoment B raw24442step2 raw24442step2Labels := by
      have ha : raw24442step2 = (fun i j => raw24442step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24442step2 raw24442step1; decide +kernel
      have hl : raw24442step2Labels = raw24442step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24442step1 raw24442step1Labels permutation10 permutation7
    mixedMoment B raw24442step2 raw24442step2Labels = mixedMoment B raw24442step3 raw24442step3Labels := by
      have ha : raw24442step3 = raw24442step2 := by apply Matrix.ext; unfold raw24442step3 raw24442step2; decide +kernel
      have hl : raw24442step2Labels = labelEmbedding1 ∘ raw24442step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24442step2 raw24442step2Labels raw24442step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1436 node1436Labels := by rfl

def raw24443 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw24443Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24443step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw24443step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24443step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw24443step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24443step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw24443step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24443 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24443 raw24443Labels = mixedMoment B node1257 node1257Labels := by
  calc
    mixedMoment B raw24443 raw24443Labels = mixedMoment B raw24443step0 raw24443step0Labels := by
      have hz : ∀ j, raw24443 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24443step0 = (fun i j => raw24443 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24443step0 raw24443; decide +kernel
      have hl : raw24443step0Labels = raw24443Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24443 raw24443Labels permutation346 hz
    mixedMoment B raw24443step0 raw24443step0Labels = mixedMoment B raw24443step1 raw24443step1Labels := by
      have ha : raw24443step1 = (fun i j => raw24443step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24443step1 raw24443step0; decide +kernel
      have hl : raw24443step1Labels = raw24443step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24443step0 raw24443step0Labels permutation34 permutation7
    mixedMoment B raw24443step1 raw24443step1Labels = mixedMoment B raw24443step2 raw24443step2Labels := by
      have ha : raw24443step2 = raw24443step1 := by apply Matrix.ext; unfold raw24443step2 raw24443step1; decide +kernel
      have hl : raw24443step1Labels = labelEmbedding1 ∘ raw24443step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24443step1 raw24443step1Labels raw24443step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1257 node1257Labels := by rfl

def raw24444 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 1, 0], ![-1, 0, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw24444Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24444step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 1, 0], ![-1, 0, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw24444step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24444step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw24444step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24444step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw24444step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24444 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24444 raw24444Labels = mixedMoment B node1257 node1257Labels := by
  calc
    mixedMoment B raw24444 raw24444Labels = mixedMoment B raw24444step0 raw24444step0Labels := by
      have hz : ∀ j, raw24444 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw24444step0 = (fun i j => raw24444 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw24444step0 raw24444; decide +kernel
      have hl : raw24444step0Labels = raw24444Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24444 raw24444Labels permutation265 hz
    mixedMoment B raw24444step0 raw24444step0Labels = mixedMoment B raw24444step1 raw24444step1Labels := by
      have ha : raw24444step1 = (fun i j => raw24444step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24444step1 raw24444step0; decide +kernel
      have hl : raw24444step1Labels = raw24444step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24444step0 raw24444step0Labels permutation34 permutation7
    mixedMoment B raw24444step1 raw24444step1Labels = mixedMoment B raw24444step2 raw24444step2Labels := by
      have ha : raw24444step2 = raw24444step1 := by apply Matrix.ext; unfold raw24444step2 raw24444step1; decide +kernel
      have hl : raw24444step1Labels = labelEmbedding1 ∘ raw24444step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24444step1 raw24444step1Labels raw24444step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1257 node1257Labels := by rfl

def raw24445 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-2, 1, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw24445Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24445step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-2, 1, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw24445step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24445step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-2, 1, 1], ![2, -3, 1], ![-2, 0, 2]]
def raw24445step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24445step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 1, -2], ![2, 0, -2]]
def raw24445step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24445step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 1, -2], ![2, 0, -2]]
def raw24445step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24445 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24445 raw24445Labels = mixedMoment B node1288 node1288Labels := by
  calc
    mixedMoment B raw24445 raw24445Labels = mixedMoment B raw24445step0 raw24445step0Labels := by
      have hz : ∀ j, raw24445 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24445step0 = (fun i j => raw24445 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24445step0 raw24445; decide +kernel
      have hl : raw24445step0Labels = raw24445Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24445 raw24445Labels permutation346 hz
    mixedMoment B raw24445step0 raw24445step0Labels = mixedMoment B raw24445step1 raw24445step1Labels := by
      have hz : ∀ j, raw24445step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24445step1 = (fun i j => raw24445step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24445step1 raw24445step0; decide +kernel
      have hl : raw24445step1Labels = raw24445step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24445step0 raw24445step0Labels permutation56 hz
    mixedMoment B raw24445step1 raw24445step1Labels = mixedMoment B raw24445step2 raw24445step2Labels := by
      have ha : raw24445step2 = (fun i j => raw24445step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24445step2 raw24445step1; decide +kernel
      have hl : raw24445step2Labels = raw24445step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24445step1 raw24445step1Labels permutation10 permutation7
    mixedMoment B raw24445step2 raw24445step2Labels = mixedMoment B raw24445step3 raw24445step3Labels := by
      have ha : raw24445step3 = raw24445step2 := by apply Matrix.ext; unfold raw24445step3 raw24445step2; decide +kernel
      have hl : raw24445step2Labels = labelEmbedding1 ∘ raw24445step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24445step2 raw24445step2Labels raw24445step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1288 node1288Labels := by rfl

def raw24446 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![-3, 1, 2]]
def raw24446Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24446step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![0, 0, 0], ![-1, 0, 1], ![2, -3, 1], ![-3, 1, 2]]
def raw24446step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24446step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![-1, 0, 1], ![2, -3, 1], ![-3, 1, 2]]
def raw24446step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24446step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def raw24446step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24446step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, -3, 2], ![1, 0, -1], ![2, 1, -3]]
def raw24446step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24446 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24446 raw24446Labels = mixedMoment B node1287 node1287Labels := by
  calc
    mixedMoment B raw24446 raw24446Labels = mixedMoment B raw24446step0 raw24446step0Labels := by
      have hz : ∀ j, raw24446 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24446step0 = (fun i j => raw24446 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24446step0 raw24446; decide +kernel
      have hl : raw24446step0Labels = raw24446Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24446 raw24446Labels permutation346 hz
    mixedMoment B raw24446step0 raw24446step0Labels = mixedMoment B raw24446step1 raw24446step1Labels := by
      have hz : ∀ j, raw24446step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24446step1 = (fun i j => raw24446step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24446step1 raw24446step0; decide +kernel
      have hl : raw24446step1Labels = raw24446step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24446step0 raw24446step0Labels permutation56 hz
    mixedMoment B raw24446step1 raw24446step1Labels = mixedMoment B raw24446step2 raw24446step2Labels := by
      have ha : raw24446step2 = (fun i j => raw24446step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24446step2 raw24446step1; decide +kernel
      have hl : raw24446step2Labels = raw24446step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24446step1 raw24446step1Labels permutation10 permutation7
    mixedMoment B raw24446step2 raw24446step2Labels = mixedMoment B raw24446step3 raw24446step3Labels := by
      have ha : raw24446step3 = raw24446step2 := by apply Matrix.ext; unfold raw24446step3 raw24446step2; decide +kernel
      have hl : raw24446step2Labels = labelEmbedding1 ∘ raw24446step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24446step2 raw24446step2Labels raw24446step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1287 node1287Labels := by rfl

def raw24447 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24447Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24447step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 3, -4], ![0, 0, 0], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24447step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24447step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 3, -4], ![-1, 0, 1], ![1, -2, 1], ![-1, -1, 2]]
def raw24447step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw24447step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw24447step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw24447step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 3, 1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw24447step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical24447 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw24447 raw24447Labels = mixedMoment B node1443 node1443Labels := by
  calc
    mixedMoment B raw24447 raw24447Labels = mixedMoment B raw24447step0 raw24447step0Labels := by
      have hz : ∀ j, raw24447 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw24447step0 = (fun i j => raw24447 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw24447step0 raw24447; decide +kernel
      have hl : raw24447step0Labels = raw24447Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24447 raw24447Labels permutation346 hz
    mixedMoment B raw24447step0 raw24447step0Labels = mixedMoment B raw24447step1 raw24447step1Labels := by
      have hz : ∀ j, raw24447step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw24447step1 = (fun i j => raw24447step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw24447step1 raw24447step0; decide +kernel
      have hl : raw24447step1Labels = raw24447step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw24447step0 raw24447step0Labels permutation56 hz
    mixedMoment B raw24447step1 raw24447step1Labels = mixedMoment B raw24447step2 raw24447step2Labels := by
      have ha : raw24447step2 = (fun i j => raw24447step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw24447step2 raw24447step1; decide +kernel
      have hl : raw24447step2Labels = raw24447step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw24447step1 raw24447step1Labels permutation10 permutation7
    mixedMoment B raw24447step2 raw24447step2Labels = mixedMoment B raw24447step3 raw24447step3Labels := by
      have ha : raw24447step3 = raw24447step2 := by apply Matrix.ext; unfold raw24447step3 raw24447step2; decide +kernel
      have hl : raw24447step2Labels = labelEmbedding1 ∘ raw24447step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw24447step2 raw24447step2Labels raw24447step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1443 node1443Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
