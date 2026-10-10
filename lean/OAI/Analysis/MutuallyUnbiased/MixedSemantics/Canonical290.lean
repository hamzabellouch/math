import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes83
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw37120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1]]
def raw37120Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37120step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw37120step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37120step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37120step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37120step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37120step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37120 raw37120Labels = mixedMoment B node5123 node5123Labels := by
  calc
    mixedMoment B raw37120 raw37120Labels = mixedMoment B raw37120step0 raw37120step0Labels := by
      have ha : raw37120step0 = (fun i j => raw37120 (permutation336 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37120step0 raw37120; decide +kernel
      have hl : raw37120step0Labels = raw37120Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37120 raw37120Labels permutation336 permutation5
    mixedMoment B raw37120step0 raw37120step0Labels = mixedMoment B raw37120step1 raw37120step1Labels := by
      have ha : raw37120step1 = -raw37120step0 := by apply Matrix.ext; change ∀ i j, raw37120step1 i j = -(raw37120step0 i j); unfold raw37120step1 raw37120step0; decide +kernel
      have hl : raw37120step1Labels = raw37120step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37120step1 raw37120step1Labels = mixedMoment B raw37120step2 raw37120step2Labels := by
      have ha : raw37120step2 = raw37120step1 := by apply Matrix.ext; unfold raw37120step2 raw37120step1; decide +kernel
      have hl : raw37120step1Labels = labelEmbedding8 ∘ raw37120step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37120step1 raw37120step1Labels raw37120step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5123 node5123Labels := by rfl

def raw37121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 4, -1], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37121Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37121step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw37121step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37121step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37121step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37121step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37121step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37121 raw37121Labels = mixedMoment B node4376 node4376Labels := by
  calc
    mixedMoment B raw37121 raw37121Labels = mixedMoment B raw37121step0 raw37121step0Labels := by
      have ha : raw37121step0 = (fun i j => raw37121 (permutation284 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37121step0 raw37121; decide +kernel
      have hl : raw37121step0Labels = raw37121Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37121 raw37121Labels permutation284 permutation5
    mixedMoment B raw37121step0 raw37121step0Labels = mixedMoment B raw37121step1 raw37121step1Labels := by
      have ha : raw37121step1 = -raw37121step0 := by apply Matrix.ext; change ∀ i j, raw37121step1 i j = -(raw37121step0 i j); unfold raw37121step1 raw37121step0; decide +kernel
      have hl : raw37121step1Labels = raw37121step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37121step1 raw37121step1Labels = mixedMoment B raw37121step2 raw37121step2Labels := by
      have ha : raw37121step2 = raw37121step1 := by apply Matrix.ext; unfold raw37121step2 raw37121step1; decide +kernel
      have hl : raw37121step1Labels = labelEmbedding8 ∘ raw37121step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37121step1 raw37121step1Labels raw37121step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4376 node4376Labels := by rfl

def raw37122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![1, 0, -1]]
def raw37122Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37122step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw37122step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37122step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw37122step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37122step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37122step2Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37122step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37122step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37122 raw37122Labels = mixedMoment B node5228 node5228Labels := by
  calc
    mixedMoment B raw37122 raw37122Labels = mixedMoment B raw37122step0 raw37122step0Labels := by
      have hz : ∀ j, raw37122 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37122step0 = (fun i j => raw37122 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37122step0 raw37122; decide +kernel
      have hl : raw37122step0Labels = raw37122Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37122 raw37122Labels permutation520 hz
    mixedMoment B raw37122step0 raw37122step0Labels = mixedMoment B raw37122step1 raw37122step1Labels := by
      have ha : raw37122step1 = (fun i j => raw37122step0 (permutation60 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37122step1 raw37122step0; decide +kernel
      have hl : raw37122step1Labels = raw37122step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37122step0 raw37122step0Labels permutation60 permutation5
    mixedMoment B raw37122step1 raw37122step1Labels = mixedMoment B raw37122step2 raw37122step2Labels := by
      have ha : raw37122step2 = -raw37122step1 := by apply Matrix.ext; change ∀ i j, raw37122step2 i j = -(raw37122step1 i j); unfold raw37122step2 raw37122step1; decide +kernel
      have hl : raw37122step2Labels = raw37122step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37122step2 raw37122step2Labels = mixedMoment B raw37122step3 raw37122step3Labels := by
      have ha : raw37122step3 = raw37122step2 := by apply Matrix.ext; unfold raw37122step3 raw37122step2; decide +kernel
      have hl : raw37122step2Labels = labelEmbedding8 ∘ raw37122step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37122step2 raw37122step2Labels raw37122step3Labels labelEmbedding8 hl
    _ = mixedMoment B node5228 node5228Labels := by rfl

def raw37123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1]]
def raw37123Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37123step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw37123step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37123step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37123step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37123step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37123step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37123 raw37123Labels = mixedMoment B node5123 node5123Labels := by
  calc
    mixedMoment B raw37123 raw37123Labels = mixedMoment B raw37123step0 raw37123step0Labels := by
      have ha : raw37123step0 = (fun i j => raw37123 (permutation334 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37123step0 raw37123; decide +kernel
      have hl : raw37123step0Labels = raw37123Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37123 raw37123Labels permutation334 permutation5
    mixedMoment B raw37123step0 raw37123step0Labels = mixedMoment B raw37123step1 raw37123step1Labels := by
      have ha : raw37123step1 = -raw37123step0 := by apply Matrix.ext; change ∀ i j, raw37123step1 i j = -(raw37123step0 i j); unfold raw37123step1 raw37123step0; decide +kernel
      have hl : raw37123step1Labels = raw37123step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37123step1 raw37123step1Labels = mixedMoment B raw37123step2 raw37123step2Labels := by
      have ha : raw37123step2 = raw37123step1 := by apply Matrix.ext; unfold raw37123step2 raw37123step1; decide +kernel
      have hl : raw37123step1Labels = labelEmbedding8 ∘ raw37123step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37123step1 raw37123step1Labels raw37123step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5123 node5123Labels := by rfl

def raw37124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-3, 4, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1]]
def raw37124Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37124step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw37124step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37124step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37124step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37124step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37124step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37124 raw37124Labels = mixedMoment B node4376 node4376Labels := by
  calc
    mixedMoment B raw37124 raw37124Labels = mixedMoment B raw37124step0 raw37124step0Labels := by
      have ha : raw37124step0 = (fun i j => raw37124 (permutation283 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37124step0 raw37124; decide +kernel
      have hl : raw37124step0Labels = raw37124Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37124 raw37124Labels permutation283 permutation5
    mixedMoment B raw37124step0 raw37124step0Labels = mixedMoment B raw37124step1 raw37124step1Labels := by
      have ha : raw37124step1 = -raw37124step0 := by apply Matrix.ext; change ∀ i j, raw37124step1 i j = -(raw37124step0 i j); unfold raw37124step1 raw37124step0; decide +kernel
      have hl : raw37124step1Labels = raw37124step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37124step1 raw37124step1Labels = mixedMoment B raw37124step2 raw37124step2Labels := by
      have ha : raw37124step2 = raw37124step1 := by apply Matrix.ext; unfold raw37124step2 raw37124step1; decide +kernel
      have hl : raw37124step1Labels = labelEmbedding8 ∘ raw37124step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37124step1 raw37124step1Labels raw37124step2Labels labelEmbedding8 hl
    _ = mixedMoment B node4376 node4376Labels := by rfl

def raw37125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1]]
def raw37125Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37125step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw37125step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37125step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37125step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37125step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37125step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37125 raw37125Labels = mixedMoment B node5123 node5123Labels := by
  calc
    mixedMoment B raw37125 raw37125Labels = mixedMoment B raw37125step0 raw37125step0Labels := by
      have ha : raw37125step0 = (fun i j => raw37125 (permutation333 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37125step0 raw37125; decide +kernel
      have hl : raw37125step0Labels = raw37125Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37125 raw37125Labels permutation333 permutation5
    mixedMoment B raw37125step0 raw37125step0Labels = mixedMoment B raw37125step1 raw37125step1Labels := by
      have ha : raw37125step1 = -raw37125step0 := by apply Matrix.ext; change ∀ i j, raw37125step1 i j = -(raw37125step0 i j); unfold raw37125step1 raw37125step0; decide +kernel
      have hl : raw37125step1Labels = raw37125step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37125step1 raw37125step1Labels = mixedMoment B raw37125step2 raw37125step2Labels := by
      have ha : raw37125step2 = raw37125step1 := by apply Matrix.ext; unfold raw37125step2 raw37125step1; decide +kernel
      have hl : raw37125step1Labels = labelEmbedding8 ∘ raw37125step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37125step1 raw37125step1Labels raw37125step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5123 node5123Labels := by rfl

def raw37126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 0, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37126Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37126step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37126step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37126 raw37126Labels = mixedMoment B node4833 node4833Labels := by
  calc
    mixedMoment B raw37126 raw37126Labels = mixedMoment B raw37126step0 raw37126step0Labels := by
      have ha : raw37126step0 = (fun i j => raw37126 (permutation283 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37126step0 raw37126; decide +kernel
      have hl : raw37126step0Labels = raw37126Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37126 raw37126Labels permutation283 permutation2
    _ = mixedMoment B node4833 node4833Labels := by rfl

def raw37127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37127Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37127step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37127step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37127step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37127step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37127step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37127step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37127 raw37127Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw37127 raw37127Labels = mixedMoment B raw37127step0 raw37127step0Labels := by
      have ha : raw37127step0 = (fun i j => raw37127 (permutation283 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37127step0 raw37127; decide +kernel
      have hl : raw37127step0Labels = raw37127Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37127 raw37127Labels permutation283 permutation7
    mixedMoment B raw37127step0 raw37127step0Labels = mixedMoment B raw37127step1 raw37127step1Labels := by
      have ha : raw37127step1 = -raw37127step0 := by apply Matrix.ext; change ∀ i j, raw37127step1 i j = -(raw37127step0 i j); unfold raw37127step1 raw37127step0; decide +kernel
      have hl : raw37127step1Labels = raw37127step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37127step1 raw37127step1Labels = mixedMoment B raw37127step2 raw37127step2Labels := by
      have ha : raw37127step2 = raw37127step1 := by apply Matrix.ext; unfold raw37127step2 raw37127step1; decide +kernel
      have hl : raw37127step1Labels = labelEmbedding10 ∘ raw37127step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37127step1 raw37127step1Labels raw37127step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

def raw37128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37128Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37128step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37128step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37128step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37128step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37128step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37128step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37128 raw37128Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw37128 raw37128Labels = mixedMoment B raw37128step0 raw37128step0Labels := by
      have ha : raw37128step0 = (fun i j => raw37128 (permutation285 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37128step0 raw37128; decide +kernel
      have hl : raw37128step0Labels = raw37128Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37128 raw37128Labels permutation285 permutation7
    mixedMoment B raw37128step0 raw37128step0Labels = mixedMoment B raw37128step1 raw37128step1Labels := by
      have ha : raw37128step1 = -raw37128step0 := by apply Matrix.ext; change ∀ i j, raw37128step1 i j = -(raw37128step0 i j); unfold raw37128step1 raw37128step0; decide +kernel
      have hl : raw37128step1Labels = raw37128step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37128step1 raw37128step1Labels = mixedMoment B raw37128step2 raw37128step2Labels := by
      have ha : raw37128step2 = raw37128step1 := by apply Matrix.ext; unfold raw37128step2 raw37128step1; decide +kernel
      have hl : raw37128step1Labels = labelEmbedding10 ∘ raw37128step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37128step1 raw37128step1Labels raw37128step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

def raw37129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw37129Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37129step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37129step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37129step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37129step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37129step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37129step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37129 raw37129Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw37129 raw37129Labels = mixedMoment B raw37129step0 raw37129step0Labels := by
      have ha : raw37129step0 = (fun i j => raw37129 (permutation287 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37129step0 raw37129; decide +kernel
      have hl : raw37129step0Labels = raw37129Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37129 raw37129Labels permutation287 permutation7
    mixedMoment B raw37129step0 raw37129step0Labels = mixedMoment B raw37129step1 raw37129step1Labels := by
      have ha : raw37129step1 = -raw37129step0 := by apply Matrix.ext; change ∀ i j, raw37129step1 i j = -(raw37129step0 i j); unfold raw37129step1 raw37129step0; decide +kernel
      have hl : raw37129step1Labels = raw37129step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37129step1 raw37129step1Labels = mixedMoment B raw37129step2 raw37129step2Labels := by
      have ha : raw37129step2 = raw37129step1 := by apply Matrix.ext; unfold raw37129step2 raw37129step1; decide +kernel
      have hl : raw37129step1Labels = labelEmbedding10 ∘ raw37129step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37129step1 raw37129step1Labels raw37129step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5257 node5257Labels := by rfl

def raw37130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw37130Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37130step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37130step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37130step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37130step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37130step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37130step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37130step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37130step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37130 raw37130Labels = mixedMoment B node5273 node5273Labels := by
  calc
    mixedMoment B raw37130 raw37130Labels = mixedMoment B raw37130step0 raw37130step0Labels := by
      have hz : ∀ j, raw37130 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw37130step0 = (fun i j => raw37130 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw37130step0 raw37130; decide +kernel
      have hl : raw37130step0Labels = raw37130Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37130 raw37130Labels permutation590 hz
    mixedMoment B raw37130step0 raw37130step0Labels = mixedMoment B raw37130step1 raw37130step1Labels := by
      have ha : raw37130step1 = (fun i j => raw37130step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37130step1 raw37130step0; decide +kernel
      have hl : raw37130step1Labels = raw37130step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37130step0 raw37130step0Labels permutation56 permutation7
    mixedMoment B raw37130step1 raw37130step1Labels = mixedMoment B raw37130step2 raw37130step2Labels := by
      have ha : raw37130step2 = -raw37130step1 := by apply Matrix.ext; change ∀ i j, raw37130step2 i j = -(raw37130step1 i j); unfold raw37130step2 raw37130step1; decide +kernel
      have hl : raw37130step2Labels = raw37130step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37130step2 raw37130step2Labels = mixedMoment B raw37130step3 raw37130step3Labels := by
      have ha : raw37130step3 = raw37130step2 := by apply Matrix.ext; unfold raw37130step3 raw37130step2; decide +kernel
      have hl : raw37130step2Labels = labelEmbedding10 ∘ raw37130step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37130step2 raw37130step2Labels raw37130step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5273 node5273Labels := by rfl

def raw37131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37131Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37131step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37131step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37131step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37131step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37131 raw37131Labels = mixedMoment B node4878 node4878Labels := by
  calc
    mixedMoment B raw37131 raw37131Labels = mixedMoment B raw37131step0 raw37131step0Labels := by
      have ha : raw37131step0 = (fun i j => raw37131 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37131step0 raw37131; decide +kernel
      have hl : raw37131step0Labels = raw37131Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37131 raw37131Labels permutation152 permutation3
    mixedMoment B raw37131step0 raw37131step0Labels = mixedMoment B raw37131step1 raw37131step1Labels := by
      have ha : raw37131step1 = raw37131step0 := by apply Matrix.ext; unfold raw37131step1 raw37131step0; decide +kernel
      have hl : raw37131step0Labels = labelEmbedding6 ∘ raw37131step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37131step0 raw37131step0Labels raw37131step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4878 node4878Labels := by rfl

def raw37132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37132Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37132step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw37132step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw37132step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37132step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw37132step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37132step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37132 raw37132Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw37132 raw37132Labels = mixedMoment B raw37132step0 raw37132step0Labels := by
      have ha : raw37132step0 = (fun i j => raw37132 (permutation336 i) (permutation6 j)) := by apply Matrix.ext; unfold raw37132step0 raw37132; decide +kernel
      have hl : raw37132step0Labels = raw37132Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37132 raw37132Labels permutation336 permutation6
    mixedMoment B raw37132step0 raw37132step0Labels = mixedMoment B raw37132step1 raw37132step1Labels := by
      have ha : raw37132step1 = -raw37132step0 := by apply Matrix.ext; change ∀ i j, raw37132step1 i j = -(raw37132step0 i j); unfold raw37132step1 raw37132step0; decide +kernel
      have hl : raw37132step1Labels = raw37132step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37132step1 raw37132step1Labels = mixedMoment B raw37132step2 raw37132step2Labels := by
      have ha : raw37132step2 = raw37132step1 := by apply Matrix.ext; unfold raw37132step2 raw37132step1; decide +kernel
      have hl : raw37132step1Labels = labelEmbedding9 ∘ raw37132step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37132step1 raw37132step1Labels raw37132step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

def raw37133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37133Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37133step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw37133step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw37133step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37133step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw37133step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37133step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37133 raw37133Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw37133 raw37133Labels = mixedMoment B raw37133step0 raw37133step0Labels := by
      have ha : raw37133step0 = (fun i j => raw37133 (permutation334 i) (permutation6 j)) := by apply Matrix.ext; unfold raw37133step0 raw37133; decide +kernel
      have hl : raw37133step0Labels = raw37133Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37133 raw37133Labels permutation334 permutation6
    mixedMoment B raw37133step0 raw37133step0Labels = mixedMoment B raw37133step1 raw37133step1Labels := by
      have ha : raw37133step1 = -raw37133step0 := by apply Matrix.ext; change ∀ i j, raw37133step1 i j = -(raw37133step0 i j); unfold raw37133step1 raw37133step0; decide +kernel
      have hl : raw37133step1Labels = raw37133step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37133step1 raw37133step1Labels = mixedMoment B raw37133step2 raw37133step2Labels := by
      have ha : raw37133step2 = raw37133step1 := by apply Matrix.ext; unfold raw37133step2 raw37133step1; decide +kernel
      have hl : raw37133step1Labels = labelEmbedding9 ∘ raw37133step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37133step1 raw37133step1Labels raw37133step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

def raw37134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw37134Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37134step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw37134step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw37134step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37134step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw37134step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37134step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37134 raw37134Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw37134 raw37134Labels = mixedMoment B raw37134step0 raw37134step0Labels := by
      have ha : raw37134step0 = (fun i j => raw37134 (permutation333 i) (permutation6 j)) := by apply Matrix.ext; unfold raw37134step0 raw37134; decide +kernel
      have hl : raw37134step0Labels = raw37134Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37134 raw37134Labels permutation333 permutation6
    mixedMoment B raw37134step0 raw37134step0Labels = mixedMoment B raw37134step1 raw37134step1Labels := by
      have ha : raw37134step1 = -raw37134step0 := by apply Matrix.ext; change ∀ i j, raw37134step1 i j = -(raw37134step0 i j); unfold raw37134step1 raw37134step0; decide +kernel
      have hl : raw37134step1Labels = raw37134step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37134step1 raw37134step1Labels = mixedMoment B raw37134step2 raw37134step2Labels := by
      have ha : raw37134step2 = raw37134step1 := by apply Matrix.ext; unfold raw37134step2 raw37134step1; decide +kernel
      have hl : raw37134step1Labels = labelEmbedding9 ∘ raw37134step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37134step1 raw37134step1Labels raw37134step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

def raw37135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw37135Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37135step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37135step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37135step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw37135step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw37135step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw37135step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw37135step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw37135step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37135 raw37135Labels = mixedMoment B node5301 node5301Labels := by
  calc
    mixedMoment B raw37135 raw37135Labels = mixedMoment B raw37135step0 raw37135step0Labels := by
      have hz : ∀ j, raw37135 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw37135step0 = (fun i j => raw37135 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw37135step0 raw37135; decide +kernel
      have hl : raw37135step0Labels = raw37135Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37135 raw37135Labels permutation590 hz
    mixedMoment B raw37135step0 raw37135step0Labels = mixedMoment B raw37135step1 raw37135step1Labels := by
      have ha : raw37135step1 = (fun i j => raw37135step0 (permutation56 i) (permutation6 j)) := by apply Matrix.ext; unfold raw37135step1 raw37135step0; decide +kernel
      have hl : raw37135step1Labels = raw37135step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37135step0 raw37135step0Labels permutation56 permutation6
    mixedMoment B raw37135step1 raw37135step1Labels = mixedMoment B raw37135step2 raw37135step2Labels := by
      have ha : raw37135step2 = -raw37135step1 := by apply Matrix.ext; change ∀ i j, raw37135step2 i j = -(raw37135step1 i j); unfold raw37135step2 raw37135step1; decide +kernel
      have hl : raw37135step2Labels = raw37135step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37135step2 raw37135step2Labels = mixedMoment B raw37135step3 raw37135step3Labels := by
      have ha : raw37135step3 = raw37135step2 := by apply Matrix.ext; unfold raw37135step3 raw37135step2; decide +kernel
      have hl : raw37135step2Labels = labelEmbedding9 ∘ raw37135step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37135step2 raw37135step2Labels raw37135step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5301 node5301Labels := by rfl

def raw37136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37136Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37136step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw37136step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37136step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw37136step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37136 raw37136Labels = mixedMoment B node4696 node4696Labels := by
  calc
    mixedMoment B raw37136 raw37136Labels = mixedMoment B raw37136step0 raw37136step0Labels := by
      have ha : raw37136step0 = (fun i j => raw37136 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37136step0 raw37136; decide +kernel
      have hl : raw37136step0Labels = raw37136Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37136 raw37136Labels permutation161 permutation3
    mixedMoment B raw37136step0 raw37136step0Labels = mixedMoment B raw37136step1 raw37136step1Labels := by
      have ha : raw37136step1 = raw37136step0 := by apply Matrix.ext; unfold raw37136step1 raw37136step0; decide +kernel
      have hl : raw37136step0Labels = labelEmbedding6 ∘ raw37136step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37136step0 raw37136step0Labels raw37136step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4696 node4696Labels := by rfl

def raw37137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37137Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37137step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37137step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37137 raw37137Labels = mixedMoment B node4679 node4679Labels := by
  calc
    mixedMoment B raw37137 raw37137Labels = mixedMoment B raw37137step0 raw37137step0Labels := by
      have ha : raw37137step0 = (fun i j => raw37137 (permutation286 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37137step0 raw37137; decide +kernel
      have hl : raw37137step0Labels = raw37137Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37137 raw37137Labels permutation286 permutation2
    _ = mixedMoment B node4679 node4679Labels := by rfl

def raw37138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37138Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37138step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw37138step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37138step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37138step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37138step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37138step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37138 raw37138Labels = mixedMoment B node5226 node5226Labels := by
  calc
    mixedMoment B raw37138 raw37138Labels = mixedMoment B raw37138step0 raw37138step0Labels := by
      have ha : raw37138step0 = (fun i j => raw37138 (permutation286 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37138step0 raw37138; decide +kernel
      have hl : raw37138step0Labels = raw37138Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37138 raw37138Labels permutation286 permutation7
    mixedMoment B raw37138step0 raw37138step0Labels = mixedMoment B raw37138step1 raw37138step1Labels := by
      have ha : raw37138step1 = -raw37138step0 := by apply Matrix.ext; change ∀ i j, raw37138step1 i j = -(raw37138step0 i j); unfold raw37138step1 raw37138step0; decide +kernel
      have hl : raw37138step1Labels = raw37138step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37138step1 raw37138step1Labels = mixedMoment B raw37138step2 raw37138step2Labels := by
      have ha : raw37138step2 = raw37138step1 := by apply Matrix.ext; unfold raw37138step2 raw37138step1; decide +kernel
      have hl : raw37138step1Labels = labelEmbedding10 ∘ raw37138step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37138step1 raw37138step1Labels raw37138step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5226 node5226Labels := by rfl

def raw37139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw37139Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37139step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw37139step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37139step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37139step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37139step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37139step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37139 raw37139Labels = mixedMoment B node5226 node5226Labels := by
  calc
    mixedMoment B raw37139 raw37139Labels = mixedMoment B raw37139step0 raw37139step0Labels := by
      have ha : raw37139step0 = (fun i j => raw37139 (permutation288 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37139step0 raw37139; decide +kernel
      have hl : raw37139step0Labels = raw37139Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37139 raw37139Labels permutation288 permutation7
    mixedMoment B raw37139step0 raw37139step0Labels = mixedMoment B raw37139step1 raw37139step1Labels := by
      have ha : raw37139step1 = -raw37139step0 := by apply Matrix.ext; change ∀ i j, raw37139step1 i j = -(raw37139step0 i j); unfold raw37139step1 raw37139step0; decide +kernel
      have hl : raw37139step1Labels = raw37139step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37139step1 raw37139step1Labels = mixedMoment B raw37139step2 raw37139step2Labels := by
      have ha : raw37139step2 = raw37139step1 := by apply Matrix.ext; unfold raw37139step2 raw37139step1; decide +kernel
      have hl : raw37139step1Labels = labelEmbedding10 ∘ raw37139step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37139step1 raw37139step1Labels raw37139step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5226 node5226Labels := by rfl

def raw37140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw37140Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37140step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37140step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37140step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37140step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37140step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37140step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37140step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37140step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37140 raw37140Labels = mixedMoment B node5237 node5237Labels := by
  calc
    mixedMoment B raw37140 raw37140Labels = mixedMoment B raw37140step0 raw37140step0Labels := by
      have hz : ∀ j, raw37140 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw37140step0 = (fun i j => raw37140 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw37140step0 raw37140; decide +kernel
      have hl : raw37140step0Labels = raw37140Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37140 raw37140Labels permutation590 hz
    mixedMoment B raw37140step0 raw37140step0Labels = mixedMoment B raw37140step1 raw37140step1Labels := by
      have ha : raw37140step1 = (fun i j => raw37140step0 (permutation59 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37140step1 raw37140step0; decide +kernel
      have hl : raw37140step1Labels = raw37140step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37140step0 raw37140step0Labels permutation59 permutation7
    mixedMoment B raw37140step1 raw37140step1Labels = mixedMoment B raw37140step2 raw37140step2Labels := by
      have ha : raw37140step2 = -raw37140step1 := by apply Matrix.ext; change ∀ i j, raw37140step2 i j = -(raw37140step1 i j); unfold raw37140step2 raw37140step1; decide +kernel
      have hl : raw37140step2Labels = raw37140step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37140step2 raw37140step2Labels = mixedMoment B raw37140step3 raw37140step3Labels := by
      have ha : raw37140step3 = raw37140step2 := by apply Matrix.ext; unfold raw37140step3 raw37140step2; decide +kernel
      have hl : raw37140step2Labels = labelEmbedding10 ∘ raw37140step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37140step2 raw37140step2Labels raw37140step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5237 node5237Labels := by rfl

def raw37141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37141Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37141step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw37141step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37141step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw37141step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37141 raw37141Labels = mixedMoment B node4696 node4696Labels := by
  calc
    mixedMoment B raw37141 raw37141Labels = mixedMoment B raw37141step0 raw37141step0Labels := by
      have ha : raw37141step0 = (fun i j => raw37141 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37141step0 raw37141; decide +kernel
      have hl : raw37141step0Labels = raw37141Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37141 raw37141Labels permutation155 permutation3
    mixedMoment B raw37141step0 raw37141step0Labels = mixedMoment B raw37141step1 raw37141step1Labels := by
      have ha : raw37141step1 = raw37141step0 := by apply Matrix.ext; unfold raw37141step1 raw37141step0; decide +kernel
      have hl : raw37141step0Labels = labelEmbedding6 ∘ raw37141step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37141step0 raw37141step0Labels raw37141step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4696 node4696Labels := by rfl

def raw37142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37142Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37142step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37142step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37142 raw37142Labels = mixedMoment B node4679 node4679Labels := by
  calc
    mixedMoment B raw37142 raw37142Labels = mixedMoment B raw37142step0 raw37142step0Labels := by
      have ha : raw37142step0 = (fun i j => raw37142 (permutation284 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37142step0 raw37142; decide +kernel
      have hl : raw37142step0Labels = raw37142Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37142 raw37142Labels permutation284 permutation2
    _ = mixedMoment B node4679 node4679Labels := by rfl

def raw37143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37143Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37143step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw37143step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37143step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37143step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37143step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37143step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37143 raw37143Labels = mixedMoment B node5226 node5226Labels := by
  calc
    mixedMoment B raw37143 raw37143Labels = mixedMoment B raw37143step0 raw37143step0Labels := by
      have ha : raw37143step0 = (fun i j => raw37143 (permutation284 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37143step0 raw37143; decide +kernel
      have hl : raw37143step0Labels = raw37143Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37143 raw37143Labels permutation284 permutation7
    mixedMoment B raw37143step0 raw37143step0Labels = mixedMoment B raw37143step1 raw37143step1Labels := by
      have ha : raw37143step1 = -raw37143step0 := by apply Matrix.ext; change ∀ i j, raw37143step1 i j = -(raw37143step0 i j); unfold raw37143step1 raw37143step0; decide +kernel
      have hl : raw37143step1Labels = raw37143step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37143step1 raw37143step1Labels = mixedMoment B raw37143step2 raw37143step2Labels := by
      have ha : raw37143step2 = raw37143step1 := by apply Matrix.ext; unfold raw37143step2 raw37143step1; decide +kernel
      have hl : raw37143step1Labels = labelEmbedding10 ∘ raw37143step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37143step1 raw37143step1Labels raw37143step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5226 node5226Labels := by rfl

def raw37144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw37144Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37144step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw37144step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37144step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37144step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37144step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37144step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37144 raw37144Labels = mixedMoment B node5226 node5226Labels := by
  calc
    mixedMoment B raw37144 raw37144Labels = mixedMoment B raw37144step0 raw37144step0Labels := by
      have ha : raw37144step0 = (fun i j => raw37144 (permutation287 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37144step0 raw37144; decide +kernel
      have hl : raw37144step0Labels = raw37144Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37144 raw37144Labels permutation287 permutation7
    mixedMoment B raw37144step0 raw37144step0Labels = mixedMoment B raw37144step1 raw37144step1Labels := by
      have ha : raw37144step1 = -raw37144step0 := by apply Matrix.ext; change ∀ i j, raw37144step1 i j = -(raw37144step0 i j); unfold raw37144step1 raw37144step0; decide +kernel
      have hl : raw37144step1Labels = raw37144step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37144step1 raw37144step1Labels = mixedMoment B raw37144step2 raw37144step2Labels := by
      have ha : raw37144step2 = raw37144step1 := by apply Matrix.ext; unfold raw37144step2 raw37144step1; decide +kernel
      have hl : raw37144step1Labels = labelEmbedding10 ∘ raw37144step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37144step1 raw37144step1Labels raw37144step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5226 node5226Labels := by rfl

def raw37145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw37145Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37145step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw37145step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37145step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37145step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37145step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37145step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37145step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37145step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37145 raw37145Labels = mixedMoment B node5237 node5237Labels := by
  calc
    mixedMoment B raw37145 raw37145Labels = mixedMoment B raw37145step0 raw37145step0Labels := by
      have hz : ∀ j, raw37145 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw37145step0 = (fun i j => raw37145 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw37145step0 raw37145; decide +kernel
      have hl : raw37145step0Labels = raw37145Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37145 raw37145Labels permutation590 hz
    mixedMoment B raw37145step0 raw37145step0Labels = mixedMoment B raw37145step1 raw37145step1Labels := by
      have ha : raw37145step1 = (fun i j => raw37145step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37145step1 raw37145step0; decide +kernel
      have hl : raw37145step1Labels = raw37145step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37145step0 raw37145step0Labels permutation57 permutation7
    mixedMoment B raw37145step1 raw37145step1Labels = mixedMoment B raw37145step2 raw37145step2Labels := by
      have ha : raw37145step2 = -raw37145step1 := by apply Matrix.ext; change ∀ i j, raw37145step2 i j = -(raw37145step1 i j); unfold raw37145step2 raw37145step1; decide +kernel
      have hl : raw37145step2Labels = raw37145step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37145step2 raw37145step2Labels = mixedMoment B raw37145step3 raw37145step3Labels := by
      have ha : raw37145step3 = raw37145step2 := by apply Matrix.ext; unfold raw37145step3 raw37145step2; decide +kernel
      have hl : raw37145step2Labels = labelEmbedding10 ∘ raw37145step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37145step2 raw37145step2Labels raw37145step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5237 node5237Labels := by rfl

def raw37146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw37146Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37146step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw37146step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37146step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw37146step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37146 raw37146Labels = mixedMoment B node4696 node4696Labels := by
  calc
    mixedMoment B raw37146 raw37146Labels = mixedMoment B raw37146step0 raw37146step0Labels := by
      have ha : raw37146step0 = (fun i j => raw37146 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37146step0 raw37146; decide +kernel
      have hl : raw37146step0Labels = raw37146Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37146 raw37146Labels permutation153 permutation3
    mixedMoment B raw37146step0 raw37146step0Labels = mixedMoment B raw37146step1 raw37146step1Labels := by
      have ha : raw37146step1 = raw37146step0 := by apply Matrix.ext; unfold raw37146step1 raw37146step0; decide +kernel
      have hl : raw37146step0Labels = labelEmbedding6 ∘ raw37146step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37146step0 raw37146step0Labels raw37146step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4696 node4696Labels := by rfl

def raw37147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw37147Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37147step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37147step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37147 raw37147Labels = mixedMoment B node4679 node4679Labels := by
  calc
    mixedMoment B raw37147 raw37147Labels = mixedMoment B raw37147step0 raw37147step0Labels := by
      have ha : raw37147step0 = (fun i j => raw37147 (permutation283 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37147step0 raw37147; decide +kernel
      have hl : raw37147step0Labels = raw37147Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37147 raw37147Labels permutation283 permutation2
    _ = mixedMoment B node4679 node4679Labels := by rfl

def raw37148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw37148Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37148step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw37148step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37148step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37148step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37148step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37148step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37148 raw37148Labels = mixedMoment B node5226 node5226Labels := by
  calc
    mixedMoment B raw37148 raw37148Labels = mixedMoment B raw37148step0 raw37148step0Labels := by
      have ha : raw37148step0 = (fun i j => raw37148 (permutation283 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37148step0 raw37148; decide +kernel
      have hl : raw37148step0Labels = raw37148Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37148 raw37148Labels permutation283 permutation7
    mixedMoment B raw37148step0 raw37148step0Labels = mixedMoment B raw37148step1 raw37148step1Labels := by
      have ha : raw37148step1 = -raw37148step0 := by apply Matrix.ext; change ∀ i j, raw37148step1 i j = -(raw37148step0 i j); unfold raw37148step1 raw37148step0; decide +kernel
      have hl : raw37148step1Labels = raw37148step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37148step1 raw37148step1Labels = mixedMoment B raw37148step2 raw37148step2Labels := by
      have ha : raw37148step2 = raw37148step1 := by apply Matrix.ext; unfold raw37148step2 raw37148step1; decide +kernel
      have hl : raw37148step1Labels = labelEmbedding10 ∘ raw37148step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37148step1 raw37148step1Labels raw37148step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5226 node5226Labels := by rfl

def raw37149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw37149Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37149step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw37149step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37149step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37149step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37149step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37149step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37149 raw37149Labels = mixedMoment B node5226 node5226Labels := by
  calc
    mixedMoment B raw37149 raw37149Labels = mixedMoment B raw37149step0 raw37149step0Labels := by
      have ha : raw37149step0 = (fun i j => raw37149 (permutation285 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37149step0 raw37149; decide +kernel
      have hl : raw37149step0Labels = raw37149Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37149 raw37149Labels permutation285 permutation7
    mixedMoment B raw37149step0 raw37149step0Labels = mixedMoment B raw37149step1 raw37149step1Labels := by
      have ha : raw37149step1 = -raw37149step0 := by apply Matrix.ext; change ∀ i j, raw37149step1 i j = -(raw37149step0 i j); unfold raw37149step1 raw37149step0; decide +kernel
      have hl : raw37149step1Labels = raw37149step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37149step1 raw37149step1Labels = mixedMoment B raw37149step2 raw37149step2Labels := by
      have ha : raw37149step2 = raw37149step1 := by apply Matrix.ext; unfold raw37149step2 raw37149step1; decide +kernel
      have hl : raw37149step1Labels = labelEmbedding10 ∘ raw37149step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37149step1 raw37149step1Labels raw37149step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5226 node5226Labels := by rfl

def raw37150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw37150Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37150step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37150step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37150step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37150step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37150step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37150step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37150step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37150step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37150 raw37150Labels = mixedMoment B node5237 node5237Labels := by
  calc
    mixedMoment B raw37150 raw37150Labels = mixedMoment B raw37150step0 raw37150step0Labels := by
      have hz : ∀ j, raw37150 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw37150step0 = (fun i j => raw37150 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw37150step0 raw37150; decide +kernel
      have hl : raw37150step0Labels = raw37150Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37150 raw37150Labels permutation590 hz
    mixedMoment B raw37150step0 raw37150step0Labels = mixedMoment B raw37150step1 raw37150step1Labels := by
      have ha : raw37150step1 = (fun i j => raw37150step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37150step1 raw37150step0; decide +kernel
      have hl : raw37150step1Labels = raw37150step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37150step0 raw37150step0Labels permutation56 permutation7
    mixedMoment B raw37150step1 raw37150step1Labels = mixedMoment B raw37150step2 raw37150step2Labels := by
      have ha : raw37150step2 = -raw37150step1 := by apply Matrix.ext; change ∀ i j, raw37150step2 i j = -(raw37150step1 i j); unfold raw37150step2 raw37150step1; decide +kernel
      have hl : raw37150step2Labels = raw37150step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37150step2 raw37150step2Labels = mixedMoment B raw37150step3 raw37150step3Labels := by
      have ha : raw37150step3 = raw37150step2 := by apply Matrix.ext; unfold raw37150step3 raw37150step2; decide +kernel
      have hl : raw37150step2Labels = labelEmbedding10 ∘ raw37150step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37150step2 raw37150step2Labels raw37150step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5237 node5237Labels := by rfl

def raw37151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37151Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37151step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37151step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37151step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 3, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37151step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37151 raw37151Labels = mixedMoment B node4695 node4695Labels := by
  calc
    mixedMoment B raw37151 raw37151Labels = mixedMoment B raw37151step0 raw37151step0Labels := by
      have ha : raw37151step0 = (fun i j => raw37151 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37151step0 raw37151; decide +kernel
      have hl : raw37151step0Labels = raw37151Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37151 raw37151Labels permutation152 permutation3
    mixedMoment B raw37151step0 raw37151step0Labels = mixedMoment B raw37151step1 raw37151step1Labels := by
      have ha : raw37151step1 = raw37151step0 := by apply Matrix.ext; unfold raw37151step1 raw37151step0; decide +kernel
      have hl : raw37151step0Labels = labelEmbedding6 ∘ raw37151step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37151step0 raw37151step0Labels raw37151step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4695 node4695Labels := by rfl

def raw37152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37152Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37152step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37152step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37152 raw37152Labels = mixedMoment B node4685 node4685Labels := by
  calc
    mixedMoment B raw37152 raw37152Labels = mixedMoment B raw37152step0 raw37152step0Labels := by
      have ha : raw37152step0 = (fun i j => raw37152 (permutation265 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37152step0 raw37152; decide +kernel
      have hl : raw37152step0Labels = raw37152Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37152 raw37152Labels permutation265 permutation2
    _ = mixedMoment B node4685 node4685Labels := by rfl

def raw37153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37153Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37153step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37153step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37153step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37153step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37153step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37153step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37153 raw37153Labels = mixedMoment B node5231 node5231Labels := by
  calc
    mixedMoment B raw37153 raw37153Labels = mixedMoment B raw37153step0 raw37153step0Labels := by
      have ha : raw37153step0 = (fun i j => raw37153 (permutation283 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37153step0 raw37153; decide +kernel
      have hl : raw37153step0Labels = raw37153Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37153 raw37153Labels permutation283 permutation7
    mixedMoment B raw37153step0 raw37153step0Labels = mixedMoment B raw37153step1 raw37153step1Labels := by
      have ha : raw37153step1 = -raw37153step0 := by apply Matrix.ext; change ∀ i j, raw37153step1 i j = -(raw37153step0 i j); unfold raw37153step1 raw37153step0; decide +kernel
      have hl : raw37153step1Labels = raw37153step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37153step1 raw37153step1Labels = mixedMoment B raw37153step2 raw37153step2Labels := by
      have ha : raw37153step2 = raw37153step1 := by apply Matrix.ext; unfold raw37153step2 raw37153step1; decide +kernel
      have hl : raw37153step1Labels = labelEmbedding10 ∘ raw37153step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37153step1 raw37153step1Labels raw37153step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5231 node5231Labels := by rfl

def raw37154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37154Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37154step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37154step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37154step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37154step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37154step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37154step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37154 raw37154Labels = mixedMoment B node5231 node5231Labels := by
  calc
    mixedMoment B raw37154 raw37154Labels = mixedMoment B raw37154step0 raw37154step0Labels := by
      have ha : raw37154step0 = (fun i j => raw37154 (permutation285 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37154step0 raw37154; decide +kernel
      have hl : raw37154step0Labels = raw37154Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37154 raw37154Labels permutation285 permutation7
    mixedMoment B raw37154step0 raw37154step0Labels = mixedMoment B raw37154step1 raw37154step1Labels := by
      have ha : raw37154step1 = -raw37154step0 := by apply Matrix.ext; change ∀ i j, raw37154step1 i j = -(raw37154step0 i j); unfold raw37154step1 raw37154step0; decide +kernel
      have hl : raw37154step1Labels = raw37154step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37154step1 raw37154step1Labels = mixedMoment B raw37154step2 raw37154step2Labels := by
      have ha : raw37154step2 = raw37154step1 := by apply Matrix.ext; unfold raw37154step2 raw37154step1; decide +kernel
      have hl : raw37154step1Labels = labelEmbedding10 ∘ raw37154step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37154step1 raw37154step1Labels raw37154step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5231 node5231Labels := by rfl

def raw37155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw37155Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37155step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37155step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37155step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37155step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw37155step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37155step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37155 raw37155Labels = mixedMoment B node5231 node5231Labels := by
  calc
    mixedMoment B raw37155 raw37155Labels = mixedMoment B raw37155step0 raw37155step0Labels := by
      have ha : raw37155step0 = (fun i j => raw37155 (permutation287 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37155step0 raw37155; decide +kernel
      have hl : raw37155step0Labels = raw37155Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37155 raw37155Labels permutation287 permutation7
    mixedMoment B raw37155step0 raw37155step0Labels = mixedMoment B raw37155step1 raw37155step1Labels := by
      have ha : raw37155step1 = -raw37155step0 := by apply Matrix.ext; change ∀ i j, raw37155step1 i j = -(raw37155step0 i j); unfold raw37155step1 raw37155step0; decide +kernel
      have hl : raw37155step1Labels = raw37155step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37155step1 raw37155step1Labels = mixedMoment B raw37155step2 raw37155step2Labels := by
      have ha : raw37155step2 = raw37155step1 := by apply Matrix.ext; unfold raw37155step2 raw37155step1; decide +kernel
      have hl : raw37155step1Labels = labelEmbedding10 ∘ raw37155step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37155step1 raw37155step1Labels raw37155step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5231 node5231Labels := by rfl

def raw37156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 0, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37156Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37156step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37156step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37156step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37156step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37156step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37156step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37156 raw37156Labels = mixedMoment B node2204 node2204Labels := by
  calc
    mixedMoment B raw37156 raw37156Labels = mixedMoment B raw37156step0 raw37156step0Labels := by
      have ha : raw37156step0 = (fun i j => raw37156 (permutation283 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37156step0 raw37156; decide +kernel
      have hl : raw37156step0Labels = raw37156Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37156 raw37156Labels permutation283 permutation7
    mixedMoment B raw37156step0 raw37156step0Labels = mixedMoment B raw37156step1 raw37156step1Labels := by
      have ha : raw37156step1 = -raw37156step0 := by apply Matrix.ext; change ∀ i j, raw37156step1 i j = -(raw37156step0 i j); unfold raw37156step1 raw37156step0; decide +kernel
      have hl : raw37156step1Labels = raw37156step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37156step1 raw37156step1Labels = mixedMoment B raw37156step2 raw37156step2Labels := by
      have ha : raw37156step2 = raw37156step1 := by apply Matrix.ext; unfold raw37156step2 raw37156step1; decide +kernel
      have hl : raw37156step1Labels = labelEmbedding1 ∘ raw37156step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37156step1 raw37156step1Labels raw37156step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2204 node2204Labels := by rfl

def raw37157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37157Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37157step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37157step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37157step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37157step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37157step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37157step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37157 raw37157Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw37157 raw37157Labels = mixedMoment B raw37157step0 raw37157step0Labels := by
      have ha : raw37157step0 = (fun i j => raw37157 (permutation283 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37157step0 raw37157; decide +kernel
      have hl : raw37157step0Labels = raw37157Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37157 raw37157Labels permutation283 permutation7
    mixedMoment B raw37157step0 raw37157step0Labels = mixedMoment B raw37157step1 raw37157step1Labels := by
      have ha : raw37157step1 = -raw37157step0 := by apply Matrix.ext; change ∀ i j, raw37157step1 i j = -(raw37157step0 i j); unfold raw37157step1 raw37157step0; decide +kernel
      have hl : raw37157step1Labels = raw37157step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37157step1 raw37157step1Labels = mixedMoment B raw37157step2 raw37157step2Labels := by
      have ha : raw37157step2 = raw37157step1 := by apply Matrix.ext; unfold raw37157step2 raw37157step1; decide +kernel
      have hl : raw37157step1Labels = labelEmbedding1 ∘ raw37157step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37157step1 raw37157step1Labels raw37157step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2721 node2721Labels := by rfl

def raw37158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37158Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37158step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37158step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37158step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37158step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37158step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37158step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37158 raw37158Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw37158 raw37158Labels = mixedMoment B raw37158step0 raw37158step0Labels := by
      have ha : raw37158step0 = (fun i j => raw37158 (permutation285 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37158step0 raw37158; decide +kernel
      have hl : raw37158step0Labels = raw37158Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37158 raw37158Labels permutation285 permutation7
    mixedMoment B raw37158step0 raw37158step0Labels = mixedMoment B raw37158step1 raw37158step1Labels := by
      have ha : raw37158step1 = -raw37158step0 := by apply Matrix.ext; change ∀ i j, raw37158step1 i j = -(raw37158step0 i j); unfold raw37158step1 raw37158step0; decide +kernel
      have hl : raw37158step1Labels = raw37158step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37158step1 raw37158step1Labels = mixedMoment B raw37158step2 raw37158step2Labels := by
      have ha : raw37158step2 = raw37158step1 := by apply Matrix.ext; unfold raw37158step2 raw37158step1; decide +kernel
      have hl : raw37158step1Labels = labelEmbedding1 ∘ raw37158step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37158step1 raw37158step1Labels raw37158step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2721 node2721Labels := by rfl

def raw37159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw37159Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37159step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37159step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37159step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37159step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37159step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37159step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37159 raw37159Labels = mixedMoment B node2721 node2721Labels := by
  calc
    mixedMoment B raw37159 raw37159Labels = mixedMoment B raw37159step0 raw37159step0Labels := by
      have ha : raw37159step0 = (fun i j => raw37159 (permutation287 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37159step0 raw37159; decide +kernel
      have hl : raw37159step0Labels = raw37159Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37159 raw37159Labels permutation287 permutation7
    mixedMoment B raw37159step0 raw37159step0Labels = mixedMoment B raw37159step1 raw37159step1Labels := by
      have ha : raw37159step1 = -raw37159step0 := by apply Matrix.ext; change ∀ i j, raw37159step1 i j = -(raw37159step0 i j); unfold raw37159step1 raw37159step0; decide +kernel
      have hl : raw37159step1Labels = raw37159step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37159step1 raw37159step1Labels = mixedMoment B raw37159step2 raw37159step2Labels := by
      have ha : raw37159step2 = raw37159step1 := by apply Matrix.ext; unfold raw37159step2 raw37159step1; decide +kernel
      have hl : raw37159step1Labels = labelEmbedding1 ∘ raw37159step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37159step1 raw37159step1Labels raw37159step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2721 node2721Labels := by rfl

def raw37160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw37160Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37160step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37160step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37160step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37160step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37160step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37160step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37160step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37160step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37160 raw37160Labels = mixedMoment B node2741 node2741Labels := by
  calc
    mixedMoment B raw37160 raw37160Labels = mixedMoment B raw37160step0 raw37160step0Labels := by
      have hz : ∀ j, raw37160 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw37160step0 = (fun i j => raw37160 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw37160step0 raw37160; decide +kernel
      have hl : raw37160step0Labels = raw37160Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37160 raw37160Labels permutation590 hz
    mixedMoment B raw37160step0 raw37160step0Labels = mixedMoment B raw37160step1 raw37160step1Labels := by
      have ha : raw37160step1 = (fun i j => raw37160step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37160step1 raw37160step0; decide +kernel
      have hl : raw37160step1Labels = raw37160step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37160step0 raw37160step0Labels permutation56 permutation7
    mixedMoment B raw37160step1 raw37160step1Labels = mixedMoment B raw37160step2 raw37160step2Labels := by
      have ha : raw37160step2 = -raw37160step1 := by apply Matrix.ext; change ∀ i j, raw37160step2 i j = -(raw37160step1 i j); unfold raw37160step2 raw37160step1; decide +kernel
      have hl : raw37160step2Labels = raw37160step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37160step2 raw37160step2Labels = mixedMoment B raw37160step3 raw37160step3Labels := by
      have ha : raw37160step3 = raw37160step2 := by apply Matrix.ext; unfold raw37160step3 raw37160step2; decide +kernel
      have hl : raw37160step2Labels = labelEmbedding1 ∘ raw37160step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37160step2 raw37160step2Labels raw37160step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2741 node2741Labels := by rfl

def raw37161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37161Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37161step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 3, -1]]
def raw37161step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37161step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw37161step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37161step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -3, 1]]
def raw37161step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37161 raw37161Labels = mixedMoment B node2234 node2234Labels := by
  calc
    mixedMoment B raw37161 raw37161Labels = mixedMoment B raw37161step0 raw37161step0Labels := by
      have ha : raw37161step0 = (fun i j => raw37161 (permutation185 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37161step0 raw37161; decide +kernel
      have hl : raw37161step0Labels = raw37161Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37161 raw37161Labels permutation185 permutation5
    mixedMoment B raw37161step0 raw37161step0Labels = mixedMoment B raw37161step1 raw37161step1Labels := by
      have ha : raw37161step1 = -raw37161step0 := by apply Matrix.ext; change ∀ i j, raw37161step1 i j = -(raw37161step0 i j); unfold raw37161step1 raw37161step0; decide +kernel
      have hl : raw37161step1Labels = raw37161step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37161step1 raw37161step1Labels = mixedMoment B raw37161step2 raw37161step2Labels := by
      have ha : raw37161step2 = raw37161step1 := by apply Matrix.ext; unfold raw37161step2 raw37161step1; decide +kernel
      have hl : raw37161step1Labels = labelEmbedding1 ∘ raw37161step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37161step1 raw37161step1Labels raw37161step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2234 node2234Labels := by rfl

def raw37162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37162Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37162step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37162step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37162step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37162step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37162step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37162step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37162 raw37162Labels = mixedMoment B node3037 node3037Labels := by
  calc
    mixedMoment B raw37162 raw37162Labels = mixedMoment B raw37162step0 raw37162step0Labels := by
      have ha : raw37162step0 = (fun i j => raw37162 (permutation283 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37162step0 raw37162; decide +kernel
      have hl : raw37162step0Labels = raw37162Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37162 raw37162Labels permutation283 permutation7
    mixedMoment B raw37162step0 raw37162step0Labels = mixedMoment B raw37162step1 raw37162step1Labels := by
      have ha : raw37162step1 = -raw37162step0 := by apply Matrix.ext; change ∀ i j, raw37162step1 i j = -(raw37162step0 i j); unfold raw37162step1 raw37162step0; decide +kernel
      have hl : raw37162step1Labels = raw37162step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37162step1 raw37162step1Labels = mixedMoment B raw37162step2 raw37162step2Labels := by
      have ha : raw37162step2 = raw37162step1 := by apply Matrix.ext; unfold raw37162step2 raw37162step1; decide +kernel
      have hl : raw37162step1Labels = labelEmbedding1 ∘ raw37162step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37162step1 raw37162step1Labels raw37162step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3037 node3037Labels := by rfl

def raw37163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37163Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37163step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37163step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37163step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37163step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37163step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37163step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37163 raw37163Labels = mixedMoment B node3037 node3037Labels := by
  calc
    mixedMoment B raw37163 raw37163Labels = mixedMoment B raw37163step0 raw37163step0Labels := by
      have ha : raw37163step0 = (fun i j => raw37163 (permutation285 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37163step0 raw37163; decide +kernel
      have hl : raw37163step0Labels = raw37163Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37163 raw37163Labels permutation285 permutation7
    mixedMoment B raw37163step0 raw37163step0Labels = mixedMoment B raw37163step1 raw37163step1Labels := by
      have ha : raw37163step1 = -raw37163step0 := by apply Matrix.ext; change ∀ i j, raw37163step1 i j = -(raw37163step0 i j); unfold raw37163step1 raw37163step0; decide +kernel
      have hl : raw37163step1Labels = raw37163step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37163step1 raw37163step1Labels = mixedMoment B raw37163step2 raw37163step2Labels := by
      have ha : raw37163step2 = raw37163step1 := by apply Matrix.ext; unfold raw37163step2 raw37163step1; decide +kernel
      have hl : raw37163step1Labels = labelEmbedding1 ∘ raw37163step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37163step1 raw37163step1Labels raw37163step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3037 node3037Labels := by rfl

def raw37164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw37164Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37164step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37164step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37164step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37164step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37164step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37164step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37164 raw37164Labels = mixedMoment B node3037 node3037Labels := by
  calc
    mixedMoment B raw37164 raw37164Labels = mixedMoment B raw37164step0 raw37164step0Labels := by
      have ha : raw37164step0 = (fun i j => raw37164 (permutation287 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37164step0 raw37164; decide +kernel
      have hl : raw37164step0Labels = raw37164Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37164 raw37164Labels permutation287 permutation7
    mixedMoment B raw37164step0 raw37164step0Labels = mixedMoment B raw37164step1 raw37164step1Labels := by
      have ha : raw37164step1 = -raw37164step0 := by apply Matrix.ext; change ∀ i j, raw37164step1 i j = -(raw37164step0 i j); unfold raw37164step1 raw37164step0; decide +kernel
      have hl : raw37164step1Labels = raw37164step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37164step1 raw37164step1Labels = mixedMoment B raw37164step2 raw37164step2Labels := by
      have ha : raw37164step2 = raw37164step1 := by apply Matrix.ext; unfold raw37164step2 raw37164step1; decide +kernel
      have hl : raw37164step1Labels = labelEmbedding1 ∘ raw37164step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37164step1 raw37164step1Labels raw37164step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3037 node3037Labels := by rfl

def raw37165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw37165Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37165step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -2, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37165step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37165step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -2, -1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37165step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37165step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37165step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37165step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37165step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37165 raw37165Labels = mixedMoment B node3053 node3053Labels := by
  calc
    mixedMoment B raw37165 raw37165Labels = mixedMoment B raw37165step0 raw37165step0Labels := by
      have hz : ∀ j, raw37165 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw37165step0 = (fun i j => raw37165 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw37165step0 raw37165; decide +kernel
      have hl : raw37165step0Labels = raw37165Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37165 raw37165Labels permutation590 hz
    mixedMoment B raw37165step0 raw37165step0Labels = mixedMoment B raw37165step1 raw37165step1Labels := by
      have ha : raw37165step1 = (fun i j => raw37165step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37165step1 raw37165step0; decide +kernel
      have hl : raw37165step1Labels = raw37165step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37165step0 raw37165step0Labels permutation56 permutation7
    mixedMoment B raw37165step1 raw37165step1Labels = mixedMoment B raw37165step2 raw37165step2Labels := by
      have ha : raw37165step2 = -raw37165step1 := by apply Matrix.ext; change ∀ i j, raw37165step2 i j = -(raw37165step1 i j); unfold raw37165step2 raw37165step1; decide +kernel
      have hl : raw37165step2Labels = raw37165step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37165step2 raw37165step2Labels = mixedMoment B raw37165step3 raw37165step3Labels := by
      have ha : raw37165step3 = raw37165step2 := by apply Matrix.ext; unfold raw37165step3 raw37165step2; decide +kernel
      have hl : raw37165step2Labels = labelEmbedding1 ∘ raw37165step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37165step2 raw37165step2Labels raw37165step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3053 node3053Labels := by rfl

def raw37166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37166Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37166step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2]]
def raw37166step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37166step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw37166step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37166step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw37166step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37166 raw37166Labels = mixedMoment B node2238 node2238Labels := by
  calc
    mixedMoment B raw37166 raw37166Labels = mixedMoment B raw37166step0 raw37166step0Labels := by
      have ha : raw37166step0 = (fun i j => raw37166 (permutation213 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37166step0 raw37166; decide +kernel
      have hl : raw37166step0Labels = raw37166Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37166 raw37166Labels permutation213 permutation5
    mixedMoment B raw37166step0 raw37166step0Labels = mixedMoment B raw37166step1 raw37166step1Labels := by
      have ha : raw37166step1 = -raw37166step0 := by apply Matrix.ext; change ∀ i j, raw37166step1 i j = -(raw37166step0 i j); unfold raw37166step1 raw37166step0; decide +kernel
      have hl : raw37166step1Labels = raw37166step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37166step1 raw37166step1Labels = mixedMoment B raw37166step2 raw37166step2Labels := by
      have ha : raw37166step2 = raw37166step1 := by apply Matrix.ext; unfold raw37166step2 raw37166step1; decide +kernel
      have hl : raw37166step1Labels = labelEmbedding1 ∘ raw37166step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37166step1 raw37166step1Labels raw37166step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2238 node2238Labels := by rfl

def raw37167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37167Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37167step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37167step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37167step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37167step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37167step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37167step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37167 raw37167Labels = mixedMoment B node2150 node2150Labels := by
  calc
    mixedMoment B raw37167 raw37167Labels = mixedMoment B raw37167step0 raw37167step0Labels := by
      have ha : raw37167step0 = (fun i j => raw37167 (permutation286 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37167step0 raw37167; decide +kernel
      have hl : raw37167step0Labels = raw37167Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37167 raw37167Labels permutation286 permutation7
    mixedMoment B raw37167step0 raw37167step0Labels = mixedMoment B raw37167step1 raw37167step1Labels := by
      have ha : raw37167step1 = -raw37167step0 := by apply Matrix.ext; change ∀ i j, raw37167step1 i j = -(raw37167step0 i j); unfold raw37167step1 raw37167step0; decide +kernel
      have hl : raw37167step1Labels = raw37167step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37167step1 raw37167step1Labels = mixedMoment B raw37167step2 raw37167step2Labels := by
      have ha : raw37167step2 = raw37167step1 := by apply Matrix.ext; unfold raw37167step2 raw37167step1; decide +kernel
      have hl : raw37167step1Labels = labelEmbedding1 ∘ raw37167step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37167step1 raw37167step1Labels raw37167step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2150 node2150Labels := by rfl

def raw37168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![2, -1, -1], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37168Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37168step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw37168step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37168step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37168step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37168step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37168step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37168 raw37168Labels = mixedMoment B node2669 node2669Labels := by
  calc
    mixedMoment B raw37168 raw37168Labels = mixedMoment B raw37168step0 raw37168step0Labels := by
      have ha : raw37168step0 = (fun i j => raw37168 (permutation286 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37168step0 raw37168; decide +kernel
      have hl : raw37168step0Labels = raw37168Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37168 raw37168Labels permutation286 permutation7
    mixedMoment B raw37168step0 raw37168step0Labels = mixedMoment B raw37168step1 raw37168step1Labels := by
      have ha : raw37168step1 = -raw37168step0 := by apply Matrix.ext; change ∀ i j, raw37168step1 i j = -(raw37168step0 i j); unfold raw37168step1 raw37168step0; decide +kernel
      have hl : raw37168step1Labels = raw37168step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37168step1 raw37168step1Labels = mixedMoment B raw37168step2 raw37168step2Labels := by
      have ha : raw37168step2 = raw37168step1 := by apply Matrix.ext; unfold raw37168step2 raw37168step1; decide +kernel
      have hl : raw37168step1Labels = labelEmbedding1 ∘ raw37168step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37168step1 raw37168step1Labels raw37168step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2669 node2669Labels := by rfl

def raw37169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![2, -1, -1], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw37169Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37169step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw37169step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37169step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37169step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37169step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37169step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37169 raw37169Labels = mixedMoment B node2669 node2669Labels := by
  calc
    mixedMoment B raw37169 raw37169Labels = mixedMoment B raw37169step0 raw37169step0Labels := by
      have ha : raw37169step0 = (fun i j => raw37169 (permutation288 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37169step0 raw37169; decide +kernel
      have hl : raw37169step0Labels = raw37169Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37169 raw37169Labels permutation288 permutation7
    mixedMoment B raw37169step0 raw37169step0Labels = mixedMoment B raw37169step1 raw37169step1Labels := by
      have ha : raw37169step1 = -raw37169step0 := by apply Matrix.ext; change ∀ i j, raw37169step1 i j = -(raw37169step0 i j); unfold raw37169step1 raw37169step0; decide +kernel
      have hl : raw37169step1Labels = raw37169step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37169step1 raw37169step1Labels = mixedMoment B raw37169step2 raw37169step2Labels := by
      have ha : raw37169step2 = raw37169step1 := by apply Matrix.ext; unfold raw37169step2 raw37169step1; decide +kernel
      have hl : raw37169step1Labels = labelEmbedding1 ∘ raw37169step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37169step1 raw37169step1Labels raw37169step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2669 node2669Labels := by rfl

def raw37170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw37170Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37170step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37170step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37170step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37170step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37170step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37170step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37170step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37170step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37170 raw37170Labels = mixedMoment B node2684 node2684Labels := by
  calc
    mixedMoment B raw37170 raw37170Labels = mixedMoment B raw37170step0 raw37170step0Labels := by
      have hz : ∀ j, raw37170 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw37170step0 = (fun i j => raw37170 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw37170step0 raw37170; decide +kernel
      have hl : raw37170step0Labels = raw37170Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37170 raw37170Labels permutation590 hz
    mixedMoment B raw37170step0 raw37170step0Labels = mixedMoment B raw37170step1 raw37170step1Labels := by
      have ha : raw37170step1 = (fun i j => raw37170step0 (permutation59 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37170step1 raw37170step0; decide +kernel
      have hl : raw37170step1Labels = raw37170step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37170step0 raw37170step0Labels permutation59 permutation7
    mixedMoment B raw37170step1 raw37170step1Labels = mixedMoment B raw37170step2 raw37170step2Labels := by
      have ha : raw37170step2 = -raw37170step1 := by apply Matrix.ext; change ∀ i j, raw37170step2 i j = -(raw37170step1 i j); unfold raw37170step2 raw37170step1; decide +kernel
      have hl : raw37170step2Labels = raw37170step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37170step2 raw37170step2Labels = mixedMoment B raw37170step3 raw37170step3Labels := by
      have ha : raw37170step3 = raw37170step2 := by apply Matrix.ext; unfold raw37170step3 raw37170step2; decide +kernel
      have hl : raw37170step2Labels = labelEmbedding1 ∘ raw37170step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37170step2 raw37170step2Labels raw37170step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2684 node2684Labels := by rfl

def raw37171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37171Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37171step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2]]
def raw37171step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37171step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw37171step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37171step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw37171step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37171 raw37171Labels = mixedMoment B node2238 node2238Labels := by
  calc
    mixedMoment B raw37171 raw37171Labels = mixedMoment B raw37171step0 raw37171step0Labels := by
      have ha : raw37171step0 = (fun i j => raw37171 (permutation189 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37171step0 raw37171; decide +kernel
      have hl : raw37171step0Labels = raw37171Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37171 raw37171Labels permutation189 permutation5
    mixedMoment B raw37171step0 raw37171step0Labels = mixedMoment B raw37171step1 raw37171step1Labels := by
      have ha : raw37171step1 = -raw37171step0 := by apply Matrix.ext; change ∀ i j, raw37171step1 i j = -(raw37171step0 i j); unfold raw37171step1 raw37171step0; decide +kernel
      have hl : raw37171step1Labels = raw37171step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37171step1 raw37171step1Labels = mixedMoment B raw37171step2 raw37171step2Labels := by
      have ha : raw37171step2 = raw37171step1 := by apply Matrix.ext; unfold raw37171step2 raw37171step1; decide +kernel
      have hl : raw37171step1Labels = labelEmbedding1 ∘ raw37171step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37171step1 raw37171step1Labels raw37171step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2238 node2238Labels := by rfl

def raw37172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37172Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37172step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37172step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37172step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37172step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37172step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37172step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37172 raw37172Labels = mixedMoment B node2150 node2150Labels := by
  calc
    mixedMoment B raw37172 raw37172Labels = mixedMoment B raw37172step0 raw37172step0Labels := by
      have ha : raw37172step0 = (fun i j => raw37172 (permutation284 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37172step0 raw37172; decide +kernel
      have hl : raw37172step0Labels = raw37172Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37172 raw37172Labels permutation284 permutation7
    mixedMoment B raw37172step0 raw37172step0Labels = mixedMoment B raw37172step1 raw37172step1Labels := by
      have ha : raw37172step1 = -raw37172step0 := by apply Matrix.ext; change ∀ i j, raw37172step1 i j = -(raw37172step0 i j); unfold raw37172step1 raw37172step0; decide +kernel
      have hl : raw37172step1Labels = raw37172step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37172step1 raw37172step1Labels = mixedMoment B raw37172step2 raw37172step2Labels := by
      have ha : raw37172step2 = raw37172step1 := by apply Matrix.ext; unfold raw37172step2 raw37172step1; decide +kernel
      have hl : raw37172step1Labels = labelEmbedding1 ∘ raw37172step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37172step1 raw37172step1Labels raw37172step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2150 node2150Labels := by rfl

def raw37173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 1, -1], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw37173Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37173step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw37173step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37173step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37173step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37173step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37173step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37173 raw37173Labels = mixedMoment B node2669 node2669Labels := by
  calc
    mixedMoment B raw37173 raw37173Labels = mixedMoment B raw37173step0 raw37173step0Labels := by
      have ha : raw37173step0 = (fun i j => raw37173 (permutation284 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37173step0 raw37173; decide +kernel
      have hl : raw37173step0Labels = raw37173Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37173 raw37173Labels permutation284 permutation7
    mixedMoment B raw37173step0 raw37173step0Labels = mixedMoment B raw37173step1 raw37173step1Labels := by
      have ha : raw37173step1 = -raw37173step0 := by apply Matrix.ext; change ∀ i j, raw37173step1 i j = -(raw37173step0 i j); unfold raw37173step1 raw37173step0; decide +kernel
      have hl : raw37173step1Labels = raw37173step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37173step1 raw37173step1Labels = mixedMoment B raw37173step2 raw37173step2Labels := by
      have ha : raw37173step2 = raw37173step1 := by apply Matrix.ext; unfold raw37173step2 raw37173step1; decide +kernel
      have hl : raw37173step1Labels = labelEmbedding1 ∘ raw37173step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37173step1 raw37173step1Labels raw37173step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2669 node2669Labels := by rfl

def raw37174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw37174Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37174step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw37174step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37174step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37174step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37174step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37174step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37174 raw37174Labels = mixedMoment B node2669 node2669Labels := by
  calc
    mixedMoment B raw37174 raw37174Labels = mixedMoment B raw37174step0 raw37174step0Labels := by
      have ha : raw37174step0 = (fun i j => raw37174 (permutation287 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37174step0 raw37174; decide +kernel
      have hl : raw37174step0Labels = raw37174Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37174 raw37174Labels permutation287 permutation7
    mixedMoment B raw37174step0 raw37174step0Labels = mixedMoment B raw37174step1 raw37174step1Labels := by
      have ha : raw37174step1 = -raw37174step0 := by apply Matrix.ext; change ∀ i j, raw37174step1 i j = -(raw37174step0 i j); unfold raw37174step1 raw37174step0; decide +kernel
      have hl : raw37174step1Labels = raw37174step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37174step1 raw37174step1Labels = mixedMoment B raw37174step2 raw37174step2Labels := by
      have ha : raw37174step2 = raw37174step1 := by apply Matrix.ext; unfold raw37174step2 raw37174step1; decide +kernel
      have hl : raw37174step1Labels = labelEmbedding1 ∘ raw37174step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37174step1 raw37174step1Labels raw37174step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2669 node2669Labels := by rfl

def raw37175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw37175Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37175step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw37175step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37175step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37175step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37175step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37175step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37175step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37175step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37175 raw37175Labels = mixedMoment B node2684 node2684Labels := by
  calc
    mixedMoment B raw37175 raw37175Labels = mixedMoment B raw37175step0 raw37175step0Labels := by
      have hz : ∀ j, raw37175 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw37175step0 = (fun i j => raw37175 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw37175step0 raw37175; decide +kernel
      have hl : raw37175step0Labels = raw37175Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37175 raw37175Labels permutation590 hz
    mixedMoment B raw37175step0 raw37175step0Labels = mixedMoment B raw37175step1 raw37175step1Labels := by
      have ha : raw37175step1 = (fun i j => raw37175step0 (permutation57 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37175step1 raw37175step0; decide +kernel
      have hl : raw37175step1Labels = raw37175step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37175step0 raw37175step0Labels permutation57 permutation7
    mixedMoment B raw37175step1 raw37175step1Labels = mixedMoment B raw37175step2 raw37175step2Labels := by
      have ha : raw37175step2 = -raw37175step1 := by apply Matrix.ext; change ∀ i j, raw37175step2 i j = -(raw37175step1 i j); unfold raw37175step2 raw37175step1; decide +kernel
      have hl : raw37175step2Labels = raw37175step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37175step2 raw37175step2Labels = mixedMoment B raw37175step3 raw37175step3Labels := by
      have ha : raw37175step3 = raw37175step2 := by apply Matrix.ext; unfold raw37175step3 raw37175step2; decide +kernel
      have hl : raw37175step2Labels = labelEmbedding1 ∘ raw37175step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37175step2 raw37175step2Labels raw37175step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2684 node2684Labels := by rfl

def raw37176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw37176Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37176step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![-1, 0, 1], ![-1, -1, 2]]
def raw37176step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37176step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw37176step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37176step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 1, -2]]
def raw37176step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37176 raw37176Labels = mixedMoment B node2238 node2238Labels := by
  calc
    mixedMoment B raw37176 raw37176Labels = mixedMoment B raw37176step0 raw37176step0Labels := by
      have ha : raw37176step0 = (fun i j => raw37176 (permutation183 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37176step0 raw37176; decide +kernel
      have hl : raw37176step0Labels = raw37176Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37176 raw37176Labels permutation183 permutation5
    mixedMoment B raw37176step0 raw37176step0Labels = mixedMoment B raw37176step1 raw37176step1Labels := by
      have ha : raw37176step1 = -raw37176step0 := by apply Matrix.ext; change ∀ i j, raw37176step1 i j = -(raw37176step0 i j); unfold raw37176step1 raw37176step0; decide +kernel
      have hl : raw37176step1Labels = raw37176step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37176step1 raw37176step1Labels = mixedMoment B raw37176step2 raw37176step2Labels := by
      have ha : raw37176step2 = raw37176step1 := by apply Matrix.ext; unfold raw37176step2 raw37176step1; decide +kernel
      have hl : raw37176step1Labels = labelEmbedding1 ∘ raw37176step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37176step1 raw37176step1Labels raw37176step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2238 node2238Labels := by rfl

def raw37177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw37177Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37177step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37177step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37177step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37177step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37177step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37177step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37177 raw37177Labels = mixedMoment B node2150 node2150Labels := by
  calc
    mixedMoment B raw37177 raw37177Labels = mixedMoment B raw37177step0 raw37177step0Labels := by
      have ha : raw37177step0 = (fun i j => raw37177 (permutation283 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37177step0 raw37177; decide +kernel
      have hl : raw37177step0Labels = raw37177Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37177 raw37177Labels permutation283 permutation7
    mixedMoment B raw37177step0 raw37177step0Labels = mixedMoment B raw37177step1 raw37177step1Labels := by
      have ha : raw37177step1 = -raw37177step0 := by apply Matrix.ext; change ∀ i j, raw37177step1 i j = -(raw37177step0 i j); unfold raw37177step1 raw37177step0; decide +kernel
      have hl : raw37177step1Labels = raw37177step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37177step1 raw37177step1Labels = mixedMoment B raw37177step2 raw37177step2Labels := by
      have ha : raw37177step2 = raw37177step1 := by apply Matrix.ext; unfold raw37177step2 raw37177step1; decide +kernel
      have hl : raw37177step1Labels = labelEmbedding1 ∘ raw37177step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37177step1 raw37177step1Labels raw37177step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2150 node2150Labels := by rfl

def raw37178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw37178Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37178step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw37178step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37178step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37178step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37178step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37178step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37178 raw37178Labels = mixedMoment B node2669 node2669Labels := by
  calc
    mixedMoment B raw37178 raw37178Labels = mixedMoment B raw37178step0 raw37178step0Labels := by
      have ha : raw37178step0 = (fun i j => raw37178 (permutation283 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37178step0 raw37178; decide +kernel
      have hl : raw37178step0Labels = raw37178Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37178 raw37178Labels permutation283 permutation7
    mixedMoment B raw37178step0 raw37178step0Labels = mixedMoment B raw37178step1 raw37178step1Labels := by
      have ha : raw37178step1 = -raw37178step0 := by apply Matrix.ext; change ∀ i j, raw37178step1 i j = -(raw37178step0 i j); unfold raw37178step1 raw37178step0; decide +kernel
      have hl : raw37178step1Labels = raw37178step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37178step1 raw37178step1Labels = mixedMoment B raw37178step2 raw37178step2Labels := by
      have ha : raw37178step2 = raw37178step1 := by apply Matrix.ext; unfold raw37178step2 raw37178step1; decide +kernel
      have hl : raw37178step1Labels = labelEmbedding1 ∘ raw37178step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37178step1 raw37178step1Labels raw37178step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2669 node2669Labels := by rfl

def raw37179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw37179Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37179step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw37179step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37179step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37179step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37179step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37179step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37179 raw37179Labels = mixedMoment B node2669 node2669Labels := by
  calc
    mixedMoment B raw37179 raw37179Labels = mixedMoment B raw37179step0 raw37179step0Labels := by
      have ha : raw37179step0 = (fun i j => raw37179 (permutation285 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37179step0 raw37179; decide +kernel
      have hl : raw37179step0Labels = raw37179Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37179 raw37179Labels permutation285 permutation7
    mixedMoment B raw37179step0 raw37179step0Labels = mixedMoment B raw37179step1 raw37179step1Labels := by
      have ha : raw37179step1 = -raw37179step0 := by apply Matrix.ext; change ∀ i j, raw37179step1 i j = -(raw37179step0 i j); unfold raw37179step1 raw37179step0; decide +kernel
      have hl : raw37179step1Labels = raw37179step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37179step1 raw37179step1Labels = mixedMoment B raw37179step2 raw37179step2Labels := by
      have ha : raw37179step2 = raw37179step1 := by apply Matrix.ext; unfold raw37179step2 raw37179step1; decide +kernel
      have hl : raw37179step1Labels = labelEmbedding1 ∘ raw37179step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37179step1 raw37179step1Labels raw37179step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2669 node2669Labels := by rfl

def raw37180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw37180Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37180step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37180step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37180step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw37180step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37180step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37180step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37180step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw37180step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37180 raw37180Labels = mixedMoment B node2684 node2684Labels := by
  calc
    mixedMoment B raw37180 raw37180Labels = mixedMoment B raw37180step0 raw37180step0Labels := by
      have hz : ∀ j, raw37180 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw37180step0 = (fun i j => raw37180 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw37180step0 raw37180; decide +kernel
      have hl : raw37180step0Labels = raw37180Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37180 raw37180Labels permutation590 hz
    mixedMoment B raw37180step0 raw37180step0Labels = mixedMoment B raw37180step1 raw37180step1Labels := by
      have ha : raw37180step1 = (fun i j => raw37180step0 (permutation56 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37180step1 raw37180step0; decide +kernel
      have hl : raw37180step1Labels = raw37180step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37180step0 raw37180step0Labels permutation56 permutation7
    mixedMoment B raw37180step1 raw37180step1Labels = mixedMoment B raw37180step2 raw37180step2Labels := by
      have ha : raw37180step2 = -raw37180step1 := by apply Matrix.ext; change ∀ i j, raw37180step2 i j = -(raw37180step1 i j); unfold raw37180step2 raw37180step1; decide +kernel
      have hl : raw37180step2Labels = raw37180step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37180step2 raw37180step2Labels = mixedMoment B raw37180step3 raw37180step3Labels := by
      have ha : raw37180step3 = raw37180step2 := by apply Matrix.ext; unfold raw37180step3 raw37180step2; decide +kernel
      have hl : raw37180step2Labels = labelEmbedding1 ∘ raw37180step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37180step2 raw37180step2Labels raw37180step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2684 node2684Labels := by rfl

def raw37181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37181Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37181step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 3, -2], ![-2, 0, 2]]
def raw37181step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37181step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw37181step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37181step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -3, 2], ![2, 0, -2]]
def raw37181step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37181 raw37181Labels = mixedMoment B node2231 node2231Labels := by
  calc
    mixedMoment B raw37181 raw37181Labels = mixedMoment B raw37181step0 raw37181step0Labels := by
      have ha : raw37181step0 = (fun i j => raw37181 (permutation184 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37181step0 raw37181; decide +kernel
      have hl : raw37181step0Labels = raw37181Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37181 raw37181Labels permutation184 permutation5
    mixedMoment B raw37181step0 raw37181step0Labels = mixedMoment B raw37181step1 raw37181step1Labels := by
      have ha : raw37181step1 = -raw37181step0 := by apply Matrix.ext; change ∀ i j, raw37181step1 i j = -(raw37181step0 i j); unfold raw37181step1 raw37181step0; decide +kernel
      have hl : raw37181step1Labels = raw37181step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37181step1 raw37181step1Labels = mixedMoment B raw37181step2 raw37181step2Labels := by
      have ha : raw37181step2 = raw37181step1 := by apply Matrix.ext; unfold raw37181step2 raw37181step1; decide +kernel
      have hl : raw37181step1Labels = labelEmbedding1 ∘ raw37181step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37181step1 raw37181step1Labels raw37181step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2231 node2231Labels := by rfl

def raw37182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 0, 3], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37182Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37182step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -2, 2], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw37182step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37182step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37182step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37182step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37182step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37182 raw37182Labels = mixedMoment B node2156 node2156Labels := by
  calc
    mixedMoment B raw37182 raw37182Labels = mixedMoment B raw37182step0 raw37182step0Labels := by
      have ha : raw37182step0 = (fun i j => raw37182 (permutation283 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37182step0 raw37182; decide +kernel
      have hl : raw37182step0Labels = raw37182Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37182 raw37182Labels permutation283 permutation7
    mixedMoment B raw37182step0 raw37182step0Labels = mixedMoment B raw37182step1 raw37182step1Labels := by
      have ha : raw37182step1 = -raw37182step0 := by apply Matrix.ext; change ∀ i j, raw37182step1 i j = -(raw37182step0 i j); unfold raw37182step1 raw37182step0; decide +kernel
      have hl : raw37182step1Labels = raw37182step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37182step1 raw37182step1Labels = mixedMoment B raw37182step2 raw37182step2Labels := by
      have ha : raw37182step2 = raw37182step1 := by apply Matrix.ext; unfold raw37182step2 raw37182step1; decide +kernel
      have hl : raw37182step1Labels = labelEmbedding1 ∘ raw37182step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37182step1 raw37182step1Labels raw37182step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2156 node2156Labels := by rfl

def raw37183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37183Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37183step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37183step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37183step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37183step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37183step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37183step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37183 raw37183Labels = mixedMoment B node2676 node2676Labels := by
  calc
    mixedMoment B raw37183 raw37183Labels = mixedMoment B raw37183step0 raw37183step0Labels := by
      have ha : raw37183step0 = (fun i j => raw37183 (permutation283 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37183step0 raw37183; decide +kernel
      have hl : raw37183step0Labels = raw37183Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37183 raw37183Labels permutation283 permutation7
    mixedMoment B raw37183step0 raw37183step0Labels = mixedMoment B raw37183step1 raw37183step1Labels := by
      have ha : raw37183step1 = -raw37183step0 := by apply Matrix.ext; change ∀ i j, raw37183step1 i j = -(raw37183step0 i j); unfold raw37183step1 raw37183step0; decide +kernel
      have hl : raw37183step1Labels = raw37183step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37183step1 raw37183step1Labels = mixedMoment B raw37183step2 raw37183step2Labels := by
      have ha : raw37183step2 = raw37183step1 := by apply Matrix.ext; unfold raw37183step2 raw37183step1; decide +kernel
      have hl : raw37183step1Labels = labelEmbedding1 ∘ raw37183step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37183step1 raw37183step1Labels raw37183step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2676 node2676Labels := by rfl

def raw37184 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw37184Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37184step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37184step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37184step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37184step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37184step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37184step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37184 raw37184Labels = mixedMoment B node2676 node2676Labels := by
  calc
    mixedMoment B raw37184 raw37184Labels = mixedMoment B raw37184step0 raw37184step0Labels := by
      have ha : raw37184step0 = (fun i j => raw37184 (permutation285 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37184step0 raw37184; decide +kernel
      have hl : raw37184step0Labels = raw37184Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37184 raw37184Labels permutation285 permutation7
    mixedMoment B raw37184step0 raw37184step0Labels = mixedMoment B raw37184step1 raw37184step1Labels := by
      have ha : raw37184step1 = -raw37184step0 := by apply Matrix.ext; change ∀ i j, raw37184step1 i j = -(raw37184step0 i j); unfold raw37184step1 raw37184step0; decide +kernel
      have hl : raw37184step1Labels = raw37184step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37184step1 raw37184step1Labels = mixedMoment B raw37184step2 raw37184step2Labels := by
      have ha : raw37184step2 = raw37184step1 := by apply Matrix.ext; unfold raw37184step2 raw37184step1; decide +kernel
      have hl : raw37184step1Labels = labelEmbedding1 ∘ raw37184step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37184step1 raw37184step1Labels raw37184step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2676 node2676Labels := by rfl

def raw37185 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, -1, 3], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw37185Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw37185step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, -1, -2], ![0, 2, -2], ![0, -2, 2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw37185step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37185step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37185step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw37185step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37185step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical37185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37185 raw37185Labels = mixedMoment B node2676 node2676Labels := by
  calc
    mixedMoment B raw37185 raw37185Labels = mixedMoment B raw37185step0 raw37185step0Labels := by
      have ha : raw37185step0 = (fun i j => raw37185 (permutation287 i) (permutation7 j)) := by apply Matrix.ext; unfold raw37185step0 raw37185; decide +kernel
      have hl : raw37185step0Labels = raw37185Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37185 raw37185Labels permutation287 permutation7
    mixedMoment B raw37185step0 raw37185step0Labels = mixedMoment B raw37185step1 raw37185step1Labels := by
      have ha : raw37185step1 = -raw37185step0 := by apply Matrix.ext; change ∀ i j, raw37185step1 i j = -(raw37185step0 i j); unfold raw37185step1 raw37185step0; decide +kernel
      have hl : raw37185step1Labels = raw37185step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37185step1 raw37185step1Labels = mixedMoment B raw37185step2 raw37185step2Labels := by
      have ha : raw37185step2 = raw37185step1 := by apply Matrix.ext; unfold raw37185step2 raw37185step1; decide +kernel
      have hl : raw37185step1Labels = labelEmbedding1 ∘ raw37185step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37185step1 raw37185step1Labels raw37185step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2676 node2676Labels := by rfl

def raw37186 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw37186Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37186step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37186step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37186step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw37186step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37186 raw37186Labels = mixedMoment B node5162 node5162Labels := by
  calc
    mixedMoment B raw37186 raw37186Labels = mixedMoment B raw37186step0 raw37186step0Labels := by
      have ha : raw37186step0 = (fun i j => raw37186 (permutation283 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37186step0 raw37186; decide +kernel
      have hl : raw37186step0Labels = raw37186Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37186 raw37186Labels permutation283 permutation3
    mixedMoment B raw37186step0 raw37186step0Labels = mixedMoment B raw37186step1 raw37186step1Labels := by
      have ha : raw37186step1 = raw37186step0 := by apply Matrix.ext; unfold raw37186step1 raw37186step0; decide +kernel
      have hl : raw37186step0Labels = labelEmbedding6 ∘ raw37186step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37186step0 raw37186step0Labels raw37186step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5162 node5162Labels := by rfl

def raw37187 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw37187Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37187step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw37187step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37187step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw37187step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37187 raw37187Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw37187 raw37187Labels = mixedMoment B raw37187step0 raw37187step0Labels := by
      have hz : ∀ j, raw37187 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37187step0 = (fun i j => raw37187 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37187step0 raw37187; decide +kernel
      have hl : raw37187step0Labels = raw37187Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37187 raw37187Labels permutation434 hz
    mixedMoment B raw37187step0 raw37187step0Labels = mixedMoment B raw37187step1 raw37187step1Labels := by
      have ha : raw37187step1 = (fun i j => raw37187step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37187step1 raw37187step0; decide +kernel
      have hl : raw37187step1Labels = raw37187step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37187step0 raw37187step0Labels permutation56 permutation2
    _ = mixedMoment B node5485 node5485Labels := by rfl

def raw37188 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw37188Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw37188step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37188step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw37188step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37188 raw37188Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw37188 raw37188Labels = mixedMoment B raw37188step0 raw37188step0Labels := by
      have hz : ∀ j, raw37188 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37188step0 = (fun i j => raw37188 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37188step0 raw37188; decide +kernel
      have hl : raw37188step0Labels = raw37188Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37188 raw37188Labels permutation520 hz
    mixedMoment B raw37188step0 raw37188step0Labels = mixedMoment B raw37188step1 raw37188step1Labels := by
      have ha : raw37188step1 = (fun i j => raw37188step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37188step1 raw37188step0; decide +kernel
      have hl : raw37188step1Labels = raw37188step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37188step0 raw37188step0Labels permutation56 permutation2
    _ = mixedMoment B node5485 node5485Labels := by rfl

def raw37189 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw37189Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37189step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw37189step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw37189step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw37189step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw37189step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw37189step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37189 raw37189Labels = mixedMoment B node5447 node5447Labels := by
  calc
    mixedMoment B raw37189 raw37189Labels = mixedMoment B raw37189step0 raw37189step0Labels := by
      have ha : raw37189step0 = (fun i j => raw37189 (permutation602 i) (permutation4 j)) := by apply Matrix.ext; unfold raw37189step0 raw37189; decide +kernel
      have hl : raw37189step0Labels = raw37189Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37189 raw37189Labels permutation602 permutation4
    mixedMoment B raw37189step0 raw37189step0Labels = mixedMoment B raw37189step1 raw37189step1Labels := by
      have ha : raw37189step1 = -raw37189step0 := by apply Matrix.ext; change ∀ i j, raw37189step1 i j = -(raw37189step0 i j); unfold raw37189step1 raw37189step0; decide +kernel
      have hl : raw37189step1Labels = raw37189step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37189step1 raw37189step1Labels = mixedMoment B raw37189step2 raw37189step2Labels := by
      have ha : raw37189step2 = raw37189step1 := by apply Matrix.ext; unfold raw37189step2 raw37189step1; decide +kernel
      have hl : raw37189step1Labels = labelEmbedding7 ∘ raw37189step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37189step1 raw37189step1Labels raw37189step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5447 node5447Labels := by rfl

def raw37190 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw37190Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37190step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37190step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37190step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37190step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37190 raw37190Labels = mixedMoment B node4936 node4936Labels := by
  calc
    mixedMoment B raw37190 raw37190Labels = mixedMoment B raw37190step0 raw37190step0Labels := by
      have ha : raw37190step0 = (fun i j => raw37190 (permutation286 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37190step0 raw37190; decide +kernel
      have hl : raw37190step0Labels = raw37190Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37190 raw37190Labels permutation286 permutation3
    mixedMoment B raw37190step0 raw37190step0Labels = mixedMoment B raw37190step1 raw37190step1Labels := by
      have ha : raw37190step1 = raw37190step0 := by apply Matrix.ext; unfold raw37190step1 raw37190step0; decide +kernel
      have hl : raw37190step0Labels = labelEmbedding6 ∘ raw37190step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37190step0 raw37190step0Labels raw37190step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4936 node4936Labels := by rfl

def raw37191 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2]]
def raw37191Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37191step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw37191step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37191step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw37191step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37191step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw37191step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37191step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw37191step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37191 raw37191Labels = mixedMoment B node5404 node5404Labels := by
  calc
    mixedMoment B raw37191 raw37191Labels = mixedMoment B raw37191step0 raw37191step0Labels := by
      have hz : ∀ j, raw37191 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37191step0 = (fun i j => raw37191 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37191step0 raw37191; decide +kernel
      have hl : raw37191step0Labels = raw37191Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37191 raw37191Labels permutation434 hz
    mixedMoment B raw37191step0 raw37191step0Labels = mixedMoment B raw37191step1 raw37191step1Labels := by
      have ha : raw37191step1 = (fun i j => raw37191step0 (permutation96 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37191step1 raw37191step0; decide +kernel
      have hl : raw37191step1Labels = raw37191step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37191step0 raw37191step0Labels permutation96 permutation3
    mixedMoment B raw37191step1 raw37191step1Labels = mixedMoment B raw37191step2 raw37191step2Labels := by
      have ha : raw37191step2 = -raw37191step1 := by apply Matrix.ext; change ∀ i j, raw37191step2 i j = -(raw37191step1 i j); unfold raw37191step2 raw37191step1; decide +kernel
      have hl : raw37191step2Labels = raw37191step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37191step2 raw37191step2Labels = mixedMoment B raw37191step3 raw37191step3Labels := by
      have ha : raw37191step3 = raw37191step2 := by apply Matrix.ext; unfold raw37191step3 raw37191step2; decide +kernel
      have hl : raw37191step2Labels = labelEmbedding6 ∘ raw37191step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37191step2 raw37191step2Labels raw37191step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5404 node5404Labels := by rfl

def raw37192 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![1, 1, -2]]
def raw37192Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37192step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw37192step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37192step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw37192step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37192step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw37192step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37192step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw37192step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37192 raw37192Labels = mixedMoment B node5404 node5404Labels := by
  calc
    mixedMoment B raw37192 raw37192Labels = mixedMoment B raw37192step0 raw37192step0Labels := by
      have hz : ∀ j, raw37192 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37192step0 = (fun i j => raw37192 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37192step0 raw37192; decide +kernel
      have hl : raw37192step0Labels = raw37192Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37192 raw37192Labels permutation520 hz
    mixedMoment B raw37192step0 raw37192step0Labels = mixedMoment B raw37192step1 raw37192step1Labels := by
      have ha : raw37192step1 = (fun i j => raw37192step0 (permutation96 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37192step1 raw37192step0; decide +kernel
      have hl : raw37192step1Labels = raw37192step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37192step0 raw37192step0Labels permutation96 permutation3
    mixedMoment B raw37192step1 raw37192step1Labels = mixedMoment B raw37192step2 raw37192step2Labels := by
      have ha : raw37192step2 = -raw37192step1 := by apply Matrix.ext; change ∀ i j, raw37192step2 i j = -(raw37192step1 i j); unfold raw37192step2 raw37192step1; decide +kernel
      have hl : raw37192step2Labels = raw37192step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37192step2 raw37192step2Labels = mixedMoment B raw37192step3 raw37192step3Labels := by
      have ha : raw37192step3 = raw37192step2 := by apply Matrix.ext; unfold raw37192step3 raw37192step2; decide +kernel
      have hl : raw37192step2Labels = labelEmbedding6 ∘ raw37192step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37192step2 raw37192step2Labels raw37192step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5404 node5404Labels := by rfl

def raw37193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2]]
def raw37193Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37193step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, 0, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw37193step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37193step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw37193step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37193step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw37193step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37193 raw37193Labels = mixedMoment B node5391 node5391Labels := by
  calc
    mixedMoment B raw37193 raw37193Labels = mixedMoment B raw37193step0 raw37193step0Labels := by
      have ha : raw37193step0 = (fun i j => raw37193 (permutation393 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37193step0 raw37193; decide +kernel
      have hl : raw37193step0Labels = raw37193Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37193 raw37193Labels permutation393 permutation3
    mixedMoment B raw37193step0 raw37193step0Labels = mixedMoment B raw37193step1 raw37193step1Labels := by
      have ha : raw37193step1 = -raw37193step0 := by apply Matrix.ext; change ∀ i j, raw37193step1 i j = -(raw37193step0 i j); unfold raw37193step1 raw37193step0; decide +kernel
      have hl : raw37193step1Labels = raw37193step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37193step1 raw37193step1Labels = mixedMoment B raw37193step2 raw37193step2Labels := by
      have ha : raw37193step2 = raw37193step1 := by apply Matrix.ext; unfold raw37193step2 raw37193step1; decide +kernel
      have hl : raw37193step1Labels = labelEmbedding6 ∘ raw37193step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37193step1 raw37193step1Labels raw37193step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5391 node5391Labels := by rfl

def raw37194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![1, 1, -2]]
def raw37194Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37194step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37194step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37194step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37194step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37194 raw37194Labels = mixedMoment B node4936 node4936Labels := by
  calc
    mixedMoment B raw37194 raw37194Labels = mixedMoment B raw37194step0 raw37194step0Labels := by
      have ha : raw37194step0 = (fun i j => raw37194 (permutation284 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37194step0 raw37194; decide +kernel
      have hl : raw37194step0Labels = raw37194Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37194 raw37194Labels permutation284 permutation3
    mixedMoment B raw37194step0 raw37194step0Labels = mixedMoment B raw37194step1 raw37194step1Labels := by
      have ha : raw37194step1 = raw37194step0 := by apply Matrix.ext; unfold raw37194step1 raw37194step0; decide +kernel
      have hl : raw37194step0Labels = labelEmbedding6 ∘ raw37194step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37194step0 raw37194step0Labels raw37194step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4936 node4936Labels := by rfl

def raw37195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![1, 1, -2]]
def raw37195Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw37195step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37195step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw37195step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37195step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw37195step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37195step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw37195step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37195 raw37195Labels = mixedMoment B node5404 node5404Labels := by
  calc
    mixedMoment B raw37195 raw37195Labels = mixedMoment B raw37195step0 raw37195step0Labels := by
      have hz : ∀ j, raw37195 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37195step0 = (fun i j => raw37195 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37195step0 raw37195; decide +kernel
      have hl : raw37195step0Labels = raw37195Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37195 raw37195Labels permutation520 hz
    mixedMoment B raw37195step0 raw37195step0Labels = mixedMoment B raw37195step1 raw37195step1Labels := by
      have ha : raw37195step1 = (fun i j => raw37195step0 (permutation120 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37195step1 raw37195step0; decide +kernel
      have hl : raw37195step1Labels = raw37195step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37195step0 raw37195step0Labels permutation120 permutation3
    mixedMoment B raw37195step1 raw37195step1Labels = mixedMoment B raw37195step2 raw37195step2Labels := by
      have ha : raw37195step2 = -raw37195step1 := by apply Matrix.ext; change ∀ i j, raw37195step2 i j = -(raw37195step1 i j); unfold raw37195step2 raw37195step1; decide +kernel
      have hl : raw37195step2Labels = raw37195step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37195step2 raw37195step2Labels = mixedMoment B raw37195step3 raw37195step3Labels := by
      have ha : raw37195step3 = raw37195step2 := by apply Matrix.ext; unfold raw37195step3 raw37195step2; decide +kernel
      have hl : raw37195step2Labels = labelEmbedding6 ∘ raw37195step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37195step2 raw37195step2Labels raw37195step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5404 node5404Labels := by rfl

def raw37196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![0, 2, -2]]
def raw37196Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37196step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, 0, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw37196step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37196step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw37196step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37196step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw37196step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37196 raw37196Labels = mixedMoment B node5391 node5391Labels := by
  calc
    mixedMoment B raw37196 raw37196Labels = mixedMoment B raw37196step0 raw37196step0Labels := by
      have ha : raw37196step0 = (fun i j => raw37196 (permutation479 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37196step0 raw37196; decide +kernel
      have hl : raw37196step0Labels = raw37196Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37196 raw37196Labels permutation479 permutation3
    mixedMoment B raw37196step0 raw37196step0Labels = mixedMoment B raw37196step1 raw37196step1Labels := by
      have ha : raw37196step1 = -raw37196step0 := by apply Matrix.ext; change ∀ i j, raw37196step1 i j = -(raw37196step0 i j); unfold raw37196step1 raw37196step0; decide +kernel
      have hl : raw37196step1Labels = raw37196step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37196step1 raw37196step1Labels = mixedMoment B raw37196step2 raw37196step2Labels := by
      have ha : raw37196step2 = raw37196step1 := by apply Matrix.ext; unfold raw37196step2 raw37196step1; decide +kernel
      have hl : raw37196step1Labels = labelEmbedding6 ∘ raw37196step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37196step1 raw37196step1Labels raw37196step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5391 node5391Labels := by rfl

def raw37197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw37197Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37197step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37197step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37197step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw37197step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37197 raw37197Labels = mixedMoment B node4936 node4936Labels := by
  calc
    mixedMoment B raw37197 raw37197Labels = mixedMoment B raw37197step0 raw37197step0Labels := by
      have ha : raw37197step0 = (fun i j => raw37197 (permutation283 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37197step0 raw37197; decide +kernel
      have hl : raw37197step0Labels = raw37197Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37197 raw37197Labels permutation283 permutation3
    mixedMoment B raw37197step0 raw37197step0Labels = mixedMoment B raw37197step1 raw37197step1Labels := by
      have ha : raw37197step1 = raw37197step0 := by apply Matrix.ext; unfold raw37197step1 raw37197step0; decide +kernel
      have hl : raw37197step0Labels = labelEmbedding6 ∘ raw37197step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37197step0 raw37197step0Labels raw37197step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4936 node4936Labels := by rfl

def raw37198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2]]
def raw37198Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![1, 1, -2]]
def raw37198step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37198step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw37198step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37198step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw37198step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37198step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw37198step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37198 raw37198Labels = mixedMoment B node5404 node5404Labels := by
  calc
    mixedMoment B raw37198 raw37198Labels = mixedMoment B raw37198step0 raw37198step0Labels := by
      have hz : ∀ j, raw37198 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37198step0 = (fun i j => raw37198 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37198step0 raw37198; decide +kernel
      have hl : raw37198step0Labels = raw37198Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37198 raw37198Labels permutation434 hz
    mixedMoment B raw37198step0 raw37198step0Labels = mixedMoment B raw37198step1 raw37198step1Labels := by
      have ha : raw37198step1 = (fun i j => raw37198step0 (permutation120 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37198step1 raw37198step0; decide +kernel
      have hl : raw37198step1Labels = raw37198step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37198step0 raw37198step0Labels permutation120 permutation3
    mixedMoment B raw37198step1 raw37198step1Labels = mixedMoment B raw37198step2 raw37198step2Labels := by
      have ha : raw37198step2 = -raw37198step1 := by apply Matrix.ext; change ∀ i j, raw37198step2 i j = -(raw37198step1 i j); unfold raw37198step2 raw37198step1; decide +kernel
      have hl : raw37198step2Labels = raw37198step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37198step2 raw37198step2Labels = mixedMoment B raw37198step3 raw37198step3Labels := by
      have ha : raw37198step3 = raw37198step2 := by apply Matrix.ext; unfold raw37198step3 raw37198step2; decide +kernel
      have hl : raw37198step2Labels = labelEmbedding6 ∘ raw37198step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37198step2 raw37198step2Labels raw37198step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5404 node5404Labels := by rfl

def raw37199 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![0, 2, -2]]
def raw37199Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37199step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, 0, -1], ![0, -2, 2], ![-2, 1, 1], ![-2, 1, 1]]
def raw37199step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37199step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw37199step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37199step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 0, 1], ![0, 2, -2], ![2, -1, -1], ![2, -1, -1]]
def raw37199step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37199 raw37199Labels = mixedMoment B node5391 node5391Labels := by
  calc
    mixedMoment B raw37199 raw37199Labels = mixedMoment B raw37199step0 raw37199step0Labels := by
      have ha : raw37199step0 = (fun i j => raw37199 (permutation545 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37199step0 raw37199; decide +kernel
      have hl : raw37199step0Labels = raw37199Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37199 raw37199Labels permutation545 permutation3
    mixedMoment B raw37199step0 raw37199step0Labels = mixedMoment B raw37199step1 raw37199step1Labels := by
      have ha : raw37199step1 = -raw37199step0 := by apply Matrix.ext; change ∀ i j, raw37199step1 i j = -(raw37199step0 i j); unfold raw37199step1 raw37199step0; decide +kernel
      have hl : raw37199step1Labels = raw37199step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37199step1 raw37199step1Labels = mixedMoment B raw37199step2 raw37199step2Labels := by
      have ha : raw37199step2 = raw37199step1 := by apply Matrix.ext; unfold raw37199step2 raw37199step1; decide +kernel
      have hl : raw37199step1Labels = labelEmbedding6 ∘ raw37199step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37199step1 raw37199step1Labels raw37199step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5391 node5391Labels := by rfl

def raw37200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 2, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37200Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37200step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37200step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37200step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37200step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37200 raw37200Labels = mixedMoment B node5167 node5167Labels := by
  calc
    mixedMoment B raw37200 raw37200Labels = mixedMoment B raw37200step0 raw37200step0Labels := by
      have ha : raw37200step0 = (fun i j => raw37200 (permutation281 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37200step0 raw37200; decide +kernel
      have hl : raw37200step0Labels = raw37200Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37200 raw37200Labels permutation281 permutation3
    mixedMoment B raw37200step0 raw37200step0Labels = mixedMoment B raw37200step1 raw37200step1Labels := by
      have ha : raw37200step1 = raw37200step0 := by apply Matrix.ext; unfold raw37200step1 raw37200step0; decide +kernel
      have hl : raw37200step0Labels = labelEmbedding6 ∘ raw37200step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37200step0 raw37200step0Labels raw37200step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5167 node5167Labels := by rfl

def raw37201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, -1, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37201Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37201step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37201step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37201step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37201step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37201 raw37201Labels = mixedMoment B node5486 node5486Labels := by
  calc
    mixedMoment B raw37201 raw37201Labels = mixedMoment B raw37201step0 raw37201step0Labels := by
      have hz : ∀ j, raw37201 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37201step0 = (fun i j => raw37201 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37201step0 raw37201; decide +kernel
      have hl : raw37201step0Labels = raw37201Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37201 raw37201Labels permutation434 hz
    mixedMoment B raw37201step0 raw37201step0Labels = mixedMoment B raw37201step1 raw37201step1Labels := by
      have ha : raw37201step1 = (fun i j => raw37201step0 (permutation56 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37201step1 raw37201step0; decide +kernel
      have hl : raw37201step1Labels = raw37201step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37201step0 raw37201step0Labels permutation56 permutation2
    _ = mixedMoment B node5486 node5486Labels := by rfl

def raw37202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw37202Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37202step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37202step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37202 raw37202Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw37202 raw37202Labels = mixedMoment B raw37202step0 raw37202step0Labels := by
      have ha : raw37202step0 = (fun i j => raw37202 (permutation277 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37202step0 raw37202; decide +kernel
      have hl : raw37202step0Labels = raw37202Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37202 raw37202Labels permutation277 permutation2
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw37203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw37203Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37203step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37203step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37203 raw37203Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw37203 raw37203Labels = mixedMoment B raw37203step0 raw37203step0Labels := by
      have ha : raw37203step0 = (fun i j => raw37203 (permutation283 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37203step0 raw37203; decide +kernel
      have hl : raw37203step0Labels = raw37203Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37203 raw37203Labels permutation283 permutation2
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw37204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw37204Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37204step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37204step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37204 raw37204Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw37204 raw37204Labels = mixedMoment B raw37204step0 raw37204step0Labels := by
      have ha : raw37204step0 = (fun i j => raw37204 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37204step0 raw37204; decide +kernel
      have hl : raw37204step0Labels = raw37204Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37204 raw37204Labels permutation164 permutation2
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw37205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw37205Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37205step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw37205step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37205 raw37205Labels = mixedMoment B node5482 node5482Labels := by
  calc
    mixedMoment B raw37205 raw37205Labels = mixedMoment B raw37205step0 raw37205step0Labels := by
      have ha : raw37205step0 = (fun i j => raw37205 (permutation170 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37205step0 raw37205; decide +kernel
      have hl : raw37205step0Labels = raw37205Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37205 raw37205Labels permutation170 permutation2
    _ = mixedMoment B node5482 node5482Labels := by rfl

def raw37206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37206Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37206step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37206step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37206step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37206step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37206 raw37206Labels = mixedMoment B node4939 node4939Labels := by
  calc
    mixedMoment B raw37206 raw37206Labels = mixedMoment B raw37206step0 raw37206step0Labels := by
      have ha : raw37206step0 = (fun i j => raw37206 (permutation169 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37206step0 raw37206; decide +kernel
      have hl : raw37206step0Labels = raw37206Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37206 raw37206Labels permutation169 permutation3
    mixedMoment B raw37206step0 raw37206step0Labels = mixedMoment B raw37206step1 raw37206step1Labels := by
      have ha : raw37206step1 = raw37206step0 := by apply Matrix.ext; unfold raw37206step1 raw37206step0; decide +kernel
      have hl : raw37206step0Labels = labelEmbedding6 ∘ raw37206step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37206step0 raw37206step0Labels raw37206step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4939 node4939Labels := by rfl

def raw37207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37207Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37207step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37207step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37207step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37207step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37207 raw37207Labels = mixedMoment B node4939 node4939Labels := by
  calc
    mixedMoment B raw37207 raw37207Labels = mixedMoment B raw37207step0 raw37207step0Labels := by
      have ha : raw37207step0 = (fun i j => raw37207 (permutation282 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37207step0 raw37207; decide +kernel
      have hl : raw37207step0Labels = raw37207Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37207 raw37207Labels permutation282 permutation3
    mixedMoment B raw37207step0 raw37207step0Labels = mixedMoment B raw37207step1 raw37207step1Labels := by
      have ha : raw37207step1 = raw37207step0 := by apply Matrix.ext; unfold raw37207step1 raw37207step0; decide +kernel
      have hl : raw37207step0Labels = labelEmbedding6 ∘ raw37207step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37207step0 raw37207step0Labels raw37207step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4939 node4939Labels := by rfl

def raw37208 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -2, 0], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37208Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37208step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37208step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![1, -1, 0], ![-2, 1, 1], ![-2, 1, 1]]
def raw37208step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37208step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw37208step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37208step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![2, -1, -1]]
def raw37208step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37208 raw37208Labels = mixedMoment B node5418 node5418Labels := by
  calc
    mixedMoment B raw37208 raw37208Labels = mixedMoment B raw37208step0 raw37208step0Labels := by
      have hz : ∀ j, raw37208 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37208step0 = (fun i j => raw37208 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37208step0 raw37208; decide +kernel
      have hl : raw37208step0Labels = raw37208Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37208 raw37208Labels permutation434 hz
    mixedMoment B raw37208step0 raw37208step0Labels = mixedMoment B raw37208step1 raw37208step1Labels := by
      have ha : raw37208step1 = (fun i j => raw37208step0 (permutation96 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37208step1 raw37208step0; decide +kernel
      have hl : raw37208step1Labels = raw37208step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37208step0 raw37208step0Labels permutation96 permutation3
    mixedMoment B raw37208step1 raw37208step1Labels = mixedMoment B raw37208step2 raw37208step2Labels := by
      have ha : raw37208step2 = -raw37208step1 := by apply Matrix.ext; change ∀ i j, raw37208step2 i j = -(raw37208step1 i j); unfold raw37208step2 raw37208step1; decide +kernel
      have hl : raw37208step2Labels = raw37208step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37208step2 raw37208step2Labels = mixedMoment B raw37208step3 raw37208step3Labels := by
      have ha : raw37208step3 = raw37208step2 := by apply Matrix.ext; unfold raw37208step3 raw37208step2; decide +kernel
      have hl : raw37208step2Labels = labelEmbedding6 ∘ raw37208step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37208step2 raw37208step2Labels raw37208step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5418 node5418Labels := by rfl

def raw37209 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -2, 0], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw37209Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37209step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw37209step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37209step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw37209step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37209step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw37209step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37209 raw37209Labels = mixedMoment B node5393 node5393Labels := by
  calc
    mixedMoment B raw37209 raw37209Labels = mixedMoment B raw37209step0 raw37209step0Labels := by
      have ha : raw37209step0 = (fun i j => raw37209 (permutation398 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37209step0 raw37209; decide +kernel
      have hl : raw37209step0Labels = raw37209Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37209 raw37209Labels permutation398 permutation3
    mixedMoment B raw37209step0 raw37209step0Labels = mixedMoment B raw37209step1 raw37209step1Labels := by
      have ha : raw37209step1 = -raw37209step0 := by apply Matrix.ext; change ∀ i j, raw37209step1 i j = -(raw37209step0 i j); unfold raw37209step1 raw37209step0; decide +kernel
      have hl : raw37209step1Labels = raw37209step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37209step1 raw37209step1Labels = mixedMoment B raw37209step2 raw37209step2Labels := by
      have ha : raw37209step2 = raw37209step1 := by apply Matrix.ext; unfold raw37209step2 raw37209step1; decide +kernel
      have hl : raw37209step1Labels = labelEmbedding6 ∘ raw37209step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37209step1 raw37209step1Labels raw37209step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5393 node5393Labels := by rfl

def raw37210 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![2, -2, 0], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw37210Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37210step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw37210step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37210step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw37210step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37210step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw37210step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37210 raw37210Labels = mixedMoment B node5393 node5393Labels := by
  calc
    mixedMoment B raw37210 raw37210Labels = mixedMoment B raw37210step0 raw37210step0Labels := by
      have ha : raw37210step0 = (fun i j => raw37210 (permutation393 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37210step0 raw37210; decide +kernel
      have hl : raw37210step0Labels = raw37210Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37210 raw37210Labels permutation393 permutation3
    mixedMoment B raw37210step0 raw37210step0Labels = mixedMoment B raw37210step1 raw37210step1Labels := by
      have ha : raw37210step1 = -raw37210step0 := by apply Matrix.ext; change ∀ i j, raw37210step1 i j = -(raw37210step0 i j); unfold raw37210step1 raw37210step0; decide +kernel
      have hl : raw37210step1Labels = raw37210step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37210step1 raw37210step1Labels = mixedMoment B raw37210step2 raw37210step2Labels := by
      have ha : raw37210step2 = raw37210step1 := by apply Matrix.ext; unfold raw37210step2 raw37210step1; decide +kernel
      have hl : raw37210step1Labels = labelEmbedding6 ∘ raw37210step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37210step1 raw37210step1Labels raw37210step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5393 node5393Labels := by rfl

def raw37211 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37211Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37211step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37211step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37211step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37211step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37211 raw37211Labels = mixedMoment B node4939 node4939Labels := by
  calc
    mixedMoment B raw37211 raw37211Labels = mixedMoment B raw37211step0 raw37211step0Labels := by
      have ha : raw37211step0 = (fun i j => raw37211 (permutation168 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37211step0 raw37211; decide +kernel
      have hl : raw37211step0Labels = raw37211Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37211 raw37211Labels permutation168 permutation3
    mixedMoment B raw37211step0 raw37211step0Labels = mixedMoment B raw37211step1 raw37211step1Labels := by
      have ha : raw37211step1 = raw37211step0 := by apply Matrix.ext; unfold raw37211step1 raw37211step0; decide +kernel
      have hl : raw37211step0Labels = labelEmbedding6 ∘ raw37211step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37211step0 raw37211step0Labels raw37211step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4939 node4939Labels := by rfl

def raw37212 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37212Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37212step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37212step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37212step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw37212step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37212 raw37212Labels = mixedMoment B node4939 node4939Labels := by
  calc
    mixedMoment B raw37212 raw37212Labels = mixedMoment B raw37212step0 raw37212step0Labels := by
      have ha : raw37212step0 = (fun i j => raw37212 (permutation281 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37212step0 raw37212; decide +kernel
      have hl : raw37212step0Labels = raw37212Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37212 raw37212Labels permutation281 permutation3
    mixedMoment B raw37212step0 raw37212step0Labels = mixedMoment B raw37212step1 raw37212step1Labels := by
      have ha : raw37212step1 = raw37212step0 := by apply Matrix.ext; unfold raw37212step1 raw37212step0; decide +kernel
      have hl : raw37212step0Labels = labelEmbedding6 ∘ raw37212step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37212step0 raw37212step0Labels raw37212step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4939 node4939Labels := by rfl

def raw37213 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![0, 1, -1], ![1, 0, -1]]
def raw37213Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37213step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw37213step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37213step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw37213step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37213step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw37213step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37213 raw37213Labels = mixedMoment B node5393 node5393Labels := by
  calc
    mixedMoment B raw37213 raw37213Labels = mixedMoment B raw37213step0 raw37213step0Labels := by
      have ha : raw37213step0 = (fun i j => raw37213 (permutation483 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37213step0 raw37213; decide +kernel
      have hl : raw37213step0Labels = raw37213Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37213 raw37213Labels permutation483 permutation3
    mixedMoment B raw37213step0 raw37213step0Labels = mixedMoment B raw37213step1 raw37213step1Labels := by
      have ha : raw37213step1 = -raw37213step0 := by apply Matrix.ext; change ∀ i j, raw37213step1 i j = -(raw37213step0 i j); unfold raw37213step1 raw37213step0; decide +kernel
      have hl : raw37213step1Labels = raw37213step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37213step1 raw37213step1Labels = mixedMoment B raw37213step2 raw37213step2Labels := by
      have ha : raw37213step2 = raw37213step1 := by apply Matrix.ext; unfold raw37213step2 raw37213step1; decide +kernel
      have hl : raw37213step1Labels = labelEmbedding6 ∘ raw37213step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37213step1 raw37213step1Labels raw37213step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5393 node5393Labels := by rfl

def raw37214 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![2, -2, 0], ![1, 0, -1], ![0, 1, -1]]
def raw37214Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37214step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw37214step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37214step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw37214step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37214step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw37214step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37214 raw37214Labels = mixedMoment B node5393 node5393Labels := by
  calc
    mixedMoment B raw37214 raw37214Labels = mixedMoment B raw37214step0 raw37214step0Labels := by
      have ha : raw37214step0 = (fun i j => raw37214 (permutation479 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37214step0 raw37214; decide +kernel
      have hl : raw37214step0Labels = raw37214Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37214 raw37214Labels permutation479 permutation3
    mixedMoment B raw37214step0 raw37214step0Labels = mixedMoment B raw37214step1 raw37214step1Labels := by
      have ha : raw37214step1 = -raw37214step0 := by apply Matrix.ext; change ∀ i j, raw37214step1 i j = -(raw37214step0 i j); unfold raw37214step1 raw37214step0; decide +kernel
      have hl : raw37214step1Labels = raw37214step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37214step1 raw37214step1Labels = mixedMoment B raw37214step2 raw37214step2Labels := by
      have ha : raw37214step2 = raw37214step1 := by apply Matrix.ext; unfold raw37214step2 raw37214step1; decide +kernel
      have hl : raw37214step1Labels = labelEmbedding6 ∘ raw37214step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37214step1 raw37214step1Labels raw37214step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5393 node5393Labels := by rfl

def raw37215 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw37215Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37215step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37215step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37215step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37215step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37215 raw37215Labels = mixedMoment B node4941 node4941Labels := by
  calc
    mixedMoment B raw37215 raw37215Labels = mixedMoment B raw37215step0 raw37215step0Labels := by
      have ha : raw37215step0 = (fun i j => raw37215 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37215step0 raw37215; decide +kernel
      have hl : raw37215step0Labels = raw37215Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37215 raw37215Labels permutation170 permutation3
    mixedMoment B raw37215step0 raw37215step0Labels = mixedMoment B raw37215step1 raw37215step1Labels := by
      have ha : raw37215step1 = raw37215step0 := by apply Matrix.ext; unfold raw37215step1 raw37215step0; decide +kernel
      have hl : raw37215step0Labels = labelEmbedding6 ∘ raw37215step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37215step0 raw37215step0Labels raw37215step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4941 node4941Labels := by rfl

def raw37216 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 2, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw37216Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37216step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37216step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37216step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37216step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37216 raw37216Labels = mixedMoment B node4941 node4941Labels := by
  calc
    mixedMoment B raw37216 raw37216Labels = mixedMoment B raw37216step0 raw37216step0Labels := by
      have ha : raw37216step0 = (fun i j => raw37216 (permutation283 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37216step0 raw37216; decide +kernel
      have hl : raw37216step0Labels = raw37216Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37216 raw37216Labels permutation283 permutation3
    mixedMoment B raw37216step0 raw37216step0Labels = mixedMoment B raw37216step1 raw37216step1Labels := by
      have ha : raw37216step1 = raw37216step0 := by apply Matrix.ext; unfold raw37216step1 raw37216step0; decide +kernel
      have hl : raw37216step0Labels = labelEmbedding6 ∘ raw37216step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37216step0 raw37216step0Labels raw37216step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4941 node4941Labels := by rfl

def raw37217 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1], ![0, 1, -1]]
def raw37217Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37217step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37217step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37217step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37217step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37217 raw37217Labels = mixedMoment B node5460 node5460Labels := by
  calc
    mixedMoment B raw37217 raw37217Labels = mixedMoment B raw37217step0 raw37217step0Labels := by
      have ha : raw37217step0 = (fun i j => raw37217 (permutation170 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37217step0 raw37217; decide +kernel
      have hl : raw37217step0Labels = raw37217Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37217 raw37217Labels permutation170 permutation3
    mixedMoment B raw37217step0 raw37217step0Labels = mixedMoment B raw37217step1 raw37217step1Labels := by
      have ha : raw37217step1 = raw37217step0 := by apply Matrix.ext; unfold raw37217step1 raw37217step0; decide +kernel
      have hl : raw37217step0Labels = labelEmbedding6 ∘ raw37217step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37217step0 raw37217step0Labels raw37217step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5460 node5460Labels := by rfl

def raw37218 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-3, 3, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37218Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37218step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37218step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37218step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw37218step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37218 raw37218Labels = mixedMoment B node4831 node4831Labels := by
  calc
    mixedMoment B raw37218 raw37218Labels = mixedMoment B raw37218step0 raw37218step0Labels := by
      have ha : raw37218step0 = (fun i j => raw37218 (permutation282 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37218step0 raw37218; decide +kernel
      have hl : raw37218step0Labels = raw37218Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37218 raw37218Labels permutation282 permutation3
    mixedMoment B raw37218step0 raw37218step0Labels = mixedMoment B raw37218step1 raw37218step1Labels := by
      have ha : raw37218step1 = raw37218step0 := by apply Matrix.ext; unfold raw37218step1 raw37218step0; decide +kernel
      have hl : raw37218step0Labels = labelEmbedding6 ∘ raw37218step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37218step0 raw37218step0Labels raw37218step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4831 node4831Labels := by rfl

def raw37219 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37219Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37219step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37219step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37219step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw37219step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37219step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw37219step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37219 raw37219Labels = mixedMoment B node5439 node5439Labels := by
  calc
    mixedMoment B raw37219 raw37219Labels = mixedMoment B raw37219step0 raw37219step0Labels := by
      have hz : ∀ j, raw37219 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37219step0 = (fun i j => raw37219 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37219step0 raw37219; decide +kernel
      have hl : raw37219step0Labels = raw37219Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37219 raw37219Labels permutation434 hz
    mixedMoment B raw37219step0 raw37219step0Labels = mixedMoment B raw37219step1 raw37219step1Labels := by
      have ha : raw37219step1 = (fun i j => raw37219step0 (permutation59 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37219step1 raw37219step0; decide +kernel
      have hl : raw37219step1Labels = raw37219step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37219step0 raw37219step0Labels permutation59 permutation3
    mixedMoment B raw37219step1 raw37219step1Labels = mixedMoment B raw37219step2 raw37219step2Labels := by
      have ha : raw37219step2 = raw37219step1 := by apply Matrix.ext; unfold raw37219step2 raw37219step1; decide +kernel
      have hl : raw37219step1Labels = labelEmbedding6 ∘ raw37219step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37219step1 raw37219step1Labels raw37219step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5439 node5439Labels := by rfl

def raw37220 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw37220Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37220step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw37220step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37220step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37220step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37220step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37220step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37220 raw37220Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw37220 raw37220Labels = mixedMoment B raw37220step0 raw37220step0Labels := by
      have ha : raw37220step0 = (fun i j => raw37220 (permutation325 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37220step0 raw37220; decide +kernel
      have hl : raw37220step0Labels = raw37220Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37220 raw37220Labels permutation325 permutation5
    mixedMoment B raw37220step0 raw37220step0Labels = mixedMoment B raw37220step1 raw37220step1Labels := by
      have ha : raw37220step1 = -raw37220step0 := by apply Matrix.ext; change ∀ i j, raw37220step1 i j = -(raw37220step0 i j); unfold raw37220step1 raw37220step0; decide +kernel
      have hl : raw37220step1Labels = raw37220step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37220step1 raw37220step1Labels = mixedMoment B raw37220step2 raw37220step2Labels := by
      have ha : raw37220step2 = raw37220step1 := by apply Matrix.ext; unfold raw37220step2 raw37220step1; decide +kernel
      have hl : raw37220step1Labels = labelEmbedding8 ∘ raw37220step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37220step1 raw37220step1Labels raw37220step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw37221 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 0, 1], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw37221Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37221step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw37221step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37221step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37221step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37221step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw37221step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37221 raw37221Labels = mixedMoment B node5424 node5424Labels := by
  calc
    mixedMoment B raw37221 raw37221Labels = mixedMoment B raw37221step0 raw37221step0Labels := by
      have ha : raw37221step0 = (fun i j => raw37221 (permutation338 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37221step0 raw37221; decide +kernel
      have hl : raw37221step0Labels = raw37221Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37221 raw37221Labels permutation338 permutation5
    mixedMoment B raw37221step0 raw37221step0Labels = mixedMoment B raw37221step1 raw37221step1Labels := by
      have ha : raw37221step1 = -raw37221step0 := by apply Matrix.ext; change ∀ i j, raw37221step1 i j = -(raw37221step0 i j); unfold raw37221step1 raw37221step0; decide +kernel
      have hl : raw37221step1Labels = raw37221step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw37221step1 raw37221step1Labels = mixedMoment B raw37221step2 raw37221step2Labels := by
      have ha : raw37221step2 = raw37221step1 := by apply Matrix.ext; unfold raw37221step2 raw37221step1; decide +kernel
      have hl : raw37221step1Labels = labelEmbedding8 ∘ raw37221step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37221step1 raw37221step1Labels raw37221step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5424 node5424Labels := by rfl

def raw37222 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 3, 0], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37222Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37222step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw37222step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37222step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw37222step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37222 raw37222Labels = mixedMoment B node4639 node4639Labels := by
  calc
    mixedMoment B raw37222 raw37222Labels = mixedMoment B raw37222step0 raw37222step0Labels := by
      have ha : raw37222step0 = (fun i j => raw37222 (permutation282 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37222step0 raw37222; decide +kernel
      have hl : raw37222step0Labels = raw37222Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37222 raw37222Labels permutation282 permutation3
    mixedMoment B raw37222step0 raw37222step0Labels = mixedMoment B raw37222step1 raw37222step1Labels := by
      have ha : raw37222step1 = raw37222step0 := by apply Matrix.ext; unfold raw37222step1 raw37222step0; decide +kernel
      have hl : raw37222step0Labels = labelEmbedding6 ∘ raw37222step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37222step0 raw37222step0Labels raw37222step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4639 node4639Labels := by rfl

def raw37223 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![2, -3, 1], ![0, 0, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37223Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![2, -3, 1], ![1, 0, -1], ![1, 0, -1]]
def raw37223step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37223step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw37223step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37223step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw37223step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37223 raw37223Labels = mixedMoment B node5248 node5248Labels := by
  calc
    mixedMoment B raw37223 raw37223Labels = mixedMoment B raw37223step0 raw37223step0Labels := by
      have hz : ∀ j, raw37223 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37223step0 = (fun i j => raw37223 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37223step0 raw37223; decide +kernel
      have hl : raw37223step0Labels = raw37223Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37223 raw37223Labels permutation434 hz
    mixedMoment B raw37223step0 raw37223step0Labels = mixedMoment B raw37223step1 raw37223step1Labels := by
      have ha : raw37223step1 = (fun i j => raw37223step0 (permutation96 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37223step1 raw37223step0; decide +kernel
      have hl : raw37223step1Labels = raw37223step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37223step0 raw37223step0Labels permutation96 permutation5
    mixedMoment B raw37223step1 raw37223step1Labels = mixedMoment B raw37223step2 raw37223step2Labels := by
      have ha : raw37223step2 = raw37223step1 := by apply Matrix.ext; unfold raw37223step2 raw37223step1; decide +kernel
      have hl : raw37223step1Labels = labelEmbedding8 ∘ raw37223step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37223step1 raw37223step1Labels raw37223step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5248 node5248Labels := by rfl

def raw37224 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![2, -3, 1], ![1, -1, 0], ![0, 1, -1], ![1, 0, -1]]
def raw37224Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37224step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw37224step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37224step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw37224step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37224 raw37224Labels = mixedMoment B node5056 node5056Labels := by
  calc
    mixedMoment B raw37224 raw37224Labels = mixedMoment B raw37224step0 raw37224step0Labels := by
      have ha : raw37224step0 = (fun i j => raw37224 (permutation398 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37224step0 raw37224; decide +kernel
      have hl : raw37224step0Labels = raw37224Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37224 raw37224Labels permutation398 permutation5
    mixedMoment B raw37224step0 raw37224step0Labels = mixedMoment B raw37224step1 raw37224step1Labels := by
      have ha : raw37224step1 = raw37224step0 := by apply Matrix.ext; unfold raw37224step1 raw37224step0; decide +kernel
      have hl : raw37224step0Labels = labelEmbedding8 ∘ raw37224step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37224step0 raw37224step0Labels raw37224step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5056 node5056Labels := by rfl

def raw37225 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1], ![0, 1, -1]]
def raw37225Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37225step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw37225step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw37225step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw37225step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37225 raw37225Labels = mixedMoment B node5056 node5056Labels := by
  calc
    mixedMoment B raw37225 raw37225Labels = mixedMoment B raw37225step0 raw37225step0Labels := by
      have ha : raw37225step0 = (fun i j => raw37225 (permutation393 i) (permutation5 j)) := by apply Matrix.ext; unfold raw37225step0 raw37225; decide +kernel
      have hl : raw37225step0Labels = raw37225Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37225 raw37225Labels permutation393 permutation5
    mixedMoment B raw37225step0 raw37225step0Labels = mixedMoment B raw37225step1 raw37225step1Labels := by
      have ha : raw37225step1 = raw37225step0 := by apply Matrix.ext; unfold raw37225step1 raw37225step0; decide +kernel
      have hl : raw37225step0Labels = labelEmbedding8 ∘ raw37225step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37225step0 raw37225step0Labels raw37225step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5056 node5056Labels := by rfl

def raw37226 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 3, 0], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1], ![1, 0, -1]]
def raw37226Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37226step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw37226step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37226step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw37226step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37226 raw37226Labels = mixedMoment B node4640 node4640Labels := by
  calc
    mixedMoment B raw37226 raw37226Labels = mixedMoment B raw37226step0 raw37226step0Labels := by
      have ha : raw37226step0 = (fun i j => raw37226 (permutation281 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37226step0 raw37226; decide +kernel
      have hl : raw37226step0Labels = raw37226Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37226 raw37226Labels permutation281 permutation3
    mixedMoment B raw37226step0 raw37226step0Labels = mixedMoment B raw37226step1 raw37226step1Labels := by
      have ha : raw37226step1 = raw37226step0 := by apply Matrix.ext; unfold raw37226step1 raw37226step0; decide +kernel
      have hl : raw37226step0Labels = labelEmbedding6 ∘ raw37226step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37226step0 raw37226step0Labels raw37226step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4640 node4640Labels := by rfl

def raw37227 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![2, -2, 0], ![0, 1, -1], ![1, 0, -1]]
def raw37227Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37227step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw37227step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37227step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw37227step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37227 raw37227Labels = mixedMoment B node5344 node5344Labels := by
  calc
    mixedMoment B raw37227 raw37227Labels = mixedMoment B raw37227step0 raw37227step0Labels := by
      have ha : raw37227step0 = (fun i j => raw37227 (permutation281 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37227step0 raw37227; decide +kernel
      have hl : raw37227step0Labels = raw37227Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37227 raw37227Labels permutation281 permutation3
    mixedMoment B raw37227step0 raw37227step0Labels = mixedMoment B raw37227step1 raw37227step1Labels := by
      have ha : raw37227step1 = raw37227step0 := by apply Matrix.ext; unfold raw37227step1 raw37227step0; decide +kernel
      have hl : raw37227step0Labels = labelEmbedding6 ∘ raw37227step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37227step0 raw37227step0Labels raw37227step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5344 node5344Labels := by rfl

def raw37228 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1], ![0, 1, -1]]
def raw37228Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37228step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw37228step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37228step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw37228step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37228 raw37228Labels = mixedMoment B node5344 node5344Labels := by
  calc
    mixedMoment B raw37228 raw37228Labels = mixedMoment B raw37228step0 raw37228step0Labels := by
      have ha : raw37228step0 = (fun i j => raw37228 (permutation287 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37228step0 raw37228; decide +kernel
      have hl : raw37228step0Labels = raw37228Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37228 raw37228Labels permutation287 permutation3
    mixedMoment B raw37228step0 raw37228step0Labels = mixedMoment B raw37228step1 raw37228step1Labels := by
      have ha : raw37228step1 = raw37228step0 := by apply Matrix.ext; unfold raw37228step1 raw37228step0; decide +kernel
      have hl : raw37228step0Labels = labelEmbedding6 ∘ raw37228step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37228step0 raw37228step0Labels raw37228step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5344 node5344Labels := by rfl

def raw37229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-3, 3, 0], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1], ![1, 0, -1]]
def raw37229Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37229step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37229step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37229step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37229step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37229 raw37229Labels = mixedMoment B node4642 node4642Labels := by
  calc
    mixedMoment B raw37229 raw37229Labels = mixedMoment B raw37229step0 raw37229step0Labels := by
      have ha : raw37229step0 = (fun i j => raw37229 (permutation285 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37229step0 raw37229; decide +kernel
      have hl : raw37229step0Labels = raw37229Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37229 raw37229Labels permutation285 permutation3
    mixedMoment B raw37229step0 raw37229step0Labels = mixedMoment B raw37229step1 raw37229step1Labels := by
      have ha : raw37229step1 = raw37229step0 := by apply Matrix.ext; unfold raw37229step1 raw37229step0; decide +kernel
      have hl : raw37229step0Labels = labelEmbedding6 ∘ raw37229step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37229step0 raw37229step0Labels raw37229step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4642 node4642Labels := by rfl

def raw37230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![0, 0, 0], ![2, -1, -1], ![1, 0, -1]]
def raw37230Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37230step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![2, -1, -1], ![1, 0, -1]]
def raw37230step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37230step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw37230step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37230step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw37230step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37230 raw37230Labels = mixedMoment B node5368 node5368Labels := by
  calc
    mixedMoment B raw37230 raw37230Labels = mixedMoment B raw37230step0 raw37230step0Labels := by
      have hz : ∀ j, raw37230 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37230step0 = (fun i j => raw37230 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37230step0 raw37230; decide +kernel
      have hl : raw37230step0Labels = raw37230Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37230 raw37230Labels permutation434 hz
    mixedMoment B raw37230step0 raw37230step0Labels = mixedMoment B raw37230step1 raw37230step1Labels := by
      have ha : raw37230step1 = (fun i j => raw37230step0 (permutation60 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37230step1 raw37230step0; decide +kernel
      have hl : raw37230step1Labels = raw37230step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37230step0 raw37230step0Labels permutation60 permutation3
    mixedMoment B raw37230step1 raw37230step1Labels = mixedMoment B raw37230step2 raw37230step2Labels := by
      have ha : raw37230step2 = raw37230step1 := by apply Matrix.ext; unfold raw37230step2 raw37230step1; decide +kernel
      have hl : raw37230step1Labels = labelEmbedding6 ∘ raw37230step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37230step1 raw37230step1Labels raw37230step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5368 node5368Labels := by rfl

def raw37231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1], ![0, 1, -1]]
def raw37231Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37231step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37231step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37231step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw37231step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37231 raw37231Labels = mixedMoment B node5346 node5346Labels := by
  calc
    mixedMoment B raw37231 raw37231Labels = mixedMoment B raw37231step0 raw37231step0Labels := by
      have ha : raw37231step0 = (fun i j => raw37231 (permutation285 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37231step0 raw37231; decide +kernel
      have hl : raw37231step0Labels = raw37231Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37231 raw37231Labels permutation285 permutation3
    mixedMoment B raw37231step0 raw37231step0Labels = mixedMoment B raw37231step1 raw37231step1Labels := by
      have ha : raw37231step1 = raw37231step0 := by apply Matrix.ext; unfold raw37231step1 raw37231step0; decide +kernel
      have hl : raw37231step0Labels = labelEmbedding6 ∘ raw37231step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37231step0 raw37231step0Labels raw37231step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5346 node5346Labels := by rfl

def raw37232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-3, 3, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw37232Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37232step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![-3, 3], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw37232step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37232step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![1, -1], ![1, -1], ![1, -1]]
def raw37232step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical37232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37232 raw37232Labels = mixedMoment B node4079 node4079Labels := by
  calc
    mixedMoment B raw37232 raw37232Labels = mixedMoment B raw37232step0 raw37232step0Labels := by
      have hz : ∀ i, raw37232 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37232step0 = (fun i j => raw37232 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37232step0 raw37232; decide +kernel
      have hl : raw37232step0Labels = (fun j => raw37232Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37232 raw37232Labels permutation6 hz
    mixedMoment B raw37232step0 raw37232step0Labels = mixedMoment B raw37232step1 raw37232step1Labels := by
      have ha : raw37232step1 = (fun i j => raw37232step0 (permutation265 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37232step1 raw37232step0; decide +kernel
      have hl : raw37232step1Labels = raw37232step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37232step0 raw37232step0Labels permutation265 permutation0
    _ = mixedMoment B node4079 node4079Labels := by rfl

def raw37233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw37233Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw37233step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37233step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]
def raw37233step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37233step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw37233step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical37233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37233 raw37233Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw37233 raw37233Labels = mixedMoment B raw37233step0 raw37233step0Labels := by
      have hz : ∀ j, raw37233 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37233step0 = (fun i j => raw37233 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37233step0 raw37233; decide +kernel
      have hl : raw37233step0Labels = raw37233Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37233 raw37233Labels permutation520 hz
    mixedMoment B raw37233step0 raw37233step0Labels = mixedMoment B raw37233step1 raw37233step1Labels := by
      have hz : ∀ i, raw37233step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37233step1 = (fun i j => raw37233step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37233step1 raw37233step0; decide +kernel
      have hl : raw37233step1Labels = (fun j => raw37233step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37233step0 raw37233step0Labels permutation6 hz
    mixedMoment B raw37233step1 raw37233step1Labels = mixedMoment B raw37233step2 raw37233step2Labels := by
      have ha : raw37233step2 = (fun i j => raw37233step1 (permutation56 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37233step2 raw37233step1; decide +kernel
      have hl : raw37233step2Labels = raw37233step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37233step1 raw37233step1Labels permutation56 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw37234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw37234Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-1, 1, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw37234step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37234step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]
def raw37234step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37234step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw37234step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical37234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37234 raw37234Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw37234 raw37234Labels = mixedMoment B raw37234step0 raw37234step0Labels := by
      have hz : ∀ j, raw37234 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw37234step0 = (fun i j => raw37234 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw37234step0 raw37234; decide +kernel
      have hl : raw37234step0Labels = raw37234Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37234 raw37234Labels permutation590 hz
    mixedMoment B raw37234step0 raw37234step0Labels = mixedMoment B raw37234step1 raw37234step1Labels := by
      have hz : ∀ i, raw37234step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37234step1 = (fun i j => raw37234step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37234step1 raw37234step0; decide +kernel
      have hl : raw37234step1Labels = (fun j => raw37234step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37234step0 raw37234step0Labels permutation6 hz
    mixedMoment B raw37234step1 raw37234step1Labels = mixedMoment B raw37234step2 raw37234step2Labels := by
      have ha : raw37234step2 = (fun i j => raw37234step1 (permutation56 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37234step2 raw37234step1; decide +kernel
      have hl : raw37234step2Labels = raw37234step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37234step1 raw37234step1Labels permutation56 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw37235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 3, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw37235Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37235step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-3, 3], ![2, -2], ![1, -1], ![1, -1], ![1, -1]]
def raw37235step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37235step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]
def raw37235step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical37235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37235 raw37235Labels = mixedMoment B node4073 node4073Labels := by
  calc
    mixedMoment B raw37235 raw37235Labels = mixedMoment B raw37235step0 raw37235step0Labels := by
      have hz : ∀ i, raw37235 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37235step0 = (fun i j => raw37235 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37235step0 raw37235; decide +kernel
      have hl : raw37235step0Labels = (fun j => raw37235Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37235 raw37235Labels permutation6 hz
    mixedMoment B raw37235step0 raw37235step0Labels = mixedMoment B raw37235step1 raw37235step1Labels := by
      have ha : raw37235step1 = (fun i j => raw37235step0 (permutation274 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37235step1 raw37235step0; decide +kernel
      have hl : raw37235step1Labels = raw37235step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37235step0 raw37235step0Labels permutation274 permutation0
    _ = mixedMoment B node4073 node4073Labels := by rfl

def raw37236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0]]
def raw37236Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37236step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw37236step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37236step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![1, -1], ![1, -1]]
def raw37236step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37236step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw37236step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical37236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37236 raw37236Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw37236 raw37236Labels = mixedMoment B raw37236step0 raw37236step0Labels := by
      have hz : ∀ j, raw37236 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw37236step0 = (fun i j => raw37236 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw37236step0 raw37236; decide +kernel
      have hl : raw37236step0Labels = raw37236Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37236 raw37236Labels permutation434 hz
    mixedMoment B raw37236step0 raw37236step0Labels = mixedMoment B raw37236step1 raw37236step1Labels := by
      have hz : ∀ i, raw37236step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37236step1 = (fun i j => raw37236step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37236step1 raw37236step0; decide +kernel
      have hl : raw37236step1Labels = (fun j => raw37236step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37236step0 raw37236step0Labels permutation6 hz
    mixedMoment B raw37236step1 raw37236step1Labels = mixedMoment B raw37236step2 raw37236step2Labels := by
      have ha : raw37236step2 = (fun i j => raw37236step1 (permutation35 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37236step2 raw37236step1; decide +kernel
      have hl : raw37236step2Labels = raw37236step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37236step1 raw37236step1Labels permutation35 permutation0
    _ = mixedMoment B node4088 node4088Labels := by rfl

def raw37237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0]]
def raw37237Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw37237step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37237step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![1, -1], ![1, -1]]
def raw37237step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37237step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw37237step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical37237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37237 raw37237Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw37237 raw37237Labels = mixedMoment B raw37237step0 raw37237step0Labels := by
      have hz : ∀ j, raw37237 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37237step0 = (fun i j => raw37237 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37237step0 raw37237; decide +kernel
      have hl : raw37237step0Labels = raw37237Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37237 raw37237Labels permutation520 hz
    mixedMoment B raw37237step0 raw37237step0Labels = mixedMoment B raw37237step1 raw37237step1Labels := by
      have hz : ∀ i, raw37237step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37237step1 = (fun i j => raw37237step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37237step1 raw37237step0; decide +kernel
      have hl : raw37237step1Labels = (fun j => raw37237step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37237step0 raw37237step0Labels permutation6 hz
    mixedMoment B raw37237step1 raw37237step1Labels = mixedMoment B raw37237step2 raw37237step2Labels := by
      have ha : raw37237step2 = (fun i j => raw37237step1 (permutation35 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37237step2 raw37237step1; decide +kernel
      have hl : raw37237step2Labels = raw37237step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37237step1 raw37237step1Labels permutation35 permutation0
    _ = mixedMoment B node4088 node4088Labels := by rfl

def raw37238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0], ![0, 0, 0]]
def raw37238Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37238step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw37238step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37238step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![2, -2], ![1, -1], ![1, -1]]
def raw37238step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37238step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw37238step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical37238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37238 raw37238Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw37238 raw37238Labels = mixedMoment B raw37238step0 raw37238step0Labels := by
      have hz : ∀ j, raw37238 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw37238step0 = (fun i j => raw37238 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw37238step0 raw37238; decide +kernel
      have hl : raw37238step0Labels = raw37238Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37238 raw37238Labels permutation590 hz
    mixedMoment B raw37238step0 raw37238step0Labels = mixedMoment B raw37238step1 raw37238step1Labels := by
      have hz : ∀ i, raw37238step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37238step1 = (fun i j => raw37238step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37238step1 raw37238step0; decide +kernel
      have hl : raw37238step1Labels = (fun j => raw37238step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37238step0 raw37238step0Labels permutation6 hz
    mixedMoment B raw37238step1 raw37238step1Labels = mixedMoment B raw37238step2 raw37238step2Labels := by
      have ha : raw37238step2 = (fun i j => raw37238step1 (permutation35 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37238step2 raw37238step1; decide +kernel
      have hl : raw37238step2Labels = raw37238step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37238step1 raw37238step1Labels permutation35 permutation0
    _ = mixedMoment B node4088 node4088Labels := by rfl

def raw37239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 3, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![1, -1, 0]]
def raw37239Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37239step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-3, 3], ![1, -1], ![2, -2], ![1, -1], ![1, -1]]
def raw37239step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37239step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]
def raw37239step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical37239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37239 raw37239Labels = mixedMoment B node4073 node4073Labels := by
  calc
    mixedMoment B raw37239 raw37239Labels = mixedMoment B raw37239step0 raw37239step0Labels := by
      have hz : ∀ i, raw37239 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37239step0 = (fun i j => raw37239 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37239step0 raw37239; decide +kernel
      have hl : raw37239step0Labels = (fun j => raw37239Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37239 raw37239Labels permutation6 hz
    mixedMoment B raw37239step0 raw37239step0Labels = mixedMoment B raw37239step1 raw37239step1Labels := by
      have ha : raw37239step1 = (fun i j => raw37239step0 (permutation268 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37239step1 raw37239step0; decide +kernel
      have hl : raw37239step1Labels = raw37239step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37239step0 raw37239step0Labels permutation268 permutation0
    _ = mixedMoment B node4073 node4073Labels := by rfl

def raw37240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0], ![1, -1, 0]]
def raw37240Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw37240step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37240step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![2, -2], ![1, -1]]
def raw37240step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37240step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw37240step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical37240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37240 raw37240Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw37240 raw37240Labels = mixedMoment B raw37240step0 raw37240step0Labels := by
      have hz : ∀ j, raw37240 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37240step0 = (fun i j => raw37240 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37240step0 raw37240; decide +kernel
      have hl : raw37240step0Labels = raw37240Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37240 raw37240Labels permutation520 hz
    mixedMoment B raw37240step0 raw37240step0Labels = mixedMoment B raw37240step1 raw37240step1Labels := by
      have hz : ∀ i, raw37240step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37240step1 = (fun i j => raw37240step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37240step1 raw37240step0; decide +kernel
      have hl : raw37240step1Labels = (fun j => raw37240step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37240step0 raw37240step0Labels permutation6 hz
    mixedMoment B raw37240step1 raw37240step1Labels = mixedMoment B raw37240step2 raw37240step2Labels := by
      have ha : raw37240step2 = (fun i j => raw37240step1 (permutation33 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37240step2 raw37240step1; decide +kernel
      have hl : raw37240step2Labels = raw37240step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37240step1 raw37240step1Labels permutation33 permutation0
    _ = mixedMoment B node4088 node4088Labels := by rfl

def raw37241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0], ![0, 0, 0]]
def raw37241Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37241step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw37241step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37241step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![2, -2], ![1, -1]]
def raw37241step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37241step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw37241step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical37241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37241 raw37241Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw37241 raw37241Labels = mixedMoment B raw37241step0 raw37241step0Labels := by
      have hz : ∀ j, raw37241 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw37241step0 = (fun i j => raw37241 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw37241step0 raw37241; decide +kernel
      have hl : raw37241step0Labels = raw37241Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37241 raw37241Labels permutation590 hz
    mixedMoment B raw37241step0 raw37241step0Labels = mixedMoment B raw37241step1 raw37241step1Labels := by
      have hz : ∀ i, raw37241step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37241step1 = (fun i j => raw37241step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37241step1 raw37241step0; decide +kernel
      have hl : raw37241step1Labels = (fun j => raw37241step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37241step0 raw37241step0Labels permutation6 hz
    mixedMoment B raw37241step1 raw37241step1Labels = mixedMoment B raw37241step2 raw37241step2Labels := by
      have ha : raw37241step2 = (fun i j => raw37241step1 (permutation33 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37241step2 raw37241step1; decide +kernel
      have hl : raw37241step2Labels = raw37241step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37241step1 raw37241step1Labels permutation33 permutation0
    _ = mixedMoment B node4088 node4088Labels := by rfl

def raw37242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-3, 3, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![1, -1, 0]]
def raw37242Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37242step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-3, 3], ![1, -1], ![1, -1], ![2, -2], ![1, -1]]
def raw37242step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw37242step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![1, -1], ![2, -2]]
def raw37242step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical37242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37242 raw37242Labels = mixedMoment B node4073 node4073Labels := by
  calc
    mixedMoment B raw37242 raw37242Labels = mixedMoment B raw37242step0 raw37242step0Labels := by
      have hz : ∀ i, raw37242 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37242step0 = (fun i j => raw37242 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37242step0 raw37242; decide +kernel
      have hl : raw37242step0Labels = (fun j => raw37242Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37242 raw37242Labels permutation6 hz
    mixedMoment B raw37242step0 raw37242step0Labels = mixedMoment B raw37242step1 raw37242step1Labels := by
      have ha : raw37242step1 = (fun i j => raw37242step0 (permutation266 i) (permutation0 j)) := by apply Matrix.ext; unfold raw37242step1 raw37242step0; decide +kernel
      have hl : raw37242step1Labels = raw37242step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37242step0 raw37242step0Labels permutation266 permutation0
    _ = mixedMoment B node4073 node4073Labels := by rfl

def raw37243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0], ![0, 0, 0]]
def raw37243Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, -2, 0]]
def raw37243step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw37243step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![1, -1], ![2, -2]]
def raw37243step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical37243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37243 raw37243Labels = mixedMoment B node4088 node4088Labels := by
  calc
    mixedMoment B raw37243 raw37243Labels = mixedMoment B raw37243step0 raw37243step0Labels := by
      have hz : ∀ j, raw37243 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw37243step0 = (fun i j => raw37243 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw37243step0 raw37243; decide +kernel
      have hl : raw37243step0Labels = raw37243Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37243 raw37243Labels permutation590 hz
    mixedMoment B raw37243step0 raw37243step0Labels = mixedMoment B raw37243step1 raw37243step1Labels := by
      have hz : ∀ i, raw37243step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw37243step1 = (fun i j => raw37243step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw37243step1 raw37243step0; decide +kernel
      have hl : raw37243step1Labels = (fun j => raw37243step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw37243step0 raw37243step0Labels permutation6 hz
    _ = mixedMoment B node4088 node4088Labels := by rfl

def raw37244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37244Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37244step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37244 raw37244Labels = mixedMoment B node5387 node5387Labels := by
  calc
    mixedMoment B raw37244 raw37244Labels = mixedMoment B raw37244step0 raw37244step0Labels := by
      have hz : ∀ j, raw37244 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw37244step0 = (fun i j => raw37244 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw37244step0 raw37244; decide +kernel
      have hl : raw37244step0Labels = raw37244Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37244 raw37244Labels permutation265 hz
    _ = mixedMoment B node5387 node5387Labels := by rfl

def raw37245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![2, 0, -2]]
def raw37245Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37245step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37245step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37245step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37245 raw37245Labels = mixedMoment B node5441 node5441Labels := by
  calc
    mixedMoment B raw37245 raw37245Labels = mixedMoment B raw37245step0 raw37245step0Labels := by
      have hz : ∀ j, raw37245 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37245step0 = (fun i j => raw37245 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37245step0 raw37245; decide +kernel
      have hl : raw37245step0Labels = raw37245Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37245 raw37245Labels permutation520 hz
    mixedMoment B raw37245step0 raw37245step0Labels = mixedMoment B raw37245step1 raw37245step1Labels := by
      have hz : ∀ j, raw37245step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw37245step1 = (fun i j => raw37245step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw37245step1 raw37245step0; decide +kernel
      have hl : raw37245step1Labels = raw37245step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37245step0 raw37245step0Labels permutation56 hz
    _ = mixedMoment B node5441 node5441Labels := by rfl

def raw37246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-2, 2, 0], ![2, -2, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37246Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37246step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw37246step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw37246step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 0, -2]]
def raw37246step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37246 raw37246Labels = mixedMoment B node5372 node5372Labels := by
  calc
    mixedMoment B raw37246 raw37246Labels = mixedMoment B raw37246step0 raw37246step0Labels := by
      have ha : raw37246step0 = (fun i j => raw37246 (permutation349 i) (permutation3 j)) := by apply Matrix.ext; unfold raw37246step0 raw37246; decide +kernel
      have hl : raw37246step0Labels = raw37246Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37246 raw37246Labels permutation349 permutation3
    mixedMoment B raw37246step0 raw37246step0Labels = mixedMoment B raw37246step1 raw37246step1Labels := by
      have ha : raw37246step1 = raw37246step0 := by apply Matrix.ext; unfold raw37246step1 raw37246step0; decide +kernel
      have hl : raw37246step0Labels = labelEmbedding6 ∘ raw37246step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw37246step0 raw37246step0Labels raw37246step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5372 node5372Labels := by rfl

def raw37247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![0, 0, 0], ![2, 0, -2]]
def raw37247Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37247step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![2, 0, -2]]
def raw37247step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37247step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw37247step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw37247step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw37247step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical37247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw37247 raw37247Labels = mixedMoment B node5387 node5387Labels := by
  calc
    mixedMoment B raw37247 raw37247Labels = mixedMoment B raw37247step0 raw37247step0Labels := by
      have hz : ∀ j, raw37247 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw37247step0 = (fun i j => raw37247 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw37247step0 raw37247; decide +kernel
      have hl : raw37247step0Labels = raw37247Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw37247 raw37247Labels permutation520 hz
    mixedMoment B raw37247step0 raw37247step0Labels = mixedMoment B raw37247step1 raw37247step1Labels := by
      have ha : raw37247step1 = (fun i j => raw37247step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw37247step1 raw37247step0; decide +kernel
      have hl : raw37247step1Labels = raw37247step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw37247step0 raw37247step0Labels permutation149 permutation2
    mixedMoment B raw37247step1 raw37247step1Labels = mixedMoment B raw37247step2 raw37247step2Labels := by
      have ha : raw37247step2 = -raw37247step1 := by apply Matrix.ext; change ∀ i j, raw37247step2 i j = -(raw37247step1 i j); unfold raw37247step2 raw37247step1; decide +kernel
      have hl : raw37247step2Labels = raw37247step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node5387 node5387Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
