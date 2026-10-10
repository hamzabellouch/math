import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes17
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes27
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes28
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes29
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes30
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes31
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes32
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes49
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes66
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes69
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes72
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes73
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw29184 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29184Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29184step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29184step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29184step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw29184step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29184step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29184step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29184step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29184step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29184 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29184 raw29184Labels = mixedMoment B node4741 node4741Labels := by
  calc
    mixedMoment B raw29184 raw29184Labels = mixedMoment B raw29184step0 raw29184step0Labels := by
      have hz : ∀ j, raw29184 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29184step0 = (fun i j => raw29184 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29184step0 raw29184; decide +kernel
      have hl : raw29184step0Labels = raw29184Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29184 raw29184Labels permutation434 hz
    mixedMoment B raw29184step0 raw29184step0Labels = mixedMoment B raw29184step1 raw29184step1Labels := by
      have ha : raw29184step1 = (fun i j => raw29184step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29184step1 raw29184step0; decide +kernel
      have hl : raw29184step1Labels = raw29184step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29184step0 raw29184step0Labels permutation151 permutation6
    mixedMoment B raw29184step1 raw29184step1Labels = mixedMoment B raw29184step2 raw29184step2Labels := by
      have ha : raw29184step2 = -raw29184step1 := by apply Matrix.ext; change ∀ i j, raw29184step2 i j = -(raw29184step1 i j); unfold raw29184step2 raw29184step1; decide +kernel
      have hl : raw29184step2Labels = raw29184step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29184step2 raw29184step2Labels = mixedMoment B raw29184step3 raw29184step3Labels := by
      have ha : raw29184step3 = raw29184step2 := by apply Matrix.ext; unfold raw29184step3 raw29184step2; decide +kernel
      have hl : raw29184step2Labels = labelEmbedding9 ∘ raw29184step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29184step2 raw29184step2Labels raw29184step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4741 node4741Labels := by rfl

def raw29185 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -3, 3]]
def raw29185Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29185step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![-1, 1, 0], ![1, -2, 1], ![0, -3, 3]]
def raw29185step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29185step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw29185step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29185step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw29185step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29185 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29185 raw29185Labels = mixedMoment B node4643 node4643Labels := by
  calc
    mixedMoment B raw29185 raw29185Labels = mixedMoment B raw29185step0 raw29185step0Labels := by
      have hz : ∀ j, raw29185 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29185step0 = (fun i j => raw29185 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29185step0 raw29185; decide +kernel
      have hl : raw29185step0Labels = raw29185Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29185 raw29185Labels permutation346 hz
    mixedMoment B raw29185step0 raw29185step0Labels = mixedMoment B raw29185step1 raw29185step1Labels := by
      have ha : raw29185step1 = (fun i j => raw29185step0 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29185step1 raw29185step0; decide +kernel
      have hl : raw29185step1Labels = raw29185step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29185step0 raw29185step0Labels permutation151 permutation4
    mixedMoment B raw29185step1 raw29185step1Labels = mixedMoment B raw29185step2 raw29185step2Labels := by
      have ha : raw29185step2 = raw29185step1 := by apply Matrix.ext; unfold raw29185step2 raw29185step1; decide +kernel
      have hl : raw29185step1Labels = labelEmbedding7 ∘ raw29185step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29185step1 raw29185step1Labels raw29185step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4643 node4643Labels := by rfl

def raw29186 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -3, 3]]
def raw29186Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29186step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![0, -3, 3]]
def raw29186step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29186step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw29186step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29186step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw29186step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29186 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29186 raw29186Labels = mixedMoment B node4645 node4645Labels := by
  calc
    mixedMoment B raw29186 raw29186Labels = mixedMoment B raw29186step0 raw29186step0Labels := by
      have hz : ∀ j, raw29186 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29186step0 = (fun i j => raw29186 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29186step0 raw29186; decide +kernel
      have hl : raw29186step0Labels = raw29186Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29186 raw29186Labels permutation346 hz
    mixedMoment B raw29186step0 raw29186step0Labels = mixedMoment B raw29186step1 raw29186step1Labels := by
      have ha : raw29186step1 = (fun i j => raw29186step0 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29186step1 raw29186step0; decide +kernel
      have hl : raw29186step1Labels = raw29186step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29186step0 raw29186step0Labels permutation151 permutation4
    mixedMoment B raw29186step1 raw29186step1Labels = mixedMoment B raw29186step2 raw29186step2Labels := by
      have ha : raw29186step2 = raw29186step1 := by apply Matrix.ext; unfold raw29186step2 raw29186step1; decide +kernel
      have hl : raw29186step1Labels = labelEmbedding7 ∘ raw29186step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29186step1 raw29186step1Labels raw29186step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4645 node4645Labels := by rfl

def raw29187 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![0, -3, 3]]
def raw29187Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29187step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw29187step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29187step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw29187step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29187 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29187 raw29187Labels = mixedMoment B node4639 node4639Labels := by
  calc
    mixedMoment B raw29187 raw29187Labels = mixedMoment B raw29187step0 raw29187step0Labels := by
      have ha : raw29187step0 = (fun i j => raw29187 (permutation682 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29187step0 raw29187; decide +kernel
      have hl : raw29187step0Labels = raw29187Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29187 raw29187Labels permutation682 permutation4
    mixedMoment B raw29187step0 raw29187step0Labels = mixedMoment B raw29187step1 raw29187step1Labels := by
      have ha : raw29187step1 = raw29187step0 := by apply Matrix.ext; unfold raw29187step1 raw29187step0; decide +kernel
      have hl : raw29187step0Labels = labelEmbedding7 ∘ raw29187step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29187step0 raw29187step0Labels raw29187step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4639 node4639Labels := by rfl

def raw29188 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![-2, 2, 0], ![1, -2, 1], ![0, -3, 3]]
def raw29188Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29188step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-2, 2, 0], ![1, -2, 1], ![0, -3, 3]]
def raw29188step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29188step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw29188step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29188step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw29188step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29188 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29188 raw29188Labels = mixedMoment B node4651 node4651Labels := by
  calc
    mixedMoment B raw29188 raw29188Labels = mixedMoment B raw29188step0 raw29188step0Labels := by
      have hz : ∀ j, raw29188 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29188step0 = (fun i j => raw29188 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29188step0 raw29188; decide +kernel
      have hl : raw29188step0Labels = raw29188Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29188 raw29188Labels permutation346 hz
    mixedMoment B raw29188step0 raw29188step0Labels = mixedMoment B raw29188step1 raw29188step1Labels := by
      have ha : raw29188step1 = (fun i j => raw29188step0 (permutation149 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29188step1 raw29188step0; decide +kernel
      have hl : raw29188step1Labels = raw29188step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29188step0 raw29188step0Labels permutation149 permutation4
    mixedMoment B raw29188step1 raw29188step1Labels = mixedMoment B raw29188step2 raw29188step2Labels := by
      have ha : raw29188step2 = raw29188step1 := by apply Matrix.ext; unfold raw29188step2 raw29188step1; decide +kernel
      have hl : raw29188step1Labels = labelEmbedding7 ∘ raw29188step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29188step1 raw29188step1Labels raw29188step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4651 node4651Labels := by rfl

def raw29189 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -4, 3]]
def raw29189Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29189step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![0, 1, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -4, 3]]
def raw29189step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29189step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw29189step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29189step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw29189step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29189 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29189 raw29189Labels = mixedMoment B node4302 node4302Labels := by
  calc
    mixedMoment B raw29189 raw29189Labels = mixedMoment B raw29189step0 raw29189step0Labels := by
      have hz : ∀ j, raw29189 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29189step0 = (fun i j => raw29189 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29189step0 raw29189; decide +kernel
      have hl : raw29189step0Labels = raw29189Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29189 raw29189Labels permutation346 hz
    mixedMoment B raw29189step0 raw29189step0Labels = mixedMoment B raw29189step1 raw29189step1Labels := by
      have ha : raw29189step1 = (fun i j => raw29189step0 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29189step1 raw29189step0; decide +kernel
      have hl : raw29189step1Labels = raw29189step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29189step0 raw29189step0Labels permutation151 permutation4
    mixedMoment B raw29189step1 raw29189step1Labels = mixedMoment B raw29189step2 raw29189step2Labels := by
      have ha : raw29189step2 = raw29189step1 := by apply Matrix.ext; unfold raw29189step2 raw29189step1; decide +kernel
      have hl : raw29189step1Labels = labelEmbedding7 ∘ raw29189step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29189step1 raw29189step1Labels raw29189step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4302 node4302Labels := by rfl

def raw29190 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -4, 3]]
def raw29190Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29190step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -4, 3]]
def raw29190step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29190step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw29190step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29190step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw29190step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29190 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29190 raw29190Labels = mixedMoment B node4304 node4304Labels := by
  calc
    mixedMoment B raw29190 raw29190Labels = mixedMoment B raw29190step0 raw29190step0Labels := by
      have hz : ∀ j, raw29190 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29190step0 = (fun i j => raw29190 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29190step0 raw29190; decide +kernel
      have hl : raw29190step0Labels = raw29190Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29190 raw29190Labels permutation346 hz
    mixedMoment B raw29190step0 raw29190step0Labels = mixedMoment B raw29190step1 raw29190step1Labels := by
      have ha : raw29190step1 = (fun i j => raw29190step0 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29190step1 raw29190step0; decide +kernel
      have hl : raw29190step1Labels = raw29190step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29190step0 raw29190step0Labels permutation151 permutation4
    mixedMoment B raw29190step1 raw29190step1Labels = mixedMoment B raw29190step2 raw29190step2Labels := by
      have ha : raw29190step2 = raw29190step1 := by apply Matrix.ext; unfold raw29190step2 raw29190step1; decide +kernel
      have hl : raw29190step1Labels = labelEmbedding7 ∘ raw29190step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29190step1 raw29190step1Labels raw29190step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4304 node4304Labels := by rfl

def raw29191 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, -4, 3]]
def raw29191Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29191step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw29191step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29191step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw29191step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29191 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29191 raw29191Labels = mixedMoment B node4297 node4297Labels := by
  calc
    mixedMoment B raw29191 raw29191Labels = mixedMoment B raw29191step0 raw29191step0Labels := by
      have ha : raw29191step0 = (fun i j => raw29191 (permutation682 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29191step0 raw29191; decide +kernel
      have hl : raw29191step0Labels = raw29191Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29191 raw29191Labels permutation682 permutation4
    mixedMoment B raw29191step0 raw29191step0Labels = mixedMoment B raw29191step1 raw29191step1Labels := by
      have ha : raw29191step1 = raw29191step0 := by apply Matrix.ext; unfold raw29191step1 raw29191step0; decide +kernel
      have hl : raw29191step0Labels = labelEmbedding7 ∘ raw29191step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29191step0 raw29191step0Labels raw29191step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4297 node4297Labels := by rfl

def raw29192 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![-2, 2, 0], ![0, -1, 1], ![1, -4, 3]]
def raw29192Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29192step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![-2, 2, 0], ![0, -1, 1], ![1, -4, 3]]
def raw29192step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29192step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw29192step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29192step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, 0, -1], ![2, -2, 0], ![2, 1, -3]]
def raw29192step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29192 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29192 raw29192Labels = mixedMoment B node4310 node4310Labels := by
  calc
    mixedMoment B raw29192 raw29192Labels = mixedMoment B raw29192step0 raw29192step0Labels := by
      have hz : ∀ j, raw29192 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29192step0 = (fun i j => raw29192 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29192step0 raw29192; decide +kernel
      have hl : raw29192step0Labels = raw29192Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29192 raw29192Labels permutation346 hz
    mixedMoment B raw29192step0 raw29192step0Labels = mixedMoment B raw29192step1 raw29192step1Labels := by
      have ha : raw29192step1 = (fun i j => raw29192step0 (permutation149 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29192step1 raw29192step0; decide +kernel
      have hl : raw29192step1Labels = raw29192step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29192step0 raw29192step0Labels permutation149 permutation4
    mixedMoment B raw29192step1 raw29192step1Labels = mixedMoment B raw29192step2 raw29192step2Labels := by
      have ha : raw29192step2 = raw29192step1 := by apply Matrix.ext; unfold raw29192step2 raw29192step1; decide +kernel
      have hl : raw29192step1Labels = labelEmbedding7 ∘ raw29192step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29192step1 raw29192step1Labels raw29192step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4310 node4310Labels := by rfl

def raw29193 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29193Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29193step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw29193step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29193step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-2, 0, 2], ![-2, 0, 2]]
def raw29193step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29193step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![2, 0, -2]]
def raw29193step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29193 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29193 raw29193Labels = mixedMoment B node2007 node2007Labels := by
  calc
    mixedMoment B raw29193 raw29193Labels = mixedMoment B raw29193step0 raw29193step0Labels := by
      have hz : ∀ j, raw29193 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29193step0 = (fun i j => raw29193 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29193step0 raw29193; decide +kernel
      have hl : raw29193step0Labels = raw29193Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29193 raw29193Labels permutation434 hz
    mixedMoment B raw29193step0 raw29193step0Labels = mixedMoment B raw29193step1 raw29193step1Labels := by
      have ha : raw29193step1 = (fun i j => raw29193step0 (permutation150 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29193step1 raw29193step0; decide +kernel
      have hl : raw29193step1Labels = raw29193step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29193step0 raw29193step0Labels permutation150 permutation2
    mixedMoment B raw29193step1 raw29193step1Labels = mixedMoment B raw29193step2 raw29193step2Labels := by
      have ha : raw29193step2 = -raw29193step1 := by apply Matrix.ext; change ∀ i j, raw29193step2 i j = -(raw29193step1 i j); unfold raw29193step2 raw29193step1; decide +kernel
      have hl : raw29193step2Labels = raw29193step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2007 node2007Labels := by rfl

def raw29194 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29194Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29194step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw29194step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29194step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 1, 2]]
def raw29194step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29194step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw29194step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29194 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29194 raw29194Labels = mixedMoment B node2003 node2003Labels := by
  calc
    mixedMoment B raw29194 raw29194Labels = mixedMoment B raw29194step0 raw29194step0Labels := by
      have hz : ∀ j, raw29194 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29194step0 = (fun i j => raw29194 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29194step0 raw29194; decide +kernel
      have hl : raw29194step0Labels = raw29194Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29194 raw29194Labels permutation434 hz
    mixedMoment B raw29194step0 raw29194step0Labels = mixedMoment B raw29194step1 raw29194step1Labels := by
      have ha : raw29194step1 = (fun i j => raw29194step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29194step1 raw29194step0; decide +kernel
      have hl : raw29194step1Labels = raw29194step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29194step0 raw29194step0Labels permutation151 permutation2
    mixedMoment B raw29194step1 raw29194step1Labels = mixedMoment B raw29194step2 raw29194step2Labels := by
      have ha : raw29194step2 = -raw29194step1 := by apply Matrix.ext; change ∀ i j, raw29194step2 i j = -(raw29194step1 i j); unfold raw29194step2 raw29194step1; decide +kernel
      have hl : raw29194step2Labels = raw29194step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2003 node2003Labels := by rfl

def raw29195 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29195Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29195step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![1, 0, -1], ![1, -1, 0], ![3, 0, -3]]
def raw29195step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29195step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-2, 0, 2], ![-3, 1, 2]]
def raw29195step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29195step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 0, -2], ![3, -1, -2]]
def raw29195step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29195 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29195 raw29195Labels = mixedMoment B node1872 node1872Labels := by
  calc
    mixedMoment B raw29195 raw29195Labels = mixedMoment B raw29195step0 raw29195step0Labels := by
      have hz : ∀ j, raw29195 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29195step0 = (fun i j => raw29195 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29195step0 raw29195; decide +kernel
      have hl : raw29195step0Labels = raw29195Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29195 raw29195Labels permutation434 hz
    mixedMoment B raw29195step0 raw29195step0Labels = mixedMoment B raw29195step1 raw29195step1Labels := by
      have ha : raw29195step1 = (fun i j => raw29195step0 (permutation145 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29195step1 raw29195step0; decide +kernel
      have hl : raw29195step1Labels = raw29195step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29195step0 raw29195step0Labels permutation145 permutation2
    mixedMoment B raw29195step1 raw29195step1Labels = mixedMoment B raw29195step2 raw29195step2Labels := by
      have ha : raw29195step2 = -raw29195step1 := by apply Matrix.ext; change ∀ i j, raw29195step2 i j = -(raw29195step1 i j); unfold raw29195step2 raw29195step1; decide +kernel
      have hl : raw29195step2Labels = raw29195step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1872 node1872Labels := by rfl

def raw29196 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29196Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29196step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![1, -1, 0], ![0, 1, -1], ![-2, 0, 2], ![-3, 1, 2]]
def raw29196step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29196step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw29196step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29196 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29196 raw29196Labels = mixedMoment B node1954 node1954Labels := by
  calc
    mixedMoment B raw29196 raw29196Labels = mixedMoment B raw29196step0 raw29196step0Labels := by
      have ha : raw29196step0 = (fun i j => raw29196 (permutation664 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29196step0 raw29196; decide +kernel
      have hl : raw29196step0Labels = raw29196Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29196 raw29196Labels permutation664 permutation2
    mixedMoment B raw29196step0 raw29196step0Labels = mixedMoment B raw29196step1 raw29196step1Labels := by
      have ha : raw29196step1 = -raw29196step0 := by apply Matrix.ext; change ∀ i j, raw29196step1 i j = -(raw29196step0 i j); unfold raw29196step1 raw29196step0; decide +kernel
      have hl : raw29196step1Labels = raw29196step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1954 node1954Labels := by rfl

def raw29197 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29197Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29197step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw29197step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29197step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![0, 1, -1], ![-2, 0, 2], ![-3, 1, 2]]
def raw29197step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29197step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw29197step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29197 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29197 raw29197Labels = mixedMoment B node1788 node1788Labels := by
  calc
    mixedMoment B raw29197 raw29197Labels = mixedMoment B raw29197step0 raw29197step0Labels := by
      have hz : ∀ j, raw29197 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29197step0 = (fun i j => raw29197 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29197step0 raw29197; decide +kernel
      have hl : raw29197step0Labels = raw29197Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29197 raw29197Labels permutation434 hz
    mixedMoment B raw29197step0 raw29197step0Labels = mixedMoment B raw29197step1 raw29197step1Labels := by
      have ha : raw29197step1 = (fun i j => raw29197step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29197step1 raw29197step0; decide +kernel
      have hl : raw29197step1Labels = raw29197step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29197step0 raw29197step0Labels permutation151 permutation2
    mixedMoment B raw29197step1 raw29197step1Labels = mixedMoment B raw29197step2 raw29197step2Labels := by
      have ha : raw29197step2 = -raw29197step1 := by apply Matrix.ext; change ∀ i j, raw29197step2 i j = -(raw29197step1 i j); unfold raw29197step2 raw29197step1; decide +kernel
      have hl : raw29197step2Labels = raw29197step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1788 node1788Labels := by rfl

def raw29198 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29198Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29198step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 0, 2], ![0, 1, -1], ![1, -1, 0], ![4, -1, -3]]
def raw29198step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29198step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![0, 1, -1], ![-2, 0, 2], ![-3, 1, 2]]
def raw29198step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29198step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![2, 0, -2], ![3, -1, -2]]
def raw29198step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29198 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29198 raw29198Labels = mixedMoment B node903 node903Labels := by
  calc
    mixedMoment B raw29198 raw29198Labels = mixedMoment B raw29198step0 raw29198step0Labels := by
      have hz : ∀ j, raw29198 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29198step0 = (fun i j => raw29198 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29198step0 raw29198; decide +kernel
      have hl : raw29198step0Labels = raw29198Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29198 raw29198Labels permutation434 hz
    mixedMoment B raw29198step0 raw29198step0Labels = mixedMoment B raw29198step1 raw29198step1Labels := by
      have ha : raw29198step1 = (fun i j => raw29198step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29198step1 raw29198step0; decide +kernel
      have hl : raw29198step1Labels = raw29198step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29198step0 raw29198step0Labels permutation151 permutation2
    mixedMoment B raw29198step1 raw29198step1Labels = mixedMoment B raw29198step2 raw29198step2Labels := by
      have ha : raw29198step2 = -raw29198step1 := by apply Matrix.ext; change ∀ i j, raw29198step2 i j = -(raw29198step1 i j); unfold raw29198step2 raw29198step1; decide +kernel
      have hl : raw29198step2Labels = raw29198step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node903 node903Labels := by rfl

def raw29199 : Matrix (Fin 6) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![0, 0], ![0, 0], ![3, -3]]
def raw29199Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29199step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![0, 0], ![3, -3]]
def raw29199step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29199step1 : Matrix (Fin 4) (Fin 2) ℤ := ![![-2, 2], ![-2, 2], ![1, -1], ![3, -3]]
def raw29199step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29199step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![3, -3], ![1, -1], ![-2, 2], ![-2, 2]]
def raw29199step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29199step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![2, -2], ![2, -2]]
def raw29199step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical29199 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29199 raw29199Labels = mixedMoment B node4082 node4082Labels := by
  calc
    mixedMoment B raw29199 raw29199Labels = mixedMoment B raw29199step0 raw29199step0Labels := by
      have hz : ∀ j, raw29199 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw29199step0 = (fun i j => raw29199 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw29199step0 raw29199; decide +kernel
      have hl : raw29199step0Labels = raw29199Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29199 raw29199Labels permutation520 hz
    mixedMoment B raw29199step0 raw29199step0Labels = mixedMoment B raw29199step1 raw29199step1Labels := by
      have hz : ∀ j, raw29199step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw29199step1 = (fun i j => raw29199step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw29199step1 raw29199step0; decide +kernel
      have hl : raw29199step1Labels = raw29199step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29199step0 raw29199step0Labels permutation104 hz
    mixedMoment B raw29199step1 raw29199step1Labels = mixedMoment B raw29199step2 raw29199step2Labels := by
      have ha : raw29199step2 = (fun i j => raw29199step1 (permutation30 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29199step2 raw29199step1; decide +kernel
      have hl : raw29199step2Labels = raw29199step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29199step1 raw29199step1Labels permutation30 permutation0
    mixedMoment B raw29199step2 raw29199step2Labels = mixedMoment B raw29199step3 raw29199step3Labels := by
      have ha : raw29199step3 = -raw29199step2 := by apply Matrix.ext; change ∀ i j, raw29199step3 i j = -(raw29199step2 i j); unfold raw29199step3 raw29199step2; decide +kernel
      have hl : raw29199step3Labels = raw29199step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4082 node4082Labels := by rfl

def raw29200 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29200Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29200step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![3, 0, -3]]
def raw29200step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29200step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw29200step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29200 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29200 raw29200Labels = mixedMoment B node1098 node1098Labels := by
  calc
    mixedMoment B raw29200 raw29200Labels = mixedMoment B raw29200step0 raw29200step0Labels := by
      have hz : ∀ j, raw29200 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29200step0 = (fun i j => raw29200 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29200step0 raw29200; decide +kernel
      have hl : raw29200step0Labels = raw29200Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29200 raw29200Labels permutation434 hz
    mixedMoment B raw29200step0 raw29200step0Labels = mixedMoment B raw29200step1 raw29200step1Labels := by
      have ha : raw29200step1 = (fun i j => raw29200step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29200step1 raw29200step0; decide +kernel
      have hl : raw29200step1Labels = raw29200step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29200step0 raw29200step0Labels permutation34 permutation2
    _ = mixedMoment B node1098 node1098Labels := by rfl

def raw29201 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29201Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29201step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -1, 0], ![-1, 1, 0], ![-1, -1, 2], ![-3, 1, 2]]
def raw29201step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29201step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![3, -1, -2]]
def raw29201step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29201 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29201 raw29201Labels = mixedMoment B node1863 node1863Labels := by
  calc
    mixedMoment B raw29201 raw29201Labels = mixedMoment B raw29201step0 raw29201step0Labels := by
      have ha : raw29201step0 = (fun i j => raw29201 (permutation646 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29201step0 raw29201; decide +kernel
      have hl : raw29201step0Labels = raw29201Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29201 raw29201Labels permutation646 permutation2
    mixedMoment B raw29201step0 raw29201step0Labels = mixedMoment B raw29201step1 raw29201step1Labels := by
      have ha : raw29201step1 = -raw29201step0 := by apply Matrix.ext; change ∀ i j, raw29201step1 i j = -(raw29201step0 i j); unfold raw29201step1 raw29201step0; decide +kernel
      have hl : raw29201step1Labels = raw29201step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1863 node1863Labels := by rfl

def raw29202 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29202Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29202step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![0, 0, 0], ![3, 0, -3]]
def raw29202step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29202step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![3, 0, -3]]
def raw29202step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29202step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![-1, -1, 2], ![-3, 1, 2]]
def raw29202step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29202step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 1, -2], ![3, -1, -2]]
def raw29202step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29202 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29202 raw29202Labels = mixedMoment B node1950 node1950Labels := by
  calc
    mixedMoment B raw29202 raw29202Labels = mixedMoment B raw29202step0 raw29202step0Labels := by
      have hz : ∀ j, raw29202 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw29202step0 = (fun i j => raw29202 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw29202step0 raw29202; decide +kernel
      have hl : raw29202step0Labels = raw29202Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29202 raw29202Labels permutation520 hz
    mixedMoment B raw29202step0 raw29202step0Labels = mixedMoment B raw29202step1 raw29202step1Labels := by
      have hz : ∀ j, raw29202step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw29202step1 = (fun i j => raw29202step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw29202step1 raw29202step0; decide +kernel
      have hl : raw29202step1Labels = raw29202step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29202step0 raw29202step0Labels permutation104 hz
    mixedMoment B raw29202step1 raw29202step1Labels = mixedMoment B raw29202step2 raw29202step2Labels := by
      have ha : raw29202step2 = (fun i j => raw29202step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29202step2 raw29202step1; decide +kernel
      have hl : raw29202step2Labels = raw29202step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29202step1 raw29202step1Labels permutation31 permutation2
    mixedMoment B raw29202step2 raw29202step2Labels = mixedMoment B raw29202step3 raw29202step3Labels := by
      have ha : raw29202step3 = -raw29202step2 := by apply Matrix.ext; change ∀ i j, raw29202step3 i j = -(raw29202step2 i j); unfold raw29202step3 raw29202step2; decide +kernel
      have hl : raw29202step3Labels = raw29202step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node1950 node1950Labels := by rfl

def raw29203 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29203Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29203step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 0, -1], ![1, -1, 0], ![2, 1, -3]]
def raw29203step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29203step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw29203step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29203 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29203 raw29203Labels = mixedMoment B node2399 node2399Labels := by
  calc
    mixedMoment B raw29203 raw29203Labels = mixedMoment B raw29203step0 raw29203step0Labels := by
      have hz : ∀ j, raw29203 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29203step0 = (fun i j => raw29203 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29203step0 raw29203; decide +kernel
      have hl : raw29203step0Labels = raw29203Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29203 raw29203Labels permutation434 hz
    mixedMoment B raw29203step0 raw29203step0Labels = mixedMoment B raw29203step1 raw29203step1Labels := by
      have ha : raw29203step1 = (fun i j => raw29203step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29203step1 raw29203step0; decide +kernel
      have hl : raw29203step1Labels = raw29203step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29203step0 raw29203step0Labels permutation34 permutation2
    _ = mixedMoment B node2399 node2399Labels := by rfl

def raw29204 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29204Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29204step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw29204step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29204step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw29204step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29204step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw29204step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29204 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29204 raw29204Labels = mixedMoment B node3522 node3522Labels := by
  calc
    mixedMoment B raw29204 raw29204Labels = mixedMoment B raw29204step0 raw29204step0Labels := by
      have hz : ∀ j, raw29204 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29204step0 = (fun i j => raw29204 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29204step0 raw29204; decide +kernel
      have hl : raw29204step0Labels = raw29204Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29204 raw29204Labels permutation434 hz
    mixedMoment B raw29204step0 raw29204step0Labels = mixedMoment B raw29204step1 raw29204step1Labels := by
      have ha : raw29204step1 = (fun i j => raw29204step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29204step1 raw29204step0; decide +kernel
      have hl : raw29204step1Labels = raw29204step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29204step0 raw29204step0Labels permutation151 permutation2
    mixedMoment B raw29204step1 raw29204step1Labels = mixedMoment B raw29204step2 raw29204step2Labels := by
      have ha : raw29204step2 = -raw29204step1 := by apply Matrix.ext; change ∀ i j, raw29204step2 i j = -(raw29204step1 i j); unfold raw29204step2 raw29204step1; decide +kernel
      have hl : raw29204step2Labels = raw29204step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3522 node3522Labels := by rfl

def raw29205 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29205Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29205step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw29205step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29205 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29205 raw29205Labels = mixedMoment B node2670 node2670Labels := by
  calc
    mixedMoment B raw29205 raw29205Labels = mixedMoment B raw29205step0 raw29205step0Labels := by
      have hz : ∀ j, raw29205 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29205step0 = (fun i j => raw29205 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29205step0 raw29205; decide +kernel
      have hl : raw29205step0Labels = raw29205Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29205 raw29205Labels permutation434 hz
    _ = mixedMoment B node2670 node2670Labels := by rfl

def raw29206 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29206Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29206 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29206 raw29206Labels = mixedMoment B node2381 node2381Labels := by
  calc
    _ = mixedMoment B node2381 node2381Labels := by rfl

def raw29207 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29207Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29207step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw29207step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29207 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29207 raw29207Labels = mixedMoment B node2387 node2387Labels := by
  calc
    mixedMoment B raw29207 raw29207Labels = mixedMoment B raw29207step0 raw29207step0Labels := by
      have hz : ∀ j, raw29207 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29207step0 = (fun i j => raw29207 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29207step0 raw29207; decide +kernel
      have hl : raw29207step0Labels = raw29207Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29207 raw29207Labels permutation434 hz
    _ = mixedMoment B node2387 node2387Labels := by rfl

def raw29208 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29208Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29208step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29208step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29208step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 3, -1], ![0, -1, 1], ![0, -3, 3]]
def raw29208step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29208step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw29208step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29208step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![1, 2, -3], ![3, -2, -1]]
def raw29208step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29208 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29208 raw29208Labels = mixedMoment B node4754 node4754Labels := by
  calc
    mixedMoment B raw29208 raw29208Labels = mixedMoment B raw29208step0 raw29208step0Labels := by
      have hz : ∀ j, raw29208 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29208step0 = (fun i j => raw29208 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29208step0 raw29208; decide +kernel
      have hl : raw29208step0Labels = raw29208Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29208 raw29208Labels permutation434 hz
    mixedMoment B raw29208step0 raw29208step0Labels = mixedMoment B raw29208step1 raw29208step1Labels := by
      have hz : ∀ j, raw29208step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29208step1 = (fun i j => raw29208step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29208step1 raw29208step0; decide +kernel
      have hl : raw29208step1Labels = raw29208step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29208step0 raw29208step0Labels permutation80 hz
    mixedMoment B raw29208step1 raw29208step1Labels = mixedMoment B raw29208step2 raw29208step2Labels := by
      have ha : raw29208step2 = (fun i j => raw29208step1 (permutation30 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29208step2 raw29208step1; decide +kernel
      have hl : raw29208step2Labels = raw29208step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29208step1 raw29208step1Labels permutation30 permutation4
    mixedMoment B raw29208step2 raw29208step2Labels = mixedMoment B raw29208step3 raw29208step3Labels := by
      have ha : raw29208step3 = raw29208step2 := by apply Matrix.ext; unfold raw29208step3 raw29208step2; decide +kernel
      have hl : raw29208step2Labels = labelEmbedding7 ∘ raw29208step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29208step2 raw29208step2Labels raw29208step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4754 node4754Labels := by rfl

def raw29209 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29209Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29209step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29209step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29209step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-1, -1, 2], ![-3, 2, 1]]
def raw29209step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29209step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw29209step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29209step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![3, -2, -1]]
def raw29209step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29209 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29209 raw29209Labels = mixedMoment B node4742 node4742Labels := by
  calc
    mixedMoment B raw29209 raw29209Labels = mixedMoment B raw29209step0 raw29209step0Labels := by
      have hz : ∀ j, raw29209 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29209step0 = (fun i j => raw29209 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29209step0 raw29209; decide +kernel
      have hl : raw29209step0Labels = raw29209Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29209 raw29209Labels permutation434 hz
    mixedMoment B raw29209step0 raw29209step0Labels = mixedMoment B raw29209step1 raw29209step1Labels := by
      have ha : raw29209step1 = (fun i j => raw29209step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29209step1 raw29209step0; decide +kernel
      have hl : raw29209step1Labels = raw29209step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29209step0 raw29209step0Labels permutation151 permutation6
    mixedMoment B raw29209step1 raw29209step1Labels = mixedMoment B raw29209step2 raw29209step2Labels := by
      have ha : raw29209step2 = -raw29209step1 := by apply Matrix.ext; change ∀ i j, raw29209step2 i j = -(raw29209step1 i j); unfold raw29209step2 raw29209step1; decide +kernel
      have hl : raw29209step2Labels = raw29209step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29209step2 raw29209step2Labels = mixedMoment B raw29209step3 raw29209step3Labels := by
      have ha : raw29209step3 = raw29209step2 := by apply Matrix.ext; unfold raw29209step3 raw29209step2; decide +kernel
      have hl : raw29209step2Labels = labelEmbedding9 ∘ raw29209step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29209step2 raw29209step2Labels raw29209step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4742 node4742Labels := by rfl

def raw29210 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw29210Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29210step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw29210step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29210step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![-1, 0, 1], ![0, -3, 3]]
def raw29210step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29210step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, -1, 2], ![-3, 2, 1]]
def raw29210step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29210step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw29210step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29210step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![3, -2, -1]]
def raw29210step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29210 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29210 raw29210Labels = mixedMoment B node4843 node4843Labels := by
  calc
    mixedMoment B raw29210 raw29210Labels = mixedMoment B raw29210step0 raw29210step0Labels := by
      have hz : ∀ j, raw29210 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29210step0 = (fun i j => raw29210 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29210step0 raw29210; decide +kernel
      have hl : raw29210step0Labels = raw29210Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29210 raw29210Labels permutation434 hz
    mixedMoment B raw29210step0 raw29210step0Labels = mixedMoment B raw29210step1 raw29210step1Labels := by
      have hz : ∀ j, raw29210step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29210step1 = (fun i j => raw29210step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29210step1 raw29210step0; decide +kernel
      have hl : raw29210step1Labels = raw29210step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29210step0 raw29210step0Labels permutation80 hz
    mixedMoment B raw29210step1 raw29210step1Labels = mixedMoment B raw29210step2 raw29210step2Labels := by
      have ha : raw29210step2 = (fun i j => raw29210step1 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29210step2 raw29210step1; decide +kernel
      have hl : raw29210step2Labels = raw29210step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29210step1 raw29210step1Labels permutation31 permutation6
    mixedMoment B raw29210step2 raw29210step2Labels = mixedMoment B raw29210step3 raw29210step3Labels := by
      have ha : raw29210step3 = -raw29210step2 := by apply Matrix.ext; change ∀ i j, raw29210step3 i j = -(raw29210step2 i j); unfold raw29210step3 raw29210step2; decide +kernel
      have hl : raw29210step3Labels = raw29210step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29210step3 raw29210step3Labels = mixedMoment B raw29210step4 raw29210step4Labels := by
      have ha : raw29210step4 = raw29210step3 := by apply Matrix.ext; unfold raw29210step4 raw29210step3; decide +kernel
      have hl : raw29210step3Labels = labelEmbedding9 ∘ raw29210step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29210step3 raw29210step3Labels raw29210step4Labels labelEmbedding9 hl
    _ = mixedMoment B node4843 node4843Labels := by rfl

def raw29211 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw29211Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29211step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw29211step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29211step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 2, -1], ![0, -1, 1], ![-1, -2, 3]]
def raw29211step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29211step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, -1, -2], ![1, 0, -1], ![-1, -1, 2], ![-3, 2, 1]]
def raw29211step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29211step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw29211step3Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29211step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 1, -2], ![3, -2, -1]]
def raw29211step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29211 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29211 raw29211Labels = mixedMoment B node5109 node5109Labels := by
  calc
    mixedMoment B raw29211 raw29211Labels = mixedMoment B raw29211step0 raw29211step0Labels := by
      have hz : ∀ j, raw29211 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29211step0 = (fun i j => raw29211 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29211step0 raw29211; decide +kernel
      have hl : raw29211step0Labels = raw29211Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29211 raw29211Labels permutation434 hz
    mixedMoment B raw29211step0 raw29211step0Labels = mixedMoment B raw29211step1 raw29211step1Labels := by
      have hz : ∀ j, raw29211step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29211step1 = (fun i j => raw29211step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29211step1 raw29211step0; decide +kernel
      have hl : raw29211step1Labels = raw29211step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29211step0 raw29211step0Labels permutation80 hz
    mixedMoment B raw29211step1 raw29211step1Labels = mixedMoment B raw29211step2 raw29211step2Labels := by
      have ha : raw29211step2 = (fun i j => raw29211step1 (permutation31 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29211step2 raw29211step1; decide +kernel
      have hl : raw29211step2Labels = raw29211step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29211step1 raw29211step1Labels permutation31 permutation6
    mixedMoment B raw29211step2 raw29211step2Labels = mixedMoment B raw29211step3 raw29211step3Labels := by
      have ha : raw29211step3 = -raw29211step2 := by apply Matrix.ext; change ∀ i j, raw29211step3 i j = -(raw29211step2 i j); unfold raw29211step3 raw29211step2; decide +kernel
      have hl : raw29211step3Labels = raw29211step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29211step3 raw29211step3Labels = mixedMoment B raw29211step4 raw29211step4Labels := by
      have ha : raw29211step4 = raw29211step3 := by apply Matrix.ext; unfold raw29211step4 raw29211step3; decide +kernel
      have hl : raw29211step3Labels = labelEmbedding9 ∘ raw29211step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29211step3 raw29211step3Labels raw29211step4Labels labelEmbedding9 hl
    _ = mixedMoment B node5109 node5109Labels := by rfl

def raw29212 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29212Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29212step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29212step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29212step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw29212step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29212step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw29212step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29212step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw29212step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29212 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29212 raw29212Labels = mixedMoment B node4643 node4643Labels := by
  calc
    mixedMoment B raw29212 raw29212Labels = mixedMoment B raw29212step0 raw29212step0Labels := by
      have hz : ∀ j, raw29212 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29212step0 = (fun i j => raw29212 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29212step0 raw29212; decide +kernel
      have hl : raw29212step0Labels = raw29212Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29212 raw29212Labels permutation434 hz
    mixedMoment B raw29212step0 raw29212step0Labels = mixedMoment B raw29212step1 raw29212step1Labels := by
      have ha : raw29212step1 = (fun i j => raw29212step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29212step1 raw29212step0; decide +kernel
      have hl : raw29212step1Labels = raw29212step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29212step0 raw29212step0Labels permutation32 permutation4
    mixedMoment B raw29212step1 raw29212step1Labels = mixedMoment B raw29212step2 raw29212step2Labels := by
      have ha : raw29212step2 = -raw29212step1 := by apply Matrix.ext; change ∀ i j, raw29212step2 i j = -(raw29212step1 i j); unfold raw29212step2 raw29212step1; decide +kernel
      have hl : raw29212step2Labels = raw29212step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29212step2 raw29212step2Labels = mixedMoment B raw29212step3 raw29212step3Labels := by
      have ha : raw29212step3 = raw29212step2 := by apply Matrix.ext; unfold raw29212step3 raw29212step2; decide +kernel
      have hl : raw29212step2Labels = labelEmbedding7 ∘ raw29212step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29212step2 raw29212step2Labels raw29212step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4643 node4643Labels := by rfl

def raw29213 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29213Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29213step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![1, -1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29213step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29213step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw29213step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29213step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw29213step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29213 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29213 raw29213Labels = mixedMoment B node4719 node4719Labels := by
  calc
    mixedMoment B raw29213 raw29213Labels = mixedMoment B raw29213step0 raw29213step0Labels := by
      have hz : ∀ j, raw29213 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29213step0 = (fun i j => raw29213 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29213step0 raw29213; decide +kernel
      have hl : raw29213step0Labels = raw29213Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29213 raw29213Labels permutation434 hz
    mixedMoment B raw29213step0 raw29213step0Labels = mixedMoment B raw29213step1 raw29213step1Labels := by
      have ha : raw29213step1 = (fun i j => raw29213step0 (permutation150 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29213step1 raw29213step0; decide +kernel
      have hl : raw29213step1Labels = raw29213step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29213step0 raw29213step0Labels permutation150 permutation4
    mixedMoment B raw29213step1 raw29213step1Labels = mixedMoment B raw29213step2 raw29213step2Labels := by
      have ha : raw29213step2 = raw29213step1 := by apply Matrix.ext; unfold raw29213step2 raw29213step1; decide +kernel
      have hl : raw29213step1Labels = labelEmbedding7 ∘ raw29213step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29213step1 raw29213step1Labels raw29213step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4719 node4719Labels := by rfl

def raw29214 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw29214Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29214step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw29214step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29214step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 1, 2]]
def raw29214step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29214step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw29214step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29214step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw29214step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29214 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29214 raw29214Labels = mixedMoment B node4788 node4788Labels := by
  calc
    mixedMoment B raw29214 raw29214Labels = mixedMoment B raw29214step0 raw29214step0Labels := by
      have hz : ∀ j, raw29214 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29214step0 = (fun i j => raw29214 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29214step0 raw29214; decide +kernel
      have hl : raw29214step0Labels = raw29214Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29214 raw29214Labels permutation434 hz
    mixedMoment B raw29214step0 raw29214step0Labels = mixedMoment B raw29214step1 raw29214step1Labels := by
      have ha : raw29214step1 = (fun i j => raw29214step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29214step1 raw29214step0; decide +kernel
      have hl : raw29214step1Labels = raw29214step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29214step0 raw29214step0Labels permutation151 permutation6
    mixedMoment B raw29214step1 raw29214step1Labels = mixedMoment B raw29214step2 raw29214step2Labels := by
      have ha : raw29214step2 = -raw29214step1 := by apply Matrix.ext; change ∀ i j, raw29214step2 i j = -(raw29214step1 i j); unfold raw29214step2 raw29214step1; decide +kernel
      have hl : raw29214step2Labels = raw29214step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29214step2 raw29214step2Labels = mixedMoment B raw29214step3 raw29214step3Labels := by
      have ha : raw29214step3 = raw29214step2 := by apply Matrix.ext; unfold raw29214step3 raw29214step2; decide +kernel
      have hl : raw29214step2Labels = labelEmbedding9 ∘ raw29214step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29214step2 raw29214step2Labels raw29214step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4788 node4788Labels := by rfl

def raw29215 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![0, 0, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw29215Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29215step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw29215step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29215step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29215step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29215step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29215step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29215 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29215 raw29215Labels = mixedMoment B node5000 node5000Labels := by
  calc
    mixedMoment B raw29215 raw29215Labels = mixedMoment B raw29215step0 raw29215step0Labels := by
      have hz : ∀ j, raw29215 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29215step0 = (fun i j => raw29215 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29215step0 raw29215; decide +kernel
      have hl : raw29215step0Labels = raw29215Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29215 raw29215Labels permutation434 hz
    mixedMoment B raw29215step0 raw29215step0Labels = mixedMoment B raw29215step1 raw29215step1Labels := by
      have ha : raw29215step1 = (fun i j => raw29215step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29215step1 raw29215step0; decide +kernel
      have hl : raw29215step1Labels = raw29215step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29215step0 raw29215step0Labels permutation32 permutation6
    mixedMoment B raw29215step1 raw29215step1Labels = mixedMoment B raw29215step2 raw29215step2Labels := by
      have ha : raw29215step2 = raw29215step1 := by apply Matrix.ext; unfold raw29215step2 raw29215step1; decide +kernel
      have hl : raw29215step1Labels = labelEmbedding9 ∘ raw29215step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29215step1 raw29215step1Labels raw29215step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5000 node5000Labels := by rfl

def raw29216 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29216Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29216step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29216step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29216step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw29216step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29216step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw29216step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29216step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw29216step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29216 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29216 raw29216Labels = mixedMoment B node4643 node4643Labels := by
  calc
    mixedMoment B raw29216 raw29216Labels = mixedMoment B raw29216step0 raw29216step0Labels := by
      have hz : ∀ j, raw29216 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29216step0 = (fun i j => raw29216 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29216step0 raw29216; decide +kernel
      have hl : raw29216step0Labels = raw29216Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29216 raw29216Labels permutation346 hz
    mixedMoment B raw29216step0 raw29216step0Labels = mixedMoment B raw29216step1 raw29216step1Labels := by
      have ha : raw29216step1 = (fun i j => raw29216step0 (permutation32 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29216step1 raw29216step0; decide +kernel
      have hl : raw29216step1Labels = raw29216step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29216step0 raw29216step0Labels permutation32 permutation4
    mixedMoment B raw29216step1 raw29216step1Labels = mixedMoment B raw29216step2 raw29216step2Labels := by
      have ha : raw29216step2 = -raw29216step1 := by apply Matrix.ext; change ∀ i j, raw29216step2 i j = -(raw29216step1 i j); unfold raw29216step2 raw29216step1; decide +kernel
      have hl : raw29216step2Labels = raw29216step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29216step2 raw29216step2Labels = mixedMoment B raw29216step3 raw29216step3Labels := by
      have ha : raw29216step3 = raw29216step2 := by apply Matrix.ext; unfold raw29216step3 raw29216step2; decide +kernel
      have hl : raw29216step2Labels = labelEmbedding7 ∘ raw29216step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29216step2 raw29216step2Labels raw29216step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4643 node4643Labels := by rfl

def raw29217 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29217Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29217step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![1, -1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29217step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29217step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw29217step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29217step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![2, 1, -3], ![3, -2, -1]]
def raw29217step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29217 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29217 raw29217Labels = mixedMoment B node4719 node4719Labels := by
  calc
    mixedMoment B raw29217 raw29217Labels = mixedMoment B raw29217step0 raw29217step0Labels := by
      have hz : ∀ j, raw29217 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29217step0 = (fun i j => raw29217 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29217step0 raw29217; decide +kernel
      have hl : raw29217step0Labels = raw29217Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29217 raw29217Labels permutation346 hz
    mixedMoment B raw29217step0 raw29217step0Labels = mixedMoment B raw29217step1 raw29217step1Labels := by
      have ha : raw29217step1 = (fun i j => raw29217step0 (permutation150 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29217step1 raw29217step0; decide +kernel
      have hl : raw29217step1Labels = raw29217step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29217step0 raw29217step0Labels permutation150 permutation4
    mixedMoment B raw29217step1 raw29217step1Labels = mixedMoment B raw29217step2 raw29217step2Labels := by
      have ha : raw29217step2 = raw29217step1 := by apply Matrix.ext; unfold raw29217step2 raw29217step1; decide +kernel
      have hl : raw29217step1Labels = labelEmbedding7 ∘ raw29217step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29217step1 raw29217step1Labels raw29217step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4719 node4719Labels := by rfl

def raw29218 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![0, -3, 3]]
def raw29218Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29218step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw29218step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29218step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw29218step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29218 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29218 raw29218Labels = mixedMoment B node4710 node4710Labels := by
  calc
    mixedMoment B raw29218 raw29218Labels = mixedMoment B raw29218step0 raw29218step0Labels := by
      have ha : raw29218step0 = (fun i j => raw29218 (permutation688 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29218step0 raw29218; decide +kernel
      have hl : raw29218step0Labels = raw29218Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29218 raw29218Labels permutation688 permutation4
    mixedMoment B raw29218step0 raw29218step0Labels = mixedMoment B raw29218step1 raw29218step1Labels := by
      have ha : raw29218step1 = raw29218step0 := by apply Matrix.ext; unfold raw29218step1 raw29218step0; decide +kernel
      have hl : raw29218step0Labels = labelEmbedding7 ∘ raw29218step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29218step0 raw29218step0Labels raw29218step1Labels labelEmbedding7 hl
    _ = mixedMoment B node4710 node4710Labels := by rfl

def raw29219 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw29219Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29219step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![-1, 0, 1], ![0, -3, 3]]
def raw29219step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29219step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 1, 2]]
def raw29219step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29219step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw29219step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29219step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw29219step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29219 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29219 raw29219Labels = mixedMoment B node4788 node4788Labels := by
  calc
    mixedMoment B raw29219 raw29219Labels = mixedMoment B raw29219step0 raw29219step0Labels := by
      have hz : ∀ j, raw29219 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29219step0 = (fun i j => raw29219 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29219step0 raw29219; decide +kernel
      have hl : raw29219step0Labels = raw29219Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29219 raw29219Labels permutation346 hz
    mixedMoment B raw29219step0 raw29219step0Labels = mixedMoment B raw29219step1 raw29219step1Labels := by
      have ha : raw29219step1 = (fun i j => raw29219step0 (permutation151 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29219step1 raw29219step0; decide +kernel
      have hl : raw29219step1Labels = raw29219step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29219step0 raw29219step0Labels permutation151 permutation6
    mixedMoment B raw29219step1 raw29219step1Labels = mixedMoment B raw29219step2 raw29219step2Labels := by
      have ha : raw29219step2 = -raw29219step1 := by apply Matrix.ext; change ∀ i j, raw29219step2 i j = -(raw29219step1 i j); unfold raw29219step2 raw29219step1; decide +kernel
      have hl : raw29219step2Labels = raw29219step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29219step2 raw29219step2Labels = mixedMoment B raw29219step3 raw29219step3Labels := by
      have ha : raw29219step3 = raw29219step2 := by apply Matrix.ext; unfold raw29219step3 raw29219step2; decide +kernel
      have hl : raw29219step2Labels = labelEmbedding9 ∘ raw29219step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29219step2 raw29219step2Labels raw29219step3Labels labelEmbedding9 hl
    _ = mixedMoment B node4788 node4788Labels := by rfl

def raw29220 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw29220Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29220step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -1, 0], ![0, -1, 1], ![-1, -2, 3]]
def raw29220step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29220step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29220step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29220step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29220step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29220 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29220 raw29220Labels = mixedMoment B node5000 node5000Labels := by
  calc
    mixedMoment B raw29220 raw29220Labels = mixedMoment B raw29220step0 raw29220step0Labels := by
      have hz : ∀ j, raw29220 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29220step0 = (fun i j => raw29220 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29220step0 raw29220; decide +kernel
      have hl : raw29220step0Labels = raw29220Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29220 raw29220Labels permutation346 hz
    mixedMoment B raw29220step0 raw29220step0Labels = mixedMoment B raw29220step1 raw29220step1Labels := by
      have ha : raw29220step1 = (fun i j => raw29220step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29220step1 raw29220step0; decide +kernel
      have hl : raw29220step1Labels = raw29220step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29220step0 raw29220step0Labels permutation32 permutation6
    mixedMoment B raw29220step1 raw29220step1Labels = mixedMoment B raw29220step2 raw29220step2Labels := by
      have ha : raw29220step2 = raw29220step1 := by apply Matrix.ext; unfold raw29220step2 raw29220step1; decide +kernel
      have hl : raw29220step1Labels = labelEmbedding9 ∘ raw29220step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29220step1 raw29220step1Labels raw29220step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5000 node5000Labels := by rfl

def raw29221 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -3, 3]]
def raw29221Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29221step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![0, -3, 3]]
def raw29221step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29221step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![1, -2, 1], ![0, -3, 3]]
def raw29221step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29221step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw29221step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29221step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw29221step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29221 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29221 raw29221Labels = mixedMoment B node4655 node4655Labels := by
  calc
    mixedMoment B raw29221 raw29221Labels = mixedMoment B raw29221step0 raw29221step0Labels := by
      have hz : ∀ j, raw29221 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29221step0 = (fun i j => raw29221 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29221step0 raw29221; decide +kernel
      have hl : raw29221step0Labels = raw29221Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29221 raw29221Labels permutation434 hz
    mixedMoment B raw29221step0 raw29221step0Labels = mixedMoment B raw29221step1 raw29221step1Labels := by
      have hz : ∀ j, raw29221step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29221step1 = (fun i j => raw29221step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29221step1 raw29221step0; decide +kernel
      have hl : raw29221step1Labels = raw29221step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29221step0 raw29221step0Labels permutation80 hz
    mixedMoment B raw29221step1 raw29221step1Labels = mixedMoment B raw29221step2 raw29221step2Labels := by
      have ha : raw29221step2 = (fun i j => raw29221step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29221step2 raw29221step1; decide +kernel
      have hl : raw29221step2Labels = raw29221step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29221step1 raw29221step1Labels permutation31 permutation4
    mixedMoment B raw29221step2 raw29221step2Labels = mixedMoment B raw29221step3 raw29221step3Labels := by
      have ha : raw29221step3 = raw29221step2 := by apply Matrix.ext; unfold raw29221step3 raw29221step2; decide +kernel
      have hl : raw29221step2Labels = labelEmbedding7 ∘ raw29221step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29221step2 raw29221step2Labels raw29221step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4655 node4655Labels := by rfl

def raw29222 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![0, -3, 3]]
def raw29222Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29222step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![0, 0, 0], ![1, -2, 1], ![0, -3, 3]]
def raw29222step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29222step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![1, -2, 1], ![0, -3, 3]]
def raw29222step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29222step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![2, 1, -3], ![3, -2, -1]]
def raw29222step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29222step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![2, 1, -3], ![3, -2, -1]]
def raw29222step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29222 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29222 raw29222Labels = mixedMoment B node4657 node4657Labels := by
  calc
    mixedMoment B raw29222 raw29222Labels = mixedMoment B raw29222step0 raw29222step0Labels := by
      have hz : ∀ j, raw29222 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29222step0 = (fun i j => raw29222 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29222step0 raw29222; decide +kernel
      have hl : raw29222step0Labels = raw29222Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29222 raw29222Labels permutation434 hz
    mixedMoment B raw29222step0 raw29222step0Labels = mixedMoment B raw29222step1 raw29222step1Labels := by
      have hz : ∀ j, raw29222step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29222step1 = (fun i j => raw29222step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29222step1 raw29222step0; decide +kernel
      have hl : raw29222step1Labels = raw29222step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29222step0 raw29222step0Labels permutation80 hz
    mixedMoment B raw29222step1 raw29222step1Labels = mixedMoment B raw29222step2 raw29222step2Labels := by
      have ha : raw29222step2 = (fun i j => raw29222step1 (permutation30 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29222step2 raw29222step1; decide +kernel
      have hl : raw29222step2Labels = raw29222step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29222step1 raw29222step1Labels permutation30 permutation4
    mixedMoment B raw29222step2 raw29222step2Labels = mixedMoment B raw29222step3 raw29222step3Labels := by
      have ha : raw29222step3 = raw29222step2 := by apply Matrix.ext; unfold raw29222step3 raw29222step2; decide +kernel
      have hl : raw29222step2Labels = labelEmbedding7 ∘ raw29222step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29222step2 raw29222step2Labels raw29222step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4657 node4657Labels := by rfl

def raw29223 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, -3, 3]]
def raw29223Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29223step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![-1, 1, 0], ![1, -2, 1], ![0, -3, 3]]
def raw29223step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29223step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw29223step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29223step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw29223step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29223 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29223 raw29223Labels = mixedMoment B node4645 node4645Labels := by
  calc
    mixedMoment B raw29223 raw29223Labels = mixedMoment B raw29223step0 raw29223step0Labels := by
      have hz : ∀ j, raw29223 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29223step0 = (fun i j => raw29223 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29223step0 raw29223; decide +kernel
      have hl : raw29223step0Labels = raw29223Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29223 raw29223Labels permutation434 hz
    mixedMoment B raw29223step0 raw29223step0Labels = mixedMoment B raw29223step1 raw29223step1Labels := by
      have ha : raw29223step1 = (fun i j => raw29223step0 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29223step1 raw29223step0; decide +kernel
      have hl : raw29223step1Labels = raw29223step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29223step0 raw29223step0Labels permutation151 permutation4
    mixedMoment B raw29223step1 raw29223step1Labels = mixedMoment B raw29223step2 raw29223step2Labels := by
      have ha : raw29223step2 = raw29223step1 := by apply Matrix.ext; unfold raw29223step2 raw29223step1; decide +kernel
      have hl : raw29223step1Labels = labelEmbedding7 ∘ raw29223step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29223step1 raw29223step1Labels raw29223step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4645 node4645Labels := by rfl

def raw29224 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw29224Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29224step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![1, -2, 1], ![-1, -2, 3]]
def raw29224step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29224step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![1, -2, 1], ![-1, -2, 3]]
def raw29224step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29224step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw29224step2Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw29224step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, 1, -2], ![3, -1, -2]]
def raw29224step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29224 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29224 raw29224Labels = mixedMoment B node5021 node5021Labels := by
  calc
    mixedMoment B raw29224 raw29224Labels = mixedMoment B raw29224step0 raw29224step0Labels := by
      have hz : ∀ j, raw29224 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29224step0 = (fun i j => raw29224 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29224step0 raw29224; decide +kernel
      have hl : raw29224step0Labels = raw29224Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29224 raw29224Labels permutation434 hz
    mixedMoment B raw29224step0 raw29224step0Labels = mixedMoment B raw29224step1 raw29224step1Labels := by
      have hz : ∀ j, raw29224step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29224step1 = (fun i j => raw29224step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29224step1 raw29224step0; decide +kernel
      have hl : raw29224step1Labels = raw29224step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29224step0 raw29224step0Labels permutation80 hz
    mixedMoment B raw29224step1 raw29224step1Labels = mixedMoment B raw29224step2 raw29224step2Labels := by
      have ha : raw29224step2 = (fun i j => raw29224step1 (permutation8 i) (permutation6 j)) := by apply Matrix.ext; unfold raw29224step2 raw29224step1; decide +kernel
      have hl : raw29224step2Labels = raw29224step1Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29224step1 raw29224step1Labels permutation8 permutation6
    mixedMoment B raw29224step2 raw29224step2Labels = mixedMoment B raw29224step3 raw29224step3Labels := by
      have ha : raw29224step3 = raw29224step2 := by apply Matrix.ext; unfold raw29224step3 raw29224step2; decide +kernel
      have hl : raw29224step2Labels = labelEmbedding9 ∘ raw29224step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29224step2 raw29224step2Labels raw29224step3Labels labelEmbedding9 hl
    _ = mixedMoment B node5021 node5021Labels := by rfl

def raw29225 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -4, 3]]
def raw29225Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29225step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![0, 0, 0], ![0, -1, 1], ![1, -4, 3]]
def raw29225step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29225step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 2, -1], ![0, -1, 1], ![1, -4, 3]]
def raw29225step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29225step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, -1, -1], ![3, 0, -3]]
def raw29225step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29225step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, -1, -1], ![3, 0, -3]]
def raw29225step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29225 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29225 raw29225Labels = mixedMoment B node4317 node4317Labels := by
  calc
    mixedMoment B raw29225 raw29225Labels = mixedMoment B raw29225step0 raw29225step0Labels := by
      have hz : ∀ j, raw29225 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29225step0 = (fun i j => raw29225 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29225step0 raw29225; decide +kernel
      have hl : raw29225step0Labels = raw29225Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29225 raw29225Labels permutation434 hz
    mixedMoment B raw29225step0 raw29225step0Labels = mixedMoment B raw29225step1 raw29225step1Labels := by
      have hz : ∀ j, raw29225step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29225step1 = (fun i j => raw29225step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29225step1 raw29225step0; decide +kernel
      have hl : raw29225step1Labels = raw29225step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29225step0 raw29225step0Labels permutation80 hz
    mixedMoment B raw29225step1 raw29225step1Labels = mixedMoment B raw29225step2 raw29225step2Labels := by
      have ha : raw29225step2 = (fun i j => raw29225step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29225step2 raw29225step1; decide +kernel
      have hl : raw29225step2Labels = raw29225step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29225step1 raw29225step1Labels permutation31 permutation4
    mixedMoment B raw29225step2 raw29225step2Labels = mixedMoment B raw29225step3 raw29225step3Labels := by
      have ha : raw29225step3 = raw29225step2 := by apply Matrix.ext; unfold raw29225step3 raw29225step2; decide +kernel
      have hl : raw29225step2Labels = labelEmbedding7 ∘ raw29225step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29225step2 raw29225step2Labels raw29225step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4317 node4317Labels := by rfl

def raw29226 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, -4, 3]]
def raw29226Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29226step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![0, 0, 0], ![0, -1, 1], ![1, -4, 3]]
def raw29226step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29226step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 3, -1], ![0, -1, 1], ![1, -4, 3]]
def raw29226step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29226step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, 1, -3], ![3, -2, -1]]
def raw29226step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29226step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![2, 1, -3], ![3, -2, -1]]
def raw29226step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29226 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29226 raw29226Labels = mixedMoment B node4319 node4319Labels := by
  calc
    mixedMoment B raw29226 raw29226Labels = mixedMoment B raw29226step0 raw29226step0Labels := by
      have hz : ∀ j, raw29226 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29226step0 = (fun i j => raw29226 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29226step0 raw29226; decide +kernel
      have hl : raw29226step0Labels = raw29226Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29226 raw29226Labels permutation434 hz
    mixedMoment B raw29226step0 raw29226step0Labels = mixedMoment B raw29226step1 raw29226step1Labels := by
      have hz : ∀ j, raw29226step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29226step1 = (fun i j => raw29226step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29226step1 raw29226step0; decide +kernel
      have hl : raw29226step1Labels = raw29226step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29226step0 raw29226step0Labels permutation80 hz
    mixedMoment B raw29226step1 raw29226step1Labels = mixedMoment B raw29226step2 raw29226step2Labels := by
      have ha : raw29226step2 = (fun i j => raw29226step1 (permutation30 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29226step2 raw29226step1; decide +kernel
      have hl : raw29226step2Labels = raw29226step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29226step1 raw29226step1Labels permutation30 permutation4
    mixedMoment B raw29226step2 raw29226step2Labels = mixedMoment B raw29226step3 raw29226step3Labels := by
      have ha : raw29226step3 = raw29226step2 := by apply Matrix.ext; unfold raw29226step3 raw29226step2; decide +kernel
      have hl : raw29226step2Labels = labelEmbedding7 ∘ raw29226step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29226step2 raw29226step2Labels raw29226step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4319 node4319Labels := by rfl

def raw29227 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, -4, 3]]
def raw29227Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29227step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![-1, 1, 0], ![0, -1, 1], ![1, -4, 3]]
def raw29227step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29227step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw29227step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29227step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 1, -3]]
def raw29227step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29227 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29227 raw29227Labels = mixedMoment B node4304 node4304Labels := by
  calc
    mixedMoment B raw29227 raw29227Labels = mixedMoment B raw29227step0 raw29227step0Labels := by
      have hz : ∀ j, raw29227 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29227step0 = (fun i j => raw29227 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29227step0 raw29227; decide +kernel
      have hl : raw29227step0Labels = raw29227Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29227 raw29227Labels permutation434 hz
    mixedMoment B raw29227step0 raw29227step0Labels = mixedMoment B raw29227step1 raw29227step1Labels := by
      have ha : raw29227step1 = (fun i j => raw29227step0 (permutation151 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29227step1 raw29227step0; decide +kernel
      have hl : raw29227step1Labels = raw29227step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29227step0 raw29227step0Labels permutation151 permutation4
    mixedMoment B raw29227step1 raw29227step1Labels = mixedMoment B raw29227step2 raw29227step2Labels := by
      have ha : raw29227step2 = raw29227step1 := by apply Matrix.ext; unfold raw29227step2 raw29227step1; decide +kernel
      have hl : raw29227step1Labels = labelEmbedding7 ∘ raw29227step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29227step1 raw29227step1Labels raw29227step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4304 node4304Labels := by rfl

def raw29228 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![0, 0, 0], ![-1, 0, 1], ![1, -4, 3]]
def raw29228Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29228step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![0, 0, 0], ![-1, 0, 1], ![1, -4, 3]]
def raw29228step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29228step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 2, -1], ![-1, 0, 1], ![1, -4, 3]]
def raw29228step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29228step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw29228step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw29228step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw29228step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29228 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29228 raw29228Labels = mixedMoment B node4431 node4431Labels := by
  calc
    mixedMoment B raw29228 raw29228Labels = mixedMoment B raw29228step0 raw29228step0Labels := by
      have hz : ∀ j, raw29228 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29228step0 = (fun i j => raw29228 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29228step0 raw29228; decide +kernel
      have hl : raw29228step0Labels = raw29228Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29228 raw29228Labels permutation434 hz
    mixedMoment B raw29228step0 raw29228step0Labels = mixedMoment B raw29228step1 raw29228step1Labels := by
      have hz : ∀ j, raw29228step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29228step1 = (fun i j => raw29228step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29228step1 raw29228step0; decide +kernel
      have hl : raw29228step1Labels = raw29228step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29228step0 raw29228step0Labels permutation80 hz
    mixedMoment B raw29228step1 raw29228step1Labels = mixedMoment B raw29228step2 raw29228step2Labels := by
      have ha : raw29228step2 = (fun i j => raw29228step1 (permutation31 i) (permutation4 j)) := by apply Matrix.ext; unfold raw29228step2 raw29228step1; decide +kernel
      have hl : raw29228step2Labels = raw29228step1Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29228step1 raw29228step1Labels permutation31 permutation4
    mixedMoment B raw29228step2 raw29228step2Labels = mixedMoment B raw29228step3 raw29228step3Labels := by
      have ha : raw29228step3 = raw29228step2 := by apply Matrix.ext; unfold raw29228step3 raw29228step2; decide +kernel
      have hl : raw29228step2Labels = labelEmbedding7 ∘ raw29228step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29228step2 raw29228step2Labels raw29228step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4431 node4431Labels := by rfl

def raw29229 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29229Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29229step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29229step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29229step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29229step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29229step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-2, 2, 0], ![-2, -1, 3]]
def raw29229step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29229step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29229step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29229 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29229 raw29229Labels = mixedMoment B node4845 node4845Labels := by
  calc
    mixedMoment B raw29229 raw29229Labels = mixedMoment B raw29229step0 raw29229step0Labels := by
      have hz : ∀ j, raw29229 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29229step0 = (fun i j => raw29229 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29229step0 raw29229; decide +kernel
      have hl : raw29229step0Labels = raw29229Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29229 raw29229Labels permutation434 hz
    mixedMoment B raw29229step0 raw29229step0Labels = mixedMoment B raw29229step1 raw29229step1Labels := by
      have hz : ∀ j, raw29229step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29229step1 = (fun i j => raw29229step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29229step1 raw29229step0; decide +kernel
      have hl : raw29229step1Labels = raw29229step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29229step0 raw29229step0Labels permutation80 hz
    mixedMoment B raw29229step1 raw29229step1Labels = mixedMoment B raw29229step2 raw29229step2Labels := by
      have ha : raw29229step2 = (fun i j => raw29229step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29229step2 raw29229step1; decide +kernel
      have hl : raw29229step2Labels = raw29229step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29229step1 raw29229step1Labels permutation31 permutation2
    mixedMoment B raw29229step2 raw29229step2Labels = mixedMoment B raw29229step3 raw29229step3Labels := by
      have ha : raw29229step3 = -raw29229step2 := by apply Matrix.ext; change ∀ i j, raw29229step3 i j = -(raw29229step2 i j); unfold raw29229step3 raw29229step2; decide +kernel
      have hl : raw29229step3Labels = raw29229step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4845 node4845Labels := by rfl

def raw29230 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29230Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29230step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29230step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29230step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw29230step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29230step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29230step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29230 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29230 raw29230Labels = mixedMoment B node4832 node4832Labels := by
  calc
    mixedMoment B raw29230 raw29230Labels = mixedMoment B raw29230step0 raw29230step0Labels := by
      have hz : ∀ j, raw29230 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29230step0 = (fun i j => raw29230 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29230step0 raw29230; decide +kernel
      have hl : raw29230step0Labels = raw29230Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29230 raw29230Labels permutation434 hz
    mixedMoment B raw29230step0 raw29230step0Labels = mixedMoment B raw29230step1 raw29230step1Labels := by
      have ha : raw29230step1 = (fun i j => raw29230step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29230step1 raw29230step0; decide +kernel
      have hl : raw29230step1Labels = raw29230step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29230step0 raw29230step0Labels permutation149 permutation2
    mixedMoment B raw29230step1 raw29230step1Labels = mixedMoment B raw29230step2 raw29230step2Labels := by
      have ha : raw29230step2 = -raw29230step1 := by apply Matrix.ext; change ∀ i j, raw29230step2 i j = -(raw29230step1 i j); unfold raw29230step2 raw29230step1; decide +kernel
      have hl : raw29230step2Labels = raw29230step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4832 node4832Labels := by rfl

def raw29231 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29231Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29231step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29231step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29231step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-2, -1, 3]]
def raw29231step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29231step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29231step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29231 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29231 raw29231Labels = mixedMoment B node4832 node4832Labels := by
  calc
    mixedMoment B raw29231 raw29231Labels = mixedMoment B raw29231step0 raw29231step0Labels := by
      have hz : ∀ j, raw29231 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29231step0 = (fun i j => raw29231 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29231step0 raw29231; decide +kernel
      have hl : raw29231step0Labels = raw29231Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29231 raw29231Labels permutation346 hz
    mixedMoment B raw29231step0 raw29231step0Labels = mixedMoment B raw29231step1 raw29231step1Labels := by
      have ha : raw29231step1 = (fun i j => raw29231step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29231step1 raw29231step0; decide +kernel
      have hl : raw29231step1Labels = raw29231step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29231step0 raw29231step0Labels permutation149 permutation2
    mixedMoment B raw29231step1 raw29231step1Labels = mixedMoment B raw29231step2 raw29231step2Labels := by
      have ha : raw29231step2 = -raw29231step1 := by apply Matrix.ext; change ∀ i j, raw29231step2 i j = -(raw29231step1 i j); unfold raw29231step2 raw29231step1; decide +kernel
      have hl : raw29231step2Labels = raw29231step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4832 node4832Labels := by rfl

def raw29232 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29232Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29232step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29232step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29232step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29232step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29232step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![3, 0, -3]]
def raw29232step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29232step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw29232step3Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29232step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw29232step4Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29232 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29232 raw29232Labels = mixedMoment B node4897 node4897Labels := by
  calc
    mixedMoment B raw29232 raw29232Labels = mixedMoment B raw29232step0 raw29232step0Labels := by
      have hz : ∀ j, raw29232 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw29232step0 = (fun i j => raw29232 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw29232step0 raw29232; decide +kernel
      have hl : raw29232step0Labels = raw29232Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29232 raw29232Labels permutation520 hz
    mixedMoment B raw29232step0 raw29232step0Labels = mixedMoment B raw29232step1 raw29232step1Labels := by
      have hz : ∀ j, raw29232step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw29232step1 = (fun i j => raw29232step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw29232step1 raw29232step0; decide +kernel
      have hl : raw29232step1Labels = raw29232step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29232step0 raw29232step0Labels permutation104 hz
    mixedMoment B raw29232step1 raw29232step1Labels = mixedMoment B raw29232step2 raw29232step2Labels := by
      have hz : ∀ j, raw29232step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw29232step2 = (fun i j => raw29232step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw29232step2 raw29232step1; decide +kernel
      have hl : raw29232step2Labels = raw29232step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29232step1 raw29232step1Labels permutation20 hz
    mixedMoment B raw29232step2 raw29232step2Labels = mixedMoment B raw29232step3 raw29232step3Labels := by
      have ha : raw29232step3 = (fun i j => raw29232step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29232step3 raw29232step2; decide +kernel
      have hl : raw29232step3Labels = raw29232step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29232step2 raw29232step2Labels permutation7 permutation7
    mixedMoment B raw29232step3 raw29232step3Labels = mixedMoment B raw29232step4 raw29232step4Labels := by
      have ha : raw29232step4 = raw29232step3 := by apply Matrix.ext; unfold raw29232step4 raw29232step3; decide +kernel
      have hl : raw29232step3Labels = labelEmbedding10 ∘ raw29232step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29232step3 raw29232step3Labels raw29232step4Labels labelEmbedding10 hl
    _ = mixedMoment B node4897 node4897Labels := by rfl

def raw29233 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29233Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29233step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29233step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29233step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29233step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29233step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw29233step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29233step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw29233step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29233 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29233 raw29233Labels = mixedMoment B node5261 node5261Labels := by
  calc
    mixedMoment B raw29233 raw29233Labels = mixedMoment B raw29233step0 raw29233step0Labels := by
      have hz : ∀ j, raw29233 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29233step0 = (fun i j => raw29233 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29233step0 raw29233; decide +kernel
      have hl : raw29233step0Labels = raw29233Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29233 raw29233Labels permutation434 hz
    mixedMoment B raw29233step0 raw29233step0Labels = mixedMoment B raw29233step1 raw29233step1Labels := by
      have hz : ∀ j, raw29233step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29233step1 = (fun i j => raw29233step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29233step1 raw29233step0; decide +kernel
      have hl : raw29233step1Labels = raw29233step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29233step0 raw29233step0Labels permutation80 hz
    mixedMoment B raw29233step1 raw29233step1Labels = mixedMoment B raw29233step2 raw29233step2Labels := by
      have ha : raw29233step2 = (fun i j => raw29233step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29233step2 raw29233step1; decide +kernel
      have hl : raw29233step2Labels = raw29233step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29233step1 raw29233step1Labels permutation31 permutation7
    mixedMoment B raw29233step2 raw29233step2Labels = mixedMoment B raw29233step3 raw29233step3Labels := by
      have ha : raw29233step3 = raw29233step2 := by apply Matrix.ext; unfold raw29233step3 raw29233step2; decide +kernel
      have hl : raw29233step2Labels = labelEmbedding10 ∘ raw29233step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29233step2 raw29233step2Labels raw29233step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5261 node5261Labels := by rfl

def raw29234 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29234Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29234step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29234step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29234 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29234 raw29234Labels = mixedMoment B node4678 node4678Labels := by
  calc
    mixedMoment B raw29234 raw29234Labels = mixedMoment B raw29234step0 raw29234step0Labels := by
      have hz : ∀ j, raw29234 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29234step0 = (fun i j => raw29234 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29234step0 raw29234; decide +kernel
      have hl : raw29234step0Labels = raw29234Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29234 raw29234Labels permutation434 hz
    _ = mixedMoment B node4678 node4678Labels := by rfl

def raw29235 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29235Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29235step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29235step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29235 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29235 raw29235Labels = mixedMoment B node4759 node4759Labels := by
  calc
    mixedMoment B raw29235 raw29235Labels = mixedMoment B raw29235step0 raw29235step0Labels := by
      have ha : raw29235step0 = (fun i j => raw29235 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29235step0 raw29235; decide +kernel
      have hl : raw29235step0Labels = raw29235Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29235 raw29235Labels permutation158 permutation2
    _ = mixedMoment B node4759 node4759Labels := by rfl

def raw29236 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29236Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29236step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29236step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29236step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29236step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29236 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29236 raw29236Labels = mixedMoment B node4837 node4837Labels := by
  calc
    mixedMoment B raw29236 raw29236Labels = mixedMoment B raw29236step0 raw29236step0Labels := by
      have hz : ∀ j, raw29236 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw29236step0 = (fun i j => raw29236 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw29236step0 raw29236; decide +kernel
      have hl : raw29236step0Labels = raw29236Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29236 raw29236Labels permutation520 hz
    mixedMoment B raw29236step0 raw29236step0Labels = mixedMoment B raw29236step1 raw29236step1Labels := by
      have hz : ∀ j, raw29236step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw29236step1 = (fun i j => raw29236step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw29236step1 raw29236step0; decide +kernel
      have hl : raw29236step1Labels = raw29236step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29236step0 raw29236step0Labels permutation104 hz
    _ = mixedMoment B node4837 node4837Labels := by rfl

def raw29237 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29237Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29237step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29237step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29237 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29237 raw29237Labels = mixedMoment B node4832 node4832Labels := by
  calc
    mixedMoment B raw29237 raw29237Labels = mixedMoment B raw29237step0 raw29237step0Labels := by
      have hz : ∀ j, raw29237 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29237step0 = (fun i j => raw29237 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29237step0 raw29237; decide +kernel
      have hl : raw29237step0Labels = raw29237Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29237 raw29237Labels permutation434 hz
    _ = mixedMoment B node4832 node4832Labels := by rfl

def raw29238 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29238Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29238step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29238step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29238 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29238 raw29238Labels = mixedMoment B node4678 node4678Labels := by
  calc
    mixedMoment B raw29238 raw29238Labels = mixedMoment B raw29238step0 raw29238step0Labels := by
      have hz : ∀ j, raw29238 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29238step0 = (fun i j => raw29238 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29238step0 raw29238; decide +kernel
      have hl : raw29238step0Labels = raw29238Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29238 raw29238Labels permutation346 hz
    _ = mixedMoment B node4678 node4678Labels := by rfl

def raw29239 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29239Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29239 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29239 raw29239Labels = mixedMoment B node4759 node4759Labels := by
  calc
    _ = mixedMoment B node4759 node4759Labels := by rfl

def raw29240 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29240Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29240step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29240step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29240step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29240step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29240 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29240 raw29240Labels = mixedMoment B node4837 node4837Labels := by
  calc
    mixedMoment B raw29240 raw29240Labels = mixedMoment B raw29240step0 raw29240step0Labels := by
      have hz : ∀ j, raw29240 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw29240step0 = (fun i j => raw29240 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw29240step0 raw29240; decide +kernel
      have hl : raw29240step0Labels = raw29240Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29240 raw29240Labels permutation520 hz
    mixedMoment B raw29240step0 raw29240step0Labels = mixedMoment B raw29240step1 raw29240step1Labels := by
      have hz : ∀ j, raw29240step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29240step1 = (fun i j => raw29240step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29240step1 raw29240step0; decide +kernel
      have hl : raw29240step1Labels = raw29240step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29240step0 raw29240step0Labels permutation80 hz
    _ = mixedMoment B node4837 node4837Labels := by rfl

def raw29241 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29241Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29241step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29241step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29241step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29241step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29241 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29241 raw29241Labels = mixedMoment B node4691 node4691Labels := by
  calc
    mixedMoment B raw29241 raw29241Labels = mixedMoment B raw29241step0 raw29241step0Labels := by
      have hz : ∀ j, raw29241 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29241step0 = (fun i j => raw29241 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29241step0 raw29241; decide +kernel
      have hl : raw29241step0Labels = raw29241Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29241 raw29241Labels permutation434 hz
    mixedMoment B raw29241step0 raw29241step0Labels = mixedMoment B raw29241step1 raw29241step1Labels := by
      have hz : ∀ j, raw29241step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29241step1 = (fun i j => raw29241step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29241step1 raw29241step0; decide +kernel
      have hl : raw29241step1Labels = raw29241step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29241step0 raw29241step0Labels permutation80 hz
    _ = mixedMoment B node4691 node4691Labels := by rfl

def raw29242 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29242Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29242step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29242step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29242step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw29242step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29242step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29242step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29242 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29242 raw29242Labels = mixedMoment B node4678 node4678Labels := by
  calc
    mixedMoment B raw29242 raw29242Labels = mixedMoment B raw29242step0 raw29242step0Labels := by
      have hz : ∀ j, raw29242 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29242step0 = (fun i j => raw29242 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29242step0 raw29242; decide +kernel
      have hl : raw29242step0Labels = raw29242Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29242 raw29242Labels permutation434 hz
    mixedMoment B raw29242step0 raw29242step0Labels = mixedMoment B raw29242step1 raw29242step1Labels := by
      have ha : raw29242step1 = (fun i j => raw29242step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29242step1 raw29242step0; decide +kernel
      have hl : raw29242step1Labels = raw29242step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29242step0 raw29242step0Labels permutation149 permutation2
    mixedMoment B raw29242step1 raw29242step1Labels = mixedMoment B raw29242step2 raw29242step2Labels := by
      have ha : raw29242step2 = -raw29242step1 := by apply Matrix.ext; change ∀ i j, raw29242step2 i j = -(raw29242step1 i j); unfold raw29242step2 raw29242step1; decide +kernel
      have hl : raw29242step2Labels = raw29242step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4678 node4678Labels := by rfl

def raw29243 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29243Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29243step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29243step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29243step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -2, 0], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw29243step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29243step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29243step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29243 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29243 raw29243Labels = mixedMoment B node4678 node4678Labels := by
  calc
    mixedMoment B raw29243 raw29243Labels = mixedMoment B raw29243step0 raw29243step0Labels := by
      have hz : ∀ j, raw29243 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29243step0 = (fun i j => raw29243 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29243step0 raw29243; decide +kernel
      have hl : raw29243step0Labels = raw29243Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29243 raw29243Labels permutation346 hz
    mixedMoment B raw29243step0 raw29243step0Labels = mixedMoment B raw29243step1 raw29243step1Labels := by
      have ha : raw29243step1 = (fun i j => raw29243step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29243step1 raw29243step0; decide +kernel
      have hl : raw29243step1Labels = raw29243step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29243step0 raw29243step0Labels permutation149 permutation2
    mixedMoment B raw29243step1 raw29243step1Labels = mixedMoment B raw29243step2 raw29243step2Labels := by
      have ha : raw29243step2 = -raw29243step1 := by apply Matrix.ext; change ∀ i j, raw29243step2 i j = -(raw29243step1 i j); unfold raw29243step2 raw29243step1; decide +kernel
      have hl : raw29243step2Labels = raw29243step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4678 node4678Labels := by rfl

def raw29244 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29244Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29244step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29244step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29244step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29244step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29244 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29244 raw29244Labels = mixedMoment B node4845 node4845Labels := by
  calc
    mixedMoment B raw29244 raw29244Labels = mixedMoment B raw29244step0 raw29244step0Labels := by
      have hz : ∀ j, raw29244 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29244step0 = (fun i j => raw29244 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29244step0 raw29244; decide +kernel
      have hl : raw29244step0Labels = raw29244Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29244 raw29244Labels permutation434 hz
    mixedMoment B raw29244step0 raw29244step0Labels = mixedMoment B raw29244step1 raw29244step1Labels := by
      have hz : ∀ j, raw29244step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29244step1 = (fun i j => raw29244step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29244step1 raw29244step0; decide +kernel
      have hl : raw29244step1Labels = raw29244step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29244step0 raw29244step0Labels permutation80 hz
    _ = mixedMoment B node4845 node4845Labels := by rfl

def raw29245 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29245Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29245step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29245step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29245step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29245step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29245step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-2, 2, 0], ![-3, 0, 3]]
def raw29245step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29245step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29245step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29245 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29245 raw29245Labels = mixedMoment B node4359 node4359Labels := by
  calc
    mixedMoment B raw29245 raw29245Labels = mixedMoment B raw29245step0 raw29245step0Labels := by
      have hz : ∀ j, raw29245 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29245step0 = (fun i j => raw29245 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29245step0 raw29245; decide +kernel
      have hl : raw29245step0Labels = raw29245Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29245 raw29245Labels permutation434 hz
    mixedMoment B raw29245step0 raw29245step0Labels = mixedMoment B raw29245step1 raw29245step1Labels := by
      have hz : ∀ j, raw29245step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29245step1 = (fun i j => raw29245step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29245step1 raw29245step0; decide +kernel
      have hl : raw29245step1Labels = raw29245step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29245step0 raw29245step0Labels permutation80 hz
    mixedMoment B raw29245step1 raw29245step1Labels = mixedMoment B raw29245step2 raw29245step2Labels := by
      have ha : raw29245step2 = (fun i j => raw29245step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29245step2 raw29245step1; decide +kernel
      have hl : raw29245step2Labels = raw29245step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29245step1 raw29245step1Labels permutation31 permutation2
    mixedMoment B raw29245step2 raw29245step2Labels = mixedMoment B raw29245step3 raw29245step3Labels := by
      have ha : raw29245step3 = -raw29245step2 := by apply Matrix.ext; change ∀ i j, raw29245step3 i j = -(raw29245step2 i j); unfold raw29245step3 raw29245step2; decide +kernel
      have hl : raw29245step3Labels = raw29245step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4359 node4359Labels := by rfl

def raw29246 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29246Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29246step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29246step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29246step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw29246step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29246step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29246step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29246 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29246 raw29246Labels = mixedMoment B node4343 node4343Labels := by
  calc
    mixedMoment B raw29246 raw29246Labels = mixedMoment B raw29246step0 raw29246step0Labels := by
      have hz : ∀ j, raw29246 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29246step0 = (fun i j => raw29246 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29246step0 raw29246; decide +kernel
      have hl : raw29246step0Labels = raw29246Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29246 raw29246Labels permutation434 hz
    mixedMoment B raw29246step0 raw29246step0Labels = mixedMoment B raw29246step1 raw29246step1Labels := by
      have ha : raw29246step1 = (fun i j => raw29246step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29246step1 raw29246step0; decide +kernel
      have hl : raw29246step1Labels = raw29246step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29246step0 raw29246step0Labels permutation149 permutation2
    mixedMoment B raw29246step1 raw29246step1Labels = mixedMoment B raw29246step2 raw29246step2Labels := by
      have ha : raw29246step2 = -raw29246step1 := by apply Matrix.ext; change ∀ i j, raw29246step2 i j = -(raw29246step1 i j); unfold raw29246step2 raw29246step1; decide +kernel
      have hl : raw29246step2Labels = raw29246step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4343 node4343Labels := by rfl

def raw29247 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29247Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29247step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29247step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29247step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw29247step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29247step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29247step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29247 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29247 raw29247Labels = mixedMoment B node4343 node4343Labels := by
  calc
    mixedMoment B raw29247 raw29247Labels = mixedMoment B raw29247step0 raw29247step0Labels := by
      have hz : ∀ j, raw29247 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29247step0 = (fun i j => raw29247 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29247step0 raw29247; decide +kernel
      have hl : raw29247step0Labels = raw29247Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29247 raw29247Labels permutation346 hz
    mixedMoment B raw29247step0 raw29247step0Labels = mixedMoment B raw29247step1 raw29247step1Labels := by
      have ha : raw29247step1 = (fun i j => raw29247step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29247step1 raw29247step0; decide +kernel
      have hl : raw29247step1Labels = raw29247step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29247step0 raw29247step0Labels permutation149 permutation2
    mixedMoment B raw29247step1 raw29247step1Labels = mixedMoment B raw29247step2 raw29247step2Labels := by
      have ha : raw29247step2 = -raw29247step1 := by apply Matrix.ext; change ∀ i j, raw29247step2 i j = -(raw29247step1 i j); unfold raw29247step2 raw29247step1; decide +kernel
      have hl : raw29247step2Labels = raw29247step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4343 node4343Labels := by rfl

def raw29248 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29248Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29248step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29248step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29248step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29248step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29248step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw29248step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29248step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw29248step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29248 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29248 raw29248Labels = mixedMoment B node2218 node2218Labels := by
  calc
    mixedMoment B raw29248 raw29248Labels = mixedMoment B raw29248step0 raw29248step0Labels := by
      have hz : ∀ j, raw29248 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29248step0 = (fun i j => raw29248 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29248step0 raw29248; decide +kernel
      have hl : raw29248step0Labels = raw29248Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29248 raw29248Labels permutation434 hz
    mixedMoment B raw29248step0 raw29248step0Labels = mixedMoment B raw29248step1 raw29248step1Labels := by
      have hz : ∀ j, raw29248step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29248step1 = (fun i j => raw29248step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29248step1 raw29248step0; decide +kernel
      have hl : raw29248step1Labels = raw29248step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29248step0 raw29248step0Labels permutation80 hz
    mixedMoment B raw29248step1 raw29248step1Labels = mixedMoment B raw29248step2 raw29248step2Labels := by
      have ha : raw29248step2 = (fun i j => raw29248step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29248step2 raw29248step1; decide +kernel
      have hl : raw29248step2Labels = raw29248step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29248step1 raw29248step1Labels permutation31 permutation7
    mixedMoment B raw29248step2 raw29248step2Labels = mixedMoment B raw29248step3 raw29248step3Labels := by
      have ha : raw29248step3 = raw29248step2 := by apply Matrix.ext; unfold raw29248step3 raw29248step2; decide +kernel
      have hl : raw29248step2Labels = labelEmbedding1 ∘ raw29248step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29248step2 raw29248step2Labels raw29248step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2218 node2218Labels := by rfl

def raw29249 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29249Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29249step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29249step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29249step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw29249step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29249step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw29249step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29249 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29249 raw29249Labels = mixedMoment B node2193 node2193Labels := by
  calc
    mixedMoment B raw29249 raw29249Labels = mixedMoment B raw29249step0 raw29249step0Labels := by
      have hz : ∀ j, raw29249 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29249step0 = (fun i j => raw29249 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29249step0 raw29249; decide +kernel
      have hl : raw29249step0Labels = raw29249Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29249 raw29249Labels permutation434 hz
    mixedMoment B raw29249step0 raw29249step0Labels = mixedMoment B raw29249step1 raw29249step1Labels := by
      have ha : raw29249step1 = (fun i j => raw29249step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29249step1 raw29249step0; decide +kernel
      have hl : raw29249step1Labels = raw29249step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29249step0 raw29249step0Labels permutation149 permutation7
    mixedMoment B raw29249step1 raw29249step1Labels = mixedMoment B raw29249step2 raw29249step2Labels := by
      have ha : raw29249step2 = raw29249step1 := by apply Matrix.ext; unfold raw29249step2 raw29249step1; decide +kernel
      have hl : raw29249step1Labels = labelEmbedding1 ∘ raw29249step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29249step1 raw29249step1Labels raw29249step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2193 node2193Labels := by rfl

def raw29250 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29250Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29250step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29250step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29250step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw29250step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29250step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw29250step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29250 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29250 raw29250Labels = mixedMoment B node2193 node2193Labels := by
  calc
    mixedMoment B raw29250 raw29250Labels = mixedMoment B raw29250step0 raw29250step0Labels := by
      have hz : ∀ j, raw29250 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29250step0 = (fun i j => raw29250 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29250step0 raw29250; decide +kernel
      have hl : raw29250step0Labels = raw29250Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29250 raw29250Labels permutation346 hz
    mixedMoment B raw29250step0 raw29250step0Labels = mixedMoment B raw29250step1 raw29250step1Labels := by
      have ha : raw29250step1 = (fun i j => raw29250step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29250step1 raw29250step0; decide +kernel
      have hl : raw29250step1Labels = raw29250step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29250step0 raw29250step0Labels permutation149 permutation7
    mixedMoment B raw29250step1 raw29250step1Labels = mixedMoment B raw29250step2 raw29250step2Labels := by
      have ha : raw29250step2 = raw29250step1 := by apply Matrix.ext; unfold raw29250step2 raw29250step1; decide +kernel
      have hl : raw29250step1Labels = labelEmbedding1 ∘ raw29250step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29250step1 raw29250step1Labels raw29250step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2193 node2193Labels := by rfl

def raw29251 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29251Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29251step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29251step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29251step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29251step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29251step2 : Matrix (Fin 3) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![3, 0, -3]]
def raw29251step2Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29251step3 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw29251step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29251step4 : Matrix (Fin 3) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![3, -1, -2]]
def raw29251step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29251 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29251 raw29251Labels = mixedMoment B node2268 node2268Labels := by
  calc
    mixedMoment B raw29251 raw29251Labels = mixedMoment B raw29251step0 raw29251step0Labels := by
      have hz : ∀ j, raw29251 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw29251step0 = (fun i j => raw29251 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw29251step0 raw29251; decide +kernel
      have hl : raw29251step0Labels = raw29251Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29251 raw29251Labels permutation520 hz
    mixedMoment B raw29251step0 raw29251step0Labels = mixedMoment B raw29251step1 raw29251step1Labels := by
      have hz : ∀ j, raw29251step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw29251step1 = (fun i j => raw29251step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw29251step1 raw29251step0; decide +kernel
      have hl : raw29251step1Labels = raw29251step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29251step0 raw29251step0Labels permutation104 hz
    mixedMoment B raw29251step1 raw29251step1Labels = mixedMoment B raw29251step2 raw29251step2Labels := by
      have hz : ∀ j, raw29251step1 (permutation20 0) j = 0 := by decide +kernel
      have ha : raw29251step2 = (fun i j => raw29251step1 (permutation20 i.succ) j) := by apply Matrix.ext; unfold raw29251step2 raw29251step1; decide +kernel
      have hl : raw29251step2Labels = raw29251step1Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29251step1 raw29251step1Labels permutation20 hz
    mixedMoment B raw29251step2 raw29251step2Labels = mixedMoment B raw29251step3 raw29251step3Labels := by
      have ha : raw29251step3 = (fun i j => raw29251step2 (permutation7 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29251step3 raw29251step2; decide +kernel
      have hl : raw29251step3Labels = raw29251step2Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29251step2 raw29251step2Labels permutation7 permutation7
    mixedMoment B raw29251step3 raw29251step3Labels = mixedMoment B raw29251step4 raw29251step4Labels := by
      have ha : raw29251step4 = raw29251step3 := by apply Matrix.ext; unfold raw29251step4 raw29251step3; decide +kernel
      have hl : raw29251step3Labels = labelEmbedding1 ∘ raw29251step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29251step3 raw29251step3Labels raw29251step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2268 node2268Labels := by rfl

def raw29252 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29252Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29252step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29252step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29252step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29252step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29252step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw29252step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29252step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![3, -1, -2]]
def raw29252step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29252 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29252 raw29252Labels = mixedMoment B node2726 node2726Labels := by
  calc
    mixedMoment B raw29252 raw29252Labels = mixedMoment B raw29252step0 raw29252step0Labels := by
      have hz : ∀ j, raw29252 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29252step0 = (fun i j => raw29252 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29252step0 raw29252; decide +kernel
      have hl : raw29252step0Labels = raw29252Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29252 raw29252Labels permutation434 hz
    mixedMoment B raw29252step0 raw29252step0Labels = mixedMoment B raw29252step1 raw29252step1Labels := by
      have hz : ∀ j, raw29252step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29252step1 = (fun i j => raw29252step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29252step1 raw29252step0; decide +kernel
      have hl : raw29252step1Labels = raw29252step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29252step0 raw29252step0Labels permutation80 hz
    mixedMoment B raw29252step1 raw29252step1Labels = mixedMoment B raw29252step2 raw29252step2Labels := by
      have ha : raw29252step2 = (fun i j => raw29252step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29252step2 raw29252step1; decide +kernel
      have hl : raw29252step2Labels = raw29252step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29252step1 raw29252step1Labels permutation31 permutation7
    mixedMoment B raw29252step2 raw29252step2Labels = mixedMoment B raw29252step3 raw29252step3Labels := by
      have ha : raw29252step3 = raw29252step2 := by apply Matrix.ext; unfold raw29252step3 raw29252step2; decide +kernel
      have hl : raw29252step2Labels = labelEmbedding1 ∘ raw29252step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29252step2 raw29252step2Labels raw29252step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2726 node2726Labels := by rfl

def raw29253 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29253Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29253step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29253step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29253step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw29253step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29253step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw29253step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29253step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw29253step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29253 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29253 raw29253Labels = mixedMoment B node2143 node2143Labels := by
  calc
    mixedMoment B raw29253 raw29253Labels = mixedMoment B raw29253step0 raw29253step0Labels := by
      have hz : ∀ j, raw29253 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29253step0 = (fun i j => raw29253 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29253step0 raw29253; decide +kernel
      have hl : raw29253step0Labels = raw29253Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29253 raw29253Labels permutation434 hz
    mixedMoment B raw29253step0 raw29253step0Labels = mixedMoment B raw29253step1 raw29253step1Labels := by
      have ha : raw29253step1 = (fun i j => raw29253step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29253step1 raw29253step0; decide +kernel
      have hl : raw29253step1Labels = raw29253step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29253step0 raw29253step0Labels permutation32 permutation7
    mixedMoment B raw29253step1 raw29253step1Labels = mixedMoment B raw29253step2 raw29253step2Labels := by
      have ha : raw29253step2 = -raw29253step1 := by apply Matrix.ext; change ∀ i j, raw29253step2 i j = -(raw29253step1 i j); unfold raw29253step2 raw29253step1; decide +kernel
      have hl : raw29253step2Labels = raw29253step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29253step2 raw29253step2Labels = mixedMoment B raw29253step3 raw29253step3Labels := by
      have ha : raw29253step3 = raw29253step2 := by apply Matrix.ext; unfold raw29253step3 raw29253step2; decide +kernel
      have hl : raw29253step2Labels = labelEmbedding1 ∘ raw29253step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29253step2 raw29253step2Labels raw29253step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2143 node2143Labels := by rfl

def raw29254 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29254Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29254step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw29254step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29254step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw29254step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29254 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29254 raw29254Labels = mixedMoment B node2170 node2170Labels := by
  calc
    mixedMoment B raw29254 raw29254Labels = mixedMoment B raw29254step0 raw29254step0Labels := by
      have ha : raw29254step0 = (fun i j => raw29254 (permutation644 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29254step0 raw29254; decide +kernel
      have hl : raw29254step0Labels = raw29254Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29254 raw29254Labels permutation644 permutation7
    mixedMoment B raw29254step0 raw29254step0Labels = mixedMoment B raw29254step1 raw29254step1Labels := by
      have ha : raw29254step1 = raw29254step0 := by apply Matrix.ext; unfold raw29254step1 raw29254step0; decide +kernel
      have hl : raw29254step0Labels = labelEmbedding1 ∘ raw29254step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29254step0 raw29254step0Labels raw29254step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2170 node2170Labels := by rfl

def raw29255 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29255Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29255step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29255step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29255step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29255step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29255step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw29255step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29255step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw29255step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29255 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29255 raw29255Labels = mixedMoment B node2208 node2208Labels := by
  calc
    mixedMoment B raw29255 raw29255Labels = mixedMoment B raw29255step0 raw29255step0Labels := by
      have hz : ∀ j, raw29255 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw29255step0 = (fun i j => raw29255 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw29255step0 raw29255; decide +kernel
      have hl : raw29255step0Labels = raw29255Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29255 raw29255Labels permutation520 hz
    mixedMoment B raw29255step0 raw29255step0Labels = mixedMoment B raw29255step1 raw29255step1Labels := by
      have hz : ∀ j, raw29255step0 (permutation104 0) j = 0 := by decide +kernel
      have ha : raw29255step1 = (fun i j => raw29255step0 (permutation104 i.succ) j) := by apply Matrix.ext; unfold raw29255step1 raw29255step0; decide +kernel
      have hl : raw29255step1Labels = raw29255step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29255step0 raw29255step0Labels permutation104 hz
    mixedMoment B raw29255step1 raw29255step1Labels = mixedMoment B raw29255step2 raw29255step2Labels := by
      have ha : raw29255step2 = (fun i j => raw29255step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29255step2 raw29255step1; decide +kernel
      have hl : raw29255step2Labels = raw29255step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29255step1 raw29255step1Labels permutation31 permutation7
    mixedMoment B raw29255step2 raw29255step2Labels = mixedMoment B raw29255step3 raw29255step3Labels := by
      have ha : raw29255step3 = raw29255step2 := by apply Matrix.ext; unfold raw29255step3 raw29255step2; decide +kernel
      have hl : raw29255step2Labels = labelEmbedding1 ∘ raw29255step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29255step2 raw29255step2Labels raw29255step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2208 node2208Labels := by rfl

def raw29256 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29256Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29256step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw29256step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29256step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -1, 1], ![0, -1, 1], ![-3, 1, 2]]
def raw29256step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29256step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw29256step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29256step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, -1, -2]]
def raw29256step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29256 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29256 raw29256Labels = mixedMoment B node2193 node2193Labels := by
  calc
    mixedMoment B raw29256 raw29256Labels = mixedMoment B raw29256step0 raw29256step0Labels := by
      have hz : ∀ j, raw29256 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29256step0 = (fun i j => raw29256 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29256step0 raw29256; decide +kernel
      have hl : raw29256step0Labels = raw29256Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29256 raw29256Labels permutation434 hz
    mixedMoment B raw29256step0 raw29256step0Labels = mixedMoment B raw29256step1 raw29256step1Labels := by
      have ha : raw29256step1 = (fun i j => raw29256step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29256step1 raw29256step0; decide +kernel
      have hl : raw29256step1Labels = raw29256step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29256step0 raw29256step0Labels permutation32 permutation7
    mixedMoment B raw29256step1 raw29256step1Labels = mixedMoment B raw29256step2 raw29256step2Labels := by
      have ha : raw29256step2 = -raw29256step1 := by apply Matrix.ext; change ∀ i j, raw29256step2 i j = -(raw29256step1 i j); unfold raw29256step2 raw29256step1; decide +kernel
      have hl : raw29256step2Labels = raw29256step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29256step2 raw29256step2Labels = mixedMoment B raw29256step3 raw29256step3Labels := by
      have ha : raw29256step3 = raw29256step2 := by apply Matrix.ext; unfold raw29256step3 raw29256step2; decide +kernel
      have hl : raw29256step2Labels = labelEmbedding1 ∘ raw29256step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29256step2 raw29256step2Labels raw29256step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2193 node2193Labels := by rfl

def raw29257 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29257Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29257step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29257step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29257step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, 2, -2], ![0, -1, 1], ![0, -1, 1], ![-3, 0, 3]]
def raw29257step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29257step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw29257step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29257step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw29257step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29257 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29257 raw29257Labels = mixedMoment B node2143 node2143Labels := by
  calc
    mixedMoment B raw29257 raw29257Labels = mixedMoment B raw29257step0 raw29257step0Labels := by
      have hz : ∀ j, raw29257 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29257step0 = (fun i j => raw29257 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29257step0 raw29257; decide +kernel
      have hl : raw29257step0Labels = raw29257Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29257 raw29257Labels permutation346 hz
    mixedMoment B raw29257step0 raw29257step0Labels = mixedMoment B raw29257step1 raw29257step1Labels := by
      have ha : raw29257step1 = (fun i j => raw29257step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29257step1 raw29257step0; decide +kernel
      have hl : raw29257step1Labels = raw29257step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29257step0 raw29257step0Labels permutation32 permutation7
    mixedMoment B raw29257step1 raw29257step1Labels = mixedMoment B raw29257step2 raw29257step2Labels := by
      have ha : raw29257step2 = -raw29257step1 := by apply Matrix.ext; change ∀ i j, raw29257step2 i j = -(raw29257step1 i j); unfold raw29257step2 raw29257step1; decide +kernel
      have hl : raw29257step2Labels = raw29257step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29257step2 raw29257step2Labels = mixedMoment B raw29257step3 raw29257step3Labels := by
      have ha : raw29257step3 = raw29257step2 := by apply Matrix.ext; unfold raw29257step3 raw29257step2; decide +kernel
      have hl : raw29257step2Labels = labelEmbedding1 ∘ raw29257step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29257step2 raw29257step2Labels raw29257step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2143 node2143Labels := by rfl

def raw29258 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29258Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29258step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw29258step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29258step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw29258step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29258 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29258 raw29258Labels = mixedMoment B node2170 node2170Labels := by
  calc
    mixedMoment B raw29258 raw29258Labels = mixedMoment B raw29258step0 raw29258step0Labels := by
      have ha : raw29258step0 = (fun i j => raw29258 (permutation662 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29258step0 raw29258; decide +kernel
      have hl : raw29258step0Labels = raw29258Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29258 raw29258Labels permutation662 permutation7
    mixedMoment B raw29258step0 raw29258step0Labels = mixedMoment B raw29258step1 raw29258step1Labels := by
      have ha : raw29258step1 = raw29258step0 := by apply Matrix.ext; unfold raw29258step1 raw29258step0; decide +kernel
      have hl : raw29258step0Labels = labelEmbedding1 ∘ raw29258step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29258step0 raw29258step0Labels raw29258step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2170 node2170Labels := by rfl

def raw29259 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![0, 0, 0], ![3, 0, -3]]
def raw29259Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29259step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29259step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29259step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29259step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29259step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw29259step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29259step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw29259step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29259 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29259 raw29259Labels = mixedMoment B node2208 node2208Labels := by
  calc
    mixedMoment B raw29259 raw29259Labels = mixedMoment B raw29259step0 raw29259step0Labels := by
      have hz : ∀ j, raw29259 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw29259step0 = (fun i j => raw29259 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw29259step0 raw29259; decide +kernel
      have hl : raw29259step0Labels = raw29259Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29259 raw29259Labels permutation520 hz
    mixedMoment B raw29259step0 raw29259step0Labels = mixedMoment B raw29259step1 raw29259step1Labels := by
      have hz : ∀ j, raw29259step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29259step1 = (fun i j => raw29259step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29259step1 raw29259step0; decide +kernel
      have hl : raw29259step1Labels = raw29259step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29259step0 raw29259step0Labels permutation80 hz
    mixedMoment B raw29259step1 raw29259step1Labels = mixedMoment B raw29259step2 raw29259step2Labels := by
      have ha : raw29259step2 = (fun i j => raw29259step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29259step2 raw29259step1; decide +kernel
      have hl : raw29259step2Labels = raw29259step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29259step1 raw29259step1Labels permutation31 permutation7
    mixedMoment B raw29259step2 raw29259step2Labels = mixedMoment B raw29259step3 raw29259step3Labels := by
      have ha : raw29259step3 = raw29259step2 := by apply Matrix.ext; unfold raw29259step3 raw29259step2; decide +kernel
      have hl : raw29259step2Labels = labelEmbedding1 ∘ raw29259step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29259step2 raw29259step2Labels raw29259step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2208 node2208Labels := by rfl

def raw29260 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29260Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29260step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29260step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29260step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29260step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29260step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![3, 0, -3]]
def raw29260step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29260step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 2, -2], ![3, 0, -3]]
def raw29260step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29260 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29260 raw29260Labels = mixedMoment B node2159 node2159Labels := by
  calc
    mixedMoment B raw29260 raw29260Labels = mixedMoment B raw29260step0 raw29260step0Labels := by
      have hz : ∀ j, raw29260 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29260step0 = (fun i j => raw29260 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29260step0 raw29260; decide +kernel
      have hl : raw29260step0Labels = raw29260Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29260 raw29260Labels permutation434 hz
    mixedMoment B raw29260step0 raw29260step0Labels = mixedMoment B raw29260step1 raw29260step1Labels := by
      have hz : ∀ j, raw29260step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29260step1 = (fun i j => raw29260step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29260step1 raw29260step0; decide +kernel
      have hl : raw29260step1Labels = raw29260step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29260step0 raw29260step0Labels permutation80 hz
    mixedMoment B raw29260step1 raw29260step1Labels = mixedMoment B raw29260step2 raw29260step2Labels := by
      have ha : raw29260step2 = (fun i j => raw29260step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29260step2 raw29260step1; decide +kernel
      have hl : raw29260step2Labels = raw29260step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29260step1 raw29260step1Labels permutation31 permutation7
    mixedMoment B raw29260step2 raw29260step2Labels = mixedMoment B raw29260step3 raw29260step3Labels := by
      have ha : raw29260step3 = raw29260step2 := by apply Matrix.ext; unfold raw29260step3 raw29260step2; decide +kernel
      have hl : raw29260step2Labels = labelEmbedding1 ∘ raw29260step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29260step2 raw29260step2Labels raw29260step3Labels labelEmbedding1 hl
    _ = mixedMoment B node2159 node2159Labels := by rfl

def raw29261 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29261Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29261step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29261step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29261step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw29261step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29261step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw29261step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29261 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29261 raw29261Labels = mixedMoment B node2143 node2143Labels := by
  calc
    mixedMoment B raw29261 raw29261Labels = mixedMoment B raw29261step0 raw29261step0Labels := by
      have hz : ∀ j, raw29261 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29261step0 = (fun i j => raw29261 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29261step0 raw29261; decide +kernel
      have hl : raw29261step0Labels = raw29261Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29261 raw29261Labels permutation434 hz
    mixedMoment B raw29261step0 raw29261step0Labels = mixedMoment B raw29261step1 raw29261step1Labels := by
      have ha : raw29261step1 = (fun i j => raw29261step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29261step1 raw29261step0; decide +kernel
      have hl : raw29261step1Labels = raw29261step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29261step0 raw29261step0Labels permutation149 permutation7
    mixedMoment B raw29261step1 raw29261step1Labels = mixedMoment B raw29261step2 raw29261step2Labels := by
      have ha : raw29261step2 = raw29261step1 := by apply Matrix.ext; unfold raw29261step2 raw29261step1; decide +kernel
      have hl : raw29261step1Labels = labelEmbedding1 ∘ raw29261step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29261step1 raw29261step1Labels raw29261step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2143 node2143Labels := by rfl

def raw29262 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29262Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29262step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29262step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29262step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw29262step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29262step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw29262step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29262 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29262 raw29262Labels = mixedMoment B node2143 node2143Labels := by
  calc
    mixedMoment B raw29262 raw29262Labels = mixedMoment B raw29262step0 raw29262step0Labels := by
      have hz : ∀ j, raw29262 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29262step0 = (fun i j => raw29262 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29262step0 raw29262; decide +kernel
      have hl : raw29262step0Labels = raw29262Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29262 raw29262Labels permutation346 hz
    mixedMoment B raw29262step0 raw29262step0Labels = mixedMoment B raw29262step1 raw29262step1Labels := by
      have ha : raw29262step1 = (fun i j => raw29262step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29262step1 raw29262step0; decide +kernel
      have hl : raw29262step1Labels = raw29262step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29262step0 raw29262step0Labels permutation149 permutation7
    mixedMoment B raw29262step1 raw29262step1Labels = mixedMoment B raw29262step2 raw29262step2Labels := by
      have ha : raw29262step2 = raw29262step1 := by apply Matrix.ext; unfold raw29262step2 raw29262step1; decide +kernel
      have hl : raw29262step1Labels = labelEmbedding1 ∘ raw29262step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29262step1 raw29262step1Labels raw29262step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2143 node2143Labels := by rfl

def raw29263 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29263Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29263step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29263step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29263step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29263step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29263step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -2, 2], ![-3, 1, 2]]
def raw29263step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29263step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw29263step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29263step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 2, -2], ![3, -1, -2]]
def raw29263step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29263 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29263 raw29263Labels = mixedMoment B node2218 node2218Labels := by
  calc
    mixedMoment B raw29263 raw29263Labels = mixedMoment B raw29263step0 raw29263step0Labels := by
      have hz : ∀ j, raw29263 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29263step0 = (fun i j => raw29263 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29263step0 raw29263; decide +kernel
      have hl : raw29263step0Labels = raw29263Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29263 raw29263Labels permutation434 hz
    mixedMoment B raw29263step0 raw29263step0Labels = mixedMoment B raw29263step1 raw29263step1Labels := by
      have hz : ∀ j, raw29263step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29263step1 = (fun i j => raw29263step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29263step1 raw29263step0; decide +kernel
      have hl : raw29263step1Labels = raw29263step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29263step0 raw29263step0Labels permutation80 hz
    mixedMoment B raw29263step1 raw29263step1Labels = mixedMoment B raw29263step2 raw29263step2Labels := by
      have ha : raw29263step2 = (fun i j => raw29263step1 (permutation8 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29263step2 raw29263step1; decide +kernel
      have hl : raw29263step2Labels = raw29263step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29263step1 raw29263step1Labels permutation8 permutation7
    mixedMoment B raw29263step2 raw29263step2Labels = mixedMoment B raw29263step3 raw29263step3Labels := by
      have ha : raw29263step3 = -raw29263step2 := by apply Matrix.ext; change ∀ i j, raw29263step3 i j = -(raw29263step2 i j); unfold raw29263step3 raw29263step2; decide +kernel
      have hl : raw29263step3Labels = raw29263step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29263step3 raw29263step3Labels = mixedMoment B raw29263step4 raw29263step4Labels := by
      have ha : raw29263step4 = raw29263step3 := by apply Matrix.ext; unfold raw29263step4 raw29263step3; decide +kernel
      have hl : raw29263step3Labels = labelEmbedding1 ∘ raw29263step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29263step3 raw29263step3Labels raw29263step4Labels labelEmbedding1 hl
    _ = mixedMoment B node2218 node2218Labels := by rfl

def raw29264 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29264Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29264step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29264step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29264step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29264step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29264step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def raw29264step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29264step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 2, -2], ![3, 0, -3]]
def raw29264step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29264 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29264 raw29264Labels = mixedMoment B node1683 node1683Labels := by
  calc
    mixedMoment B raw29264 raw29264Labels = mixedMoment B raw29264step0 raw29264step0Labels := by
      have hz : ∀ j, raw29264 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29264step0 = (fun i j => raw29264 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29264step0 raw29264; decide +kernel
      have hl : raw29264step0Labels = raw29264Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29264 raw29264Labels permutation434 hz
    mixedMoment B raw29264step0 raw29264step0Labels = mixedMoment B raw29264step1 raw29264step1Labels := by
      have hz : ∀ j, raw29264step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29264step1 = (fun i j => raw29264step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29264step1 raw29264step0; decide +kernel
      have hl : raw29264step1Labels = raw29264step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29264step0 raw29264step0Labels permutation80 hz
    mixedMoment B raw29264step1 raw29264step1Labels = mixedMoment B raw29264step2 raw29264step2Labels := by
      have ha : raw29264step2 = (fun i j => raw29264step1 (permutation31 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29264step2 raw29264step1; decide +kernel
      have hl : raw29264step2Labels = raw29264step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29264step1 raw29264step1Labels permutation31 permutation7
    mixedMoment B raw29264step2 raw29264step2Labels = mixedMoment B raw29264step3 raw29264step3Labels := by
      have ha : raw29264step3 = raw29264step2 := by apply Matrix.ext; unfold raw29264step3 raw29264step2; decide +kernel
      have hl : raw29264step2Labels = labelEmbedding1 ∘ raw29264step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29264step2 raw29264step2Labels raw29264step3Labels labelEmbedding1 hl
    _ = mixedMoment B node1683 node1683Labels := by rfl

def raw29265 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29265Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29265step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29265step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29265step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw29265step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29265step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw29265step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29265 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29265 raw29265Labels = mixedMoment B node1666 node1666Labels := by
  calc
    mixedMoment B raw29265 raw29265Labels = mixedMoment B raw29265step0 raw29265step0Labels := by
      have hz : ∀ j, raw29265 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29265step0 = (fun i j => raw29265 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29265step0 raw29265; decide +kernel
      have hl : raw29265step0Labels = raw29265Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29265 raw29265Labels permutation434 hz
    mixedMoment B raw29265step0 raw29265step0Labels = mixedMoment B raw29265step1 raw29265step1Labels := by
      have ha : raw29265step1 = (fun i j => raw29265step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29265step1 raw29265step0; decide +kernel
      have hl : raw29265step1Labels = raw29265step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29265step0 raw29265step0Labels permutation149 permutation7
    mixedMoment B raw29265step1 raw29265step1Labels = mixedMoment B raw29265step2 raw29265step2Labels := by
      have ha : raw29265step2 = raw29265step1 := by apply Matrix.ext; unfold raw29265step2 raw29265step1; decide +kernel
      have hl : raw29265step1Labels = labelEmbedding1 ∘ raw29265step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29265step1 raw29265step1Labels raw29265step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1666 node1666Labels := by rfl

def raw29266 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29266Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29266step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29266step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw29266step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw29266step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw29266step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, -1, 4], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![3, 0, -3]]
def raw29266step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29266 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29266 raw29266Labels = mixedMoment B node1666 node1666Labels := by
  calc
    mixedMoment B raw29266 raw29266Labels = mixedMoment B raw29266step0 raw29266step0Labels := by
      have hz : ∀ j, raw29266 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29266step0 = (fun i j => raw29266 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29266step0 raw29266; decide +kernel
      have hl : raw29266step0Labels = raw29266Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29266 raw29266Labels permutation346 hz
    mixedMoment B raw29266step0 raw29266step0Labels = mixedMoment B raw29266step1 raw29266step1Labels := by
      have ha : raw29266step1 = (fun i j => raw29266step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29266step1 raw29266step0; decide +kernel
      have hl : raw29266step1Labels = raw29266step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29266step0 raw29266step0Labels permutation149 permutation7
    mixedMoment B raw29266step1 raw29266step1Labels = mixedMoment B raw29266step2 raw29266step2Labels := by
      have ha : raw29266step2 = raw29266step1 := by apply Matrix.ext; unfold raw29266step2 raw29266step1; decide +kernel
      have hl : raw29266step1Labels = labelEmbedding1 ∘ raw29266step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29266step1 raw29266step1Labels raw29266step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1666 node1666Labels := by rfl

def raw29267 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29267Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29267step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29267step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29267step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29267step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29267step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![-2, 2, 0], ![-2, -1, 3]]
def raw29267step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29267step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![2, -2, 0], ![2, 1, -3]]
def raw29267step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29267 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29267 raw29267Labels = mixedMoment B node2065 node2065Labels := by
  calc
    mixedMoment B raw29267 raw29267Labels = mixedMoment B raw29267step0 raw29267step0Labels := by
      have hz : ∀ j, raw29267 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29267step0 = (fun i j => raw29267 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29267step0 raw29267; decide +kernel
      have hl : raw29267step0Labels = raw29267Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29267 raw29267Labels permutation434 hz
    mixedMoment B raw29267step0 raw29267step0Labels = mixedMoment B raw29267step1 raw29267step1Labels := by
      have hz : ∀ j, raw29267step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29267step1 = (fun i j => raw29267step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29267step1 raw29267step0; decide +kernel
      have hl : raw29267step1Labels = raw29267step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29267step0 raw29267step0Labels permutation80 hz
    mixedMoment B raw29267step1 raw29267step1Labels = mixedMoment B raw29267step2 raw29267step2Labels := by
      have ha : raw29267step2 = (fun i j => raw29267step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29267step2 raw29267step1; decide +kernel
      have hl : raw29267step2Labels = raw29267step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29267step1 raw29267step1Labels permutation31 permutation2
    mixedMoment B raw29267step2 raw29267step2Labels = mixedMoment B raw29267step3 raw29267step3Labels := by
      have ha : raw29267step3 = -raw29267step2 := by apply Matrix.ext; change ∀ i j, raw29267step3 i j = -(raw29267step2 i j); unfold raw29267step3 raw29267step2; decide +kernel
      have hl : raw29267step3Labels = raw29267step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2065 node2065Labels := by rfl

def raw29268 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29268Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29268step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29268step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29268step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29268step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29268 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29268 raw29268Labels = mixedMoment B node2056 node2056Labels := by
  calc
    mixedMoment B raw29268 raw29268Labels = mixedMoment B raw29268step0 raw29268step0Labels := by
      have hz : ∀ j, raw29268 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29268step0 = (fun i j => raw29268 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29268step0 raw29268; decide +kernel
      have hl : raw29268step0Labels = raw29268Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29268 raw29268Labels permutation434 hz
    mixedMoment B raw29268step0 raw29268step0Labels = mixedMoment B raw29268step1 raw29268step1Labels := by
      have hz : ∀ j, raw29268step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29268step1 = (fun i j => raw29268step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29268step1 raw29268step0; decide +kernel
      have hl : raw29268step1Labels = raw29268step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29268step0 raw29268step0Labels permutation80 hz
    _ = mixedMoment B node2056 node2056Labels := by rfl

def raw29269 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29269Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29269step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29269step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29269 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29269 raw29269Labels = mixedMoment B node1804 node1804Labels := by
  calc
    mixedMoment B raw29269 raw29269Labels = mixedMoment B raw29269step0 raw29269step0Labels := by
      have hz : ∀ j, raw29269 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29269step0 = (fun i j => raw29269 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29269step0 raw29269; decide +kernel
      have hl : raw29269step0Labels = raw29269Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29269 raw29269Labels permutation434 hz
    _ = mixedMoment B node1804 node1804Labels := by rfl

def raw29270 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29270Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29270step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29270step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29270 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29270 raw29270Labels = mixedMoment B node1804 node1804Labels := by
  calc
    mixedMoment B raw29270 raw29270Labels = mixedMoment B raw29270step0 raw29270step0Labels := by
      have hz : ∀ j, raw29270 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29270step0 = (fun i j => raw29270 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29270step0 raw29270; decide +kernel
      have hl : raw29270step0Labels = raw29270Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29270 raw29270Labels permutation346 hz
    _ = mixedMoment B node1804 node1804Labels := by rfl

def raw29271 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29271Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29271step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29271step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29271step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29271step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29271 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29271 raw29271Labels = mixedMoment B node1817 node1817Labels := by
  calc
    mixedMoment B raw29271 raw29271Labels = mixedMoment B raw29271step0 raw29271step0Labels := by
      have hz : ∀ j, raw29271 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29271step0 = (fun i j => raw29271 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29271step0 raw29271; decide +kernel
      have hl : raw29271step0Labels = raw29271Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29271 raw29271Labels permutation434 hz
    mixedMoment B raw29271step0 raw29271step0Labels = mixedMoment B raw29271step1 raw29271step1Labels := by
      have hz : ∀ j, raw29271step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29271step1 = (fun i j => raw29271step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29271step1 raw29271step0; decide +kernel
      have hl : raw29271step1Labels = raw29271step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29271step0 raw29271step0Labels permutation80 hz
    _ = mixedMoment B node1817 node1817Labels := by rfl

def raw29272 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29272Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29272step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29272step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29272step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![4, -1, -3]]
def raw29272step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29272step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![4, -1, -3], ![1, -1, 0], ![-2, 2, 0], ![-3, 0, 3]]
def raw29272step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29272step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![2, -2, 0], ![3, 0, -3]]
def raw29272step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29272 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29272 raw29272Labels = mixedMoment B node937 node937Labels := by
  calc
    mixedMoment B raw29272 raw29272Labels = mixedMoment B raw29272step0 raw29272step0Labels := by
      have hz : ∀ j, raw29272 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29272step0 = (fun i j => raw29272 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29272step0 raw29272; decide +kernel
      have hl : raw29272step0Labels = raw29272Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29272 raw29272Labels permutation434 hz
    mixedMoment B raw29272step0 raw29272step0Labels = mixedMoment B raw29272step1 raw29272step1Labels := by
      have hz : ∀ j, raw29272step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29272step1 = (fun i j => raw29272step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29272step1 raw29272step0; decide +kernel
      have hl : raw29272step1Labels = raw29272step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29272step0 raw29272step0Labels permutation80 hz
    mixedMoment B raw29272step1 raw29272step1Labels = mixedMoment B raw29272step2 raw29272step2Labels := by
      have ha : raw29272step2 = (fun i j => raw29272step1 (permutation31 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29272step2 raw29272step1; decide +kernel
      have hl : raw29272step2Labels = raw29272step1Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29272step1 raw29272step1Labels permutation31 permutation2
    mixedMoment B raw29272step2 raw29272step2Labels = mixedMoment B raw29272step3 raw29272step3Labels := by
      have ha : raw29272step3 = -raw29272step2 := by apply Matrix.ext; change ∀ i j, raw29272step3 i j = -(raw29272step2 i j); unfold raw29272step3 raw29272step2; decide +kernel
      have hl : raw29272step3Labels = raw29272step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node937 node937Labels := by rfl

def raw29273 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29273Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29273step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29273step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29273step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-2, -1, 3]]
def raw29273step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29273step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, 1, -3]]
def raw29273step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29273 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29273 raw29273Labels = mixedMoment B node4744 node4744Labels := by
  calc
    mixedMoment B raw29273 raw29273Labels = mixedMoment B raw29273step0 raw29273step0Labels := by
      have hz : ∀ j, raw29273 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29273step0 = (fun i j => raw29273 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29273step0 raw29273; decide +kernel
      have hl : raw29273step0Labels = raw29273Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29273 raw29273Labels permutation346 hz
    mixedMoment B raw29273step0 raw29273step0Labels = mixedMoment B raw29273step1 raw29273step1Labels := by
      have ha : raw29273step1 = (fun i j => raw29273step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29273step1 raw29273step0; decide +kernel
      have hl : raw29273step1Labels = raw29273step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29273step0 raw29273step0Labels permutation151 permutation2
    mixedMoment B raw29273step1 raw29273step1Labels = mixedMoment B raw29273step2 raw29273step2Labels := by
      have ha : raw29273step2 = -raw29273step1 := by apply Matrix.ext; change ∀ i j, raw29273step2 i j = -(raw29273step1 i j); unfold raw29273step2 raw29273step1; decide +kernel
      have hl : raw29273step2Labels = raw29273step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4744 node4744Labels := by rfl

def raw29274 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29274Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29274step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw29274step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29274step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw29274step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29274 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29274 raw29274Labels = mixedMoment B node4728 node4728Labels := by
  calc
    mixedMoment B raw29274 raw29274Labels = mixedMoment B raw29274step0 raw29274step0Labels := by
      have ha : raw29274step0 = (fun i j => raw29274 (permutation674 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29274step0 raw29274; decide +kernel
      have hl : raw29274step0Labels = raw29274Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29274 raw29274Labels permutation674 permutation7
    mixedMoment B raw29274step0 raw29274step0Labels = mixedMoment B raw29274step1 raw29274step1Labels := by
      have ha : raw29274step1 = raw29274step0 := by apply Matrix.ext; unfold raw29274step1 raw29274step0; decide +kernel
      have hl : raw29274step0Labels = labelEmbedding10 ∘ raw29274step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29274step0 raw29274step0Labels raw29274step1Labels labelEmbedding10 hl
    _ = mixedMoment B node4728 node4728Labels := by rfl

def raw29275 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29275Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29275step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29275step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29275step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29275step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29275step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29275step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29275 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29275 raw29275Labels = mixedMoment B node4741 node4741Labels := by
  calc
    mixedMoment B raw29275 raw29275Labels = mixedMoment B raw29275step0 raw29275step0Labels := by
      have hz : ∀ j, raw29275 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29275step0 = (fun i j => raw29275 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29275step0 raw29275; decide +kernel
      have hl : raw29275step0Labels = raw29275Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29275 raw29275Labels permutation346 hz
    mixedMoment B raw29275step0 raw29275step0Labels = mixedMoment B raw29275step1 raw29275step1Labels := by
      have ha : raw29275step1 = (fun i j => raw29275step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29275step1 raw29275step0; decide +kernel
      have hl : raw29275step1Labels = raw29275step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29275step0 raw29275step0Labels permutation149 permutation7
    mixedMoment B raw29275step1 raw29275step1Labels = mixedMoment B raw29275step2 raw29275step2Labels := by
      have ha : raw29275step2 = raw29275step1 := by apply Matrix.ext; unfold raw29275step2 raw29275step1; decide +kernel
      have hl : raw29275step1Labels = labelEmbedding10 ∘ raw29275step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29275step1 raw29275step1Labels raw29275step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4741 node4741Labels := by rfl

def raw29276 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw29276Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29276step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw29276step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29276step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw29276step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29276step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw29276step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29276 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29276 raw29276Labels = mixedMoment B node4804 node4804Labels := by
  calc
    mixedMoment B raw29276 raw29276Labels = mixedMoment B raw29276step0 raw29276step0Labels := by
      have hz : ∀ j, raw29276 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29276step0 = (fun i j => raw29276 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29276step0 raw29276; decide +kernel
      have hl : raw29276step0Labels = raw29276Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29276 raw29276Labels permutation346 hz
    mixedMoment B raw29276step0 raw29276step0Labels = mixedMoment B raw29276step1 raw29276step1Labels := by
      have ha : raw29276step1 = (fun i j => raw29276step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29276step1 raw29276step0; decide +kernel
      have hl : raw29276step1Labels = raw29276step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29276step0 raw29276step0Labels permutation149 permutation7
    mixedMoment B raw29276step1 raw29276step1Labels = mixedMoment B raw29276step2 raw29276step2Labels := by
      have ha : raw29276step2 = raw29276step1 := by apply Matrix.ext; unfold raw29276step2 raw29276step1; decide +kernel
      have hl : raw29276step1Labels = labelEmbedding10 ∘ raw29276step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29276step1 raw29276step1Labels raw29276step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4804 node4804Labels := by rfl

def raw29277 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29277Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29277step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29277step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29277step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw29277step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29277step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![3, -1, -2]]
def raw29277step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29277 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29277 raw29277Labels = mixedMoment B node5075 node5075Labels := by
  calc
    mixedMoment B raw29277 raw29277Labels = mixedMoment B raw29277step0 raw29277step0Labels := by
      have hz : ∀ j, raw29277 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29277step0 = (fun i j => raw29277 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29277step0 raw29277; decide +kernel
      have hl : raw29277step0Labels = raw29277Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29277 raw29277Labels permutation346 hz
    mixedMoment B raw29277step0 raw29277step0Labels = mixedMoment B raw29277step1 raw29277step1Labels := by
      have ha : raw29277step1 = (fun i j => raw29277step0 (permutation149 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29277step1 raw29277step0; decide +kernel
      have hl : raw29277step1Labels = raw29277step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29277step0 raw29277step0Labels permutation149 permutation7
    mixedMoment B raw29277step1 raw29277step1Labels = mixedMoment B raw29277step2 raw29277step2Labels := by
      have ha : raw29277step2 = raw29277step1 := by apply Matrix.ext; unfold raw29277step2 raw29277step1; decide +kernel
      have hl : raw29277step1Labels = labelEmbedding10 ∘ raw29277step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29277step1 raw29277step1Labels raw29277step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5075 node5075Labels := by rfl

def raw29278 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29278Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29278step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29278step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29278step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29278step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29278 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29278 raw29278Labels = mixedMoment B node4426 node4426Labels := by
  calc
    mixedMoment B raw29278 raw29278Labels = mixedMoment B raw29278step0 raw29278step0Labels := by
      have hz : ∀ j, raw29278 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29278step0 = (fun i j => raw29278 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29278step0 raw29278; decide +kernel
      have hl : raw29278step0Labels = raw29278Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29278 raw29278Labels permutation346 hz
    mixedMoment B raw29278step0 raw29278step0Labels = mixedMoment B raw29278step1 raw29278step1Labels := by
      have hz : ∀ j, raw29278step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw29278step1 = (fun i j => raw29278step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw29278step1 raw29278step0; decide +kernel
      have hl : raw29278step1Labels = raw29278step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29278step0 raw29278step0Labels permutation56 hz
    _ = mixedMoment B node4426 node4426Labels := by rfl

def raw29279 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29279Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29279step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw29279step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29279 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29279 raw29279Labels = mixedMoment B node4658 node4658Labels := by
  calc
    mixedMoment B raw29279 raw29279Labels = mixedMoment B raw29279step0 raw29279step0Labels := by
      have ha : raw29279step0 = (fun i j => raw29279 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29279step0 raw29279; decide +kernel
      have hl : raw29279step0Labels = raw29279Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29279 raw29279Labels permutation158 permutation2
    _ = mixedMoment B node4658 node4658Labels := by rfl

def raw29280 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29280Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29280step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw29280step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29280 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29280 raw29280Labels = mixedMoment B node4708 node4708Labels := by
  calc
    mixedMoment B raw29280 raw29280Labels = mixedMoment B raw29280step0 raw29280step0Labels := by
      have ha : raw29280step0 = (fun i j => raw29280 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29280step0 raw29280; decide +kernel
      have hl : raw29280step0Labels = raw29280Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29280 raw29280Labels permutation200 permutation2
    _ = mixedMoment B node4708 node4708Labels := by rfl

def raw29281 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![0, 1, -1], ![3, 0, -3]]
def raw29281Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29281step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw29281step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29281 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29281 raw29281Labels = mixedMoment B node4778 node4778Labels := by
  calc
    mixedMoment B raw29281 raw29281Labels = mixedMoment B raw29281step0 raw29281step0Labels := by
      have ha : raw29281step0 = (fun i j => raw29281 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29281step0 raw29281; decide +kernel
      have hl : raw29281step0Labels = raw29281Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29281 raw29281Labels permutation160 permutation2
    _ = mixedMoment B node4778 node4778Labels := by rfl

def raw29282 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29282Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29282step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-3, 1, 2]]
def raw29282step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29282step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29282step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29282step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -1, -2]]
def raw29282step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29282 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29282 raw29282Labels = mixedMoment B node4779 node4779Labels := by
  calc
    mixedMoment B raw29282 raw29282Labels = mixedMoment B raw29282step0 raw29282step0Labels := by
      have ha : raw29282step0 = (fun i j => raw29282 (permutation200 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29282step0 raw29282; decide +kernel
      have hl : raw29282step0Labels = raw29282Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29282 raw29282Labels permutation200 permutation7
    mixedMoment B raw29282step0 raw29282step0Labels = mixedMoment B raw29282step1 raw29282step1Labels := by
      have ha : raw29282step1 = -raw29282step0 := by apply Matrix.ext; change ∀ i j, raw29282step1 i j = -(raw29282step0 i j); unfold raw29282step1 raw29282step0; decide +kernel
      have hl : raw29282step1Labels = raw29282step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29282step1 raw29282step1Labels = mixedMoment B raw29282step2 raw29282step2Labels := by
      have ha : raw29282step2 = raw29282step1 := by apply Matrix.ext; unfold raw29282step2 raw29282step1; decide +kernel
      have hl : raw29282step1Labels = labelEmbedding10 ∘ raw29282step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29282step1 raw29282step1Labels raw29282step2Labels labelEmbedding10 hl
    _ = mixedMoment B node4779 node4779Labels := by rfl

def raw29283 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29283Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29283step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29283step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29283 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29283 raw29283Labels = mixedMoment B node4673 node4673Labels := by
  calc
    mixedMoment B raw29283 raw29283Labels = mixedMoment B raw29283step0 raw29283step0Labels := by
      have hz : ∀ j, raw29283 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29283step0 = (fun i j => raw29283 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29283step0 raw29283; decide +kernel
      have hl : raw29283step0Labels = raw29283Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29283 raw29283Labels permutation346 hz
    _ = mixedMoment B node4673 node4673Labels := by rfl

def raw29284 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![3, 0, -3]]
def raw29284Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29284step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw29284step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29284step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29284step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29284 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29284 raw29284Labels = mixedMoment B node4720 node4720Labels := by
  calc
    mixedMoment B raw29284 raw29284Labels = mixedMoment B raw29284step0 raw29284step0Labels := by
      have ha : raw29284step0 = (fun i j => raw29284 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29284step0 raw29284; decide +kernel
      have hl : raw29284step0Labels = raw29284Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29284 raw29284Labels permutation686 permutation2
    mixedMoment B raw29284step0 raw29284step0Labels = mixedMoment B raw29284step1 raw29284step1Labels := by
      have ha : raw29284step1 = -raw29284step0 := by apply Matrix.ext; change ∀ i j, raw29284step1 i j = -(raw29284step0 i j); unfold raw29284step1 raw29284step0; decide +kernel
      have hl : raw29284step1Labels = raw29284step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4720 node4720Labels := by rfl

def raw29285 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![0, 1, -1], ![3, 0, -3]]
def raw29285Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29285step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![3, 0, -3]]
def raw29285step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29285step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, 0, -3]]
def raw29285step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29285 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29285 raw29285Labels = mixedMoment B node4800 node4800Labels := by
  calc
    mixedMoment B raw29285 raw29285Labels = mixedMoment B raw29285step0 raw29285step0Labels := by
      have hz : ∀ j, raw29285 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29285step0 = (fun i j => raw29285 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29285step0 raw29285; decide +kernel
      have hl : raw29285step0Labels = raw29285Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29285 raw29285Labels permutation346 hz
    mixedMoment B raw29285step0 raw29285step0Labels = mixedMoment B raw29285step1 raw29285step1Labels := by
      have ha : raw29285step1 = (fun i j => raw29285step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29285step1 raw29285step0; decide +kernel
      have hl : raw29285step1Labels = raw29285step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29285step0 raw29285step0Labels permutation34 permutation2
    _ = mixedMoment B node4800 node4800Labels := by rfl

def raw29286 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29286Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29286step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw29286step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29286 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29286 raw29286Labels = mixedMoment B node4827 node4827Labels := by
  calc
    mixedMoment B raw29286 raw29286Labels = mixedMoment B raw29286step0 raw29286step0Labels := by
      have hz : ∀ j, raw29286 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29286step0 = (fun i j => raw29286 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29286step0 raw29286; decide +kernel
      have hl : raw29286step0Labels = raw29286Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29286 raw29286Labels permutation346 hz
    _ = mixedMoment B node4827 node4827Labels := by rfl

def raw29287 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw29287Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29287step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw29287step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29287step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![0, -1, 1], ![-2, 2, 0], ![-3, 0, 3]]
def raw29287step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29287step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw29287step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29287 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29287 raw29287Labels = mixedMoment B node4636 node4636Labels := by
  calc
    mixedMoment B raw29287 raw29287Labels = mixedMoment B raw29287step0 raw29287step0Labels := by
      have hz : ∀ j, raw29287 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29287step0 = (fun i j => raw29287 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29287step0 raw29287; decide +kernel
      have hl : raw29287step0Labels = raw29287Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29287 raw29287Labels permutation346 hz
    mixedMoment B raw29287step0 raw29287step0Labels = mixedMoment B raw29287step1 raw29287step1Labels := by
      have ha : raw29287step1 = (fun i j => raw29287step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29287step1 raw29287step0; decide +kernel
      have hl : raw29287step1Labels = raw29287step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29287step0 raw29287step0Labels permutation151 permutation2
    mixedMoment B raw29287step1 raw29287step1Labels = mixedMoment B raw29287step2 raw29287step2Labels := by
      have ha : raw29287step2 = -raw29287step1 := by apply Matrix.ext; change ∀ i j, raw29287step2 i j = -(raw29287step1 i j); unfold raw29287step2 raw29287step1; decide +kernel
      have hl : raw29287step2Labels = raw29287step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4636 node4636Labels := by rfl

def raw29288 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![3, 0, -3]]
def raw29288Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29288step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw29288step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29288step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29288step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29288 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29288 raw29288Labels = mixedMoment B node4630 node4630Labels := by
  calc
    mixedMoment B raw29288 raw29288Labels = mixedMoment B raw29288step0 raw29288step0Labels := by
      have ha : raw29288step0 = (fun i j => raw29288 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29288step0 raw29288; decide +kernel
      have hl : raw29288step0Labels = raw29288Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29288 raw29288Labels permutation686 permutation2
    mixedMoment B raw29288step0 raw29288step0Labels = mixedMoment B raw29288step1 raw29288step1Labels := by
      have ha : raw29288step1 = -raw29288step0 := by apply Matrix.ext; change ∀ i j, raw29288step1 i j = -(raw29288step0 i j); unfold raw29288step1 raw29288step0; decide +kernel
      have hl : raw29288step1Labels = raw29288step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4630 node4630Labels := by rfl

def raw29289 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![2, -1, -1], ![3, 0, -3]]
def raw29289Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29289step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 0, 1], ![2, -1, -1], ![3, 0, -3]]
def raw29289step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29289step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![2, -1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw29289step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29289step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw29289step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29289 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29289 raw29289Labels = mixedMoment B node4643 node4643Labels := by
  calc
    mixedMoment B raw29289 raw29289Labels = mixedMoment B raw29289step0 raw29289step0Labels := by
      have hz : ∀ j, raw29289 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29289step0 = (fun i j => raw29289 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29289step0 raw29289; decide +kernel
      have hl : raw29289step0Labels = raw29289Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29289 raw29289Labels permutation346 hz
    mixedMoment B raw29289step0 raw29289step0Labels = mixedMoment B raw29289step1 raw29289step1Labels := by
      have ha : raw29289step1 = (fun i j => raw29289step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29289step1 raw29289step0; decide +kernel
      have hl : raw29289step1Labels = raw29289step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29289step0 raw29289step0Labels permutation149 permutation2
    mixedMoment B raw29289step1 raw29289step1Labels = mixedMoment B raw29289step2 raw29289step2Labels := by
      have ha : raw29289step2 = -raw29289step1 := by apply Matrix.ext; change ∀ i j, raw29289step2 i j = -(raw29289step1 i j); unfold raw29289step2 raw29289step1; decide +kernel
      have hl : raw29289step2Labels = raw29289step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4643 node4643Labels := by rfl

def raw29290 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw29290Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29290step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw29290step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29290step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-3, 1, 2]]
def raw29290step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29290step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw29290step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw29290step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![3, -1, -2]]
def raw29290step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29290 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29290 raw29290Labels = mixedMoment B node4788 node4788Labels := by
  calc
    mixedMoment B raw29290 raw29290Labels = mixedMoment B raw29290step0 raw29290step0Labels := by
      have hz : ∀ j, raw29290 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29290step0 = (fun i j => raw29290 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29290step0 raw29290; decide +kernel
      have hl : raw29290step0Labels = raw29290Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29290 raw29290Labels permutation346 hz
    mixedMoment B raw29290step0 raw29290step0Labels = mixedMoment B raw29290step1 raw29290step1Labels := by
      have ha : raw29290step1 = (fun i j => raw29290step0 (permutation38 i) (permutation7 j)) := by apply Matrix.ext; unfold raw29290step1 raw29290step0; decide +kernel
      have hl : raw29290step1Labels = raw29290step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29290step0 raw29290step0Labels permutation38 permutation7
    mixedMoment B raw29290step1 raw29290step1Labels = mixedMoment B raw29290step2 raw29290step2Labels := by
      have ha : raw29290step2 = -raw29290step1 := by apply Matrix.ext; change ∀ i j, raw29290step2 i j = -(raw29290step1 i j); unfold raw29290step2 raw29290step1; decide +kernel
      have hl : raw29290step2Labels = raw29290step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw29290step2 raw29290step2Labels = mixedMoment B raw29290step3 raw29290step3Labels := by
      have ha : raw29290step3 = raw29290step2 := by apply Matrix.ext; unfold raw29290step3 raw29290step2; decide +kernel
      have hl : raw29290step2Labels = labelEmbedding10 ∘ raw29290step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw29290step2 raw29290step2Labels raw29290step3Labels labelEmbedding10 hl
    _ = mixedMoment B node4788 node4788Labels := by rfl

def raw29291 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw29291Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29291step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw29291step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29291step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-2, 2, 0], ![-3, 0, 3]]
def raw29291step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29291step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![3, 0, -3]]
def raw29291step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29291 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29291 raw29291Labels = mixedMoment B node4294 node4294Labels := by
  calc
    mixedMoment B raw29291 raw29291Labels = mixedMoment B raw29291step0 raw29291step0Labels := by
      have hz : ∀ j, raw29291 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29291step0 = (fun i j => raw29291 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29291step0 raw29291; decide +kernel
      have hl : raw29291step0Labels = raw29291Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29291 raw29291Labels permutation346 hz
    mixedMoment B raw29291step0 raw29291step0Labels = mixedMoment B raw29291step1 raw29291step1Labels := by
      have ha : raw29291step1 = (fun i j => raw29291step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29291step1 raw29291step0; decide +kernel
      have hl : raw29291step1Labels = raw29291step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29291step0 raw29291step0Labels permutation151 permutation2
    mixedMoment B raw29291step1 raw29291step1Labels = mixedMoment B raw29291step2 raw29291step2Labels := by
      have ha : raw29291step2 = -raw29291step1 := by apply Matrix.ext; change ∀ i j, raw29291step2 i j = -(raw29291step1 i j); unfold raw29291step2 raw29291step1; decide +kernel
      have hl : raw29291step2Labels = raw29291step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4294 node4294Labels := by rfl

def raw29292 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![4, -1, -3]]
def raw29292Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29292step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-3, 0, 3]]
def raw29292step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29292step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, 0, -3]]
def raw29292step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29292 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29292 raw29292Labels = mixedMoment B node4286 node4286Labels := by
  calc
    mixedMoment B raw29292 raw29292Labels = mixedMoment B raw29292step0 raw29292step0Labels := by
      have ha : raw29292step0 = (fun i j => raw29292 (permutation686 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29292step0 raw29292; decide +kernel
      have hl : raw29292step0Labels = raw29292Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29292 raw29292Labels permutation686 permutation2
    mixedMoment B raw29292step0 raw29292step0Labels = mixedMoment B raw29292step1 raw29292step1Labels := by
      have ha : raw29292step1 = -raw29292step0 := by apply Matrix.ext; change ∀ i j, raw29292step1 i j = -(raw29292step0 i j); unfold raw29292step1 raw29292step0; decide +kernel
      have hl : raw29292step1Labels = raw29292step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4286 node4286Labels := by rfl

def raw29293 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -1, -3]]
def raw29293Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29293step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![4, -1, -3]]
def raw29293step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29293step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![1, 0, -1], ![-1, 1, 0], ![-1, 0, 1], ![-3, 0, 3]]
def raw29293step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29293step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![3, 0, -3]]
def raw29293step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29293 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29293 raw29293Labels = mixedMoment B node4302 node4302Labels := by
  calc
    mixedMoment B raw29293 raw29293Labels = mixedMoment B raw29293step0 raw29293step0Labels := by
      have hz : ∀ j, raw29293 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29293step0 = (fun i j => raw29293 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29293step0 raw29293; decide +kernel
      have hl : raw29293step0Labels = raw29293Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29293 raw29293Labels permutation346 hz
    mixedMoment B raw29293step0 raw29293step0Labels = mixedMoment B raw29293step1 raw29293step1Labels := by
      have ha : raw29293step1 = (fun i j => raw29293step0 (permutation149 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29293step1 raw29293step0; decide +kernel
      have hl : raw29293step1Labels = raw29293step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29293step0 raw29293step0Labels permutation149 permutation2
    mixedMoment B raw29293step1 raw29293step1Labels = mixedMoment B raw29293step2 raw29293step2Labels := by
      have ha : raw29293step2 = -raw29293step1 := by apply Matrix.ext; change ∀ i j, raw29293step2 i j = -(raw29293step1 i j); unfold raw29293step2 raw29293step1; decide +kernel
      have hl : raw29293step2Labels = raw29293step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4302 node4302Labels := by rfl

def raw29294 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw29294Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29294step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![4, -1, -3]]
def raw29294step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29294step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![4, -1, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-3, 0, 3]]
def raw29294step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw29294step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![3, 0, -3]]
def raw29294step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical29294 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29294 raw29294Labels = mixedMoment B node4398 node4398Labels := by
  calc
    mixedMoment B raw29294 raw29294Labels = mixedMoment B raw29294step0 raw29294step0Labels := by
      have hz : ∀ j, raw29294 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29294step0 = (fun i j => raw29294 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29294step0 raw29294; decide +kernel
      have hl : raw29294step0Labels = raw29294Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29294 raw29294Labels permutation346 hz
    mixedMoment B raw29294step0 raw29294step0Labels = mixedMoment B raw29294step1 raw29294step1Labels := by
      have ha : raw29294step1 = (fun i j => raw29294step0 (permutation151 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29294step1 raw29294step0; decide +kernel
      have hl : raw29294step1Labels = raw29294step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29294step0 raw29294step0Labels permutation151 permutation2
    mixedMoment B raw29294step1 raw29294step1Labels = mixedMoment B raw29294step2 raw29294step2Labels := by
      have ha : raw29294step2 = -raw29294step1 := by apply Matrix.ext; change ∀ i j, raw29294step2 i j = -(raw29294step1 i j); unfold raw29294step2 raw29294step1; decide +kernel
      have hl : raw29294step2Labels = raw29294step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4398 node4398Labels := by rfl

def raw29295 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![1, -1, 0], ![0, 0, 0], ![1, -1, 0], ![3, -3, 0]]
def raw29295Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29295step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw29295step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29295step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![3, -3]]
def raw29295step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical29295 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29295 raw29295Labels = mixedMoment B node4074 node4074Labels := by
  calc
    mixedMoment B raw29295 raw29295Labels = mixedMoment B raw29295step0 raw29295step0Labels := by
      have hz : ∀ j, raw29295 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29295step0 = (fun i j => raw29295 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29295step0 raw29295; decide +kernel
      have hl : raw29295step0Labels = raw29295Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29295 raw29295Labels permutation434 hz
    mixedMoment B raw29295step0 raw29295step0Labels = mixedMoment B raw29295step1 raw29295step1Labels := by
      have hz : ∀ i, raw29295step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw29295step1 = (fun i j => raw29295step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw29295step1 raw29295step0; decide +kernel
      have hl : raw29295step1Labels = (fun j => raw29295step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw29295step0 raw29295step0Labels permutation6 hz
    _ = mixedMoment B node4074 node4074Labels := by rfl

def raw29296 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![1, -1, 0], ![-1, 1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw29296Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29296step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![1, -1], ![-1, 1], ![1, -1], ![3, -3]]
def raw29296step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29296step1 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![3, -3]]
def raw29296step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical29296 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29296 raw29296Labels = mixedMoment B node4077 node4077Labels := by
  calc
    mixedMoment B raw29296 raw29296Labels = mixedMoment B raw29296step0 raw29296step0Labels := by
      have hz : ∀ i, raw29296 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw29296step0 = (fun i j => raw29296 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw29296step0 raw29296; decide +kernel
      have hl : raw29296step0Labels = (fun j => raw29296Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw29296 raw29296Labels permutation6 hz
    mixedMoment B raw29296step0 raw29296step0Labels = mixedMoment B raw29296step1 raw29296step1Labels := by
      have ha : raw29296step1 = (fun i j => raw29296step0 (permutation158 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29296step1 raw29296step0; decide +kernel
      have hl : raw29296step1Labels = raw29296step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29296step0 raw29296step0Labels permutation158 permutation0
    _ = mixedMoment B node4077 node4077Labels := by rfl

def raw29297 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw29297Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29297step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw29297step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29297step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![3, -3]]
def raw29297step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical29297 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29297 raw29297Labels = mixedMoment B node4074 node4074Labels := by
  calc
    mixedMoment B raw29297 raw29297Labels = mixedMoment B raw29297step0 raw29297step0Labels := by
      have hz : ∀ j, raw29297 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29297step0 = (fun i j => raw29297 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29297step0 raw29297; decide +kernel
      have hl : raw29297step0Labels = raw29297Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29297 raw29297Labels permutation346 hz
    mixedMoment B raw29297step0 raw29297step0Labels = mixedMoment B raw29297step1 raw29297step1Labels := by
      have hz : ∀ i, raw29297step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw29297step1 = (fun i j => raw29297step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw29297step1 raw29297step0; decide +kernel
      have hl : raw29297step1Labels = (fun j => raw29297step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw29297step0 raw29297step0Labels permutation6 hz
    _ = mixedMoment B node4074 node4074Labels := by rfl

def raw29298 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![1, -1, 0], ![3, -3, 0]]
def raw29298Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29298step0 : Matrix (Fin 6) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![1, -1], ![1, -1], ![3, -3]]
def raw29298step0Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical29298 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29298 raw29298Labels = mixedMoment B node4077 node4077Labels := by
  calc
    mixedMoment B raw29298 raw29298Labels = mixedMoment B raw29298step0 raw29298step0Labels := by
      have hz : ∀ i, raw29298 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw29298step0 = (fun i j => raw29298 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw29298step0 raw29298; decide +kernel
      have hl : raw29298step0Labels = (fun j => raw29298Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw29298 raw29298Labels permutation6 hz
    _ = mixedMoment B node4077 node4077Labels := by rfl

def raw29299 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![2, -2, 0], ![3, -3, 0]]
def raw29299Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29299step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![0, 0, 0], ![2, -2, 0], ![3, -3, 0]]
def raw29299step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29299step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![2, -2, 0], ![3, -3, 0]]
def raw29299step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29299step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![2, -2], ![3, -3]]
def raw29299step2Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical29299 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29299 raw29299Labels = mixedMoment B node4076 node4076Labels := by
  calc
    mixedMoment B raw29299 raw29299Labels = mixedMoment B raw29299step0 raw29299step0Labels := by
      have hz : ∀ j, raw29299 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29299step0 = (fun i j => raw29299 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29299step0 raw29299; decide +kernel
      have hl : raw29299step0Labels = raw29299Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29299 raw29299Labels permutation434 hz
    mixedMoment B raw29299step0 raw29299step0Labels = mixedMoment B raw29299step1 raw29299step1Labels := by
      have hz : ∀ j, raw29299step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29299step1 = (fun i j => raw29299step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29299step1 raw29299step0; decide +kernel
      have hl : raw29299step1Labels = raw29299step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29299step0 raw29299step0Labels permutation80 hz
    mixedMoment B raw29299step1 raw29299step1Labels = mixedMoment B raw29299step2 raw29299step2Labels := by
      have hz : ∀ i, raw29299step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw29299step2 = (fun i j => raw29299step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw29299step2 raw29299step1; decide +kernel
      have hl : raw29299step2Labels = (fun j => raw29299step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw29299step1 raw29299step1Labels permutation6 hz
    _ = mixedMoment B node4076 node4076Labels := by rfl

def raw29300 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![2, -2, 0], ![3, -3, 0]]
def raw29300Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29300step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -3, 0]]
def raw29300step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29300step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![2, -2], ![3, -3]]
def raw29300step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29300step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![2, -2], ![-1, 1], ![-1, 1], ![-3, 3]]
def raw29300step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29300step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![3, -3]]
def raw29300step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical29300 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29300 raw29300Labels = mixedMoment B node4074 node4074Labels := by
  calc
    mixedMoment B raw29300 raw29300Labels = mixedMoment B raw29300step0 raw29300step0Labels := by
      have hz : ∀ j, raw29300 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29300step0 = (fun i j => raw29300 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29300step0 raw29300; decide +kernel
      have hl : raw29300step0Labels = raw29300Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29300 raw29300Labels permutation434 hz
    mixedMoment B raw29300step0 raw29300step0Labels = mixedMoment B raw29300step1 raw29300step1Labels := by
      have hz : ∀ i, raw29300step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw29300step1 = (fun i j => raw29300step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw29300step1 raw29300step0; decide +kernel
      have hl : raw29300step1Labels = (fun j => raw29300step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw29300step0 raw29300step0Labels permutation6 hz
    mixedMoment B raw29300step1 raw29300step1Labels = mixedMoment B raw29300step2 raw29300step2Labels := by
      have ha : raw29300step2 = (fun i j => raw29300step1 (permutation149 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29300step2 raw29300step1; decide +kernel
      have hl : raw29300step2Labels = raw29300step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29300step1 raw29300step1Labels permutation149 permutation0
    mixedMoment B raw29300step2 raw29300step2Labels = mixedMoment B raw29300step3 raw29300step3Labels := by
      have ha : raw29300step3 = -raw29300step2 := by apply Matrix.ext; change ∀ i j, raw29300step3 i j = -(raw29300step2 i j); unfold raw29300step3 raw29300step2; decide +kernel
      have hl : raw29300step3Labels = raw29300step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4074 node4074Labels := by rfl

def raw29301 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -3, 0]]
def raw29301Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29301step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![-1, 1, 0], ![2, -2, 0], ![3, -3, 0]]
def raw29301step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29301step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![2, -2], ![3, -3]]
def raw29301step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29301step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![3, -3], ![2, -2], ![-1, 1], ![-1, 1], ![-3, 3]]
def raw29301step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29301step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![1, -1], ![3, -3]]
def raw29301step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical29301 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29301 raw29301Labels = mixedMoment B node4074 node4074Labels := by
  calc
    mixedMoment B raw29301 raw29301Labels = mixedMoment B raw29301step0 raw29301step0Labels := by
      have hz : ∀ j, raw29301 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29301step0 = (fun i j => raw29301 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29301step0 raw29301; decide +kernel
      have hl : raw29301step0Labels = raw29301Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29301 raw29301Labels permutation346 hz
    mixedMoment B raw29301step0 raw29301step0Labels = mixedMoment B raw29301step1 raw29301step1Labels := by
      have hz : ∀ i, raw29301step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw29301step1 = (fun i j => raw29301step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw29301step1 raw29301step0; decide +kernel
      have hl : raw29301step1Labels = (fun j => raw29301step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw29301step0 raw29301step0Labels permutation6 hz
    mixedMoment B raw29301step1 raw29301step1Labels = mixedMoment B raw29301step2 raw29301step2Labels := by
      have ha : raw29301step2 = (fun i j => raw29301step1 (permutation149 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29301step2 raw29301step1; decide +kernel
      have hl : raw29301step2Labels = raw29301step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29301step1 raw29301step1Labels permutation149 permutation0
    mixedMoment B raw29301step2 raw29301step2Labels = mixedMoment B raw29301step3 raw29301step3Labels := by
      have ha : raw29301step3 = -raw29301step2 := by apply Matrix.ext; change ∀ i j, raw29301step3 i j = -(raw29301step2 i j); unfold raw29301step3 raw29301step2; decide +kernel
      have hl : raw29301step3Labels = raw29301step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4074 node4074Labels := by rfl

def raw29302 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![0, 0, 0], ![0, 0, 0], ![1, -1, 0], ![4, -4, 0]]
def raw29302Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29302step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![0, 0, 0], ![1, -1, 0], ![4, -4, 0]]
def raw29302step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29302step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-3, 3, 0], ![-2, 2, 0], ![1, -1, 0], ![4, -4, 0]]
def raw29302step1Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29302step2 : Matrix (Fin 4) (Fin 2) ℤ := ![![-3, 3], ![-2, 2], ![1, -1], ![4, -4]]
def raw29302step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29302step3 : Matrix (Fin 4) (Fin 2) ℤ := ![![4, -4], ![1, -1], ![-2, 2], ![-3, 3]]
def raw29302step3Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29302step4 : Matrix (Fin 4) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![2, -2], ![3, -3]]
def raw29302step4Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical29302 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29302 raw29302Labels = mixedMoment B node4067 node4067Labels := by
  calc
    mixedMoment B raw29302 raw29302Labels = mixedMoment B raw29302step0 raw29302step0Labels := by
      have hz : ∀ j, raw29302 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29302step0 = (fun i j => raw29302 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29302step0 raw29302; decide +kernel
      have hl : raw29302step0Labels = raw29302Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29302 raw29302Labels permutation434 hz
    mixedMoment B raw29302step0 raw29302step0Labels = mixedMoment B raw29302step1 raw29302step1Labels := by
      have hz : ∀ j, raw29302step0 (permutation80 0) j = 0 := by decide +kernel
      have ha : raw29302step1 = (fun i j => raw29302step0 (permutation80 i.succ) j) := by apply Matrix.ext; unfold raw29302step1 raw29302step0; decide +kernel
      have hl : raw29302step1Labels = raw29302step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29302step0 raw29302step0Labels permutation80 hz
    mixedMoment B raw29302step1 raw29302step1Labels = mixedMoment B raw29302step2 raw29302step2Labels := by
      have hz : ∀ i, raw29302step1 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw29302step2 = (fun i j => raw29302step1 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw29302step2 raw29302step1; decide +kernel
      have hl : raw29302step2Labels = (fun j => raw29302step1Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw29302step1 raw29302step1Labels permutation6 hz
    mixedMoment B raw29302step2 raw29302step2Labels = mixedMoment B raw29302step3 raw29302step3Labels := by
      have ha : raw29302step3 = (fun i j => raw29302step2 (permutation31 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29302step3 raw29302step2; decide +kernel
      have hl : raw29302step3Labels = raw29302step2Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29302step2 raw29302step2Labels permutation31 permutation0
    mixedMoment B raw29302step3 raw29302step3Labels = mixedMoment B raw29302step4 raw29302step4Labels := by
      have ha : raw29302step4 = -raw29302step3 := by apply Matrix.ext; change ∀ i j, raw29302step4 i j = -(raw29302step3 i j); unfold raw29302step4 raw29302step3; decide +kernel
      have hl : raw29302step4Labels = raw29302step3Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4067 node4067Labels := by rfl

def raw29303 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![-1, 1, 0], ![0, 0, 0], ![1, -1, 0], ![4, -4, 0]]
def raw29303Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29303step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -4, 0]]
def raw29303step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29303step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![1, -1], ![4, -4]]
def raw29303step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29303step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![4, -4], ![1, -1], ![-1, 1], ![-1, 1], ![-3, 3]]
def raw29303step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29303step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![3, -3]]
def raw29303step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical29303 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29303 raw29303Labels = mixedMoment B node4064 node4064Labels := by
  calc
    mixedMoment B raw29303 raw29303Labels = mixedMoment B raw29303step0 raw29303step0Labels := by
      have hz : ∀ j, raw29303 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw29303step0 = (fun i j => raw29303 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw29303step0 raw29303; decide +kernel
      have hl : raw29303step0Labels = raw29303Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29303 raw29303Labels permutation434 hz
    mixedMoment B raw29303step0 raw29303step0Labels = mixedMoment B raw29303step1 raw29303step1Labels := by
      have hz : ∀ i, raw29303step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw29303step1 = (fun i j => raw29303step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw29303step1 raw29303step0; decide +kernel
      have hl : raw29303step1Labels = (fun j => raw29303step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw29303step0 raw29303step0Labels permutation6 hz
    mixedMoment B raw29303step1 raw29303step1Labels = mixedMoment B raw29303step2 raw29303step2Labels := by
      have ha : raw29303step2 = (fun i j => raw29303step1 (permutation149 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29303step2 raw29303step1; decide +kernel
      have hl : raw29303step2Labels = raw29303step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29303step1 raw29303step1Labels permutation149 permutation0
    mixedMoment B raw29303step2 raw29303step2Labels = mixedMoment B raw29303step3 raw29303step3Labels := by
      have ha : raw29303step3 = -raw29303step2 := by apply Matrix.ext; change ∀ i j, raw29303step3 i j = -(raw29303step2 i j); unfold raw29303step3 raw29303step2; decide +kernel
      have hl : raw29303step3Labels = raw29303step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4064 node4064Labels := by rfl

def raw29304 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![0, 0, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -4, 0]]
def raw29304Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29304step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 1, 0], ![-1, 1, 0], ![1, -1, 0], ![4, -4, 0]]
def raw29304step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw29304step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-3, 3], ![-1, 1], ![-1, 1], ![1, -1], ![4, -4]]
def raw29304step1Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29304step2 : Matrix (Fin 5) (Fin 2) ℤ := ![![4, -4], ![1, -1], ![-1, 1], ![-1, 1], ![-3, 3]]
def raw29304step2Labels : Fin 2 → Fin 2 := ![0, 1]

def raw29304step3 : Matrix (Fin 5) (Fin 2) ℤ := ![![-4, 4], ![-1, 1], ![1, -1], ![1, -1], ![3, -3]]
def raw29304step3Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical29304 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29304 raw29304Labels = mixedMoment B node4064 node4064Labels := by
  calc
    mixedMoment B raw29304 raw29304Labels = mixedMoment B raw29304step0 raw29304step0Labels := by
      have hz : ∀ j, raw29304 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29304step0 = (fun i j => raw29304 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29304step0 raw29304; decide +kernel
      have hl : raw29304step0Labels = raw29304Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29304 raw29304Labels permutation346 hz
    mixedMoment B raw29304step0 raw29304step0Labels = mixedMoment B raw29304step1 raw29304step1Labels := by
      have hz : ∀ i, raw29304step0 i (permutation6 0) = 0 := by decide +kernel
      have ha : raw29304step1 = (fun i j => raw29304step0 i (permutation6 j.succ)) := by apply Matrix.ext; unfold raw29304step1 raw29304step0; decide +kernel
      have hl : raw29304step1Labels = (fun j => raw29304step0Labels (permutation6 j.succ)) := by decide +kernel
      rw [ha, hl]
      exact delete_zero_factor B raw29304step0 raw29304step0Labels permutation6 hz
    mixedMoment B raw29304step1 raw29304step1Labels = mixedMoment B raw29304step2 raw29304step2Labels := by
      have ha : raw29304step2 = (fun i j => raw29304step1 (permutation149 i) (permutation0 j)) := by apply Matrix.ext; unfold raw29304step2 raw29304step1; decide +kernel
      have hl : raw29304step2Labels = raw29304step1Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29304step1 raw29304step1Labels permutation149 permutation0
    mixedMoment B raw29304step2 raw29304step2Labels = mixedMoment B raw29304step3 raw29304step3Labels := by
      have ha : raw29304step3 = -raw29304step2 := by apply Matrix.ext; change ∀ i j, raw29304step3 i j = -(raw29304step2 i j); unfold raw29304step3 raw29304step2; decide +kernel
      have hl : raw29304step3Labels = raw29304step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4064 node4064Labels := by rfl

def raw29305 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29305Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29305step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-2, 2, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29305step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29305 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29305 raw29305Labels = mixedMoment B node1816 node1816Labels := by
  calc
    mixedMoment B raw29305 raw29305Labels = mixedMoment B raw29305step0 raw29305step0Labels := by
      have hz : ∀ j, raw29305 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29305step0 = (fun i j => raw29305 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29305step0 raw29305; decide +kernel
      have hl : raw29305step0Labels = raw29305Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29305 raw29305Labels permutation346 hz
    _ = mixedMoment B node1816 node1816Labels := by rfl

def raw29306 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29306Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29306 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29306 raw29306Labels = mixedMoment B node1968 node1968Labels := by
  calc
    _ = mixedMoment B node1968 node1968Labels := by rfl

def raw29307 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29307Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29307step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 2, -2], ![2, -2, 0], ![2, -1, -1]]
def raw29307step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29307 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29307 raw29307Labels = mixedMoment B node2039 node2039Labels := by
  calc
    mixedMoment B raw29307 raw29307Labels = mixedMoment B raw29307step0 raw29307step0Labels := by
      have hz : ∀ j, raw29307 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29307step0 = (fun i j => raw29307 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29307step0 raw29307; decide +kernel
      have hl : raw29307step0Labels = raw29307Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29307 raw29307Labels permutation346 hz
    _ = mixedMoment B node2039 node2039Labels := by rfl

def raw29308 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 0, 0], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw29308Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29308step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 1, -2], ![2, -2, 0], ![1, 0, -1]]
def raw29308step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29308step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw29308step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29308 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29308 raw29308Labels = mixedMoment B node2058 node2058Labels := by
  calc
    mixedMoment B raw29308 raw29308Labels = mixedMoment B raw29308step0 raw29308step0Labels := by
      have hz : ∀ j, raw29308 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29308step0 = (fun i j => raw29308 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29308step0 raw29308; decide +kernel
      have hl : raw29308step0Labels = raw29308Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29308 raw29308Labels permutation346 hz
    mixedMoment B raw29308step0 raw29308step0Labels = mixedMoment B raw29308step1 raw29308step1Labels := by
      have ha : raw29308step1 = (fun i j => raw29308step0 (permutation36 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29308step1 raw29308step0; decide +kernel
      have hl : raw29308step1Labels = raw29308step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29308step0 raw29308step0Labels permutation36 permutation2
    _ = mixedMoment B node2058 node2058Labels := by rfl

def raw29309 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![0, 0, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw29309Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29309step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -1, 1], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw29309step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29309step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw29309step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29309 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29309 raw29309Labels = mixedMoment B node3174 node3174Labels := by
  calc
    mixedMoment B raw29309 raw29309Labels = mixedMoment B raw29309step0 raw29309step0Labels := by
      have hz : ∀ j, raw29309 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29309step0 = (fun i j => raw29309 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29309step0 raw29309; decide +kernel
      have hl : raw29309step0Labels = raw29309Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29309 raw29309Labels permutation346 hz
    mixedMoment B raw29309step0 raw29309step0Labels = mixedMoment B raw29309step1 raw29309step1Labels := by
      have ha : raw29309step1 = (fun i j => raw29309step0 (permutation39 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29309step1 raw29309step0; decide +kernel
      have hl : raw29309step1Labels = raw29309step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29309step0 raw29309step0Labels permutation39 permutation2
    _ = mixedMoment B node3174 node3174Labels := by rfl

def raw29310 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![1, -1, 0], ![-1, -1, 2], ![2, 0, -2], ![2, -1, -1]]
def raw29310Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29310step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, -1, 2], ![-1, 0, 1], ![1, -1, 0], ![2, -1, -1], ![2, 0, -2]]
def raw29310step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29310 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29310 raw29310Labels = mixedMoment B node3162 node3162Labels := by
  calc
    mixedMoment B raw29310 raw29310Labels = mixedMoment B raw29310step0 raw29310step0Labels := by
      have ha : raw29310step0 = (fun i j => raw29310 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29310step0 raw29310; decide +kernel
      have hl : raw29310step0Labels = raw29310Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29310 raw29310Labels permutation201 permutation2
    _ = mixedMoment B node3162 node3162Labels := by rfl

def raw29311 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![0, 0, 0], ![-1, -1, 2], ![3, -1, -2], ![2, -1, -1]]
def raw29311Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29311step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![-1, 0, 1], ![-1, -1, 2], ![3, -1, -2], ![2, -1, -1]]
def raw29311step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29311step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, -1, -2], ![2, -1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-3, 3, 0]]
def raw29311step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw29311step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, 0, -1], ![1, 1, -2], ![3, -3, 0]]
def raw29311step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical29311 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw29311 raw29311Labels = mixedMoment B node2340 node2340Labels := by
  calc
    mixedMoment B raw29311 raw29311Labels = mixedMoment B raw29311step0 raw29311step0Labels := by
      have hz : ∀ j, raw29311 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw29311step0 = (fun i j => raw29311 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw29311step0 raw29311; decide +kernel
      have hl : raw29311step0Labels = raw29311Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw29311 raw29311Labels permutation346 hz
    mixedMoment B raw29311step0 raw29311step0Labels = mixedMoment B raw29311step1 raw29311step1Labels := by
      have ha : raw29311step1 = (fun i j => raw29311step0 (permutation125 i) (permutation2 j)) := by apply Matrix.ext; unfold raw29311step1 raw29311step0; decide +kernel
      have hl : raw29311step1Labels = raw29311step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw29311step0 raw29311step0Labels permutation125 permutation2
    mixedMoment B raw29311step1 raw29311step1Labels = mixedMoment B raw29311step2 raw29311step2Labels := by
      have ha : raw29311step2 = -raw29311step1 := by apply Matrix.ext; change ∀ i j, raw29311step2 i j = -(raw29311step1 i j); unfold raw29311step2 raw29311step1; decide +kernel
      have hl : raw29311step2Labels = raw29311step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2340 node2340Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
