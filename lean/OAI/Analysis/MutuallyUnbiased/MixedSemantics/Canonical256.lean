import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes14
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes36
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes53
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes58
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes59
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes67
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes77
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes80
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw32768 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32768Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32768step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32768step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32768step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32768step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32768step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32768step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32768 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32768 raw32768Labels = mixedMoment B node3850 node3850Labels := by
  calc
    mixedMoment B raw32768 raw32768Labels = mixedMoment B raw32768step0 raw32768step0Labels := by
      have hz : ∀ j, raw32768 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32768step0 = (fun i j => raw32768 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32768step0 raw32768; decide +kernel
      have hl : raw32768step0Labels = raw32768Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32768 raw32768Labels permutation346 hz
    mixedMoment B raw32768step0 raw32768step0Labels = mixedMoment B raw32768step1 raw32768step1Labels := by
      have ha : raw32768step1 = (fun i j => raw32768step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32768step1 raw32768step0; decide +kernel
      have hl : raw32768step1Labels = raw32768step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32768step0 raw32768step0Labels permutation143 permutation7
    mixedMoment B raw32768step1 raw32768step1Labels = mixedMoment B raw32768step2 raw32768step2Labels := by
      have ha : raw32768step2 = raw32768step1 := by apply Matrix.ext; unfold raw32768step2 raw32768step1; decide +kernel
      have hl : raw32768step1Labels = labelEmbedding1 ∘ raw32768step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32768step1 raw32768step1Labels raw32768step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3850 node3850Labels := by rfl

def raw32769 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw32769Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32769step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw32769step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32769step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32769step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32769step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32769step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32769 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32769 raw32769Labels = mixedMoment B node3807 node3807Labels := by
  calc
    mixedMoment B raw32769 raw32769Labels = mixedMoment B raw32769step0 raw32769step0Labels := by
      have hz : ∀ j, raw32769 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32769step0 = (fun i j => raw32769 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32769step0 raw32769; decide +kernel
      have hl : raw32769step0Labels = raw32769Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32769 raw32769Labels permutation346 hz
    mixedMoment B raw32769step0 raw32769step0Labels = mixedMoment B raw32769step1 raw32769step1Labels := by
      have ha : raw32769step1 = (fun i j => raw32769step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32769step1 raw32769step0; decide +kernel
      have hl : raw32769step1Labels = raw32769step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32769step0 raw32769step0Labels permutation143 permutation7
    mixedMoment B raw32769step1 raw32769step1Labels = mixedMoment B raw32769step2 raw32769step2Labels := by
      have ha : raw32769step2 = raw32769step1 := by apply Matrix.ext; unfold raw32769step2 raw32769step1; decide +kernel
      have hl : raw32769step1Labels = labelEmbedding1 ∘ raw32769step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32769step1 raw32769step1Labels raw32769step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3807 node3807Labels := by rfl

def raw32770 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32770Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32770step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32770step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32770step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-2, 1, 1]]
def raw32770step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32770step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw32770step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32770step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1]]
def raw32770step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32770 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32770 raw32770Labels = mixedMoment B node3876 node3876Labels := by
  calc
    mixedMoment B raw32770 raw32770Labels = mixedMoment B raw32770step0 raw32770step0Labels := by
      have hz : ∀ j, raw32770 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32770step0 = (fun i j => raw32770 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32770step0 raw32770; decide +kernel
      have hl : raw32770step0Labels = raw32770Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32770 raw32770Labels permutation346 hz
    mixedMoment B raw32770step0 raw32770step0Labels = mixedMoment B raw32770step1 raw32770step1Labels := by
      have ha : raw32770step1 = (fun i j => raw32770step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32770step1 raw32770step0; decide +kernel
      have hl : raw32770step1Labels = raw32770step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32770step0 raw32770step0Labels permutation44 permutation7
    mixedMoment B raw32770step1 raw32770step1Labels = mixedMoment B raw32770step2 raw32770step2Labels := by
      have ha : raw32770step2 = -raw32770step1 := by apply Matrix.ext; change ∀ i j, raw32770step2 i j = -(raw32770step1 i j); unfold raw32770step2 raw32770step1; decide +kernel
      have hl : raw32770step2Labels = raw32770step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32770step2 raw32770step2Labels = mixedMoment B raw32770step3 raw32770step3Labels := by
      have ha : raw32770step3 = raw32770step2 := by apply Matrix.ext; unfold raw32770step3 raw32770step2; decide +kernel
      have hl : raw32770step2Labels = labelEmbedding1 ∘ raw32770step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32770step2 raw32770step2Labels raw32770step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3876 node3876Labels := by rfl

def raw32771 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32771Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32771step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32771step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32771step1 : Matrix (Fin 4) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32771step1Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32771step2 : Matrix (Fin 4) (Fin 3) ℤ := ![![2, 2, -4], ![1, -2, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw32771step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32771step3 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32771step3Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32771step4 : Matrix (Fin 4) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 2, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32771step4Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32771 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32771 raw32771Labels = mixedMoment B node3305 node3305Labels := by
  calc
    mixedMoment B raw32771 raw32771Labels = mixedMoment B raw32771step0 raw32771step0Labels := by
      have hz : ∀ j, raw32771 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32771step0 = (fun i j => raw32771 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32771step0 raw32771; decide +kernel
      have hl : raw32771step0Labels = raw32771Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32771 raw32771Labels permutation346 hz
    mixedMoment B raw32771step0 raw32771step0Labels = mixedMoment B raw32771step1 raw32771step1Labels := by
      have hz : ∀ j, raw32771step0 (permutation56 0) j = 0 := by decide +kernel
      have ha : raw32771step1 = (fun i j => raw32771step0 (permutation56 i.succ) j) := by apply Matrix.ext; unfold raw32771step1 raw32771step0; decide +kernel
      have hl : raw32771step1Labels = raw32771step0Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32771step0 raw32771step0Labels permutation56 hz
    mixedMoment B raw32771step1 raw32771step1Labels = mixedMoment B raw32771step2 raw32771step2Labels := by
      have ha : raw32771step2 = (fun i j => raw32771step1 (permutation10 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32771step2 raw32771step1; decide +kernel
      have hl : raw32771step2Labels = raw32771step1Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32771step1 raw32771step1Labels permutation10 permutation7
    mixedMoment B raw32771step2 raw32771step2Labels = mixedMoment B raw32771step3 raw32771step3Labels := by
      have ha : raw32771step3 = -raw32771step2 := by apply Matrix.ext; change ∀ i j, raw32771step3 i j = -(raw32771step2 i j); unfold raw32771step3 raw32771step2; decide +kernel
      have hl : raw32771step3Labels = raw32771step2Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32771step3 raw32771step3Labels = mixedMoment B raw32771step4 raw32771step4Labels := by
      have ha : raw32771step4 = raw32771step3 := by apply Matrix.ext; unfold raw32771step4 raw32771step3; decide +kernel
      have hl : raw32771step3Labels = labelEmbedding1 ∘ raw32771step4Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32771step3 raw32771step3Labels raw32771step4Labels labelEmbedding1 hl
    _ = mixedMoment B node3305 node3305Labels := by rfl

def raw32772 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32772Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32772step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw32772step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32772step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32772step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32772step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32772step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32772 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32772 raw32772Labels = mixedMoment B node3553 node3553Labels := by
  calc
    mixedMoment B raw32772 raw32772Labels = mixedMoment B raw32772step0 raw32772step0Labels := by
      have ha : raw32772step0 = (fun i j => raw32772 (permutation224 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32772step0 raw32772; decide +kernel
      have hl : raw32772step0Labels = raw32772Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32772 raw32772Labels permutation224 permutation7
    mixedMoment B raw32772step0 raw32772step0Labels = mixedMoment B raw32772step1 raw32772step1Labels := by
      have ha : raw32772step1 = -raw32772step0 := by apply Matrix.ext; change ∀ i j, raw32772step1 i j = -(raw32772step0 i j); unfold raw32772step1 raw32772step0; decide +kernel
      have hl : raw32772step1Labels = raw32772step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32772step1 raw32772step1Labels = mixedMoment B raw32772step2 raw32772step2Labels := by
      have ha : raw32772step2 = raw32772step1 := by apply Matrix.ext; unfold raw32772step2 raw32772step1; decide +kernel
      have hl : raw32772step1Labels = labelEmbedding1 ∘ raw32772step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32772step1 raw32772step1Labels raw32772step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3553 node3553Labels := by rfl

def raw32773 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32773Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32773step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 1, 0], ![-2, 0, 2]]
def raw32773step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32773step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32773step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32773step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw32773step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32773 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32773 raw32773Labels = mixedMoment B node3557 node3557Labels := by
  calc
    mixedMoment B raw32773 raw32773Labels = mixedMoment B raw32773step0 raw32773step0Labels := by
      have ha : raw32773step0 = (fun i j => raw32773 (permutation224 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32773step0 raw32773; decide +kernel
      have hl : raw32773step0Labels = raw32773Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32773 raw32773Labels permutation224 permutation7
    mixedMoment B raw32773step0 raw32773step0Labels = mixedMoment B raw32773step1 raw32773step1Labels := by
      have ha : raw32773step1 = -raw32773step0 := by apply Matrix.ext; change ∀ i j, raw32773step1 i j = -(raw32773step0 i j); unfold raw32773step1 raw32773step0; decide +kernel
      have hl : raw32773step1Labels = raw32773step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32773step1 raw32773step1Labels = mixedMoment B raw32773step2 raw32773step2Labels := by
      have ha : raw32773step2 = raw32773step1 := by apply Matrix.ext; unfold raw32773step2 raw32773step1; decide +kernel
      have hl : raw32773step1Labels = labelEmbedding1 ∘ raw32773step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32773step1 raw32773step1Labels raw32773step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3557 node3557Labels := by rfl

def raw32774 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![0, -1, 1], ![2, 0, -2]]
def raw32774Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32774step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 0, 2]]
def raw32774step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32774step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32774step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32774step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32774step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32774 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32774 raw32774Labels = mixedMoment B node3514 node3514Labels := by
  calc
    mixedMoment B raw32774 raw32774Labels = mixedMoment B raw32774step0 raw32774step0Labels := by
      have ha : raw32774step0 = (fun i j => raw32774 (permutation224 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32774step0 raw32774; decide +kernel
      have hl : raw32774step0Labels = raw32774Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32774 raw32774Labels permutation224 permutation7
    mixedMoment B raw32774step0 raw32774step0Labels = mixedMoment B raw32774step1 raw32774step1Labels := by
      have ha : raw32774step1 = -raw32774step0 := by apply Matrix.ext; change ∀ i j, raw32774step1 i j = -(raw32774step0 i j); unfold raw32774step1 raw32774step0; decide +kernel
      have hl : raw32774step1Labels = raw32774step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32774step1 raw32774step1Labels = mixedMoment B raw32774step2 raw32774step2Labels := by
      have ha : raw32774step2 = raw32774step1 := by apply Matrix.ext; unfold raw32774step2 raw32774step1; decide +kernel
      have hl : raw32774step1Labels = labelEmbedding1 ∘ raw32774step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32774step1 raw32774step1Labels raw32774step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3514 node3514Labels := by rfl

def raw32775 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32775Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32775step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw32775step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32775step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32775step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32775step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32775step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32775 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32775 raw32775Labels = mixedMoment B node3558 node3558Labels := by
  calc
    mixedMoment B raw32775 raw32775Labels = mixedMoment B raw32775step0 raw32775step0Labels := by
      have ha : raw32775step0 = (fun i j => raw32775 (permutation224 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32775step0 raw32775; decide +kernel
      have hl : raw32775step0Labels = raw32775Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32775 raw32775Labels permutation224 permutation7
    mixedMoment B raw32775step0 raw32775step0Labels = mixedMoment B raw32775step1 raw32775step1Labels := by
      have ha : raw32775step1 = -raw32775step0 := by apply Matrix.ext; change ∀ i j, raw32775step1 i j = -(raw32775step0 i j); unfold raw32775step1 raw32775step0; decide +kernel
      have hl : raw32775step1Labels = raw32775step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32775step1 raw32775step1Labels = mixedMoment B raw32775step2 raw32775step2Labels := by
      have ha : raw32775step2 = raw32775step1 := by apply Matrix.ext; unfold raw32775step2 raw32775step1; decide +kernel
      have hl : raw32775step1Labels = labelEmbedding1 ∘ raw32775step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32775step1 raw32775step1Labels raw32775step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3558 node3558Labels := by rfl

def raw32776 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32776Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32776step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32776step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32776step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![-1, -1, 2], ![-2, 0, 2]]
def raw32776step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32776step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw32776step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32776step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 1, -2], ![2, 0, -2]]
def raw32776step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32776 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32776 raw32776Labels = mixedMoment B node3555 node3555Labels := by
  calc
    mixedMoment B raw32776 raw32776Labels = mixedMoment B raw32776step0 raw32776step0Labels := by
      have hz : ∀ j, raw32776 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32776step0 = (fun i j => raw32776 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32776step0 raw32776; decide +kernel
      have hl : raw32776step0Labels = raw32776Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32776 raw32776Labels permutation346 hz
    mixedMoment B raw32776step0 raw32776step0Labels = mixedMoment B raw32776step1 raw32776step1Labels := by
      have ha : raw32776step1 = (fun i j => raw32776step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32776step1 raw32776step0; decide +kernel
      have hl : raw32776step1Labels = raw32776step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32776step0 raw32776step0Labels permutation44 permutation7
    mixedMoment B raw32776step1 raw32776step1Labels = mixedMoment B raw32776step2 raw32776step2Labels := by
      have ha : raw32776step2 = -raw32776step1 := by apply Matrix.ext; change ∀ i j, raw32776step2 i j = -(raw32776step1 i j); unfold raw32776step2 raw32776step1; decide +kernel
      have hl : raw32776step2Labels = raw32776step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32776step2 raw32776step2Labels = mixedMoment B raw32776step3 raw32776step3Labels := by
      have ha : raw32776step3 = raw32776step2 := by apply Matrix.ext; unfold raw32776step3 raw32776step2; decide +kernel
      have hl : raw32776step2Labels = labelEmbedding1 ∘ raw32776step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32776step2 raw32776step2Labels raw32776step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3555 node3555Labels := by rfl

def raw32777 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32777Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32777step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw32777step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32777step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw32777step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32777step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw32777step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32777 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32777 raw32777Labels = mixedMoment B node3556 node3556Labels := by
  calc
    mixedMoment B raw32777 raw32777Labels = mixedMoment B raw32777step0 raw32777step0Labels := by
      have ha : raw32777step0 = (fun i j => raw32777 (permutation224 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32777step0 raw32777; decide +kernel
      have hl : raw32777step0Labels = raw32777Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32777 raw32777Labels permutation224 permutation7
    mixedMoment B raw32777step0 raw32777step0Labels = mixedMoment B raw32777step1 raw32777step1Labels := by
      have ha : raw32777step1 = -raw32777step0 := by apply Matrix.ext; change ∀ i j, raw32777step1 i j = -(raw32777step0 i j); unfold raw32777step1 raw32777step0; decide +kernel
      have hl : raw32777step1Labels = raw32777step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32777step1 raw32777step1Labels = mixedMoment B raw32777step2 raw32777step2Labels := by
      have ha : raw32777step2 = raw32777step1 := by apply Matrix.ext; unfold raw32777step2 raw32777step1; decide +kernel
      have hl : raw32777step1Labels = labelEmbedding1 ∘ raw32777step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32777step1 raw32777step1Labels raw32777step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3556 node3556Labels := by rfl

def raw32778 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw32778Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32778step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![0, -1, 1], ![2, 0, -2]]
def raw32778step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32778step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, -1, 2], ![-2, 0, 2]]
def raw32778step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32778step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw32778step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32778step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw32778step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32778 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32778 raw32778Labels = mixedMoment B node3522 node3522Labels := by
  calc
    mixedMoment B raw32778 raw32778Labels = mixedMoment B raw32778step0 raw32778step0Labels := by
      have hz : ∀ j, raw32778 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32778step0 = (fun i j => raw32778 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32778step0 raw32778; decide +kernel
      have hl : raw32778step0Labels = raw32778Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32778 raw32778Labels permutation346 hz
    mixedMoment B raw32778step0 raw32778step0Labels = mixedMoment B raw32778step1 raw32778step1Labels := by
      have ha : raw32778step1 = (fun i j => raw32778step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32778step1 raw32778step0; decide +kernel
      have hl : raw32778step1Labels = raw32778step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32778step0 raw32778step0Labels permutation44 permutation7
    mixedMoment B raw32778step1 raw32778step1Labels = mixedMoment B raw32778step2 raw32778step2Labels := by
      have ha : raw32778step2 = -raw32778step1 := by apply Matrix.ext; change ∀ i j, raw32778step2 i j = -(raw32778step1 i j); unfold raw32778step2 raw32778step1; decide +kernel
      have hl : raw32778step2Labels = raw32778step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32778step2 raw32778step2Labels = mixedMoment B raw32778step3 raw32778step3Labels := by
      have ha : raw32778step3 = raw32778step2 := by apply Matrix.ext; unfold raw32778step3 raw32778step2; decide +kernel
      have hl : raw32778step2Labels = labelEmbedding1 ∘ raw32778step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32778step2 raw32778step2Labels raw32778step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3522 node3522Labels := by rfl

def raw32779 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32779Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32779step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![2, -1, -1], ![1, -2, 1], ![1, 1, -2]]
def raw32779step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32779step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, -1, 2], ![-2, 1, 1]]
def raw32779step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32779step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw32779step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32779step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw32779step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32779 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32779 raw32779Labels = mixedMoment B node3565 node3565Labels := by
  calc
    mixedMoment B raw32779 raw32779Labels = mixedMoment B raw32779step0 raw32779step0Labels := by
      have hz : ∀ j, raw32779 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32779step0 = (fun i j => raw32779 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32779step0 raw32779; decide +kernel
      have hl : raw32779step0Labels = raw32779Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32779 raw32779Labels permutation346 hz
    mixedMoment B raw32779step0 raw32779step0Labels = mixedMoment B raw32779step1 raw32779step1Labels := by
      have ha : raw32779step1 = (fun i j => raw32779step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32779step1 raw32779step0; decide +kernel
      have hl : raw32779step1Labels = raw32779step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32779step0 raw32779step0Labels permutation44 permutation7
    mixedMoment B raw32779step1 raw32779step1Labels = mixedMoment B raw32779step2 raw32779step2Labels := by
      have ha : raw32779step2 = -raw32779step1 := by apply Matrix.ext; change ∀ i j, raw32779step2 i j = -(raw32779step1 i j); unfold raw32779step2 raw32779step1; decide +kernel
      have hl : raw32779step2Labels = raw32779step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32779step2 raw32779step2Labels = mixedMoment B raw32779step3 raw32779step3Labels := by
      have ha : raw32779step3 = raw32779step2 := by apply Matrix.ext; unfold raw32779step3 raw32779step2; decide +kernel
      have hl : raw32779step2Labels = labelEmbedding1 ∘ raw32779step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32779step2 raw32779step2Labels raw32779step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3565 node3565Labels := by rfl

def raw32780 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw32780Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32780step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw32780step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32780step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw32780step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32780step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 2, -3], ![2, 0, -2]]
def raw32780step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32780 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32780 raw32780Labels = mixedMoment B node2659 node2659Labels := by
  calc
    mixedMoment B raw32780 raw32780Labels = mixedMoment B raw32780step0 raw32780step0Labels := by
      have hz : ∀ j, raw32780 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32780step0 = (fun i j => raw32780 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32780step0 raw32780; decide +kernel
      have hl : raw32780step0Labels = raw32780Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32780 raw32780Labels permutation346 hz
    mixedMoment B raw32780step0 raw32780step0Labels = mixedMoment B raw32780step1 raw32780step1Labels := by
      have ha : raw32780step1 = (fun i j => raw32780step0 (permutation126 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32780step1 raw32780step0; decide +kernel
      have hl : raw32780step1Labels = raw32780step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32780step0 raw32780step0Labels permutation126 permutation5
    mixedMoment B raw32780step1 raw32780step1Labels = mixedMoment B raw32780step2 raw32780step2Labels := by
      have ha : raw32780step2 = raw32780step1 := by apply Matrix.ext; unfold raw32780step2 raw32780step1; decide +kernel
      have hl : raw32780step1Labels = labelEmbedding1 ∘ raw32780step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32780step1 raw32780step1Labels raw32780step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2659 node2659Labels := by rfl

def raw32781 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![2, 0, -2]]
def raw32781Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32781step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw32781step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32781step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw32781step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32781 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32781 raw32781Labels = mixedMoment B node2655 node2655Labels := by
  calc
    mixedMoment B raw32781 raw32781Labels = mixedMoment B raw32781step0 raw32781step0Labels := by
      have ha : raw32781step0 = (fun i j => raw32781 (permutation587 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32781step0 raw32781; decide +kernel
      have hl : raw32781step0Labels = raw32781Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32781 raw32781Labels permutation587 permutation5
    mixedMoment B raw32781step0 raw32781step0Labels = mixedMoment B raw32781step1 raw32781step1Labels := by
      have ha : raw32781step1 = raw32781step0 := by apply Matrix.ext; unfold raw32781step1 raw32781step0; decide +kernel
      have hl : raw32781step0Labels = labelEmbedding1 ∘ raw32781step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32781step0 raw32781step0Labels raw32781step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2655 node2655Labels := by rfl

def raw32782 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw32782Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32782step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw32782step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32782step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw32782step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32782step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw32782step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32782 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32782 raw32782Labels = mixedMoment B node2681 node2681Labels := by
  calc
    mixedMoment B raw32782 raw32782Labels = mixedMoment B raw32782step0 raw32782step0Labels := by
      have hz : ∀ j, raw32782 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32782step0 = (fun i j => raw32782 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32782step0 raw32782; decide +kernel
      have hl : raw32782step0Labels = raw32782Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32782 raw32782Labels permutation346 hz
    mixedMoment B raw32782step0 raw32782step0Labels = mixedMoment B raw32782step1 raw32782step1Labels := by
      have ha : raw32782step1 = (fun i j => raw32782step0 (permutation127 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32782step1 raw32782step0; decide +kernel
      have hl : raw32782step1Labels = raw32782step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32782step0 raw32782step0Labels permutation127 permutation5
    mixedMoment B raw32782step1 raw32782step1Labels = mixedMoment B raw32782step2 raw32782step2Labels := by
      have ha : raw32782step2 = raw32782step1 := by apply Matrix.ext; unfold raw32782step2 raw32782step1; decide +kernel
      have hl : raw32782step1Labels = labelEmbedding1 ∘ raw32782step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32782step1 raw32782step1Labels raw32782step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2681 node2681Labels := by rfl

def raw32783 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw32783Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32783step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -3, 1], ![1, 1, -2]]
def raw32783step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32783step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw32783step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32783step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 2, -3]]
def raw32783step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32783 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32783 raw32783Labels = mixedMoment B node2735 node2735Labels := by
  calc
    mixedMoment B raw32783 raw32783Labels = mixedMoment B raw32783step0 raw32783step0Labels := by
      have hz : ∀ j, raw32783 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32783step0 = (fun i j => raw32783 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32783step0 raw32783; decide +kernel
      have hl : raw32783step0Labels = raw32783Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32783 raw32783Labels permutation346 hz
    mixedMoment B raw32783step0 raw32783step0Labels = mixedMoment B raw32783step1 raw32783step1Labels := by
      have ha : raw32783step1 = (fun i j => raw32783step0 (permutation121 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32783step1 raw32783step0; decide +kernel
      have hl : raw32783step1Labels = raw32783step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32783step0 raw32783step0Labels permutation121 permutation5
    mixedMoment B raw32783step1 raw32783step1Labels = mixedMoment B raw32783step2 raw32783step2Labels := by
      have ha : raw32783step2 = raw32783step1 := by apply Matrix.ext; unfold raw32783step2 raw32783step1; decide +kernel
      have hl : raw32783step1Labels = labelEmbedding1 ∘ raw32783step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32783step1 raw32783step1Labels raw32783step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2735 node2735Labels := by rfl

def raw32784 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32784Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32784step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32784step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32784step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw32784step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32784step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 2, -2], ![1, -2, 1], ![2, 1, -3]]
def raw32784step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32784 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32784 raw32784Labels = mixedMoment B node3475 node3475Labels := by
  calc
    mixedMoment B raw32784 raw32784Labels = mixedMoment B raw32784step0 raw32784step0Labels := by
      have hz : ∀ j, raw32784 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32784step0 = (fun i j => raw32784 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32784step0 raw32784; decide +kernel
      have hl : raw32784step0Labels = raw32784Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32784 raw32784Labels permutation346 hz
    mixedMoment B raw32784step0 raw32784step0Labels = mixedMoment B raw32784step1 raw32784step1Labels := by
      have ha : raw32784step1 = (fun i j => raw32784step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32784step1 raw32784step0; decide +kernel
      have hl : raw32784step1Labels = raw32784step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32784step0 raw32784step0Labels permutation143 permutation7
    mixedMoment B raw32784step1 raw32784step1Labels = mixedMoment B raw32784step2 raw32784step2Labels := by
      have ha : raw32784step2 = raw32784step1 := by apply Matrix.ext; unfold raw32784step2 raw32784step1; decide +kernel
      have hl : raw32784step1Labels = labelEmbedding1 ∘ raw32784step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32784step1 raw32784step1Labels raw32784step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3475 node3475Labels := by rfl

def raw32785 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32785Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32785step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw32785step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32785step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw32785step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32785 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32785 raw32785Labels = mixedMoment B node3458 node3458Labels := by
  calc
    mixedMoment B raw32785 raw32785Labels = mixedMoment B raw32785step0 raw32785step0Labels := by
      have ha : raw32785step0 = (fun i j => raw32785 (permutation653 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32785step0 raw32785; decide +kernel
      have hl : raw32785step0Labels = raw32785Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32785 raw32785Labels permutation653 permutation7
    mixedMoment B raw32785step0 raw32785step0Labels = mixedMoment B raw32785step1 raw32785step1Labels := by
      have ha : raw32785step1 = raw32785step0 := by apply Matrix.ext; unfold raw32785step1 raw32785step0; decide +kernel
      have hl : raw32785step0Labels = labelEmbedding1 ∘ raw32785step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32785step0 raw32785step0Labels raw32785step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3458 node3458Labels := by rfl

def raw32786 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32786Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32786step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![3, -1, -2]]
def raw32786step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32786step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw32786step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32786step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![2, 1, -3]]
def raw32786step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32786 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32786 raw32786Labels = mixedMoment B node3530 node3530Labels := by
  calc
    mixedMoment B raw32786 raw32786Labels = mixedMoment B raw32786step0 raw32786step0Labels := by
      have hz : ∀ j, raw32786 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32786step0 = (fun i j => raw32786 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32786step0 raw32786; decide +kernel
      have hl : raw32786step0Labels = raw32786Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32786 raw32786Labels permutation346 hz
    mixedMoment B raw32786step0 raw32786step0Labels = mixedMoment B raw32786step1 raw32786step1Labels := by
      have ha : raw32786step1 = (fun i j => raw32786step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32786step1 raw32786step0; decide +kernel
      have hl : raw32786step1Labels = raw32786step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32786step0 raw32786step0Labels permutation143 permutation7
    mixedMoment B raw32786step1 raw32786step1Labels = mixedMoment B raw32786step2 raw32786step2Labels := by
      have ha : raw32786step2 = raw32786step1 := by apply Matrix.ext; unfold raw32786step2 raw32786step1; decide +kernel
      have hl : raw32786step1Labels = labelEmbedding1 ∘ raw32786step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32786step1 raw32786step1Labels raw32786step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3530 node3530Labels := by rfl

def raw32787 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 0, 0], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw32787Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32787step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, 0, -1], ![0, -1, 1], ![3, -1, -2]]
def raw32787step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32787step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw32787step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32787step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, 1, -3]]
def raw32787step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32787 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32787 raw32787Labels = mixedMoment B node3468 node3468Labels := by
  calc
    mixedMoment B raw32787 raw32787Labels = mixedMoment B raw32787step0 raw32787step0Labels := by
      have hz : ∀ j, raw32787 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32787step0 = (fun i j => raw32787 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32787step0 raw32787; decide +kernel
      have hl : raw32787step0Labels = raw32787Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32787 raw32787Labels permutation346 hz
    mixedMoment B raw32787step0 raw32787step0Labels = mixedMoment B raw32787step1 raw32787step1Labels := by
      have ha : raw32787step1 = (fun i j => raw32787step0 (permutation143 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32787step1 raw32787step0; decide +kernel
      have hl : raw32787step1Labels = raw32787step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32787step0 raw32787step0Labels permutation143 permutation7
    mixedMoment B raw32787step1 raw32787step1Labels = mixedMoment B raw32787step2 raw32787step2Labels := by
      have ha : raw32787step2 = raw32787step1 := by apply Matrix.ext; unfold raw32787step2 raw32787step1; decide +kernel
      have hl : raw32787step1Labels = labelEmbedding1 ∘ raw32787step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32787step1 raw32787step1Labels raw32787step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3468 node3468Labels := by rfl

def raw32788 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, 0, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32788Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32788step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32788step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32788step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32788step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32788 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32788 raw32788Labels = mixedMoment B node3732 node3732Labels := by
  calc
    mixedMoment B raw32788 raw32788Labels = mixedMoment B raw32788step0 raw32788step0Labels := by
      have hz : ∀ j, raw32788 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32788step0 = (fun i j => raw32788 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32788step0 raw32788; decide +kernel
      have hl : raw32788step0Labels = raw32788Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32788 raw32788Labels permutation346 hz
    mixedMoment B raw32788step0 raw32788step0Labels = mixedMoment B raw32788step1 raw32788step1Labels := by
      have ha : raw32788step1 = (fun i j => raw32788step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32788step1 raw32788step0; decide +kernel
      have hl : raw32788step1Labels = raw32788step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32788step0 raw32788step0Labels permutation34 permutation2
    _ = mixedMoment B node3732 node3732Labels := by rfl

def raw32789 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -1, 0], ![1, 0, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32789Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32789step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32789step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32789 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32789 raw32789Labels = mixedMoment B node2353 node2353Labels := by
  calc
    mixedMoment B raw32789 raw32789Labels = mixedMoment B raw32789step0 raw32789step0Labels := by
      have ha : raw32789step0 = (fun i j => raw32789 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32789step0 raw32789; decide +kernel
      have hl : raw32789step0Labels = raw32789Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32789 raw32789Labels permutation164 permutation2
    _ = mixedMoment B node2353 node2353Labels := by rfl

def raw32790 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, 0, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32790Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32790step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![2, -1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw32790step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32790step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![2, -1, -1], ![2, 0, -2]]
def raw32790step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32790 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32790 raw32790Labels = mixedMoment B node2356 node2356Labels := by
  calc
    mixedMoment B raw32790 raw32790Labels = mixedMoment B raw32790step0 raw32790step0Labels := by
      have hz : ∀ j, raw32790 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32790step0 = (fun i j => raw32790 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32790step0 raw32790; decide +kernel
      have hl : raw32790step0Labels = raw32790Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32790 raw32790Labels permutation346 hz
    mixedMoment B raw32790step0 raw32790step0Labels = mixedMoment B raw32790step1 raw32790step1Labels := by
      have ha : raw32790step1 = (fun i j => raw32790step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32790step1 raw32790step0; decide +kernel
      have hl : raw32790step1Labels = raw32790step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32790step0 raw32790step0Labels permutation34 permutation2
    _ = mixedMoment B node2356 node2356Labels := by rfl

def raw32791 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32791Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32791step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32791step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32791step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw32791step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32791step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32791step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32791step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32791step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32791 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32791 raw32791Labels = mixedMoment B node5404 node5404Labels := by
  calc
    mixedMoment B raw32791 raw32791Labels = mixedMoment B raw32791step0 raw32791step0Labels := by
      have hz : ∀ j, raw32791 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32791step0 = (fun i j => raw32791 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32791step0 raw32791; decide +kernel
      have hl : raw32791step0Labels = raw32791Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32791 raw32791Labels permutation346 hz
    mixedMoment B raw32791step0 raw32791step0Labels = mixedMoment B raw32791step1 raw32791step1Labels := by
      have ha : raw32791step1 = (fun i j => raw32791step0 (permutation144 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32791step1 raw32791step0; decide +kernel
      have hl : raw32791step1Labels = raw32791step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32791step0 raw32791step0Labels permutation144 permutation3
    mixedMoment B raw32791step1 raw32791step1Labels = mixedMoment B raw32791step2 raw32791step2Labels := by
      have ha : raw32791step2 = -raw32791step1 := by apply Matrix.ext; change ∀ i j, raw32791step2 i j = -(raw32791step1 i j); unfold raw32791step2 raw32791step1; decide +kernel
      have hl : raw32791step2Labels = raw32791step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32791step2 raw32791step2Labels = mixedMoment B raw32791step3 raw32791step3Labels := by
      have ha : raw32791step3 = raw32791step2 := by apply Matrix.ext; unfold raw32791step3 raw32791step2; decide +kernel
      have hl : raw32791step2Labels = labelEmbedding6 ∘ raw32791step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32791step2 raw32791step2Labels raw32791step3Labels labelEmbedding6 hl
    _ = mixedMoment B node5404 node5404Labels := by rfl

def raw32792 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32792Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32792step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw32792step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32792step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32792step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32792step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32792step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32792 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32792 raw32792Labels = mixedMoment B node5401 node5401Labels := by
  calc
    mixedMoment B raw32792 raw32792Labels = mixedMoment B raw32792step0 raw32792step0Labels := by
      have ha : raw32792step0 = (fun i j => raw32792 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32792step0 raw32792; decide +kernel
      have hl : raw32792step0Labels = raw32792Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32792 raw32792Labels permutation662 permutation3
    mixedMoment B raw32792step0 raw32792step0Labels = mixedMoment B raw32792step1 raw32792step1Labels := by
      have ha : raw32792step1 = -raw32792step0 := by apply Matrix.ext; change ∀ i j, raw32792step1 i j = -(raw32792step0 i j); unfold raw32792step1 raw32792step0; decide +kernel
      have hl : raw32792step1Labels = raw32792step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32792step1 raw32792step1Labels = mixedMoment B raw32792step2 raw32792step2Labels := by
      have ha : raw32792step2 = raw32792step1 := by apply Matrix.ext; unfold raw32792step2 raw32792step1; decide +kernel
      have hl : raw32792step1Labels = labelEmbedding6 ∘ raw32792step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32792step1 raw32792step1Labels raw32792step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5401 node5401Labels := by rfl

def raw32793 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw32793Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32793step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw32793step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32793step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32793step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw32793step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32793step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32793 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32793 raw32793Labels = mixedMoment B node5411 node5411Labels := by
  calc
    mixedMoment B raw32793 raw32793Labels = mixedMoment B raw32793step0 raw32793step0Labels := by
      have hz : ∀ j, raw32793 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32793step0 = (fun i j => raw32793 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32793step0 raw32793; decide +kernel
      have hl : raw32793step0Labels = raw32793Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32793 raw32793Labels permutation346 hz
    mixedMoment B raw32793step0 raw32793step0Labels = mixedMoment B raw32793step1 raw32793step1Labels := by
      have ha : raw32793step1 = (fun i j => raw32793step0 (permutation142 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32793step1 raw32793step0; decide +kernel
      have hl : raw32793step1Labels = raw32793step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32793step0 raw32793step0Labels permutation142 permutation5
    mixedMoment B raw32793step1 raw32793step1Labels = mixedMoment B raw32793step2 raw32793step2Labels := by
      have ha : raw32793step2 = raw32793step1 := by apply Matrix.ext; unfold raw32793step2 raw32793step1; decide +kernel
      have hl : raw32793step1Labels = labelEmbedding8 ∘ raw32793step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32793step1 raw32793step1Labels raw32793step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5411 node5411Labels := by rfl

def raw32794 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw32794Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32794step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw32794step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32794step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw32794step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32794 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32794 raw32794Labels = mixedMoment B node5485 node5485Labels := by
  calc
    mixedMoment B raw32794 raw32794Labels = mixedMoment B raw32794step0 raw32794step0Labels := by
      have hz : ∀ j, raw32794 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32794step0 = (fun i j => raw32794 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32794step0 raw32794; decide +kernel
      have hl : raw32794step0Labels = raw32794Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32794 raw32794Labels permutation346 hz
    mixedMoment B raw32794step0 raw32794step0Labels = mixedMoment B raw32794step1 raw32794step1Labels := by
      have ha : raw32794step1 = (fun i j => raw32794step0 (permutation33 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32794step1 raw32794step0; decide +kernel
      have hl : raw32794step1Labels = raw32794step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32794step0 raw32794step0Labels permutation33 permutation2
    _ = mixedMoment B node5485 node5485Labels := by rfl

def raw32795 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32795Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32795step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32795step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32795step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32795step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32795 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32795 raw32795Labels = mixedMoment B node4337 node4337Labels := by
  calc
    mixedMoment B raw32795 raw32795Labels = mixedMoment B raw32795step0 raw32795step0Labels := by
      have ha : raw32795step0 = (fun i j => raw32795 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32795step0 raw32795; decide +kernel
      have hl : raw32795step0Labels = raw32795Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32795 raw32795Labels permutation164 permutation3
    mixedMoment B raw32795step0 raw32795step0Labels = mixedMoment B raw32795step1 raw32795step1Labels := by
      have ha : raw32795step1 = raw32795step0 := by apply Matrix.ext; unfold raw32795step1 raw32795step0; decide +kernel
      have hl : raw32795step0Labels = labelEmbedding6 ∘ raw32795step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32795step0 raw32795step0Labels raw32795step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4337 node4337Labels := by rfl

def raw32796 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32796Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32796step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32796step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32796step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32796step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32796 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32796 raw32796Labels = mixedMoment B node4936 node4936Labels := by
  calc
    mixedMoment B raw32796 raw32796Labels = mixedMoment B raw32796step0 raw32796step0Labels := by
      have ha : raw32796step0 = (fun i j => raw32796 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32796step0 raw32796; decide +kernel
      have hl : raw32796step0Labels = raw32796Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32796 raw32796Labels permutation164 permutation3
    mixedMoment B raw32796step0 raw32796step0Labels = mixedMoment B raw32796step1 raw32796step1Labels := by
      have ha : raw32796step1 = raw32796step0 := by apply Matrix.ext; unfold raw32796step1 raw32796step0; decide +kernel
      have hl : raw32796step0Labels = labelEmbedding6 ∘ raw32796step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32796step0 raw32796step0Labels raw32796step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4936 node4936Labels := by rfl

def raw32797 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw32797Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32797step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32797step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32797step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32797step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32797 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32797 raw32797Labels = mixedMoment B node5123 node5123Labels := by
  calc
    mixedMoment B raw32797 raw32797Labels = mixedMoment B raw32797step0 raw32797step0Labels := by
      have ha : raw32797step0 = (fun i j => raw32797 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32797step0 raw32797; decide +kernel
      have hl : raw32797step0Labels = raw32797Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32797 raw32797Labels permutation164 permutation3
    mixedMoment B raw32797step0 raw32797step0Labels = mixedMoment B raw32797step1 raw32797step1Labels := by
      have ha : raw32797step1 = raw32797step0 := by apply Matrix.ext; unfold raw32797step1 raw32797step0; decide +kernel
      have hl : raw32797step0Labels = labelEmbedding6 ∘ raw32797step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32797step0 raw32797step0Labels raw32797step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5123 node5123Labels := by rfl

def raw32798 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw32798Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32798step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32798step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32798step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32798step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32798 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32798 raw32798Labels = mixedMoment B node5162 node5162Labels := by
  calc
    mixedMoment B raw32798 raw32798Labels = mixedMoment B raw32798step0 raw32798step0Labels := by
      have ha : raw32798step0 = (fun i j => raw32798 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32798step0 raw32798; decide +kernel
      have hl : raw32798step0Labels = raw32798Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32798 raw32798Labels permutation164 permutation3
    mixedMoment B raw32798step0 raw32798step0Labels = mixedMoment B raw32798step1 raw32798step1Labels := by
      have ha : raw32798step1 = raw32798step0 := by apply Matrix.ext; unfold raw32798step1 raw32798step0; decide +kernel
      have hl : raw32798step0Labels = labelEmbedding6 ∘ raw32798step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32798step0 raw32798step0Labels raw32798step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5162 node5162Labels := by rfl

def raw32799 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32799Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32799step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32799step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32799step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw32799step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32799step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw32799step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32799 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32799 raw32799Labels = mixedMoment B node4339 node4339Labels := by
  calc
    mixedMoment B raw32799 raw32799Labels = mixedMoment B raw32799step0 raw32799step0Labels := by
      have hz : ∀ j, raw32799 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32799step0 = (fun i j => raw32799 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32799step0 raw32799; decide +kernel
      have hl : raw32799step0Labels = raw32799Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32799 raw32799Labels permutation346 hz
    mixedMoment B raw32799step0 raw32799step0Labels = mixedMoment B raw32799step1 raw32799step1Labels := by
      have ha : raw32799step1 = (fun i j => raw32799step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32799step1 raw32799step0; decide +kernel
      have hl : raw32799step1Labels = raw32799step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32799step0 raw32799step0Labels permutation34 permutation3
    mixedMoment B raw32799step1 raw32799step1Labels = mixedMoment B raw32799step2 raw32799step2Labels := by
      have ha : raw32799step2 = raw32799step1 := by apply Matrix.ext; unfold raw32799step2 raw32799step1; decide +kernel
      have hl : raw32799step1Labels = labelEmbedding6 ∘ raw32799step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32799step1 raw32799step1Labels raw32799step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4339 node4339Labels := by rfl

def raw32800 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32800Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32800step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32800step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32800step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw32800step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32800step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw32800step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32800 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32800 raw32800Labels = mixedMoment B node4937 node4937Labels := by
  calc
    mixedMoment B raw32800 raw32800Labels = mixedMoment B raw32800step0 raw32800step0Labels := by
      have hz : ∀ j, raw32800 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32800step0 = (fun i j => raw32800 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32800step0 raw32800; decide +kernel
      have hl : raw32800step0Labels = raw32800Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32800 raw32800Labels permutation346 hz
    mixedMoment B raw32800step0 raw32800step0Labels = mixedMoment B raw32800step1 raw32800step1Labels := by
      have ha : raw32800step1 = (fun i j => raw32800step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32800step1 raw32800step0; decide +kernel
      have hl : raw32800step1Labels = raw32800step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32800step0 raw32800step0Labels permutation34 permutation3
    mixedMoment B raw32800step1 raw32800step1Labels = mixedMoment B raw32800step2 raw32800step2Labels := by
      have ha : raw32800step2 = raw32800step1 := by apply Matrix.ext; unfold raw32800step2 raw32800step1; decide +kernel
      have hl : raw32800step1Labels = labelEmbedding6 ∘ raw32800step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32800step1 raw32800step1Labels raw32800step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4937 node4937Labels := by rfl

def raw32801 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32801Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32801step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw32801step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32801step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw32801step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32801 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32801 raw32801Labels = mixedMoment B node5032 node5032Labels := by
  calc
    mixedMoment B raw32801 raw32801Labels = mixedMoment B raw32801step0 raw32801step0Labels := by
      have ha : raw32801step0 = (fun i j => raw32801 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32801step0 raw32801; decide +kernel
      have hl : raw32801step0Labels = raw32801Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32801 raw32801Labels permutation178 permutation3
    mixedMoment B raw32801step0 raw32801step0Labels = mixedMoment B raw32801step1 raw32801step1Labels := by
      have ha : raw32801step1 = raw32801step0 := by apply Matrix.ext; unfold raw32801step1 raw32801step0; decide +kernel
      have hl : raw32801step0Labels = labelEmbedding6 ∘ raw32801step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32801step0 raw32801step0Labels raw32801step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5032 node5032Labels := by rfl

def raw32802 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![0, 2, -2], ![2, -2, 0]]
def raw32802Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32802step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![0, 2, -2], ![2, -2, 0]]
def raw32802step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32802step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw32802step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32802step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw32802step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32802 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32802 raw32802Labels = mixedMoment B node5125 node5125Labels := by
  calc
    mixedMoment B raw32802 raw32802Labels = mixedMoment B raw32802step0 raw32802step0Labels := by
      have hz : ∀ j, raw32802 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32802step0 = (fun i j => raw32802 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32802step0 raw32802; decide +kernel
      have hl : raw32802step0Labels = raw32802Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32802 raw32802Labels permutation346 hz
    mixedMoment B raw32802step0 raw32802step0Labels = mixedMoment B raw32802step1 raw32802step1Labels := by
      have ha : raw32802step1 = (fun i j => raw32802step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32802step1 raw32802step0; decide +kernel
      have hl : raw32802step1Labels = raw32802step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32802step0 raw32802step0Labels permutation34 permutation3
    mixedMoment B raw32802step1 raw32802step1Labels = mixedMoment B raw32802step2 raw32802step2Labels := by
      have ha : raw32802step2 = raw32802step1 := by apply Matrix.ext; unfold raw32802step2 raw32802step1; decide +kernel
      have hl : raw32802step1Labels = labelEmbedding6 ∘ raw32802step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32802step1 raw32802step1Labels raw32802step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5125 node5125Labels := by rfl

def raw32803 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2], ![1, -1, 0]]
def raw32803Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32803step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![1, 1, -2], ![1, -1, 0]]
def raw32803step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32803step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32803step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32803step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32803step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32803 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32803 raw32803Labels = mixedMoment B node5163 node5163Labels := by
  calc
    mixedMoment B raw32803 raw32803Labels = mixedMoment B raw32803step0 raw32803step0Labels := by
      have hz : ∀ j, raw32803 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32803step0 = (fun i j => raw32803 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32803step0 raw32803; decide +kernel
      have hl : raw32803step0Labels = raw32803Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32803 raw32803Labels permutation346 hz
    mixedMoment B raw32803step0 raw32803step0Labels = mixedMoment B raw32803step1 raw32803step1Labels := by
      have ha : raw32803step1 = (fun i j => raw32803step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32803step1 raw32803step0; decide +kernel
      have hl : raw32803step1Labels = raw32803step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32803step0 raw32803step0Labels permutation35 permutation3
    mixedMoment B raw32803step1 raw32803step1Labels = mixedMoment B raw32803step2 raw32803step2Labels := by
      have ha : raw32803step2 = raw32803step1 := by apply Matrix.ext; unfold raw32803step2 raw32803step1; decide +kernel
      have hl : raw32803step1Labels = labelEmbedding6 ∘ raw32803step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32803step1 raw32803step1Labels raw32803step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5163 node5163Labels := by rfl

def raw32804 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32804Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32804step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-2, 1, 1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32804step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32804step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-2, 1, 1]]
def raw32804step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32804step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32804step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32804 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32804 raw32804Labels = mixedMoment B node3790 node3790Labels := by
  calc
    mixedMoment B raw32804 raw32804Labels = mixedMoment B raw32804step0 raw32804step0Labels := by
      have hz : ∀ j, raw32804 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32804step0 = (fun i j => raw32804 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32804step0 raw32804; decide +kernel
      have hl : raw32804step0Labels = raw32804Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32804 raw32804Labels permutation346 hz
    mixedMoment B raw32804step0 raw32804step0Labels = mixedMoment B raw32804step1 raw32804step1Labels := by
      have ha : raw32804step1 = (fun i j => raw32804step0 (permutation144 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32804step1 raw32804step0; decide +kernel
      have hl : raw32804step1Labels = raw32804step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32804step0 raw32804step0Labels permutation144 permutation3
    mixedMoment B raw32804step1 raw32804step1Labels = mixedMoment B raw32804step2 raw32804step2Labels := by
      have ha : raw32804step2 = -raw32804step1 := by apply Matrix.ext; change ∀ i j, raw32804step2 i j = -(raw32804step1 i j); unfold raw32804step2 raw32804step1; decide +kernel
      have hl : raw32804step2Labels = raw32804step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3790 node3790Labels := by rfl

def raw32805 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32805Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32805step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw32805step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32805step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32805step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32805 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32805 raw32805Labels = mixedMoment B node3787 node3787Labels := by
  calc
    mixedMoment B raw32805 raw32805Labels = mixedMoment B raw32805step0 raw32805step0Labels := by
      have ha : raw32805step0 = (fun i j => raw32805 (permutation662 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32805step0 raw32805; decide +kernel
      have hl : raw32805step0Labels = raw32805Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32805 raw32805Labels permutation662 permutation3
    mixedMoment B raw32805step0 raw32805step0Labels = mixedMoment B raw32805step1 raw32805step1Labels := by
      have ha : raw32805step1 = -raw32805step0 := by apply Matrix.ext; change ∀ i j, raw32805step1 i j = -(raw32805step0 i j); unfold raw32805step1 raw32805step0; decide +kernel
      have hl : raw32805step1Labels = raw32805step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3787 node3787Labels := by rfl

def raw32806 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw32806Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32806step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw32806step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32806step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, -2, 2], ![-1, 1, 0], ![-2, 1, 1]]
def raw32806step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32806step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw32806step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32806 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32806 raw32806Labels = mixedMoment B node3813 node3813Labels := by
  calc
    mixedMoment B raw32806 raw32806Labels = mixedMoment B raw32806step0 raw32806step0Labels := by
      have hz : ∀ j, raw32806 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32806step0 = (fun i j => raw32806 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32806step0 raw32806; decide +kernel
      have hl : raw32806step0Labels = raw32806Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32806 raw32806Labels permutation346 hz
    mixedMoment B raw32806step0 raw32806step0Labels = mixedMoment B raw32806step1 raw32806step1Labels := by
      have ha : raw32806step1 = (fun i j => raw32806step0 (permutation145 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32806step1 raw32806step0; decide +kernel
      have hl : raw32806step1Labels = raw32806step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32806step0 raw32806step0Labels permutation145 permutation3
    mixedMoment B raw32806step1 raw32806step1Labels = mixedMoment B raw32806step2 raw32806step2Labels := by
      have ha : raw32806step2 = -raw32806step1 := by apply Matrix.ext; change ∀ i j, raw32806step2 i j = -(raw32806step1 i j); unfold raw32806step2 raw32806step1; decide +kernel
      have hl : raw32806step2Labels = raw32806step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3813 node3813Labels := by rfl

def raw32807 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![0, 0, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw32807Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32807step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw32807step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32807step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw32807step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32807 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32807 raw32807Labels = mixedMoment B node3998 node3998Labels := by
  calc
    mixedMoment B raw32807 raw32807Labels = mixedMoment B raw32807step0 raw32807step0Labels := by
      have hz : ∀ j, raw32807 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32807step0 = (fun i j => raw32807 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32807step0 raw32807; decide +kernel
      have hl : raw32807step0Labels = raw32807Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32807 raw32807Labels permutation346 hz
    mixedMoment B raw32807step0 raw32807step0Labels = mixedMoment B raw32807step1 raw32807step1Labels := by
      have ha : raw32807step1 = (fun i j => raw32807step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32807step1 raw32807step0; decide +kernel
      have hl : raw32807step1Labels = raw32807step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32807step0 raw32807step0Labels permutation34 permutation3
    _ = mixedMoment B node3998 node3998Labels := by rfl

def raw32808 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32808Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32808step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32808step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32808 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32808 raw32808Labels = mixedMoment B node915 node915Labels := by
  calc
    mixedMoment B raw32808 raw32808Labels = mixedMoment B raw32808step0 raw32808step0Labels := by
      have ha : raw32808step0 = (fun i j => raw32808 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32808step0 raw32808; decide +kernel
      have hl : raw32808step0Labels = raw32808Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32808 raw32808Labels permutation164 permutation3
    _ = mixedMoment B node915 node915Labels := by rfl

def raw32809 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32809Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32809step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32809step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32809 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32809 raw32809Labels = mixedMoment B node2328 node2328Labels := by
  calc
    mixedMoment B raw32809 raw32809Labels = mixedMoment B raw32809step0 raw32809step0Labels := by
      have ha : raw32809step0 = (fun i j => raw32809 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32809step0 raw32809; decide +kernel
      have hl : raw32809step0Labels = raw32809Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32809 raw32809Labels permutation164 permutation3
    _ = mixedMoment B node2328 node2328Labels := by rfl

def raw32810 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![0, 2, -2], ![2, -2, 0]]
def raw32810Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32810step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, 0, -2]]
def raw32810step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32810 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32810 raw32810Labels = mixedMoment B node2536 node2536Labels := by
  calc
    mixedMoment B raw32810 raw32810Labels = mixedMoment B raw32810step0 raw32810step0Labels := by
      have ha : raw32810step0 = (fun i j => raw32810 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32810step0 raw32810; decide +kernel
      have hl : raw32810step0Labels = raw32810Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32810 raw32810Labels permutation164 permutation3
    _ = mixedMoment B node2536 node2536Labels := by rfl

def raw32811 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2], ![1, -1, 0]]
def raw32811Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32811step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32811step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32811 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32811 raw32811Labels = mixedMoment B node2589 node2589Labels := by
  calc
    mixedMoment B raw32811 raw32811Labels = mixedMoment B raw32811step0 raw32811step0Labels := by
      have ha : raw32811step0 = (fun i j => raw32811 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32811step0 raw32811; decide +kernel
      have hl : raw32811step0Labels = raw32811Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32811 raw32811Labels permutation164 permutation3
    _ = mixedMoment B node2589 node2589Labels := by rfl

def raw32812 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32812Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32812step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32812step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32812step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw32812step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32812 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32812 raw32812Labels = mixedMoment B node917 node917Labels := by
  calc
    mixedMoment B raw32812 raw32812Labels = mixedMoment B raw32812step0 raw32812step0Labels := by
      have hz : ∀ j, raw32812 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32812step0 = (fun i j => raw32812 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32812step0 raw32812; decide +kernel
      have hl : raw32812step0Labels = raw32812Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32812 raw32812Labels permutation346 hz
    mixedMoment B raw32812step0 raw32812step0Labels = mixedMoment B raw32812step1 raw32812step1Labels := by
      have ha : raw32812step1 = (fun i j => raw32812step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32812step1 raw32812step0; decide +kernel
      have hl : raw32812step1Labels = raw32812step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32812step0 raw32812step0Labels permutation34 permutation3
    _ = mixedMoment B node917 node917Labels := by rfl

def raw32813 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32813Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32813step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32813step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32813step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw32813step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32813 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32813 raw32813Labels = mixedMoment B node2329 node2329Labels := by
  calc
    mixedMoment B raw32813 raw32813Labels = mixedMoment B raw32813step0 raw32813step0Labels := by
      have hz : ∀ j, raw32813 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32813step0 = (fun i j => raw32813 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32813step0 raw32813; decide +kernel
      have hl : raw32813step0Labels = raw32813Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32813 raw32813Labels permutation346 hz
    mixedMoment B raw32813step0 raw32813step0Labels = mixedMoment B raw32813step1 raw32813step1Labels := by
      have ha : raw32813step1 = (fun i j => raw32813step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32813step1 raw32813step0; decide +kernel
      have hl : raw32813step1Labels = raw32813step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32813step0 raw32813step0Labels permutation34 permutation3
    _ = mixedMoment B node2329 node2329Labels := by rfl

def raw32814 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 1, 0], ![2, -2, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32814Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32814step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, -2, 1], ![2, 0, -2], ![2, 0, -2]]
def raw32814step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32814 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32814 raw32814Labels = mixedMoment B node2424 node2424Labels := by
  calc
    mixedMoment B raw32814 raw32814Labels = mixedMoment B raw32814step0 raw32814step0Labels := by
      have ha : raw32814step0 = (fun i j => raw32814 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32814step0 raw32814; decide +kernel
      have hl : raw32814step0Labels = raw32814Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32814 raw32814Labels permutation178 permutation3
    _ = mixedMoment B node2424 node2424Labels := by rfl

def raw32815 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![0, 2, -2], ![2, -2, 0]]
def raw32815Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32815step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![0, 2, -2], ![2, -2, 0]]
def raw32815step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32815step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -2, 2], ![2, 0, -2], ![2, 0, -2]]
def raw32815step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32815 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32815 raw32815Labels = mixedMoment B node2539 node2539Labels := by
  calc
    mixedMoment B raw32815 raw32815Labels = mixedMoment B raw32815step0 raw32815step0Labels := by
      have hz : ∀ j, raw32815 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32815step0 = (fun i j => raw32815 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32815step0 raw32815; decide +kernel
      have hl : raw32815step0Labels = raw32815Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32815 raw32815Labels permutation346 hz
    mixedMoment B raw32815step0 raw32815step0Labels = mixedMoment B raw32815step1 raw32815step1Labels := by
      have ha : raw32815step1 = (fun i j => raw32815step0 (permutation34 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32815step1 raw32815step0; decide +kernel
      have hl : raw32815step1Labels = raw32815step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32815step0 raw32815step0Labels permutation34 permutation3
    _ = mixedMoment B node2539 node2539Labels := by rfl

def raw32816 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 0, 0], ![2, -2, 0], ![1, 1, -2], ![1, -1, 0]]
def raw32816Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32816step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![2, -2, 0], ![1, 1, -2], ![1, -1, 0]]
def raw32816step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw32816step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32816step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32816 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32816 raw32816Labels = mixedMoment B node2590 node2590Labels := by
  calc
    mixedMoment B raw32816 raw32816Labels = mixedMoment B raw32816step0 raw32816step0Labels := by
      have hz : ∀ j, raw32816 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32816step0 = (fun i j => raw32816 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32816step0 raw32816; decide +kernel
      have hl : raw32816step0Labels = raw32816Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32816 raw32816Labels permutation346 hz
    mixedMoment B raw32816step0 raw32816step0Labels = mixedMoment B raw32816step1 raw32816step1Labels := by
      have ha : raw32816step1 = (fun i j => raw32816step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32816step1 raw32816step0; decide +kernel
      have hl : raw32816step1Labels = raw32816step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32816step0 raw32816step0Labels permutation35 permutation3
    _ = mixedMoment B node2590 node2590Labels := by rfl

def raw32817 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw32817Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32817step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw32817step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32817step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32817step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw32817step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32817step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32817 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32817 raw32817Labels = mixedMoment B node5170 node5170Labels := by
  calc
    mixedMoment B raw32817 raw32817Labels = mixedMoment B raw32817step0 raw32817step0Labels := by
      have hz : ∀ j, raw32817 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32817step0 = (fun i j => raw32817 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32817step0 raw32817; decide +kernel
      have hl : raw32817step0Labels = raw32817Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32817 raw32817Labels permutation346 hz
    mixedMoment B raw32817step0 raw32817step0Labels = mixedMoment B raw32817step1 raw32817step1Labels := by
      have ha : raw32817step1 = (fun i j => raw32817step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32817step1 raw32817step0; decide +kernel
      have hl : raw32817step1Labels = raw32817step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32817step0 raw32817step0Labels permutation32 permutation7
    mixedMoment B raw32817step1 raw32817step1Labels = mixedMoment B raw32817step2 raw32817step2Labels := by
      have ha : raw32817step2 = raw32817step1 := by apply Matrix.ext; unfold raw32817step2 raw32817step1; decide +kernel
      have hl : raw32817step1Labels = labelEmbedding10 ∘ raw32817step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32817step1 raw32817step1Labels raw32817step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5170 node5170Labels := by rfl

def raw32818 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw32818Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32818step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32818step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw32818step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, 1, -2], ![2, -2, 0]]
def raw32818step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32818 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32818 raw32818Labels = mixedMoment B node5074 node5074Labels := by
  calc
    mixedMoment B raw32818 raw32818Labels = mixedMoment B raw32818step0 raw32818step0Labels := by
      have ha : raw32818step0 = (fun i j => raw32818 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32818step0 raw32818; decide +kernel
      have hl : raw32818step0Labels = raw32818Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32818 raw32818Labels permutation152 permutation7
    mixedMoment B raw32818step0 raw32818step0Labels = mixedMoment B raw32818step1 raw32818step1Labels := by
      have ha : raw32818step1 = raw32818step0 := by apply Matrix.ext; unfold raw32818step1 raw32818step0; decide +kernel
      have hl : raw32818step0Labels = labelEmbedding10 ∘ raw32818step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32818step0 raw32818step0Labels raw32818step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5074 node5074Labels := by rfl

def raw32819 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw32819Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32819step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw32819step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32819step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32819step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw32819step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw32819step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32819 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32819 raw32819Labels = mixedMoment B node5105 node5105Labels := by
  calc
    mixedMoment B raw32819 raw32819Labels = mixedMoment B raw32819step0 raw32819step0Labels := by
      have hz : ∀ j, raw32819 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32819step0 = (fun i j => raw32819 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32819step0 raw32819; decide +kernel
      have hl : raw32819step0Labels = raw32819Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32819 raw32819Labels permutation346 hz
    mixedMoment B raw32819step0 raw32819step0Labels = mixedMoment B raw32819step1 raw32819step1Labels := by
      have ha : raw32819step1 = (fun i j => raw32819step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32819step1 raw32819step0; decide +kernel
      have hl : raw32819step1Labels = raw32819step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32819step0 raw32819step0Labels permutation32 permutation7
    mixedMoment B raw32819step1 raw32819step1Labels = mixedMoment B raw32819step2 raw32819step2Labels := by
      have ha : raw32819step2 = raw32819step1 := by apply Matrix.ext; unfold raw32819step2 raw32819step1; decide +kernel
      have hl : raw32819step1Labels = labelEmbedding10 ∘ raw32819step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32819step1 raw32819step1Labels raw32819step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5105 node5105Labels := by rfl

def raw32820 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![-3, 2, 1], ![0, -2, 2]]
def raw32820Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32820step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-3, 2, 1], ![0, -2, 2]]
def raw32820step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32820step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw32820step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw32820step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 2, -3], ![2, -2, 0]]
def raw32820step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32820 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32820 raw32820Labels = mixedMoment B node5103 node5103Labels := by
  calc
    mixedMoment B raw32820 raw32820Labels = mixedMoment B raw32820step0 raw32820step0Labels := by
      have hz : ∀ j, raw32820 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32820step0 = (fun i j => raw32820 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32820step0 raw32820; decide +kernel
      have hl : raw32820step0Labels = raw32820Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32820 raw32820Labels permutation346 hz
    mixedMoment B raw32820step0 raw32820step0Labels = mixedMoment B raw32820step1 raw32820step1Labels := by
      have ha : raw32820step1 = (fun i j => raw32820step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32820step1 raw32820step0; decide +kernel
      have hl : raw32820step1Labels = raw32820step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32820step0 raw32820step0Labels permutation32 permutation7
    mixedMoment B raw32820step1 raw32820step1Labels = mixedMoment B raw32820step2 raw32820step2Labels := by
      have ha : raw32820step2 = raw32820step1 := by apply Matrix.ext; unfold raw32820step2 raw32820step1; decide +kernel
      have hl : raw32820step1Labels = labelEmbedding10 ∘ raw32820step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32820step1 raw32820step1Labels raw32820step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5103 node5103Labels := by rfl

def raw32821 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw32821Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32821step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw32821step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32821step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw32821step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw32821step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 1, -2], ![2, -1, -1]]
def raw32821step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32821 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32821 raw32821Labels = mixedMoment B node5102 node5102Labels := by
  calc
    mixedMoment B raw32821 raw32821Labels = mixedMoment B raw32821step0 raw32821step0Labels := by
      have hz : ∀ j, raw32821 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32821step0 = (fun i j => raw32821 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32821step0 raw32821; decide +kernel
      have hl : raw32821step0Labels = raw32821Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32821 raw32821Labels permutation346 hz
    mixedMoment B raw32821step0 raw32821step0Labels = mixedMoment B raw32821step1 raw32821step1Labels := by
      have ha : raw32821step1 = (fun i j => raw32821step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32821step1 raw32821step0; decide +kernel
      have hl : raw32821step1Labels = raw32821step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32821step0 raw32821step0Labels permutation32 permutation7
    mixedMoment B raw32821step1 raw32821step1Labels = mixedMoment B raw32821step2 raw32821step2Labels := by
      have ha : raw32821step2 = raw32821step1 := by apply Matrix.ext; unfold raw32821step2 raw32821step1; decide +kernel
      have hl : raw32821step1Labels = labelEmbedding10 ∘ raw32821step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32821step1 raw32821step1Labels raw32821step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5102 node5102Labels := by rfl

def raw32822 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw32822Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32822step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw32822step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32822step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -2, 1], ![-1, 2, -1], ![-1, 0, 1], ![-2, 0, 2]]
def raw32822step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw32822step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32822step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw32822step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32822step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32822 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32822 raw32822Labels = mixedMoment B node4860 node4860Labels := by
  calc
    mixedMoment B raw32822 raw32822Labels = mixedMoment B raw32822step0 raw32822step0Labels := by
      have hz : ∀ j, raw32822 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32822step0 = (fun i j => raw32822 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32822step0 raw32822; decide +kernel
      have hl : raw32822step0Labels = raw32822Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32822 raw32822Labels permutation346 hz
    mixedMoment B raw32822step0 raw32822step0Labels = mixedMoment B raw32822step1 raw32822step1Labels := by
      have ha : raw32822step1 = (fun i j => raw32822step0 (permutation44 i) (permutation4 j)) := by apply Matrix.ext; unfold raw32822step1 raw32822step0; decide +kernel
      have hl : raw32822step1Labels = raw32822step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32822step0 raw32822step0Labels permutation44 permutation4
    mixedMoment B raw32822step1 raw32822step1Labels = mixedMoment B raw32822step2 raw32822step2Labels := by
      have ha : raw32822step2 = -raw32822step1 := by apply Matrix.ext; change ∀ i j, raw32822step2 i j = -(raw32822step1 i j); unfold raw32822step2 raw32822step1; decide +kernel
      have hl : raw32822step2Labels = raw32822step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32822step2 raw32822step2Labels = mixedMoment B raw32822step3 raw32822step3Labels := by
      have ha : raw32822step3 = raw32822step2 := by apply Matrix.ext; unfold raw32822step3 raw32822step2; decide +kernel
      have hl : raw32822step2Labels = labelEmbedding7 ∘ raw32822step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32822step2 raw32822step2Labels raw32822step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4860 node4860Labels := by rfl

def raw32823 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 1, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw32823Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32823step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32823step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32823step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32823step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32823 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32823 raw32823Labels = mixedMoment B node5183 node5183Labels := by
  calc
    mixedMoment B raw32823 raw32823Labels = mixedMoment B raw32823step0 raw32823step0Labels := by
      have ha : raw32823step0 = (fun i j => raw32823 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32823step0 raw32823; decide +kernel
      have hl : raw32823step0Labels = raw32823Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32823 raw32823Labels permutation154 permutation6
    mixedMoment B raw32823step0 raw32823step0Labels = mixedMoment B raw32823step1 raw32823step1Labels := by
      have ha : raw32823step1 = raw32823step0 := by apply Matrix.ext; unfold raw32823step1 raw32823step0; decide +kernel
      have hl : raw32823step0Labels = labelEmbedding9 ∘ raw32823step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32823step0 raw32823step0Labels raw32823step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5183 node5183Labels := by rfl

def raw32824 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw32824Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32824step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![-1, 0, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw32824step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32824step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw32824step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32824step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, 0, -2]]
def raw32824step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32824 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32824 raw32824Labels = mixedMoment B node5198 node5198Labels := by
  calc
    mixedMoment B raw32824 raw32824Labels = mixedMoment B raw32824step0 raw32824step0Labels := by
      have hz : ∀ j, raw32824 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32824step0 = (fun i j => raw32824 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32824step0 raw32824; decide +kernel
      have hl : raw32824step0Labels = raw32824Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32824 raw32824Labels permutation346 hz
    mixedMoment B raw32824step0 raw32824step0Labels = mixedMoment B raw32824step1 raw32824step1Labels := by
      have ha : raw32824step1 = (fun i j => raw32824step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32824step1 raw32824step0; decide +kernel
      have hl : raw32824step1Labels = raw32824step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32824step0 raw32824step0Labels permutation34 permutation6
    mixedMoment B raw32824step1 raw32824step1Labels = mixedMoment B raw32824step2 raw32824step2Labels := by
      have ha : raw32824step2 = raw32824step1 := by apply Matrix.ext; unfold raw32824step2 raw32824step1; decide +kernel
      have hl : raw32824step1Labels = labelEmbedding9 ∘ raw32824step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32824step1 raw32824step1Labels raw32824step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5198 node5198Labels := by rfl

def raw32825 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![-3, 2, 1], ![0, -2, 2]]
def raw32825Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32825step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, -1, 1], ![-3, 2, 1], ![0, -2, 2]]
def raw32825step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32825step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw32825step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32825step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw32825step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32825 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32825 raw32825Labels = mixedMoment B node5195 node5195Labels := by
  calc
    mixedMoment B raw32825 raw32825Labels = mixedMoment B raw32825step0 raw32825step0Labels := by
      have hz : ∀ j, raw32825 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32825step0 = (fun i j => raw32825 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32825step0 raw32825; decide +kernel
      have hl : raw32825step0Labels = raw32825Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32825 raw32825Labels permutation346 hz
    mixedMoment B raw32825step0 raw32825step0Labels = mixedMoment B raw32825step1 raw32825step1Labels := by
      have ha : raw32825step1 = (fun i j => raw32825step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32825step1 raw32825step0; decide +kernel
      have hl : raw32825step1Labels = raw32825step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32825step0 raw32825step0Labels permutation34 permutation6
    mixedMoment B raw32825step1 raw32825step1Labels = mixedMoment B raw32825step2 raw32825step2Labels := by
      have ha : raw32825step2 = raw32825step1 := by apply Matrix.ext; unfold raw32825step2 raw32825step1; decide +kernel
      have hl : raw32825step1Labels = labelEmbedding9 ∘ raw32825step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32825step1 raw32825step1Labels raw32825step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5195 node5195Labels := by rfl

def raw32826 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw32826Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32826step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -1, -1], ![0, -1, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw32826step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32826step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw32826step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32826step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw32826step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32826 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32826 raw32826Labels = mixedMoment B node5199 node5199Labels := by
  calc
    mixedMoment B raw32826 raw32826Labels = mixedMoment B raw32826step0 raw32826step0Labels := by
      have hz : ∀ j, raw32826 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32826step0 = (fun i j => raw32826 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32826step0 raw32826; decide +kernel
      have hl : raw32826step0Labels = raw32826Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32826 raw32826Labels permutation346 hz
    mixedMoment B raw32826step0 raw32826step0Labels = mixedMoment B raw32826step1 raw32826step1Labels := by
      have ha : raw32826step1 = (fun i j => raw32826step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32826step1 raw32826step0; decide +kernel
      have hl : raw32826step1Labels = raw32826step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32826step0 raw32826step0Labels permutation34 permutation6
    mixedMoment B raw32826step1 raw32826step1Labels = mixedMoment B raw32826step2 raw32826step2Labels := by
      have ha : raw32826step2 = raw32826step1 := by apply Matrix.ext; unfold raw32826step2 raw32826step1; decide +kernel
      have hl : raw32826step1Labels = labelEmbedding9 ∘ raw32826step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32826step1 raw32826step1Labels raw32826step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5199 node5199Labels := by rfl

def raw32827 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw32827Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32827step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32827step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32827step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32827step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32827 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32827 raw32827Labels = mixedMoment B node4798 node4798Labels := by
  calc
    mixedMoment B raw32827 raw32827Labels = mixedMoment B raw32827step0 raw32827step0Labels := by
      have ha : raw32827step0 = (fun i j => raw32827 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32827step0 raw32827; decide +kernel
      have hl : raw32827step0Labels = raw32827Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32827 raw32827Labels permutation154 permutation6
    mixedMoment B raw32827step0 raw32827step0Labels = mixedMoment B raw32827step1 raw32827step1Labels := by
      have ha : raw32827step1 = raw32827step0 := by apply Matrix.ext; unfold raw32827step1 raw32827step0; decide +kernel
      have hl : raw32827step0Labels = labelEmbedding9 ∘ raw32827step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32827step0 raw32827step0Labels raw32827step1Labels labelEmbedding9 hl
    _ = mixedMoment B node4798 node4798Labels := by rfl

def raw32828 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw32828Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32828step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32828step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32828step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, 0, -2]]
def raw32828step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32828 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32828 raw32828Labels = mixedMoment B node5070 node5070Labels := by
  calc
    mixedMoment B raw32828 raw32828Labels = mixedMoment B raw32828step0 raw32828step0Labels := by
      have ha : raw32828step0 = (fun i j => raw32828 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32828step0 raw32828; decide +kernel
      have hl : raw32828step0Labels = raw32828Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32828 raw32828Labels permutation154 permutation6
    mixedMoment B raw32828step0 raw32828step0Labels = mixedMoment B raw32828step1 raw32828step1Labels := by
      have ha : raw32828step1 = raw32828step0 := by apply Matrix.ext; unfold raw32828step1 raw32828step0; decide +kernel
      have hl : raw32828step0Labels = labelEmbedding9 ∘ raw32828step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32828step0 raw32828step0Labels raw32828step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5070 node5070Labels := by rfl

def raw32829 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -1, 0], ![0, -1, 1], ![-3, 2, 1], ![0, -2, 2]]
def raw32829Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32829step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw32829step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32829step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![2, 0, -2]]
def raw32829step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32829 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32829 raw32829Labels = mixedMoment B node5143 node5143Labels := by
  calc
    mixedMoment B raw32829 raw32829Labels = mixedMoment B raw32829step0 raw32829step0Labels := by
      have ha : raw32829step0 = (fun i j => raw32829 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32829step0 raw32829; decide +kernel
      have hl : raw32829step0Labels = raw32829Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32829 raw32829Labels permutation154 permutation6
    mixedMoment B raw32829step0 raw32829step0Labels = mixedMoment B raw32829step1 raw32829step1Labels := by
      have ha : raw32829step1 = raw32829step0 := by apply Matrix.ext; unfold raw32829step1 raw32829step0; decide +kernel
      have hl : raw32829step0Labels = labelEmbedding9 ∘ raw32829step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32829step0 raw32829step0Labels raw32829step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5143 node5143Labels := by rfl

def raw32830 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw32830Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32830step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw32830step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32830step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw32830step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32830step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw32830step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32830 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32830 raw32830Labels = mixedMoment B node4828 node4828Labels := by
  calc
    mixedMoment B raw32830 raw32830Labels = mixedMoment B raw32830step0 raw32830step0Labels := by
      have hz : ∀ j, raw32830 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32830step0 = (fun i j => raw32830 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32830step0 raw32830; decide +kernel
      have hl : raw32830step0Labels = raw32830Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32830 raw32830Labels permutation346 hz
    mixedMoment B raw32830step0 raw32830step0Labels = mixedMoment B raw32830step1 raw32830step1Labels := by
      have ha : raw32830step1 = (fun i j => raw32830step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32830step1 raw32830step0; decide +kernel
      have hl : raw32830step1Labels = raw32830step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32830step0 raw32830step0Labels permutation34 permutation6
    mixedMoment B raw32830step1 raw32830step1Labels = mixedMoment B raw32830step2 raw32830step2Labels := by
      have ha : raw32830step2 = raw32830step1 := by apply Matrix.ext; unfold raw32830step2 raw32830step1; decide +kernel
      have hl : raw32830step1Labels = labelEmbedding9 ∘ raw32830step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32830step1 raw32830step1Labels raw32830step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4828 node4828Labels := by rfl

def raw32831 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![1, -2, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw32831Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32831step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![1, -2, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw32831step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32831step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw32831step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32831step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw32831step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32831 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32831 raw32831Labels = mixedMoment B node5095 node5095Labels := by
  calc
    mixedMoment B raw32831 raw32831Labels = mixedMoment B raw32831step0 raw32831step0Labels := by
      have hz : ∀ j, raw32831 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32831step0 = (fun i j => raw32831 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32831step0 raw32831; decide +kernel
      have hl : raw32831step0Labels = raw32831Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32831 raw32831Labels permutation346 hz
    mixedMoment B raw32831step0 raw32831step0Labels = mixedMoment B raw32831step1 raw32831step1Labels := by
      have ha : raw32831step1 = (fun i j => raw32831step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32831step1 raw32831step0; decide +kernel
      have hl : raw32831step1Labels = raw32831step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32831step0 raw32831step0Labels permutation34 permutation6
    mixedMoment B raw32831step1 raw32831step1Labels = mixedMoment B raw32831step2 raw32831step2Labels := by
      have ha : raw32831step2 = raw32831step1 := by apply Matrix.ext; unfold raw32831step2 raw32831step1; decide +kernel
      have hl : raw32831step1Labels = labelEmbedding9 ∘ raw32831step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32831step1 raw32831step1Labels raw32831step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5095 node5095Labels := by rfl

def raw32832 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![1, -2, 1], ![-2, 1, 1], ![0, -2, 2]]
def raw32832Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32832step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw32832step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32832step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -2, 1], ![1, 1, -2], ![2, 0, -2]]
def raw32832step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32832 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32832 raw32832Labels = mixedMoment B node5132 node5132Labels := by
  calc
    mixedMoment B raw32832 raw32832Labels = mixedMoment B raw32832step0 raw32832step0Labels := by
      have ha : raw32832step0 = (fun i j => raw32832 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32832step0 raw32832; decide +kernel
      have hl : raw32832step0Labels = raw32832Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32832 raw32832Labels permutation154 permutation6
    mixedMoment B raw32832step0 raw32832step0Labels = mixedMoment B raw32832step1 raw32832step1Labels := by
      have ha : raw32832step1 = raw32832step0 := by apply Matrix.ext; unfold raw32832step1 raw32832step0; decide +kernel
      have hl : raw32832step0Labels = labelEmbedding9 ∘ raw32832step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32832step0 raw32832step0Labels raw32832step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5132 node5132Labels := by rfl

def raw32833 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![-3, 2, 1], ![0, -2, 2]]
def raw32833Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32833step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -2, 1], ![-3, 2, 1], ![0, -2, 2]]
def raw32833step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32833step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![1, 1, -2], ![2, 0, -2]]
def raw32833step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32833step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -3, 2], ![1, 1, -2], ![2, 0, -2]]
def raw32833step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32833 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32833 raw32833Labels = mixedMoment B node5158 node5158Labels := by
  calc
    mixedMoment B raw32833 raw32833Labels = mixedMoment B raw32833step0 raw32833step0Labels := by
      have hz : ∀ j, raw32833 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32833step0 = (fun i j => raw32833 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32833step0 raw32833; decide +kernel
      have hl : raw32833step0Labels = raw32833Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32833 raw32833Labels permutation346 hz
    mixedMoment B raw32833step0 raw32833step0Labels = mixedMoment B raw32833step1 raw32833step1Labels := by
      have ha : raw32833step1 = (fun i j => raw32833step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32833step1 raw32833step0; decide +kernel
      have hl : raw32833step1Labels = raw32833step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32833step0 raw32833step0Labels permutation34 permutation6
    mixedMoment B raw32833step1 raw32833step1Labels = mixedMoment B raw32833step2 raw32833step2Labels := by
      have ha : raw32833step2 = raw32833step1 := by apply Matrix.ext; unfold raw32833step2 raw32833step1; decide +kernel
      have hl : raw32833step1Labels = labelEmbedding9 ∘ raw32833step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32833step1 raw32833step1Labels raw32833step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5158 node5158Labels := by rfl

def raw32834 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![1, -2, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw32834Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32834step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![1, -2, 1], ![-2, 1, 1], ![-1, -1, 2]]
def raw32834step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32834step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw32834step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32834step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 1, -2], ![2, -1, -1]]
def raw32834step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32834 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32834 raw32834Labels = mixedMoment B node5164 node5164Labels := by
  calc
    mixedMoment B raw32834 raw32834Labels = mixedMoment B raw32834step0 raw32834step0Labels := by
      have hz : ∀ j, raw32834 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32834step0 = (fun i j => raw32834 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32834step0 raw32834; decide +kernel
      have hl : raw32834step0Labels = raw32834Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32834 raw32834Labels permutation346 hz
    mixedMoment B raw32834step0 raw32834step0Labels = mixedMoment B raw32834step1 raw32834step1Labels := by
      have ha : raw32834step1 = (fun i j => raw32834step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32834step1 raw32834step0; decide +kernel
      have hl : raw32834step1Labels = raw32834step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32834step0 raw32834step0Labels permutation34 permutation6
    mixedMoment B raw32834step1 raw32834step1Labels = mixedMoment B raw32834step2 raw32834step2Labels := by
      have ha : raw32834step2 = raw32834step1 := by apply Matrix.ext; unfold raw32834step2 raw32834step1; decide +kernel
      have hl : raw32834step1Labels = labelEmbedding9 ∘ raw32834step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32834step1 raw32834step1Labels raw32834step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5164 node5164Labels := by rfl

def raw32835 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw32835Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32835step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw32835step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32835step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32835step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32835step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32835step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32835 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32835 raw32835Labels = mixedMoment B node4834 node4834Labels := by
  calc
    mixedMoment B raw32835 raw32835Labels = mixedMoment B raw32835step0 raw32835step0Labels := by
      have hz : ∀ j, raw32835 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32835step0 = (fun i j => raw32835 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32835step0 raw32835; decide +kernel
      have hl : raw32835step0Labels = raw32835Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32835 raw32835Labels permutation346 hz
    mixedMoment B raw32835step0 raw32835step0Labels = mixedMoment B raw32835step1 raw32835step1Labels := by
      have ha : raw32835step1 = (fun i j => raw32835step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32835step1 raw32835step0; decide +kernel
      have hl : raw32835step1Labels = raw32835step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32835step0 raw32835step0Labels permutation34 permutation6
    mixedMoment B raw32835step1 raw32835step1Labels = mixedMoment B raw32835step2 raw32835step2Labels := by
      have ha : raw32835step2 = raw32835step1 := by apply Matrix.ext; unfold raw32835step2 raw32835step1; decide +kernel
      have hl : raw32835step1Labels = labelEmbedding9 ∘ raw32835step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32835step1 raw32835step1Labels raw32835step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4834 node4834Labels := by rfl

def raw32836 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw32836Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32836step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw32836step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32836step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32836step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32836step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32836step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32836 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32836 raw32836Labels = mixedMoment B node5101 node5101Labels := by
  calc
    mixedMoment B raw32836 raw32836Labels = mixedMoment B raw32836step0 raw32836step0Labels := by
      have hz : ∀ j, raw32836 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32836step0 = (fun i j => raw32836 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32836step0 raw32836; decide +kernel
      have hl : raw32836step0Labels = raw32836Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32836 raw32836Labels permutation346 hz
    mixedMoment B raw32836step0 raw32836step0Labels = mixedMoment B raw32836step1 raw32836step1Labels := by
      have ha : raw32836step1 = (fun i j => raw32836step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32836step1 raw32836step0; decide +kernel
      have hl : raw32836step1Labels = raw32836step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32836step0 raw32836step0Labels permutation34 permutation6
    mixedMoment B raw32836step1 raw32836step1Labels = mixedMoment B raw32836step2 raw32836step2Labels := by
      have ha : raw32836step2 = raw32836step1 := by apply Matrix.ext; unfold raw32836step2 raw32836step1; decide +kernel
      have hl : raw32836step1Labels = labelEmbedding9 ∘ raw32836step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32836step1 raw32836step1Labels raw32836step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5101 node5101Labels := by rfl

def raw32837 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -2, 2]]
def raw32837Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32837step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32837step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32837step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 0, -2]]
def raw32837step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32837 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32837 raw32837Labels = mixedMoment B node5134 node5134Labels := by
  calc
    mixedMoment B raw32837 raw32837Labels = mixedMoment B raw32837step0 raw32837step0Labels := by
      have ha : raw32837step0 = (fun i j => raw32837 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32837step0 raw32837; decide +kernel
      have hl : raw32837step0Labels = raw32837Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32837 raw32837Labels permutation154 permutation6
    mixedMoment B raw32837step0 raw32837step0Labels = mixedMoment B raw32837step1 raw32837step1Labels := by
      have ha : raw32837step1 = raw32837step0 := by apply Matrix.ext; unfold raw32837step1 raw32837step0; decide +kernel
      have hl : raw32837step0Labels = labelEmbedding9 ∘ raw32837step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32837step0 raw32837step0Labels raw32837step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5134 node5134Labels := by rfl

def raw32838 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw32838Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32838step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![1, 0, -1], ![0, -1, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw32838step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32838step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw32838step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32838step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw32838step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32838 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32838 raw32838Labels = mixedMoment B node4827 node4827Labels := by
  calc
    mixedMoment B raw32838 raw32838Labels = mixedMoment B raw32838step0 raw32838step0Labels := by
      have hz : ∀ j, raw32838 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32838step0 = (fun i j => raw32838 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32838step0 raw32838; decide +kernel
      have hl : raw32838step0Labels = raw32838Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32838 raw32838Labels permutation346 hz
    mixedMoment B raw32838step0 raw32838step0Labels = mixedMoment B raw32838step1 raw32838step1Labels := by
      have ha : raw32838step1 = (fun i j => raw32838step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32838step1 raw32838step0; decide +kernel
      have hl : raw32838step1Labels = raw32838step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32838step0 raw32838step0Labels permutation34 permutation6
    mixedMoment B raw32838step1 raw32838step1Labels = mixedMoment B raw32838step2 raw32838step2Labels := by
      have ha : raw32838step2 = raw32838step1 := by apply Matrix.ext; unfold raw32838step2 raw32838step1; decide +kernel
      have hl : raw32838step1Labels = labelEmbedding9 ∘ raw32838step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32838step1 raw32838step1Labels raw32838step2Labels labelEmbedding9 hl
    _ = mixedMoment B node4827 node4827Labels := by rfl

def raw32839 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, 0, 0], ![0, -1, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw32839Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32839step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![0, 1, -1], ![0, -1, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw32839step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32839step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw32839step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw32839step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -2, 1], ![1, 0, -1], ![2, 1, -3]]
def raw32839step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32839 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32839 raw32839Labels = mixedMoment B node5094 node5094Labels := by
  calc
    mixedMoment B raw32839 raw32839Labels = mixedMoment B raw32839step0 raw32839step0Labels := by
      have hz : ∀ j, raw32839 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32839step0 = (fun i j => raw32839 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32839step0 raw32839; decide +kernel
      have hl : raw32839step0Labels = raw32839Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32839 raw32839Labels permutation346 hz
    mixedMoment B raw32839step0 raw32839step0Labels = mixedMoment B raw32839step1 raw32839step1Labels := by
      have ha : raw32839step1 = (fun i j => raw32839step0 (permutation145 i) (permutation4 j)) := by apply Matrix.ext; unfold raw32839step1 raw32839step0; decide +kernel
      have hl : raw32839step1Labels = raw32839step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32839step0 raw32839step0Labels permutation145 permutation4
    mixedMoment B raw32839step1 raw32839step1Labels = mixedMoment B raw32839step2 raw32839step2Labels := by
      have ha : raw32839step2 = raw32839step1 := by apply Matrix.ext; unfold raw32839step2 raw32839step1; decide +kernel
      have hl : raw32839step1Labels = labelEmbedding7 ∘ raw32839step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32839step1 raw32839step1Labels raw32839step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5094 node5094Labels := by rfl

def raw32840 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 1, 0], ![0, -1, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw32840Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32840step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw32840step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw32840step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw32840step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32840 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32840 raw32840Labels = mixedMoment B node5069 node5069Labels := by
  calc
    mixedMoment B raw32840 raw32840Labels = mixedMoment B raw32840step0 raw32840step0Labels := by
      have ha : raw32840step0 = (fun i j => raw32840 (permutation654 i) (permutation4 j)) := by apply Matrix.ext; unfold raw32840step0 raw32840; decide +kernel
      have hl : raw32840step0Labels = raw32840Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32840 raw32840Labels permutation654 permutation4
    mixedMoment B raw32840step0 raw32840step0Labels = mixedMoment B raw32840step1 raw32840step1Labels := by
      have ha : raw32840step1 = raw32840step0 := by apply Matrix.ext; unfold raw32840step1 raw32840step0; decide +kernel
      have hl : raw32840step0Labels = labelEmbedding7 ∘ raw32840step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32840step0 raw32840step0Labels raw32840step1Labels labelEmbedding7 hl
    _ = mixedMoment B node5069 node5069Labels := by rfl

def raw32841 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw32841Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32841step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![-1, 0, 1], ![-2, 1, 1], ![1, -3, 2]]
def raw32841step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32841step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw32841step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw32841step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, -1, 0], ![2, 1, -3]]
def raw32841step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32841 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32841 raw32841Labels = mixedMoment B node5161 node5161Labels := by
  calc
    mixedMoment B raw32841 raw32841Labels = mixedMoment B raw32841step0 raw32841step0Labels := by
      have hz : ∀ j, raw32841 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32841step0 = (fun i j => raw32841 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32841step0 raw32841; decide +kernel
      have hl : raw32841step0Labels = raw32841Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32841 raw32841Labels permutation346 hz
    mixedMoment B raw32841step0 raw32841step0Labels = mixedMoment B raw32841step1 raw32841step1Labels := by
      have ha : raw32841step1 = (fun i j => raw32841step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw32841step1 raw32841step0; decide +kernel
      have hl : raw32841step1Labels = raw32841step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32841step0 raw32841step0Labels permutation34 permutation6
    mixedMoment B raw32841step1 raw32841step1Labels = mixedMoment B raw32841step2 raw32841step2Labels := by
      have ha : raw32841step2 = raw32841step1 := by apply Matrix.ext; unfold raw32841step2 raw32841step1; decide +kernel
      have hl : raw32841step1Labels = labelEmbedding9 ∘ raw32841step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32841step1 raw32841step1Labels raw32841step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5161 node5161Labels := by rfl

def raw32842 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, 0, 0], ![0, -1, 1], ![-3, 2, 1], ![1, -3, 2]]
def raw32842Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32842step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, 0, -1], ![0, -1, 1], ![-3, 2, 1], ![1, -3, 2]]
def raw32842step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32842step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw32842step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw32842step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, 1, -1], ![2, -3, 1], ![2, 1, -3]]
def raw32842step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32842 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32842 raw32842Labels = mixedMoment B node5079 node5079Labels := by
  calc
    mixedMoment B raw32842 raw32842Labels = mixedMoment B raw32842step0 raw32842step0Labels := by
      have hz : ∀ j, raw32842 (permutation346 0) j = 0 := by decide +kernel
      have ha : raw32842step0 = (fun i j => raw32842 (permutation346 i.succ) j) := by apply Matrix.ext; unfold raw32842step0 raw32842; decide +kernel
      have hl : raw32842step0Labels = raw32842Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32842 raw32842Labels permutation346 hz
    mixedMoment B raw32842step0 raw32842step0Labels = mixedMoment B raw32842step1 raw32842step1Labels := by
      have ha : raw32842step1 = (fun i j => raw32842step0 (permutation143 i) (permutation4 j)) := by apply Matrix.ext; unfold raw32842step1 raw32842step0; decide +kernel
      have hl : raw32842step1Labels = raw32842step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32842step0 raw32842step0Labels permutation143 permutation4
    mixedMoment B raw32842step1 raw32842step1Labels = mixedMoment B raw32842step2 raw32842step2Labels := by
      have ha : raw32842step2 = raw32842step1 := by apply Matrix.ext; unfold raw32842step2 raw32842step1; decide +kernel
      have hl : raw32842step1Labels = labelEmbedding7 ∘ raw32842step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32842step1 raw32842step1Labels raw32842step2Labels labelEmbedding7 hl
    _ = mixedMoment B node5079 node5079Labels := by rfl

def raw32843 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32843Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32843 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32843 raw32843Labels = mixedMoment B node4964 node4964Labels := by
  calc
    _ = mixedMoment B node4964 node4964Labels := by rfl

def raw32844 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32844Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32844step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw32844step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32844 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32844 raw32844Labels = mixedMoment B node5145 node5145Labels := by
  calc
    mixedMoment B raw32844 raw32844Labels = mixedMoment B raw32844step0 raw32844step0Labels := by
      have ha : raw32844step0 = (fun i j => raw32844 (permutation158 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32844step0 raw32844; decide +kernel
      have hl : raw32844step0Labels = raw32844Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32844 raw32844Labels permutation158 permutation2
    _ = mixedMoment B node5145 node5145Labels := by rfl

def raw32845 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw32845Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32845step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -1, -1]]
def raw32845step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32845 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32845 raw32845Labels = mixedMoment B node5145 node5145Labels := by
  calc
    mixedMoment B raw32845 raw32845Labels = mixedMoment B raw32845step0 raw32845step0Labels := by
      have ha : raw32845step0 = (fun i j => raw32845 (permutation164 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32845step0 raw32845; decide +kernel
      have hl : raw32845step0Labels = raw32845Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32845 raw32845Labels permutation164 permutation2
    _ = mixedMoment B node5145 node5145Labels := by rfl

def raw32846 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32846Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32846step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32846step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32846 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32846 raw32846Labels = mixedMoment B node4958 node4958Labels := by
  calc
    mixedMoment B raw32846 raw32846Labels = mixedMoment B raw32846step0 raw32846step0Labels := by
      have ha : raw32846step0 = (fun i j => raw32846 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32846step0 raw32846; decide +kernel
      have hl : raw32846step0Labels = raw32846Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32846 raw32846Labels permutation154 permutation2
    _ = mixedMoment B node4958 node4958Labels := by rfl

def raw32847 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32847Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32847step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32847step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32847 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32847 raw32847Labels = mixedMoment B node5039 node5039Labels := by
  calc
    mixedMoment B raw32847 raw32847Labels = mixedMoment B raw32847step0 raw32847step0Labels := by
      have ha : raw32847step0 = (fun i j => raw32847 (permutation178 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32847step0 raw32847; decide +kernel
      have hl : raw32847step0Labels = raw32847Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32847 raw32847Labels permutation178 permutation2
    _ = mixedMoment B node5039 node5039Labels := by rfl

def raw32848 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw32848Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32848step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32848step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32848 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32848 raw32848Labels = mixedMoment B node5130 node5130Labels := by
  calc
    mixedMoment B raw32848 raw32848Labels = mixedMoment B raw32848step0 raw32848step0Labels := by
      have ha : raw32848step0 = (fun i j => raw32848 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32848step0 raw32848; decide +kernel
      have hl : raw32848step0Labels = raw32848Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32848 raw32848Labels permutation154 permutation2
    _ = mixedMoment B node5130 node5130Labels := by rfl

def raw32849 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32849Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32849 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32849 raw32849Labels = mixedMoment B node4958 node4958Labels := by
  calc
    _ = mixedMoment B node4958 node4958Labels := by rfl

def raw32850 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32850Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32850step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32850step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32850 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32850 raw32850Labels = mixedMoment B node5039 node5039Labels := by
  calc
    mixedMoment B raw32850 raw32850Labels = mixedMoment B raw32850step0 raw32850step0Labels := by
      have ha : raw32850step0 = (fun i j => raw32850 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32850step0 raw32850; decide +kernel
      have hl : raw32850step0Labels = raw32850Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32850 raw32850Labels permutation176 permutation2
    _ = mixedMoment B node5039 node5039Labels := by rfl

def raw32851 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32851Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32851 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32851 raw32851Labels = mixedMoment B node5130 node5130Labels := by
  calc
    _ = mixedMoment B node5130 node5130Labels := by rfl

def raw32852 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32852Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32852 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32852 raw32852Labels = mixedMoment B node4956 node4956Labels := by
  calc
    _ = mixedMoment B node4956 node4956Labels := by rfl

def raw32853 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32853Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32853step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32853step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32853 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32853 raw32853Labels = mixedMoment B node5037 node5037Labels := by
  calc
    mixedMoment B raw32853 raw32853Labels = mixedMoment B raw32853step0 raw32853step0Labels := by
      have ha : raw32853step0 = (fun i j => raw32853 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32853step0 raw32853; decide +kernel
      have hl : raw32853step0Labels = raw32853Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32853 raw32853Labels permutation176 permutation2
    _ = mixedMoment B node5037 node5037Labels := by rfl

def raw32854 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32854Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32854 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32854 raw32854Labels = mixedMoment B node5128 node5128Labels := by
  calc
    _ = mixedMoment B node5128 node5128Labels := by rfl

def raw32855 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw32855Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32855step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32855step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32855 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32855 raw32855Labels = mixedMoment B node5128 node5128Labels := by
  calc
    mixedMoment B raw32855 raw32855Labels = mixedMoment B raw32855step0 raw32855step0Labels := by
      have ha : raw32855step0 = (fun i j => raw32855 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32855step0 raw32855; decide +kernel
      have hl : raw32855step0Labels = raw32855Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32855 raw32855Labels permutation154 permutation2
    _ = mixedMoment B node5128 node5128Labels := by rfl

def raw32856 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32856Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32856step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32856step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32856step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw32856step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32856step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw32856step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32856 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32856 raw32856Labels = mixedMoment B node3836 node3836Labels := by
  calc
    mixedMoment B raw32856 raw32856Labels = mixedMoment B raw32856step0 raw32856step0Labels := by
      have ha : raw32856step0 = (fun i j => raw32856 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32856step0 raw32856; decide +kernel
      have hl : raw32856step0Labels = raw32856Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32856 raw32856Labels permutation176 permutation7
    mixedMoment B raw32856step0 raw32856step0Labels = mixedMoment B raw32856step1 raw32856step1Labels := by
      have ha : raw32856step1 = -raw32856step0 := by apply Matrix.ext; change ∀ i j, raw32856step1 i j = -(raw32856step0 i j); unfold raw32856step1 raw32856step0; decide +kernel
      have hl : raw32856step1Labels = raw32856step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32856step1 raw32856step1Labels = mixedMoment B raw32856step2 raw32856step2Labels := by
      have ha : raw32856step2 = raw32856step1 := by apply Matrix.ext; unfold raw32856step2 raw32856step1; decide +kernel
      have hl : raw32856step1Labels = labelEmbedding1 ∘ raw32856step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32856step1 raw32856step1Labels raw32856step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3836 node3836Labels := by rfl

def raw32857 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32857Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32857step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32857step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32857step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw32857step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32857step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw32857step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32857 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32857 raw32857Labels = mixedMoment B node3798 node3798Labels := by
  calc
    mixedMoment B raw32857 raw32857Labels = mixedMoment B raw32857step0 raw32857step0Labels := by
      have ha : raw32857step0 = (fun i j => raw32857 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32857step0 raw32857; decide +kernel
      have hl : raw32857step0Labels = raw32857Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32857 raw32857Labels permutation176 permutation7
    mixedMoment B raw32857step0 raw32857step0Labels = mixedMoment B raw32857step1 raw32857step1Labels := by
      have ha : raw32857step1 = -raw32857step0 := by apply Matrix.ext; change ∀ i j, raw32857step1 i j = -(raw32857step0 i j); unfold raw32857step1 raw32857step0; decide +kernel
      have hl : raw32857step1Labels = raw32857step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32857step1 raw32857step1Labels = mixedMoment B raw32857step2 raw32857step2Labels := by
      have ha : raw32857step2 = raw32857step1 := by apply Matrix.ext; unfold raw32857step2 raw32857step1; decide +kernel
      have hl : raw32857step1Labels = labelEmbedding1 ∘ raw32857step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32857step1 raw32857step1Labels raw32857step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3798 node3798Labels := by rfl

def raw32858 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32858Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32858step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw32858step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32858step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32858step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32858step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32858step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32858 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32858 raw32858Labels = mixedMoment B node3843 node3843Labels := by
  calc
    mixedMoment B raw32858 raw32858Labels = mixedMoment B raw32858step0 raw32858step0Labels := by
      have ha : raw32858step0 = (fun i j => raw32858 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32858step0 raw32858; decide +kernel
      have hl : raw32858step0Labels = raw32858Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32858 raw32858Labels permutation176 permutation7
    mixedMoment B raw32858step0 raw32858step0Labels = mixedMoment B raw32858step1 raw32858step1Labels := by
      have ha : raw32858step1 = -raw32858step0 := by apply Matrix.ext; change ∀ i j, raw32858step1 i j = -(raw32858step0 i j); unfold raw32858step1 raw32858step0; decide +kernel
      have hl : raw32858step1Labels = raw32858step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32858step1 raw32858step1Labels = mixedMoment B raw32858step2 raw32858step2Labels := by
      have ha : raw32858step2 = raw32858step1 := by apply Matrix.ext; unfold raw32858step2 raw32858step1; decide +kernel
      have hl : raw32858step1Labels = labelEmbedding1 ∘ raw32858step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32858step1 raw32858step1Labels raw32858step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3843 node3843Labels := by rfl

def raw32859 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw32859Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32859step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw32859step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32859step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32859step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32859step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32859step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32859 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32859 raw32859Labels = mixedMoment B node3843 node3843Labels := by
  calc
    mixedMoment B raw32859 raw32859Labels = mixedMoment B raw32859step0 raw32859step0Labels := by
      have ha : raw32859step0 = (fun i j => raw32859 (permutation178 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32859step0 raw32859; decide +kernel
      have hl : raw32859step0Labels = raw32859Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32859 raw32859Labels permutation178 permutation7
    mixedMoment B raw32859step0 raw32859step0Labels = mixedMoment B raw32859step1 raw32859step1Labels := by
      have ha : raw32859step1 = -raw32859step0 := by apply Matrix.ext; change ∀ i j, raw32859step1 i j = -(raw32859step0 i j); unfold raw32859step1 raw32859step0; decide +kernel
      have hl : raw32859step1Labels = raw32859step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32859step1 raw32859step1Labels = mixedMoment B raw32859step2 raw32859step2Labels := by
      have ha : raw32859step2 = raw32859step1 := by apply Matrix.ext; unfold raw32859step2 raw32859step1; decide +kernel
      have hl : raw32859step1Labels = labelEmbedding1 ∘ raw32859step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32859step1 raw32859step1Labels raw32859step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3843 node3843Labels := by rfl

def raw32860 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32860Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32860step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw32860step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32860step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32860step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32860step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32860step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32860 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32860 raw32860Labels = mixedMoment B node3844 node3844Labels := by
  calc
    mixedMoment B raw32860 raw32860Labels = mixedMoment B raw32860step0 raw32860step0Labels := by
      have ha : raw32860step0 = (fun i j => raw32860 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32860step0 raw32860; decide +kernel
      have hl : raw32860step0Labels = raw32860Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32860 raw32860Labels permutation176 permutation7
    mixedMoment B raw32860step0 raw32860step0Labels = mixedMoment B raw32860step1 raw32860step1Labels := by
      have ha : raw32860step1 = -raw32860step0 := by apply Matrix.ext; change ∀ i j, raw32860step1 i j = -(raw32860step0 i j); unfold raw32860step1 raw32860step0; decide +kernel
      have hl : raw32860step1Labels = raw32860step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32860step1 raw32860step1Labels = mixedMoment B raw32860step2 raw32860step2Labels := by
      have ha : raw32860step2 = raw32860step1 := by apply Matrix.ext; unfold raw32860step2 raw32860step1; decide +kernel
      have hl : raw32860step1Labels = labelEmbedding1 ∘ raw32860step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32860step1 raw32860step1Labels raw32860step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3844 node3844Labels := by rfl

def raw32861 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 0, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32861Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32861step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32861step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32861step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32861step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32861step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw32861step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32861step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw32861step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32861 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32861 raw32861Labels = mixedMoment B node3299 node3299Labels := by
  calc
    mixedMoment B raw32861 raw32861Labels = mixedMoment B raw32861step0 raw32861step0Labels := by
      have hz : ∀ j, raw32861 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw32861step0 = (fun i j => raw32861 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw32861step0 raw32861; decide +kernel
      have hl : raw32861step0Labels = raw32861Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32861 raw32861Labels permutation265 hz
    mixedMoment B raw32861step0 raw32861step0Labels = mixedMoment B raw32861step1 raw32861step1Labels := by
      have ha : raw32861step1 = (fun i j => raw32861step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32861step1 raw32861step0; decide +kernel
      have hl : raw32861step1Labels = raw32861step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32861step0 raw32861step0Labels permutation32 permutation7
    mixedMoment B raw32861step1 raw32861step1Labels = mixedMoment B raw32861step2 raw32861step2Labels := by
      have ha : raw32861step2 = -raw32861step1 := by apply Matrix.ext; change ∀ i j, raw32861step2 i j = -(raw32861step1 i j); unfold raw32861step2 raw32861step1; decide +kernel
      have hl : raw32861step2Labels = raw32861step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32861step2 raw32861step2Labels = mixedMoment B raw32861step3 raw32861step3Labels := by
      have ha : raw32861step3 = raw32861step2 := by apply Matrix.ext; unfold raw32861step3 raw32861step2; decide +kernel
      have hl : raw32861step2Labels = labelEmbedding1 ∘ raw32861step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32861step2 raw32861step2Labels raw32861step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3299 node3299Labels := by rfl

def raw32862 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32862Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32862step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32862step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32862step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw32862step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32862step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw32862step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32862 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32862 raw32862Labels = mixedMoment B node3554 node3554Labels := by
  calc
    mixedMoment B raw32862 raw32862Labels = mixedMoment B raw32862step0 raw32862step0Labels := by
      have ha : raw32862step0 = (fun i j => raw32862 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32862step0 raw32862; decide +kernel
      have hl : raw32862step0Labels = raw32862Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32862 raw32862Labels permutation176 permutation7
    mixedMoment B raw32862step0 raw32862step0Labels = mixedMoment B raw32862step1 raw32862step1Labels := by
      have ha : raw32862step1 = -raw32862step0 := by apply Matrix.ext; change ∀ i j, raw32862step1 i j = -(raw32862step0 i j); unfold raw32862step1 raw32862step0; decide +kernel
      have hl : raw32862step1Labels = raw32862step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32862step1 raw32862step1Labels = mixedMoment B raw32862step2 raw32862step2Labels := by
      have ha : raw32862step2 = raw32862step1 := by apply Matrix.ext; unfold raw32862step2 raw32862step1; decide +kernel
      have hl : raw32862step1Labels = labelEmbedding1 ∘ raw32862step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32862step1 raw32862step1Labels raw32862step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3554 node3554Labels := by rfl

def raw32863 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32863Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32863step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw32863step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32863step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32863step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32863step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32863step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32863 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32863 raw32863Labels = mixedMoment B node3562 node3562Labels := by
  calc
    mixedMoment B raw32863 raw32863Labels = mixedMoment B raw32863step0 raw32863step0Labels := by
      have ha : raw32863step0 = (fun i j => raw32863 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32863step0 raw32863; decide +kernel
      have hl : raw32863step0Labels = raw32863Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32863 raw32863Labels permutation176 permutation7
    mixedMoment B raw32863step0 raw32863step0Labels = mixedMoment B raw32863step1 raw32863step1Labels := by
      have ha : raw32863step1 = -raw32863step0 := by apply Matrix.ext; change ∀ i j, raw32863step1 i j = -(raw32863step0 i j); unfold raw32863step1 raw32863step0; decide +kernel
      have hl : raw32863step1Labels = raw32863step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32863step1 raw32863step1Labels = mixedMoment B raw32863step2 raw32863step2Labels := by
      have ha : raw32863step2 = raw32863step1 := by apply Matrix.ext; unfold raw32863step2 raw32863step1; decide +kernel
      have hl : raw32863step1Labels = labelEmbedding1 ∘ raw32863step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32863step1 raw32863step1Labels raw32863step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3562 node3562Labels := by rfl

def raw32864 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw32864Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32864step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, -1, 2]]
def raw32864step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32864step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32864step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32864step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw32864step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32864 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32864 raw32864Labels = mixedMoment B node3562 node3562Labels := by
  calc
    mixedMoment B raw32864 raw32864Labels = mixedMoment B raw32864step0 raw32864step0Labels := by
      have ha : raw32864step0 = (fun i j => raw32864 (permutation178 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32864step0 raw32864; decide +kernel
      have hl : raw32864step0Labels = raw32864Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32864 raw32864Labels permutation178 permutation7
    mixedMoment B raw32864step0 raw32864step0Labels = mixedMoment B raw32864step1 raw32864step1Labels := by
      have ha : raw32864step1 = -raw32864step0 := by apply Matrix.ext; change ∀ i j, raw32864step1 i j = -(raw32864step0 i j); unfold raw32864step1 raw32864step0; decide +kernel
      have hl : raw32864step1Labels = raw32864step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32864step1 raw32864step1Labels = mixedMoment B raw32864step2 raw32864step2Labels := by
      have ha : raw32864step2 = raw32864step1 := by apply Matrix.ext; unfold raw32864step2 raw32864step1; decide +kernel
      have hl : raw32864step1Labels = labelEmbedding1 ∘ raw32864step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32864step1 raw32864step1Labels raw32864step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3562 node3562Labels := by rfl

def raw32865 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32865Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32865step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw32865step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32865step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32865step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32865step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32865step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32865 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32865 raw32865Labels = mixedMoment B node3563 node3563Labels := by
  calc
    mixedMoment B raw32865 raw32865Labels = mixedMoment B raw32865step0 raw32865step0Labels := by
      have ha : raw32865step0 = (fun i j => raw32865 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32865step0 raw32865; decide +kernel
      have hl : raw32865step0Labels = raw32865Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32865 raw32865Labels permutation176 permutation7
    mixedMoment B raw32865step0 raw32865step0Labels = mixedMoment B raw32865step1 raw32865step1Labels := by
      have ha : raw32865step1 = -raw32865step0 := by apply Matrix.ext; change ∀ i j, raw32865step1 i j = -(raw32865step0 i j); unfold raw32865step1 raw32865step0; decide +kernel
      have hl : raw32865step1Labels = raw32865step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32865step1 raw32865step1Labels = mixedMoment B raw32865step2 raw32865step2Labels := by
      have ha : raw32865step2 = raw32865step1 := by apply Matrix.ext; unfold raw32865step2 raw32865step1; decide +kernel
      have hl : raw32865step1Labels = labelEmbedding1 ∘ raw32865step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32865step1 raw32865step1Labels raw32865step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3563 node3563Labels := by rfl

def raw32866 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32866Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32866step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw32866step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32866step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw32866step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32866step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw32866step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32866 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32866 raw32866Labels = mixedMoment B node3511 node3511Labels := by
  calc
    mixedMoment B raw32866 raw32866Labels = mixedMoment B raw32866step0 raw32866step0Labels := by
      have ha : raw32866step0 = (fun i j => raw32866 (permutation178 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32866step0 raw32866; decide +kernel
      have hl : raw32866step0Labels = raw32866Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32866 raw32866Labels permutation178 permutation7
    mixedMoment B raw32866step0 raw32866step0Labels = mixedMoment B raw32866step1 raw32866step1Labels := by
      have ha : raw32866step1 = -raw32866step0 := by apply Matrix.ext; change ∀ i j, raw32866step1 i j = -(raw32866step0 i j); unfold raw32866step1 raw32866step0; decide +kernel
      have hl : raw32866step1Labels = raw32866step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32866step1 raw32866step1Labels = mixedMoment B raw32866step2 raw32866step2Labels := by
      have ha : raw32866step2 = raw32866step1 := by apply Matrix.ext; unfold raw32866step2 raw32866step1; decide +kernel
      have hl : raw32866step1Labels = labelEmbedding1 ∘ raw32866step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32866step1 raw32866step1Labels raw32866step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3511 node3511Labels := by rfl

def raw32867 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32867Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32867step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw32867step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32867step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw32867step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32867step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw32867step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32867 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32867 raw32867Labels = mixedMoment B node3456 node3456Labels := by
  calc
    mixedMoment B raw32867 raw32867Labels = mixedMoment B raw32867step0 raw32867step0Labels := by
      have ha : raw32867step0 = (fun i j => raw32867 (permutation178 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32867step0 raw32867; decide +kernel
      have hl : raw32867step0Labels = raw32867Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32867 raw32867Labels permutation178 permutation7
    mixedMoment B raw32867step0 raw32867step0Labels = mixedMoment B raw32867step1 raw32867step1Labels := by
      have ha : raw32867step1 = -raw32867step0 := by apply Matrix.ext; change ∀ i j, raw32867step1 i j = -(raw32867step0 i j); unfold raw32867step1 raw32867step0; decide +kernel
      have hl : raw32867step1Labels = raw32867step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32867step1 raw32867step1Labels = mixedMoment B raw32867step2 raw32867step2Labels := by
      have ha : raw32867step2 = raw32867step1 := by apply Matrix.ext; unfold raw32867step2 raw32867step1; decide +kernel
      have hl : raw32867step1Labels = labelEmbedding1 ∘ raw32867step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32867step1 raw32867step1Labels raw32867step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3456 node3456Labels := by rfl

def raw32868 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![0, 1, -1], ![2, -1, -1]]
def raw32868Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32868step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw32868step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32868step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw32868step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32868step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw32868step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32868 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32868 raw32868Labels = mixedMoment B node3520 node3520Labels := by
  calc
    mixedMoment B raw32868 raw32868Labels = mixedMoment B raw32868step0 raw32868step0Labels := by
      have ha : raw32868step0 = (fun i j => raw32868 (permutation178 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32868step0 raw32868; decide +kernel
      have hl : raw32868step0Labels = raw32868Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32868 raw32868Labels permutation178 permutation7
    mixedMoment B raw32868step0 raw32868step0Labels = mixedMoment B raw32868step1 raw32868step1Labels := by
      have ha : raw32868step1 = -raw32868step0 := by apply Matrix.ext; change ∀ i j, raw32868step1 i j = -(raw32868step0 i j); unfold raw32868step1 raw32868step0; decide +kernel
      have hl : raw32868step1Labels = raw32868step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32868step1 raw32868step1Labels = mixedMoment B raw32868step2 raw32868step2Labels := by
      have ha : raw32868step2 = raw32868step1 := by apply Matrix.ext; unfold raw32868step2 raw32868step1; decide +kernel
      have hl : raw32868step1Labels = labelEmbedding1 ∘ raw32868step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32868step1 raw32868step1Labels raw32868step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3520 node3520Labels := by rfl

def raw32869 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw32869Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32869step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32869step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32869step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw32869step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32869step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw32869step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32869 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32869 raw32869Labels = mixedMoment B node3521 node3521Labels := by
  calc
    mixedMoment B raw32869 raw32869Labels = mixedMoment B raw32869step0 raw32869step0Labels := by
      have ha : raw32869step0 = (fun i j => raw32869 (permutation179 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32869step0 raw32869; decide +kernel
      have hl : raw32869step0Labels = raw32869Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32869 raw32869Labels permutation179 permutation7
    mixedMoment B raw32869step0 raw32869step0Labels = mixedMoment B raw32869step1 raw32869step1Labels := by
      have ha : raw32869step1 = -raw32869step0 := by apply Matrix.ext; change ∀ i j, raw32869step1 i j = -(raw32869step0 i j); unfold raw32869step1 raw32869step0; decide +kernel
      have hl : raw32869step1Labels = raw32869step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32869step1 raw32869step1Labels = mixedMoment B raw32869step2 raw32869step2Labels := by
      have ha : raw32869step2 = raw32869step1 := by apply Matrix.ext; unfold raw32869step2 raw32869step1; decide +kernel
      have hl : raw32869step1Labels = labelEmbedding1 ∘ raw32869step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32869step1 raw32869step1Labels raw32869step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3521 node3521Labels := by rfl

def raw32870 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32870Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32870step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw32870step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32870step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw32870step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32870step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw32870step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32870 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32870 raw32870Labels = mixedMoment B node3511 node3511Labels := by
  calc
    mixedMoment B raw32870 raw32870Labels = mixedMoment B raw32870step0 raw32870step0Labels := by
      have ha : raw32870step0 = (fun i j => raw32870 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32870step0 raw32870; decide +kernel
      have hl : raw32870step0Labels = raw32870Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32870 raw32870Labels permutation176 permutation7
    mixedMoment B raw32870step0 raw32870step0Labels = mixedMoment B raw32870step1 raw32870step1Labels := by
      have ha : raw32870step1 = -raw32870step0 := by apply Matrix.ext; change ∀ i j, raw32870step1 i j = -(raw32870step0 i j); unfold raw32870step1 raw32870step0; decide +kernel
      have hl : raw32870step1Labels = raw32870step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32870step1 raw32870step1Labels = mixedMoment B raw32870step2 raw32870step2Labels := by
      have ha : raw32870step2 = raw32870step1 := by apply Matrix.ext; unfold raw32870step2 raw32870step1; decide +kernel
      have hl : raw32870step1Labels = labelEmbedding1 ∘ raw32870step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32870step1 raw32870step1Labels raw32870step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3511 node3511Labels := by rfl

def raw32871 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32871Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32871step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, -1, 2], ![-1, -1, 2]]
def raw32871step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32871step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw32871step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32871step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![1, 1, -2]]
def raw32871step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32871 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32871 raw32871Labels = mixedMoment B node3456 node3456Labels := by
  calc
    mixedMoment B raw32871 raw32871Labels = mixedMoment B raw32871step0 raw32871step0Labels := by
      have ha : raw32871step0 = (fun i j => raw32871 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32871step0 raw32871; decide +kernel
      have hl : raw32871step0Labels = raw32871Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32871 raw32871Labels permutation176 permutation7
    mixedMoment B raw32871step0 raw32871step0Labels = mixedMoment B raw32871step1 raw32871step1Labels := by
      have ha : raw32871step1 = -raw32871step0 := by apply Matrix.ext; change ∀ i j, raw32871step1 i j = -(raw32871step0 i j); unfold raw32871step1 raw32871step0; decide +kernel
      have hl : raw32871step1Labels = raw32871step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32871step1 raw32871step1Labels = mixedMoment B raw32871step2 raw32871step2Labels := by
      have ha : raw32871step2 = raw32871step1 := by apply Matrix.ext; unfold raw32871step2 raw32871step1; decide +kernel
      have hl : raw32871step1Labels = labelEmbedding1 ∘ raw32871step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32871step1 raw32871step1Labels raw32871step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3456 node3456Labels := by rfl

def raw32872 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32872Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32872step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 1, 0], ![-1, -1, 2], ![-1, -1, 2]]
def raw32872step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32872step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw32872step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32872step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![1, 1, -2]]
def raw32872step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32872 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32872 raw32872Labels = mixedMoment B node3520 node3520Labels := by
  calc
    mixedMoment B raw32872 raw32872Labels = mixedMoment B raw32872step0 raw32872step0Labels := by
      have ha : raw32872step0 = (fun i j => raw32872 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32872step0 raw32872; decide +kernel
      have hl : raw32872step0Labels = raw32872Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32872 raw32872Labels permutation176 permutation7
    mixedMoment B raw32872step0 raw32872step0Labels = mixedMoment B raw32872step1 raw32872step1Labels := by
      have ha : raw32872step1 = -raw32872step0 := by apply Matrix.ext; change ∀ i j, raw32872step1 i j = -(raw32872step0 i j); unfold raw32872step1 raw32872step0; decide +kernel
      have hl : raw32872step1Labels = raw32872step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32872step1 raw32872step1Labels = mixedMoment B raw32872step2 raw32872step2Labels := by
      have ha : raw32872step2 = raw32872step1 := by apply Matrix.ext; unfold raw32872step2 raw32872step1; decide +kernel
      have hl : raw32872step1Labels = labelEmbedding1 ∘ raw32872step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32872step1 raw32872step1Labels raw32872step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3520 node3520Labels := by rfl

def raw32873 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw32873Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32873step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -1, 2]]
def raw32873step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32873step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw32873step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32873step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw32873step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32873 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32873 raw32873Labels = mixedMoment B node3521 node3521Labels := by
  calc
    mixedMoment B raw32873 raw32873Labels = mixedMoment B raw32873step0 raw32873step0Labels := by
      have ha : raw32873step0 = (fun i j => raw32873 (permutation177 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32873step0 raw32873; decide +kernel
      have hl : raw32873step0Labels = raw32873Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32873 raw32873Labels permutation177 permutation7
    mixedMoment B raw32873step0 raw32873step0Labels = mixedMoment B raw32873step1 raw32873step1Labels := by
      have ha : raw32873step1 = -raw32873step0 := by apply Matrix.ext; change ∀ i j, raw32873step1 i j = -(raw32873step0 i j); unfold raw32873step1 raw32873step0; decide +kernel
      have hl : raw32873step1Labels = raw32873step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32873step1 raw32873step1Labels = mixedMoment B raw32873step2 raw32873step2Labels := by
      have ha : raw32873step2 = raw32873step1 := by apply Matrix.ext; unfold raw32873step2 raw32873step1; decide +kernel
      have hl : raw32873step1Labels = labelEmbedding1 ∘ raw32873step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32873step1 raw32873step1Labels raw32873step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3521 node3521Labels := by rfl

def raw32874 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32874Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32874step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, 2, -2], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw32874step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32874step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw32874step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32874step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw32874step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32874 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32874 raw32874Labels = mixedMoment B node3510 node3510Labels := by
  calc
    mixedMoment B raw32874 raw32874Labels = mixedMoment B raw32874step0 raw32874step0Labels := by
      have ha : raw32874step0 = (fun i j => raw32874 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32874step0 raw32874; decide +kernel
      have hl : raw32874step0Labels = raw32874Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32874 raw32874Labels permutation176 permutation7
    mixedMoment B raw32874step0 raw32874step0Labels = mixedMoment B raw32874step1 raw32874step1Labels := by
      have ha : raw32874step1 = -raw32874step0 := by apply Matrix.ext; change ∀ i j, raw32874step1 i j = -(raw32874step0 i j); unfold raw32874step1 raw32874step0; decide +kernel
      have hl : raw32874step1Labels = raw32874step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32874step1 raw32874step1Labels = mixedMoment B raw32874step2 raw32874step2Labels := by
      have ha : raw32874step2 = raw32874step1 := by apply Matrix.ext; unfold raw32874step2 raw32874step1; decide +kernel
      have hl : raw32874step1Labels = labelEmbedding1 ∘ raw32874step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32874step1 raw32874step1Labels raw32874step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3510 node3510Labels := by rfl

def raw32875 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![-1, 0, 1], ![1, 0, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32875Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32875step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, 0, -1], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, -2, 3]]
def raw32875step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32875step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw32875step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32875step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 0, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 2, -3]]
def raw32875step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32875 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32875 raw32875Labels = mixedMoment B node3455 node3455Labels := by
  calc
    mixedMoment B raw32875 raw32875Labels = mixedMoment B raw32875step0 raw32875step0Labels := by
      have ha : raw32875step0 = (fun i j => raw32875 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw32875step0 raw32875; decide +kernel
      have hl : raw32875step0Labels = raw32875Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32875 raw32875Labels permutation176 permutation7
    mixedMoment B raw32875step0 raw32875step0Labels = mixedMoment B raw32875step1 raw32875step1Labels := by
      have ha : raw32875step1 = -raw32875step0 := by apply Matrix.ext; change ∀ i j, raw32875step1 i j = -(raw32875step0 i j); unfold raw32875step1 raw32875step0; decide +kernel
      have hl : raw32875step1Labels = raw32875step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw32875step1 raw32875step1Labels = mixedMoment B raw32875step2 raw32875step2Labels := by
      have ha : raw32875step2 = raw32875step1 := by apply Matrix.ext; unfold raw32875step2 raw32875step1; decide +kernel
      have hl : raw32875step1Labels = labelEmbedding1 ∘ raw32875step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32875step1 raw32875step1Labels raw32875step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3455 node3455Labels := by rfl

def raw32876 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw32876Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32876step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw32876step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32876step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw32876step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32876 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32876 raw32876Labels = mixedMoment B node3519 node3519Labels := by
  calc
    mixedMoment B raw32876 raw32876Labels = mixedMoment B raw32876step0 raw32876step0Labels := by
      have ha : raw32876step0 = (fun i j => raw32876 (permutation646 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32876step0 raw32876; decide +kernel
      have hl : raw32876step0Labels = raw32876Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32876 raw32876Labels permutation646 permutation5
    mixedMoment B raw32876step0 raw32876step0Labels = mixedMoment B raw32876step1 raw32876step1Labels := by
      have ha : raw32876step1 = raw32876step0 := by apply Matrix.ext; unfold raw32876step1 raw32876step0; decide +kernel
      have hl : raw32876step0Labels = labelEmbedding1 ∘ raw32876step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32876step0 raw32876step0Labels raw32876step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3519 node3519Labels := by rfl

def raw32877 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![0, 1, -1], ![3, -2, -1]]
def raw32877Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw32877step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw32877step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw32877step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw32877step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32877 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32877 raw32877Labels = mixedMoment B node3519 node3519Labels := by
  calc
    mixedMoment B raw32877 raw32877Labels = mixedMoment B raw32877step0 raw32877step0Labels := by
      have ha : raw32877step0 = (fun i j => raw32877 (permutation640 i) (permutation5 j)) := by apply Matrix.ext; unfold raw32877step0 raw32877; decide +kernel
      have hl : raw32877step0Labels = raw32877Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32877 raw32877Labels permutation640 permutation5
    mixedMoment B raw32877step0 raw32877step0Labels = mixedMoment B raw32877step1 raw32877step1Labels := by
      have ha : raw32877step1 = raw32877step0 := by apply Matrix.ext; unfold raw32877step1 raw32877step0; decide +kernel
      have hl : raw32877step0Labels = labelEmbedding1 ∘ raw32877step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32877step0 raw32877step0Labels raw32877step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3519 node3519Labels := by rfl

def raw32878 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32878Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32878 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32878 raw32878Labels = mixedMoment B node3721 node3721Labels := by
  calc
    _ = mixedMoment B node3721 node3721Labels := by rfl

def raw32879 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32879Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32879 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32879 raw32879Labels = mixedMoment B node2354 node2354Labels := by
  calc
    _ = mixedMoment B node2354 node2354Labels := by rfl

def raw32880 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![2, -1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32880Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw32880step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 2, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, -1, -1]]
def raw32880step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical32880 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32880 raw32880Labels = mixedMoment B node2351 node2351Labels := by
  calc
    mixedMoment B raw32880 raw32880Labels = mixedMoment B raw32880step0 raw32880step0Labels := by
      have ha : raw32880step0 = (fun i j => raw32880 (permutation154 i) (permutation2 j)) := by apply Matrix.ext; unfold raw32880step0 raw32880; decide +kernel
      have hl : raw32880step0Labels = raw32880Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32880 raw32880Labels permutation154 permutation2
    _ = mixedMoment B node2351 node2351Labels := by rfl

def raw32881 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32881Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32881step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32881step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32881step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32881step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32881 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32881 raw32881Labels = mixedMoment B node4344 node4344Labels := by
  calc
    mixedMoment B raw32881 raw32881Labels = mixedMoment B raw32881step0 raw32881step0Labels := by
      have ha : raw32881step0 = (fun i j => raw32881 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32881step0 raw32881; decide +kernel
      have hl : raw32881step0Labels = raw32881Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32881 raw32881Labels permutation152 permutation3
    mixedMoment B raw32881step0 raw32881step0Labels = mixedMoment B raw32881step1 raw32881step1Labels := by
      have ha : raw32881step1 = raw32881step0 := by apply Matrix.ext; unfold raw32881step1 raw32881step0; decide +kernel
      have hl : raw32881step0Labels = labelEmbedding6 ∘ raw32881step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32881step0 raw32881step0Labels raw32881step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4344 node4344Labels := by rfl

def raw32882 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![1, 0, -1], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32882Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32882step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32882step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32882step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw32882step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32882 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32882 raw32882Labels = mixedMoment B node4941 node4941Labels := by
  calc
    mixedMoment B raw32882 raw32882Labels = mixedMoment B raw32882step0 raw32882step0Labels := by
      have ha : raw32882step0 = (fun i j => raw32882 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32882step0 raw32882; decide +kernel
      have hl : raw32882step0Labels = raw32882Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32882 raw32882Labels permutation152 permutation3
    mixedMoment B raw32882step0 raw32882step0Labels = mixedMoment B raw32882step1 raw32882step1Labels := by
      have ha : raw32882step1 = raw32882step0 := by apply Matrix.ext; unfold raw32882step1 raw32882step0; decide +kernel
      have hl : raw32882step0Labels = labelEmbedding6 ∘ raw32882step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32882step0 raw32882step0Labels raw32882step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4941 node4941Labels := by rfl

def raw32883 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![0, 0, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32883Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32883step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32883step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32883step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32883step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32883step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32883step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32883 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32883 raw32883Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw32883 raw32883Labels = mixedMoment B raw32883step0 raw32883step0Labels := by
      have hz : ∀ j, raw32883 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw32883step0 = (fun i j => raw32883 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw32883step0 raw32883; decide +kernel
      have hl : raw32883step0Labels = raw32883Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32883 raw32883Labels permutation434 hz
    mixedMoment B raw32883step0 raw32883step0Labels = mixedMoment B raw32883step1 raw32883step1Labels := by
      have ha : raw32883step1 = (fun i j => raw32883step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32883step1 raw32883step0; decide +kernel
      have hl : raw32883step1Labels = raw32883step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32883step0 raw32883step0Labels permutation32 permutation3
    mixedMoment B raw32883step1 raw32883step1Labels = mixedMoment B raw32883step2 raw32883step2Labels := by
      have ha : raw32883step2 = raw32883step1 := by apply Matrix.ext; unfold raw32883step2 raw32883step1; decide +kernel
      have hl : raw32883step1Labels = labelEmbedding6 ∘ raw32883step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32883step1 raw32883step1Labels raw32883step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5169 node5169Labels := by rfl

def raw32884 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![0, 0, 0], ![2, -1, -1]]
def raw32884Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32884step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![1, 0, -1], ![1, -1, 0], ![2, -1, -1]]
def raw32884step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32884step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32884step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32884step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw32884step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32884 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32884 raw32884Labels = mixedMoment B node5169 node5169Labels := by
  calc
    mixedMoment B raw32884 raw32884Labels = mixedMoment B raw32884step0 raw32884step0Labels := by
      have hz : ∀ j, raw32884 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32884step0 = (fun i j => raw32884 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32884step0 raw32884; decide +kernel
      have hl : raw32884step0Labels = raw32884Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32884 raw32884Labels permutation520 hz
    mixedMoment B raw32884step0 raw32884step0Labels = mixedMoment B raw32884step1 raw32884step1Labels := by
      have ha : raw32884step1 = (fun i j => raw32884step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32884step1 raw32884step0; decide +kernel
      have hl : raw32884step1Labels = raw32884step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32884step0 raw32884step0Labels permutation32 permutation3
    mixedMoment B raw32884step1 raw32884step1Labels = mixedMoment B raw32884step2 raw32884step2Labels := by
      have ha : raw32884step2 = raw32884step1 := by apply Matrix.ext; unfold raw32884step2 raw32884step1; decide +kernel
      have hl : raw32884step1Labels = labelEmbedding6 ∘ raw32884step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32884step1 raw32884step1Labels raw32884step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5169 node5169Labels := by rfl

def raw32885 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32885Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32885step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32885step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32885step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32885step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32885 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32885 raw32885Labels = mixedMoment B node4323 node4323Labels := by
  calc
    mixedMoment B raw32885 raw32885Labels = mixedMoment B raw32885step0 raw32885step0Labels := by
      have ha : raw32885step0 = (fun i j => raw32885 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32885step0 raw32885; decide +kernel
      have hl : raw32885step0Labels = raw32885Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32885 raw32885Labels permutation155 permutation3
    mixedMoment B raw32885step0 raw32885step0Labels = mixedMoment B raw32885step1 raw32885step1Labels := by
      have ha : raw32885step1 = raw32885step0 := by apply Matrix.ext; unfold raw32885step1 raw32885step0; decide +kernel
      have hl : raw32885step0Labels = labelEmbedding6 ∘ raw32885step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32885step0 raw32885step0Labels raw32885step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4323 node4323Labels := by rfl

def raw32886 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 1, -1], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32886Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32886step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32886step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32886step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32886step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32886 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32886 raw32886Labels = mixedMoment B node4928 node4928Labels := by
  calc
    mixedMoment B raw32886 raw32886Labels = mixedMoment B raw32886step0 raw32886step0Labels := by
      have ha : raw32886step0 = (fun i j => raw32886 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32886step0 raw32886; decide +kernel
      have hl : raw32886step0Labels = raw32886Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32886 raw32886Labels permutation155 permutation3
    mixedMoment B raw32886step0 raw32886step0Labels = mixedMoment B raw32886step1 raw32886step1Labels := by
      have ha : raw32886step1 = raw32886step0 := by apply Matrix.ext; unfold raw32886step1 raw32886step0; decide +kernel
      have hl : raw32886step0Labels = labelEmbedding6 ∘ raw32886step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32886step0 raw32886step0Labels raw32886step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4928 node4928Labels := by rfl

def raw32887 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 2, -1], ![2, -2, 0], ![1, -1, 0], ![2, -1, -1]]
def raw32887Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32887step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32887step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32887step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32887step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32887 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32887 raw32887Labels = mixedMoment B node4987 node4987Labels := by
  calc
    mixedMoment B raw32887 raw32887Labels = mixedMoment B raw32887step0 raw32887step0Labels := by
      have ha : raw32887step0 = (fun i j => raw32887 (permutation179 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32887step0 raw32887; decide +kernel
      have hl : raw32887step0Labels = raw32887Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32887 raw32887Labels permutation179 permutation3
    mixedMoment B raw32887step0 raw32887step0Labels = mixedMoment B raw32887step1 raw32887step1Labels := by
      have ha : raw32887step1 = raw32887step0 := by apply Matrix.ext; unfold raw32887step1 raw32887step0; decide +kernel
      have hl : raw32887step0Labels = labelEmbedding6 ∘ raw32887step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32887step0 raw32887step0Labels raw32887step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4987 node4987Labels := by rfl

def raw32888 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![0, 0, 0], ![2, -1, -1]]
def raw32888Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32888step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32888step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32888step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw32888step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32888step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw32888step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32888 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32888 raw32888Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw32888 raw32888Labels = mixedMoment B raw32888step0 raw32888step0Labels := by
      have hz : ∀ j, raw32888 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw32888step0 = (fun i j => raw32888 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw32888step0 raw32888; decide +kernel
      have hl : raw32888step0Labels = raw32888Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32888 raw32888Labels permutation520 hz
    mixedMoment B raw32888step0 raw32888step0Labels = mixedMoment B raw32888step1 raw32888step1Labels := by
      have ha : raw32888step1 = (fun i j => raw32888step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32888step1 raw32888step0; decide +kernel
      have hl : raw32888step1Labels = raw32888step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32888step0 raw32888step0Labels permutation33 permutation3
    mixedMoment B raw32888step1 raw32888step1Labels = mixedMoment B raw32888step2 raw32888step2Labels := by
      have ha : raw32888step2 = raw32888step1 := by apply Matrix.ext; unfold raw32888step2 raw32888step1; decide +kernel
      have hl : raw32888step1Labels = labelEmbedding6 ∘ raw32888step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32888step1 raw32888step1Labels raw32888step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5141 node5141Labels := by rfl

def raw32889 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw32889Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32889step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32889step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32889step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32889step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32889 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32889 raw32889Labels = mixedMoment B node4323 node4323Labels := by
  calc
    mixedMoment B raw32889 raw32889Labels = mixedMoment B raw32889step0 raw32889step0Labels := by
      have ha : raw32889step0 = (fun i j => raw32889 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32889step0 raw32889; decide +kernel
      have hl : raw32889step0Labels = raw32889Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32889 raw32889Labels permutation153 permutation3
    mixedMoment B raw32889step0 raw32889step0Labels = mixedMoment B raw32889step1 raw32889step1Labels := by
      have ha : raw32889step1 = raw32889step0 := by apply Matrix.ext; unfold raw32889step1 raw32889step0; decide +kernel
      have hl : raw32889step0Labels = labelEmbedding6 ∘ raw32889step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32889step0 raw32889step0Labels raw32889step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4323 node4323Labels := by rfl

def raw32890 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw32890Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32890step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32890step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32890step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32890step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32890 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32890 raw32890Labels = mixedMoment B node4928 node4928Labels := by
  calc
    mixedMoment B raw32890 raw32890Labels = mixedMoment B raw32890step0 raw32890step0Labels := by
      have ha : raw32890step0 = (fun i j => raw32890 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32890step0 raw32890; decide +kernel
      have hl : raw32890step0Labels = raw32890Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32890 raw32890Labels permutation153 permutation3
    mixedMoment B raw32890step0 raw32890step0Labels = mixedMoment B raw32890step1 raw32890step1Labels := by
      have ha : raw32890step1 = raw32890step0 := by apply Matrix.ext; unfold raw32890step1 raw32890step0; decide +kernel
      have hl : raw32890step0Labels = labelEmbedding6 ∘ raw32890step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32890step0 raw32890step0Labels raw32890step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4928 node4928Labels := by rfl

def raw32891 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![2, -2, 0], ![2, -1, -1]]
def raw32891Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32891step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32891step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32891step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![2, -1, -1], ![2, 0, -2]]
def raw32891step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32891 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32891 raw32891Labels = mixedMoment B node4987 node4987Labels := by
  calc
    mixedMoment B raw32891 raw32891Labels = mixedMoment B raw32891step0 raw32891step0Labels := by
      have ha : raw32891step0 = (fun i j => raw32891 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32891step0 raw32891; decide +kernel
      have hl : raw32891step0Labels = raw32891Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32891 raw32891Labels permutation177 permutation3
    mixedMoment B raw32891step0 raw32891step0Labels = mixedMoment B raw32891step1 raw32891step1Labels := by
      have ha : raw32891step1 = raw32891step0 := by apply Matrix.ext; unfold raw32891step1 raw32891step0; decide +kernel
      have hl : raw32891step0Labels = labelEmbedding6 ∘ raw32891step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32891step0 raw32891step0Labels raw32891step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4987 node4987Labels := by rfl

def raw32892 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![0, 0, 0], ![2, -2, 0], ![2, -1, -1]]
def raw32892Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32892step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, 1, -1], ![2, -2, 0], ![2, -1, -1]]
def raw32892step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32892step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw32892step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32892step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, -1, 1], ![2, -1, -1], ![2, 0, -2]]
def raw32892step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32892 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32892 raw32892Labels = mixedMoment B node5141 node5141Labels := by
  calc
    mixedMoment B raw32892 raw32892Labels = mixedMoment B raw32892step0 raw32892step0Labels := by
      have hz : ∀ j, raw32892 (permutation434 0) j = 0 := by decide +kernel
      have ha : raw32892step0 = (fun i j => raw32892 (permutation434 i.succ) j) := by apply Matrix.ext; unfold raw32892step0 raw32892; decide +kernel
      have hl : raw32892step0Labels = raw32892Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw32892 raw32892Labels permutation434 hz
    mixedMoment B raw32892step0 raw32892step0Labels = mixedMoment B raw32892step1 raw32892step1Labels := by
      have ha : raw32892step1 = (fun i j => raw32892step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32892step1 raw32892step0; decide +kernel
      have hl : raw32892step1Labels = raw32892step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32892step0 raw32892step0Labels permutation33 permutation3
    mixedMoment B raw32892step1 raw32892step1Labels = mixedMoment B raw32892step2 raw32892step2Labels := by
      have ha : raw32892step2 = raw32892step1 := by apply Matrix.ext; unfold raw32892step2 raw32892step1; decide +kernel
      have hl : raw32892step1Labels = labelEmbedding6 ∘ raw32892step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32892step1 raw32892step1Labels raw32892step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5141 node5141Labels := by rfl

def raw32893 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![-1, 0, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw32893Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32893step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw32893step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32893step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![-1, 1, 0], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw32893step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32893 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32893 raw32893Labels = mixedMoment B node4322 node4322Labels := by
  calc
    mixedMoment B raw32893 raw32893Labels = mixedMoment B raw32893step0 raw32893step0Labels := by
      have ha : raw32893step0 = (fun i j => raw32893 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32893step0 raw32893; decide +kernel
      have hl : raw32893step0Labels = raw32893Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32893 raw32893Labels permutation152 permutation3
    mixedMoment B raw32893step0 raw32893step0Labels = mixedMoment B raw32893step1 raw32893step1Labels := by
      have ha : raw32893step1 = raw32893step0 := by apply Matrix.ext; unfold raw32893step1 raw32893step0; decide +kernel
      have hl : raw32893step0Labels = labelEmbedding6 ∘ raw32893step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32893step0 raw32893step0Labels raw32893step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4322 node4322Labels := by rfl

def raw32894 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-2, 1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw32894Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32894step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw32894step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32894step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-2, 1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw32894step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32894 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32894 raw32894Labels = mixedMoment B node4927 node4927Labels := by
  calc
    mixedMoment B raw32894 raw32894Labels = mixedMoment B raw32894step0 raw32894step0Labels := by
      have ha : raw32894step0 = (fun i j => raw32894 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32894step0 raw32894; decide +kernel
      have hl : raw32894step0Labels = raw32894Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32894 raw32894Labels permutation152 permutation3
    mixedMoment B raw32894step0 raw32894step0Labels = mixedMoment B raw32894step1 raw32894step1Labels := by
      have ha : raw32894step1 = raw32894step0 := by apply Matrix.ext; unfold raw32894step1 raw32894step0; decide +kernel
      have hl : raw32894step0Labels = labelEmbedding6 ∘ raw32894step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32894step0 raw32894step0Labels raw32894step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4927 node4927Labels := by rfl

def raw32895 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![3, -2, -1]]
def raw32895Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw32895step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw32895step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw32895step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![-1, 1, 0], ![1, 0, -1], ![1, 0, -1], ![3, -1, -2]]
def raw32895step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical32895 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw32895 raw32895Labels = mixedMoment B node4986 node4986Labels := by
  calc
    mixedMoment B raw32895 raw32895Labels = mixedMoment B raw32895step0 raw32895step0Labels := by
      have ha : raw32895step0 = (fun i j => raw32895 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw32895step0 raw32895; decide +kernel
      have hl : raw32895step0Labels = raw32895Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw32895 raw32895Labels permutation176 permutation3
    mixedMoment B raw32895step0 raw32895step0Labels = mixedMoment B raw32895step1 raw32895step1Labels := by
      have ha : raw32895step1 = raw32895step0 := by apply Matrix.ext; unfold raw32895step1 raw32895step0; decide +kernel
      have hl : raw32895step0Labels = labelEmbedding6 ∘ raw32895step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw32895step0 raw32895step0Labels raw32895step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4986 node4986Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
