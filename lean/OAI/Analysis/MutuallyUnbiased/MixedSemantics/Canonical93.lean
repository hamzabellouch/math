import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes15
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes16
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes21
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes22
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes24
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes25
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes26
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes33
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes37
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes40
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes43
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes45
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes52
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes54
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes56
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes68
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes74
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes75
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes78
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw11904 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw11904Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11904step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11904step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11904step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11904step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11904 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11904 raw11904Labels = mixedMoment B node5185 node5185Labels := by
  calc
    mixedMoment B raw11904 raw11904Labels = mixedMoment B raw11904step0 raw11904step0Labels := by
      have ha : raw11904step0 = (fun i j => raw11904 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11904step0 raw11904; decide +kernel
      have hl : raw11904step0Labels = raw11904Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11904 raw11904Labels permutation177 permutation3
    mixedMoment B raw11904step0 raw11904step0Labels = mixedMoment B raw11904step1 raw11904step1Labels := by
      have ha : raw11904step1 = raw11904step0 := by apply Matrix.ext; unfold raw11904step1 raw11904step0; decide +kernel
      have hl : raw11904step0Labels = labelEmbedding6 ∘ raw11904step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11904step0 raw11904step0Labels raw11904step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5185 node5185Labels := by rfl

def raw11905 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw11905Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11905step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw11905step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11905step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw11905step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11905 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11905 raw11905Labels = mixedMoment B node5244 node5244Labels := by
  calc
    mixedMoment B raw11905 raw11905Labels = mixedMoment B raw11905step0 raw11905step0Labels := by
      have ha : raw11905step0 = (fun i j => raw11905 (permutation159 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11905step0 raw11905; decide +kernel
      have hl : raw11905step0Labels = raw11905Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11905 raw11905Labels permutation159 permutation3
    mixedMoment B raw11905step0 raw11905step0Labels = mixedMoment B raw11905step1 raw11905step1Labels := by
      have ha : raw11905step1 = raw11905step0 := by apply Matrix.ext; unfold raw11905step1 raw11905step0; decide +kernel
      have hl : raw11905step0Labels = labelEmbedding6 ∘ raw11905step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11905step0 raw11905step0Labels raw11905step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5244 node5244Labels := by rfl

def raw11906 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw11906Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11906step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw11906step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11906step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw11906step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11906step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw11906step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11906 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11906 raw11906Labels = mixedMoment B node5266 node5266Labels := by
  calc
    mixedMoment B raw11906 raw11906Labels = mixedMoment B raw11906step0 raw11906step0Labels := by
      have hz : ∀ j, raw11906 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw11906step0 = (fun i j => raw11906 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw11906step0 raw11906; decide +kernel
      have hl : raw11906step0Labels = raw11906Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11906 raw11906Labels permutation590 hz
    mixedMoment B raw11906step0 raw11906step0Labels = mixedMoment B raw11906step1 raw11906step1Labels := by
      have ha : raw11906step1 = (fun i j => raw11906step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11906step1 raw11906step0; decide +kernel
      have hl : raw11906step1Labels = raw11906step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11906step0 raw11906step0Labels permutation32 permutation3
    mixedMoment B raw11906step1 raw11906step1Labels = mixedMoment B raw11906step2 raw11906step2Labels := by
      have ha : raw11906step2 = raw11906step1 := by apply Matrix.ext; unfold raw11906step2 raw11906step1; decide +kernel
      have hl : raw11906step1Labels = labelEmbedding6 ∘ raw11906step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11906step1 raw11906step1Labels raw11906step2Labels labelEmbedding6 hl
    _ = mixedMoment B node5266 node5266Labels := by rfl

def raw11907 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11907Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11907step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11907step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11907step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11907step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11907 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11907 raw11907Labels = mixedMoment B node4406 node4406Labels := by
  calc
    mixedMoment B raw11907 raw11907Labels = mixedMoment B raw11907step0 raw11907step0Labels := by
      have ha : raw11907step0 = (fun i j => raw11907 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11907step0 raw11907; decide +kernel
      have hl : raw11907step0Labels = raw11907Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11907 raw11907Labels permutation152 permutation3
    mixedMoment B raw11907step0 raw11907step0Labels = mixedMoment B raw11907step1 raw11907step1Labels := by
      have ha : raw11907step1 = raw11907step0 := by apply Matrix.ext; unfold raw11907step1 raw11907step0; decide +kernel
      have hl : raw11907step0Labels = labelEmbedding6 ∘ raw11907step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11907step0 raw11907step0Labels raw11907step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4406 node4406Labels := by rfl

def raw11908 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11908Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11908step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11908step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11908step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11908step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11908 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11908 raw11908Labels = mixedMoment B node5004 node5004Labels := by
  calc
    mixedMoment B raw11908 raw11908Labels = mixedMoment B raw11908step0 raw11908step0Labels := by
      have ha : raw11908step0 = (fun i j => raw11908 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11908step0 raw11908; decide +kernel
      have hl : raw11908step0Labels = raw11908Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11908 raw11908Labels permutation152 permutation3
    mixedMoment B raw11908step0 raw11908step0Labels = mixedMoment B raw11908step1 raw11908step1Labels := by
      have ha : raw11908step1 = raw11908step0 := by apply Matrix.ext; unfold raw11908step1 raw11908step0; decide +kernel
      have hl : raw11908step0Labels = labelEmbedding6 ∘ raw11908step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11908step0 raw11908step0Labels raw11908step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5004 node5004Labels := by rfl

def raw11909 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11909Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11909step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11909step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11909step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11909step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11909 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11909 raw11909Labels = mixedMoment B node5184 node5184Labels := by
  calc
    mixedMoment B raw11909 raw11909Labels = mixedMoment B raw11909step0 raw11909step0Labels := by
      have ha : raw11909step0 = (fun i j => raw11909 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11909step0 raw11909; decide +kernel
      have hl : raw11909step0Labels = raw11909Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11909 raw11909Labels permutation176 permutation3
    mixedMoment B raw11909step0 raw11909step0Labels = mixedMoment B raw11909step1 raw11909step1Labels := by
      have ha : raw11909step1 = raw11909step0 := by apply Matrix.ext; unfold raw11909step1 raw11909step0; decide +kernel
      have hl : raw11909step0Labels = labelEmbedding6 ∘ raw11909step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11909step0 raw11909step0Labels raw11909step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5184 node5184Labels := by rfl

def raw11910 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11910Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11910step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw11910step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11910step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw11910step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11910 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11910 raw11910Labels = mixedMoment B node5243 node5243Labels := by
  calc
    mixedMoment B raw11910 raw11910Labels = mixedMoment B raw11910step0 raw11910step0Labels := by
      have ha : raw11910step0 = (fun i j => raw11910 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11910step0 raw11910; decide +kernel
      have hl : raw11910step0Labels = raw11910Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11910 raw11910Labels permutation158 permutation3
    mixedMoment B raw11910step0 raw11910step0Labels = mixedMoment B raw11910step1 raw11910step1Labels := by
      have ha : raw11910step1 = raw11910step0 := by apply Matrix.ext; unfold raw11910step1 raw11910step0; decide +kernel
      have hl : raw11910step0Labels = labelEmbedding6 ∘ raw11910step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11910step0 raw11910step0Labels raw11910step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5243 node5243Labels := by rfl

def raw11911 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw11911Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11911step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw11911step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw11911step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw11911step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11911 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11911 raw11911Labels = mixedMoment B node5243 node5243Labels := by
  calc
    mixedMoment B raw11911 raw11911Labels = mixedMoment B raw11911step0 raw11911step0Labels := by
      have ha : raw11911step0 = (fun i j => raw11911 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11911step0 raw11911; decide +kernel
      have hl : raw11911step0Labels = raw11911Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11911 raw11911Labels permutation164 permutation3
    mixedMoment B raw11911step0 raw11911step0Labels = mixedMoment B raw11911step1 raw11911step1Labels := by
      have ha : raw11911step1 = raw11911step0 := by apply Matrix.ext; unfold raw11911step1 raw11911step0; decide +kernel
      have hl : raw11911step0Labels = labelEmbedding6 ∘ raw11911step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11911step0 raw11911step0Labels raw11911step1Labels labelEmbedding6 hl
    _ = mixedMoment B node5243 node5243Labels := by rfl

def raw11912 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11912Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11912step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-1, -1, 2]]
def raw11912step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11912step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw11912step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11912 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11912 raw11912Labels = mixedMoment B node3874 node3874Labels := by
  calc
    mixedMoment B raw11912 raw11912Labels = mixedMoment B raw11912step0 raw11912step0Labels := by
      have ha : raw11912step0 = (fun i j => raw11912 (permutation364 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11912step0 raw11912; decide +kernel
      have hl : raw11912step0Labels = raw11912Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11912 raw11912Labels permutation364 permutation6
    mixedMoment B raw11912step0 raw11912step0Labels = mixedMoment B raw11912step1 raw11912step1Labels := by
      have ha : raw11912step1 = -raw11912step0 := by apply Matrix.ext; change ∀ i j, raw11912step1 i j = -(raw11912step0 i j); unfold raw11912step1 raw11912step0; decide +kernel
      have hl : raw11912step1Labels = raw11912step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3874 node3874Labels := by rfl

def raw11913 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11913Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11913step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11913step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11913 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11913 raw11913Labels = mixedMoment B node4002 node4002Labels := by
  calc
    mixedMoment B raw11913 raw11913Labels = mixedMoment B raw11913step0 raw11913step0Labels := by
      have ha : raw11913step0 = (fun i j => raw11913 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11913step0 raw11913; decide +kernel
      have hl : raw11913step0Labels = raw11913Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11913 raw11913Labels permutation176 permutation3
    _ = mixedMoment B node4002 node4002Labels := by rfl

def raw11914 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11914Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11914step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw11914step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11914step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11914step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11914 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11914 raw11914Labels = mixedMoment B node3875 node3875Labels := by
  calc
    mixedMoment B raw11914 raw11914Labels = mixedMoment B raw11914step0 raw11914step0Labels := by
      have ha : raw11914step0 = (fun i j => raw11914 (permutation365 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11914step0 raw11914; decide +kernel
      have hl : raw11914step0Labels = raw11914Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11914 raw11914Labels permutation365 permutation6
    mixedMoment B raw11914step0 raw11914step0Labels = mixedMoment B raw11914step1 raw11914step1Labels := by
      have ha : raw11914step1 = -raw11914step0 := by apply Matrix.ext; change ∀ i j, raw11914step1 i j = -(raw11914step0 i j); unfold raw11914step1 raw11914step0; decide +kernel
      have hl : raw11914step1Labels = raw11914step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3875 node3875Labels := by rfl

def raw11915 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw11915Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11915step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw11915step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11915step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11915step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11915 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11915 raw11915Labels = mixedMoment B node3875 node3875Labels := by
  calc
    mixedMoment B raw11915 raw11915Labels = mixedMoment B raw11915step0 raw11915step0Labels := by
      have ha : raw11915step0 = (fun i j => raw11915 (permutation363 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11915step0 raw11915; decide +kernel
      have hl : raw11915step0Labels = raw11915Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11915 raw11915Labels permutation363 permutation6
    mixedMoment B raw11915step0 raw11915step0Labels = mixedMoment B raw11915step1 raw11915step1Labels := by
      have ha : raw11915step1 = -raw11915step0 := by apply Matrix.ext; change ∀ i j, raw11915step1 i j = -(raw11915step0 i j); unfold raw11915step1 raw11915step0; decide +kernel
      have hl : raw11915step1Labels = raw11915step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3875 node3875Labels := by rfl

def raw11916 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw11916Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11916step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw11916step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11916step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw11916step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11916step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11916step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11916 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11916 raw11916Labels = mixedMoment B node3887 node3887Labels := by
  calc
    mixedMoment B raw11916 raw11916Labels = mixedMoment B raw11916step0 raw11916step0Labels := by
      have hz : ∀ j, raw11916 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw11916step0 = (fun i j => raw11916 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw11916step0 raw11916; decide +kernel
      have hl : raw11916step0Labels = raw11916Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11916 raw11916Labels permutation590 hz
    mixedMoment B raw11916step0 raw11916step0Labels = mixedMoment B raw11916step1 raw11916step1Labels := by
      have ha : raw11916step1 = (fun i j => raw11916step0 (permutation83 i) (permutation6 j)) := by apply Matrix.ext; unfold raw11916step1 raw11916step0; decide +kernel
      have hl : raw11916step1Labels = raw11916step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11916step0 raw11916step0Labels permutation83 permutation6
    mixedMoment B raw11916step1 raw11916step1Labels = mixedMoment B raw11916step2 raw11916step2Labels := by
      have ha : raw11916step2 = -raw11916step1 := by apply Matrix.ext; change ∀ i j, raw11916step2 i j = -(raw11916step1 i j); unfold raw11916step2 raw11916step1; decide +kernel
      have hl : raw11916step2Labels = raw11916step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node3887 node3887Labels := by rfl

def raw11917 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11917Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11917step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11917step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11917 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11917 raw11917Labels = mixedMoment B node1056 node1056Labels := by
  calc
    mixedMoment B raw11917 raw11917Labels = mixedMoment B raw11917step0 raw11917step0Labels := by
      have ha : raw11917step0 = (fun i j => raw11917 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11917step0 raw11917; decide +kernel
      have hl : raw11917step0Labels = raw11917Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11917 raw11917Labels permutation176 permutation3
    _ = mixedMoment B node1056 node1056Labels := by rfl

def raw11918 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11918Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11918step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11918step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11918 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11918 raw11918Labels = mixedMoment B node2636 node2636Labels := by
  calc
    mixedMoment B raw11918 raw11918Labels = mixedMoment B raw11918step0 raw11918step0Labels := by
      have ha : raw11918step0 = (fun i j => raw11918 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11918step0 raw11918; decide +kernel
      have hl : raw11918step0Labels = raw11918Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11918 raw11918Labels permutation176 permutation3
    _ = mixedMoment B node2636 node2636Labels := by rfl

def raw11919 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11919Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11919step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11919step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11919 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11919 raw11919Labels = mixedMoment B node2730 node2730Labels := by
  calc
    mixedMoment B raw11919 raw11919Labels = mixedMoment B raw11919step0 raw11919step0Labels := by
      have ha : raw11919step0 = (fun i j => raw11919 (permutation206 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11919step0 raw11919; decide +kernel
      have hl : raw11919step0Labels = raw11919Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11919 raw11919Labels permutation206 permutation3
    _ = mixedMoment B node2730 node2730Labels := by rfl

def raw11920 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw11920Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11920step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11920step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11920 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11920 raw11920Labels = mixedMoment B node2730 node2730Labels := by
  calc
    mixedMoment B raw11920 raw11920Labels = mixedMoment B raw11920step0 raw11920step0Labels := by
      have ha : raw11920step0 = (fun i j => raw11920 (permutation230 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11920step0 raw11920; decide +kernel
      have hl : raw11920step0Labels = raw11920Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11920 raw11920Labels permutation230 permutation3
    _ = mixedMoment B node2730 node2730Labels := by rfl

def raw11921 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw11921Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11921step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw11921step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11921step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw11921step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11921 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11921 raw11921Labels = mixedMoment B node2775 node2775Labels := by
  calc
    mixedMoment B raw11921 raw11921Labels = mixedMoment B raw11921step0 raw11921step0Labels := by
      have hz : ∀ j, raw11921 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw11921step0 = (fun i j => raw11921 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw11921step0 raw11921; decide +kernel
      have hl : raw11921step0Labels = raw11921Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11921 raw11921Labels permutation590 hz
    mixedMoment B raw11921step0 raw11921step0Labels = mixedMoment B raw11921step1 raw11921step1Labels := by
      have ha : raw11921step1 = (fun i j => raw11921step0 (permutation38 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11921step1 raw11921step0; decide +kernel
      have hl : raw11921step1Labels = raw11921step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11921step0 raw11921step0Labels permutation38 permutation3
    _ = mixedMoment B node2775 node2775Labels := by rfl

def raw11922 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11922Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11922step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw11922step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11922 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11922 raw11922Labels = mixedMoment B node995 node995Labels := by
  calc
    mixedMoment B raw11922 raw11922Labels = mixedMoment B raw11922step0 raw11922step0Labels := by
      have ha : raw11922step0 = (fun i j => raw11922 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11922step0 raw11922; decide +kernel
      have hl : raw11922step0Labels = raw11922Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11922 raw11922Labels permutation161 permutation3
    _ = mixedMoment B node995 node995Labels := by rfl

def raw11923 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11923Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11923step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw11923step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11923 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11923 raw11923Labels = mixedMoment B node2396 node2396Labels := by
  calc
    mixedMoment B raw11923 raw11923Labels = mixedMoment B raw11923step0 raw11923step0Labels := by
      have ha : raw11923step0 = (fun i j => raw11923 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11923step0 raw11923; decide +kernel
      have hl : raw11923step0Labels = raw11923Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11923 raw11923Labels permutation161 permutation3
    _ = mixedMoment B node2396 node2396Labels := by rfl

def raw11924 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11924Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11924step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw11924step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11924 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11924 raw11924Labels = mixedMoment B node2700 node2700Labels := by
  calc
    mixedMoment B raw11924 raw11924Labels = mixedMoment B raw11924step0 raw11924step0Labels := by
      have ha : raw11924step0 = (fun i j => raw11924 (permutation161 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11924step0 raw11924; decide +kernel
      have hl : raw11924step0Labels = raw11924Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11924 raw11924Labels permutation161 permutation3
    _ = mixedMoment B node2700 node2700Labels := by rfl

def raw11925 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw11925Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11925step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 2, -3]]
def raw11925step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11925 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11925 raw11925Labels = mixedMoment B node2700 node2700Labels := by
  calc
    mixedMoment B raw11925 raw11925Labels = mixedMoment B raw11925step0 raw11925step0Labels := by
      have ha : raw11925step0 = (fun i j => raw11925 (permutation167 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11925step0 raw11925; decide +kernel
      have hl : raw11925step0Labels = raw11925Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11925 raw11925Labels permutation167 permutation3
    _ = mixedMoment B node2700 node2700Labels := by rfl

def raw11926 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw11926Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11926step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw11926step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11926step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw11926step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11926 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11926 raw11926Labels = mixedMoment B node2738 node2738Labels := by
  calc
    mixedMoment B raw11926 raw11926Labels = mixedMoment B raw11926step0 raw11926step0Labels := by
      have hz : ∀ j, raw11926 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw11926step0 = (fun i j => raw11926 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw11926step0 raw11926; decide +kernel
      have hl : raw11926step0Labels = raw11926Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11926 raw11926Labels permutation590 hz
    mixedMoment B raw11926step0 raw11926step0Labels = mixedMoment B raw11926step1 raw11926step1Labels := by
      have ha : raw11926step1 = (fun i j => raw11926step0 (permutation35 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11926step1 raw11926step0; decide +kernel
      have hl : raw11926step1Labels = raw11926step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11926step0 raw11926step0Labels permutation35 permutation3
    _ = mixedMoment B node2738 node2738Labels := by rfl

def raw11927 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11927Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11927step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11927step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11927 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11927 raw11927Labels = mixedMoment B node988 node988Labels := by
  calc
    mixedMoment B raw11927 raw11927Labels = mixedMoment B raw11927step0 raw11927step0Labels := by
      have ha : raw11927step0 = (fun i j => raw11927 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11927step0 raw11927; decide +kernel
      have hl : raw11927step0Labels = raw11927Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11927 raw11927Labels permutation155 permutation3
    _ = mixedMoment B node988 node988Labels := by rfl

def raw11928 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11928Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11928step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11928step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11928 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11928 raw11928Labels = mixedMoment B node2390 node2390Labels := by
  calc
    mixedMoment B raw11928 raw11928Labels = mixedMoment B raw11928step0 raw11928step0Labels := by
      have ha : raw11928step0 = (fun i j => raw11928 (permutation155 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11928step0 raw11928; decide +kernel
      have hl : raw11928step0Labels = raw11928Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11928 raw11928Labels permutation155 permutation3
    _ = mixedMoment B node2390 node2390Labels := by rfl

def raw11929 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11929Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11929step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11929step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11929 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11929 raw11929Labels = mixedMoment B node2615 node2615Labels := by
  calc
    mixedMoment B raw11929 raw11929Labels = mixedMoment B raw11929step0 raw11929step0Labels := by
      have ha : raw11929step0 = (fun i j => raw11929 (permutation179 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11929step0 raw11929; decide +kernel
      have hl : raw11929step0Labels = raw11929Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11929 raw11929Labels permutation179 permutation3
    _ = mixedMoment B node2615 node2615Labels := by rfl

def raw11930 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw11930Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11930step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw11930step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11930 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11930 raw11930Labels = mixedMoment B node2698 node2698Labels := by
  calc
    mixedMoment B raw11930 raw11930Labels = mixedMoment B raw11930step0 raw11930step0Labels := by
      have ha : raw11930step0 = (fun i j => raw11930 (permutation165 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11930step0 raw11930; decide +kernel
      have hl : raw11930step0Labels = raw11930Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11930 raw11930Labels permutation165 permutation3
    _ = mixedMoment B node2698 node2698Labels := by rfl

def raw11931 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw11931Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11931step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1]]
def raw11931step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11931step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw11931step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11931 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11931 raw11931Labels = mixedMoment B node2731 node2731Labels := by
  calc
    mixedMoment B raw11931 raw11931Labels = mixedMoment B raw11931step0 raw11931step0Labels := by
      have hz : ∀ j, raw11931 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw11931step0 = (fun i j => raw11931 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw11931step0 raw11931; decide +kernel
      have hl : raw11931step0Labels = raw11931Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11931 raw11931Labels permutation590 hz
    mixedMoment B raw11931step0 raw11931step0Labels = mixedMoment B raw11931step1 raw11931step1Labels := by
      have ha : raw11931step1 = (fun i j => raw11931step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11931step1 raw11931step0; decide +kernel
      have hl : raw11931step1Labels = raw11931step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11931step0 raw11931step0Labels permutation33 permutation3
    _ = mixedMoment B node2731 node2731Labels := by rfl

def raw11932 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw11932Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11932step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11932step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11932 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11932 raw11932Labels = mixedMoment B node988 node988Labels := by
  calc
    mixedMoment B raw11932 raw11932Labels = mixedMoment B raw11932step0 raw11932step0Labels := by
      have ha : raw11932step0 = (fun i j => raw11932 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11932step0 raw11932; decide +kernel
      have hl : raw11932step0Labels = raw11932Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11932 raw11932Labels permutation153 permutation3
    _ = mixedMoment B node988 node988Labels := by rfl

def raw11933 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw11933Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11933step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11933step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11933 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11933 raw11933Labels = mixedMoment B node2390 node2390Labels := by
  calc
    mixedMoment B raw11933 raw11933Labels = mixedMoment B raw11933step0 raw11933step0Labels := by
      have ha : raw11933step0 = (fun i j => raw11933 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11933step0 raw11933; decide +kernel
      have hl : raw11933step0Labels = raw11933Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11933 raw11933Labels permutation153 permutation3
    _ = mixedMoment B node2390 node2390Labels := by rfl

def raw11934 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw11934Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11934step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11934step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11934 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11934 raw11934Labels = mixedMoment B node2615 node2615Labels := by
  calc
    mixedMoment B raw11934 raw11934Labels = mixedMoment B raw11934step0 raw11934step0Labels := by
      have ha : raw11934step0 = (fun i j => raw11934 (permutation177 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11934step0 raw11934; decide +kernel
      have hl : raw11934step0Labels = raw11934Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11934 raw11934Labels permutation177 permutation3
    _ = mixedMoment B node2615 node2615Labels := by rfl

def raw11935 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw11935Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11935step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, 0, -1], ![2, -1, -1]]
def raw11935step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11935 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11935 raw11935Labels = mixedMoment B node2698 node2698Labels := by
  calc
    mixedMoment B raw11935 raw11935Labels = mixedMoment B raw11935step0 raw11935step0Labels := by
      have ha : raw11935step0 = (fun i j => raw11935 (permutation159 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11935step0 raw11935; decide +kernel
      have hl : raw11935step0Labels = raw11935Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11935 raw11935Labels permutation159 permutation3
    _ = mixedMoment B node2698 node2698Labels := by rfl

def raw11936 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw11936Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11936step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw11936step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11936step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, -1, -1]]
def raw11936step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11936 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11936 raw11936Labels = mixedMoment B node2731 node2731Labels := by
  calc
    mixedMoment B raw11936 raw11936Labels = mixedMoment B raw11936step0 raw11936step0Labels := by
      have hz : ∀ j, raw11936 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw11936step0 = (fun i j => raw11936 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw11936step0 raw11936; decide +kernel
      have hl : raw11936step0Labels = raw11936Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11936 raw11936Labels permutation590 hz
    mixedMoment B raw11936step0 raw11936step0Labels = mixedMoment B raw11936step1 raw11936step1Labels := by
      have ha : raw11936step1 = (fun i j => raw11936step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11936step1 raw11936step0; decide +kernel
      have hl : raw11936step1Labels = raw11936step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11936step0 raw11936step0Labels permutation32 permutation3
    _ = mixedMoment B node2731 node2731Labels := by rfl

def raw11937 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11937Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11937step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 1, 3], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11937step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11937 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11937 raw11937Labels = mixedMoment B node987 node987Labels := by
  calc
    mixedMoment B raw11937 raw11937Labels = mixedMoment B raw11937step0 raw11937step0Labels := by
      have ha : raw11937step0 = (fun i j => raw11937 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11937step0 raw11937; decide +kernel
      have hl : raw11937step0Labels = raw11937Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11937 raw11937Labels permutation152 permutation3
    _ = mixedMoment B node987 node987Labels := by rfl

def raw11938 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11938Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11938step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, -1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11938step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11938 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11938 raw11938Labels = mixedMoment B node2389 node2389Labels := by
  calc
    mixedMoment B raw11938 raw11938Labels = mixedMoment B raw11938step0 raw11938step0Labels := by
      have ha : raw11938step0 = (fun i j => raw11938 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11938step0 raw11938; decide +kernel
      have hl : raw11938step0Labels = raw11938Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11938 raw11938Labels permutation152 permutation3
    _ = mixedMoment B node2389 node2389Labels := by rfl

def raw11939 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11939Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11939step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw11939step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11939 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11939 raw11939Labels = mixedMoment B node2614 node2614Labels := by
  calc
    mixedMoment B raw11939 raw11939Labels = mixedMoment B raw11939step0 raw11939step0Labels := by
      have ha : raw11939step0 = (fun i j => raw11939 (permutation176 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11939step0 raw11939; decide +kernel
      have hl : raw11939step0Labels = raw11939Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11939 raw11939Labels permutation176 permutation3
    _ = mixedMoment B node2614 node2614Labels := by rfl

def raw11940 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11940Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11940step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw11940step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11940 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11940 raw11940Labels = mixedMoment B node2697 node2697Labels := by
  calc
    mixedMoment B raw11940 raw11940Labels = mixedMoment B raw11940step0 raw11940step0Labels := by
      have ha : raw11940step0 = (fun i j => raw11940 (permutation158 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11940step0 raw11940; decide +kernel
      have hl : raw11940step0Labels = raw11940Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11940 raw11940Labels permutation158 permutation3
    _ = mixedMoment B node2697 node2697Labels := by rfl

def raw11941 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw11941Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw11941step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![2, 0, -2]]
def raw11941step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11941 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11941 raw11941Labels = mixedMoment B node2697 node2697Labels := by
  calc
    mixedMoment B raw11941 raw11941Labels = mixedMoment B raw11941step0 raw11941step0Labels := by
      have ha : raw11941step0 = (fun i j => raw11941 (permutation164 i) (permutation3 j)) := by apply Matrix.ext; unfold raw11941step0 raw11941; decide +kernel
      have hl : raw11941step0Labels = raw11941Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11941 raw11941Labels permutation164 permutation3
    _ = mixedMoment B node2697 node2697Labels := by rfl

def raw11942 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11942Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11942step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw11942step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11942step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11942step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11942step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11942step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11942 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11942 raw11942Labels = mixedMoment B node3954 node3954Labels := by
  calc
    mixedMoment B raw11942 raw11942Labels = mixedMoment B raw11942step0 raw11942step0Labels := by
      have ha : raw11942step0 = (fun i j => raw11942 (permutation274 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11942step0 raw11942; decide +kernel
      have hl : raw11942step0Labels = raw11942Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11942 raw11942Labels permutation274 permutation5
    mixedMoment B raw11942step0 raw11942step0Labels = mixedMoment B raw11942step1 raw11942step1Labels := by
      have ha : raw11942step1 = -raw11942step0 := by apply Matrix.ext; change ∀ i j, raw11942step1 i j = -(raw11942step0 i j); unfold raw11942step1 raw11942step0; decide +kernel
      have hl : raw11942step1Labels = raw11942step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11942step1 raw11942step1Labels = mixedMoment B raw11942step2 raw11942step2Labels := by
      have ha : raw11942step2 = raw11942step1 := by apply Matrix.ext; unfold raw11942step2 raw11942step1; decide +kernel
      have hl : raw11942step1Labels = labelEmbedding1 ∘ raw11942step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11942step1 raw11942step1Labels raw11942step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3954 node3954Labels := by rfl

def raw11943 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11943Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11943step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -1, -1], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw11943step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11943step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11943step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11943step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11943step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11943 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11943 raw11943Labels = mixedMoment B node3957 node3957Labels := by
  calc
    mixedMoment B raw11943 raw11943Labels = mixedMoment B raw11943step0 raw11943step0Labels := by
      have ha : raw11943step0 = (fun i j => raw11943 (permutation361 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11943step0 raw11943; decide +kernel
      have hl : raw11943step0Labels = raw11943Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11943 raw11943Labels permutation361 permutation7
    mixedMoment B raw11943step0 raw11943step0Labels = mixedMoment B raw11943step1 raw11943step1Labels := by
      have ha : raw11943step1 = -raw11943step0 := by apply Matrix.ext; change ∀ i j, raw11943step1 i j = -(raw11943step0 i j); unfold raw11943step1 raw11943step0; decide +kernel
      have hl : raw11943step1Labels = raw11943step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11943step1 raw11943step1Labels = mixedMoment B raw11943step2 raw11943step2Labels := by
      have ha : raw11943step2 = raw11943step1 := by apply Matrix.ext; unfold raw11943step2 raw11943step1; decide +kernel
      have hl : raw11943step1Labels = labelEmbedding1 ∘ raw11943step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11943step1 raw11943step1Labels raw11943step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3957 node3957Labels := by rfl

def raw11944 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11944Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11944step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw11944step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11944step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11944step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11944step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11944step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11944 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11944 raw11944Labels = mixedMoment B node4026 node4026Labels := by
  calc
    mixedMoment B raw11944 raw11944Labels = mixedMoment B raw11944step0 raw11944step0Labels := by
      have ha : raw11944step0 = (fun i j => raw11944 (permutation361 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11944step0 raw11944; decide +kernel
      have hl : raw11944step0Labels = raw11944Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11944 raw11944Labels permutation361 permutation7
    mixedMoment B raw11944step0 raw11944step0Labels = mixedMoment B raw11944step1 raw11944step1Labels := by
      have ha : raw11944step1 = -raw11944step0 := by apply Matrix.ext; change ∀ i j, raw11944step1 i j = -(raw11944step0 i j); unfold raw11944step1 raw11944step0; decide +kernel
      have hl : raw11944step1Labels = raw11944step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11944step1 raw11944step1Labels = mixedMoment B raw11944step2 raw11944step2Labels := by
      have ha : raw11944step2 = raw11944step1 := by apply Matrix.ext; unfold raw11944step2 raw11944step1; decide +kernel
      have hl : raw11944step1Labels = labelEmbedding1 ∘ raw11944step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11944step1 raw11944step1Labels raw11944step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4026 node4026Labels := by rfl

def raw11945 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw11945Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11945step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw11945step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11945step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11945step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11945step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw11945step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11945 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11945 raw11945Labels = mixedMoment B node4026 node4026Labels := by
  calc
    mixedMoment B raw11945 raw11945Labels = mixedMoment B raw11945step0 raw11945step0Labels := by
      have ha : raw11945step0 = (fun i j => raw11945 (permutation362 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11945step0 raw11945; decide +kernel
      have hl : raw11945step0Labels = raw11945Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11945 raw11945Labels permutation362 permutation7
    mixedMoment B raw11945step0 raw11945step0Labels = mixedMoment B raw11945step1 raw11945step1Labels := by
      have ha : raw11945step1 = -raw11945step0 := by apply Matrix.ext; change ∀ i j, raw11945step1 i j = -(raw11945step0 i j); unfold raw11945step1 raw11945step0; decide +kernel
      have hl : raw11945step1Labels = raw11945step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11945step1 raw11945step1Labels = mixedMoment B raw11945step2 raw11945step2Labels := by
      have ha : raw11945step2 = raw11945step1 := by apply Matrix.ext; unfold raw11945step2 raw11945step1; decide +kernel
      have hl : raw11945step1Labels = labelEmbedding1 ∘ raw11945step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11945step1 raw11945step1Labels raw11945step2Labels labelEmbedding1 hl
    _ = mixedMoment B node4026 node4026Labels := by rfl

def raw11946 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw11946Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11946step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw11946step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11946step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw11946step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11946step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11946step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11946step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11946step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11946 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11946 raw11946Labels = mixedMoment B node4029 node4029Labels := by
  calc
    mixedMoment B raw11946 raw11946Labels = mixedMoment B raw11946step0 raw11946step0Labels := by
      have hz : ∀ j, raw11946 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw11946step0 = (fun i j => raw11946 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw11946step0 raw11946; decide +kernel
      have hl : raw11946step0Labels = raw11946Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11946 raw11946Labels permutation590 hz
    mixedMoment B raw11946step0 raw11946step0Labels = mixedMoment B raw11946step1 raw11946step1Labels := by
      have ha : raw11946step1 = (fun i j => raw11946step0 (permutation80 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11946step1 raw11946step0; decide +kernel
      have hl : raw11946step1Labels = raw11946step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11946step0 raw11946step0Labels permutation80 permutation7
    mixedMoment B raw11946step1 raw11946step1Labels = mixedMoment B raw11946step2 raw11946step2Labels := by
      have ha : raw11946step2 = -raw11946step1 := by apply Matrix.ext; change ∀ i j, raw11946step2 i j = -(raw11946step1 i j); unfold raw11946step2 raw11946step1; decide +kernel
      have hl : raw11946step2Labels = raw11946step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11946step2 raw11946step2Labels = mixedMoment B raw11946step3 raw11946step3Labels := by
      have ha : raw11946step3 = raw11946step2 := by apply Matrix.ext; unfold raw11946step3 raw11946step2; decide +kernel
      have hl : raw11946step2Labels = labelEmbedding1 ∘ raw11946step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11946step2 raw11946step2Labels raw11946step3Labels labelEmbedding1 hl
    _ = mixedMoment B node4029 node4029Labels := by rfl

def raw11947 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11947Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11947step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw11947step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11947step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11947step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11947step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11947step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11947 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11947 raw11947Labels = mixedMoment B node1699 node1699Labels := by
  calc
    mixedMoment B raw11947 raw11947Labels = mixedMoment B raw11947step0 raw11947step0Labels := by
      have ha : raw11947step0 = (fun i j => raw11947 (permutation161 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11947step0 raw11947; decide +kernel
      have hl : raw11947step0Labels = raw11947Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11947 raw11947Labels permutation161 permutation5
    mixedMoment B raw11947step0 raw11947step0Labels = mixedMoment B raw11947step1 raw11947step1Labels := by
      have ha : raw11947step1 = -raw11947step0 := by apply Matrix.ext; change ∀ i j, raw11947step1 i j = -(raw11947step0 i j); unfold raw11947step1 raw11947step0; decide +kernel
      have hl : raw11947step1Labels = raw11947step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11947step1 raw11947step1Labels = mixedMoment B raw11947step2 raw11947step2Labels := by
      have ha : raw11947step2 = raw11947step1 := by apply Matrix.ext; unfold raw11947step2 raw11947step1; decide +kernel
      have hl : raw11947step1Labels = labelEmbedding1 ∘ raw11947step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11947step1 raw11947step1Labels raw11947step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1699 node1699Labels := by rfl

def raw11948 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11948Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11948step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1]]
def raw11948step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11948step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw11948step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11948step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw11948step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11948 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11948 raw11948Labels = mixedMoment B node3617 node3617Labels := by
  calc
    mixedMoment B raw11948 raw11948Labels = mixedMoment B raw11948step0 raw11948step0Labels := by
      have ha : raw11948step0 = (fun i j => raw11948 (permutation160 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11948step0 raw11948; decide +kernel
      have hl : raw11948step0Labels = raw11948Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11948 raw11948Labels permutation160 permutation5
    mixedMoment B raw11948step0 raw11948step0Labels = mixedMoment B raw11948step1 raw11948step1Labels := by
      have ha : raw11948step1 = -raw11948step0 := by apply Matrix.ext; change ∀ i j, raw11948step1 i j = -(raw11948step0 i j); unfold raw11948step1 raw11948step0; decide +kernel
      have hl : raw11948step1Labels = raw11948step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11948step1 raw11948step1Labels = mixedMoment B raw11948step2 raw11948step2Labels := by
      have ha : raw11948step2 = raw11948step1 := by apply Matrix.ext; unfold raw11948step2 raw11948step1; decide +kernel
      have hl : raw11948step1Labels = labelEmbedding1 ∘ raw11948step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11948step1 raw11948step1Labels raw11948step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3617 node3617Labels := by rfl

def raw11949 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11949Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11949step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw11949step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11949step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11949step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11949step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11949step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11949 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11949 raw11949Labels = mixedMoment B node3526 node3526Labels := by
  calc
    mixedMoment B raw11949 raw11949Labels = mixedMoment B raw11949step0 raw11949step0Labels := by
      have ha : raw11949step0 = (fun i j => raw11949 (permutation203 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11949step0 raw11949; decide +kernel
      have hl : raw11949step0Labels = raw11949Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11949 raw11949Labels permutation203 permutation5
    mixedMoment B raw11949step0 raw11949step0Labels = mixedMoment B raw11949step1 raw11949step1Labels := by
      have ha : raw11949step1 = -raw11949step0 := by apply Matrix.ext; change ∀ i j, raw11949step1 i j = -(raw11949step0 i j); unfold raw11949step1 raw11949step0; decide +kernel
      have hl : raw11949step1Labels = raw11949step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11949step1 raw11949step1Labels = mixedMoment B raw11949step2 raw11949step2Labels := by
      have ha : raw11949step2 = raw11949step1 := by apply Matrix.ext; unfold raw11949step2 raw11949step1; decide +kernel
      have hl : raw11949step1Labels = labelEmbedding1 ∘ raw11949step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11949step1 raw11949step1Labels raw11949step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3526 node3526Labels := by rfl

def raw11950 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw11950Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11950step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw11950step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11950step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11950step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11950step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11950step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11950 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11950 raw11950Labels = mixedMoment B node3526 node3526Labels := by
  calc
    mixedMoment B raw11950 raw11950Labels = mixedMoment B raw11950step0 raw11950step0Labels := by
      have ha : raw11950step0 = (fun i j => raw11950 (permutation227 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11950step0 raw11950; decide +kernel
      have hl : raw11950step0Labels = raw11950Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11950 raw11950Labels permutation227 permutation5
    mixedMoment B raw11950step0 raw11950step0Labels = mixedMoment B raw11950step1 raw11950step1Labels := by
      have ha : raw11950step1 = -raw11950step0 := by apply Matrix.ext; change ∀ i j, raw11950step1 i j = -(raw11950step0 i j); unfold raw11950step1 raw11950step0; decide +kernel
      have hl : raw11950step1Labels = raw11950step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11950step1 raw11950step1Labels = mixedMoment B raw11950step2 raw11950step2Labels := by
      have ha : raw11950step2 = raw11950step1 := by apply Matrix.ext; unfold raw11950step2 raw11950step1; decide +kernel
      have hl : raw11950step1Labels = labelEmbedding1 ∘ raw11950step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11950step1 raw11950step1Labels raw11950step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3526 node3526Labels := by rfl

def raw11951 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw11951Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11951step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw11951step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11951step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0]]
def raw11951step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11951step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw11951step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11951step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0]]
def raw11951step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11951 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11951 raw11951Labels = mixedMoment B node3619 node3619Labels := by
  calc
    mixedMoment B raw11951 raw11951Labels = mixedMoment B raw11951step0 raw11951step0Labels := by
      have hz : ∀ j, raw11951 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw11951step0 = (fun i j => raw11951 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw11951step0 raw11951; decide +kernel
      have hl : raw11951step0Labels = raw11951Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11951 raw11951Labels permutation590 hz
    mixedMoment B raw11951step0 raw11951step0Labels = mixedMoment B raw11951step1 raw11951step1Labels := by
      have ha : raw11951step1 = (fun i j => raw11951step0 (permutation35 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11951step1 raw11951step0; decide +kernel
      have hl : raw11951step1Labels = raw11951step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11951step0 raw11951step0Labels permutation35 permutation5
    mixedMoment B raw11951step1 raw11951step1Labels = mixedMoment B raw11951step2 raw11951step2Labels := by
      have ha : raw11951step2 = -raw11951step1 := by apply Matrix.ext; change ∀ i j, raw11951step2 i j = -(raw11951step1 i j); unfold raw11951step2 raw11951step1; decide +kernel
      have hl : raw11951step2Labels = raw11951step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11951step2 raw11951step2Labels = mixedMoment B raw11951step3 raw11951step3Labels := by
      have ha : raw11951step3 = raw11951step2 := by apply Matrix.ext; unfold raw11951step3 raw11951step2; decide +kernel
      have hl : raw11951step2Labels = labelEmbedding1 ∘ raw11951step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11951step2 raw11951step2Labels raw11951step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3619 node3619Labels := by rfl

def raw11952 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11952Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11952step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 2, 1]]
def raw11952step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11952step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw11952step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11952step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -2, -1]]
def raw11952step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11952 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11952 raw11952Labels = mixedMoment B node1593 node1593Labels := by
  calc
    mixedMoment B raw11952 raw11952Labels = mixedMoment B raw11952step0 raw11952step0Labels := by
      have ha : raw11952step0 = (fun i j => raw11952 (permutation161 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11952step0 raw11952; decide +kernel
      have hl : raw11952step0Labels = raw11952Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11952 raw11952Labels permutation161 permutation5
    mixedMoment B raw11952step0 raw11952step0Labels = mixedMoment B raw11952step1 raw11952step1Labels := by
      have ha : raw11952step1 = -raw11952step0 := by apply Matrix.ext; change ∀ i j, raw11952step1 i j = -(raw11952step0 i j); unfold raw11952step1 raw11952step0; decide +kernel
      have hl : raw11952step1Labels = raw11952step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11952step1 raw11952step1Labels = mixedMoment B raw11952step2 raw11952step2Labels := by
      have ha : raw11952step2 = raw11952step1 := by apply Matrix.ext; unfold raw11952step2 raw11952step1; decide +kernel
      have hl : raw11952step1Labels = labelEmbedding1 ∘ raw11952step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11952step1 raw11952step1Labels raw11952step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1593 node1593Labels := by rfl

def raw11953 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11953Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11953step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw11953step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11953step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1], ![2, -1, -1], ![2, 1, -3]]
def raw11953step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11953 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11953 raw11953Labels = mixedMoment B node2912 node2912Labels := by
  calc
    mixedMoment B raw11953 raw11953Labels = mixedMoment B raw11953step0 raw11953step0Labels := by
      have ha : raw11953step0 = (fun i j => raw11953 (permutation427 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11953step0 raw11953; decide +kernel
      have hl : raw11953step0Labels = raw11953Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11953 raw11953Labels permutation427 permutation5
    mixedMoment B raw11953step0 raw11953step0Labels = mixedMoment B raw11953step1 raw11953step1Labels := by
      have ha : raw11953step1 = raw11953step0 := by apply Matrix.ext; unfold raw11953step1 raw11953step0; decide +kernel
      have hl : raw11953step0Labels = labelEmbedding1 ∘ raw11953step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11953step0 raw11953step0Labels raw11953step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2912 node2912Labels := by rfl

def raw11954 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11954Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11954step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw11954step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11954step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw11954step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11954 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11954 raw11954Labels = mixedMoment B node2923 node2923Labels := by
  calc
    mixedMoment B raw11954 raw11954Labels = mixedMoment B raw11954step0 raw11954step0Labels := by
      have ha : raw11954step0 = (fun i j => raw11954 (permutation431 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11954step0 raw11954; decide +kernel
      have hl : raw11954step0Labels = raw11954Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11954 raw11954Labels permutation431 permutation5
    mixedMoment B raw11954step0 raw11954step0Labels = mixedMoment B raw11954step1 raw11954step1Labels := by
      have ha : raw11954step1 = raw11954step0 := by apply Matrix.ext; unfold raw11954step1 raw11954step0; decide +kernel
      have hl : raw11954step0Labels = labelEmbedding1 ∘ raw11954step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11954step0 raw11954step0Labels raw11954step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2923 node2923Labels := by rfl

def raw11955 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw11955Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11955step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw11955step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11955step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 1, -3]]
def raw11955step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11955 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11955 raw11955Labels = mixedMoment B node2923 node2923Labels := by
  calc
    mixedMoment B raw11955 raw11955Labels = mixedMoment B raw11955step0 raw11955step0Labels := by
      have ha : raw11955step0 = (fun i j => raw11955 (permutation425 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11955step0 raw11955; decide +kernel
      have hl : raw11955step0Labels = raw11955Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11955 raw11955Labels permutation425 permutation5
    mixedMoment B raw11955step0 raw11955step0Labels = mixedMoment B raw11955step1 raw11955step1Labels := by
      have ha : raw11955step1 = raw11955step0 := by apply Matrix.ext; unfold raw11955step1 raw11955step0; decide +kernel
      have hl : raw11955step0Labels = labelEmbedding1 ∘ raw11955step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11955step0 raw11955step0Labels raw11955step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2923 node2923Labels := by rfl

def raw11956 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw11956Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11956step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1]]
def raw11956step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11956step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw11956step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11956step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw11956step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11956 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11956 raw11956Labels = mixedMoment B node3075 node3075Labels := by
  calc
    mixedMoment B raw11956 raw11956Labels = mixedMoment B raw11956step0 raw11956step0Labels := by
      have hz : ∀ j, raw11956 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw11956step0 = (fun i j => raw11956 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw11956step0 raw11956; decide +kernel
      have hl : raw11956step0Labels = raw11956Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11956 raw11956Labels permutation590 hz
    mixedMoment B raw11956step0 raw11956step0Labels = mixedMoment B raw11956step1 raw11956step1Labels := by
      have ha : raw11956step1 = (fun i j => raw11956step0 (permutation97 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11956step1 raw11956step0; decide +kernel
      have hl : raw11956step1Labels = raw11956step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11956step0 raw11956step0Labels permutation97 permutation5
    mixedMoment B raw11956step1 raw11956step1Labels = mixedMoment B raw11956step2 raw11956step2Labels := by
      have ha : raw11956step2 = raw11956step1 := by apply Matrix.ext; unfold raw11956step2 raw11956step1; decide +kernel
      have hl : raw11956step1Labels = labelEmbedding1 ∘ raw11956step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11956step1 raw11956step1Labels raw11956step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3075 node3075Labels := by rfl

def raw11957 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11957Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11957step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw11957step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11957step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11957step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11957step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11957step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11957 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11957 raw11957Labels = mixedMoment B node1601 node1601Labels := by
  calc
    mixedMoment B raw11957 raw11957Labels = mixedMoment B raw11957step0 raw11957step0Labels := by
      have ha : raw11957step0 = (fun i j => raw11957 (permutation169 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11957step0 raw11957; decide +kernel
      have hl : raw11957step0Labels = raw11957Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11957 raw11957Labels permutation169 permutation5
    mixedMoment B raw11957step0 raw11957step0Labels = mixedMoment B raw11957step1 raw11957step1Labels := by
      have ha : raw11957step1 = -raw11957step0 := by apply Matrix.ext; change ∀ i j, raw11957step1 i j = -(raw11957step0 i j); unfold raw11957step1 raw11957step0; decide +kernel
      have hl : raw11957step1Labels = raw11957step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11957step1 raw11957step1Labels = mixedMoment B raw11957step2 raw11957step2Labels := by
      have ha : raw11957step2 = raw11957step1 := by apply Matrix.ext; unfold raw11957step2 raw11957step1; decide +kernel
      have hl : raw11957step1Labels = labelEmbedding1 ∘ raw11957step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11957step1 raw11957step1Labels raw11957step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1601 node1601Labels := by rfl

def raw11958 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11958Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11958step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw11958step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11958step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11958step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11958step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11958step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11958 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11958 raw11958Labels = mixedMoment B node3342 node3342Labels := by
  calc
    mixedMoment B raw11958 raw11958Labels = mixedMoment B raw11958step0 raw11958step0Labels := by
      have ha : raw11958step0 = (fun i j => raw11958 (permutation169 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11958step0 raw11958; decide +kernel
      have hl : raw11958step0Labels = raw11958Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11958 raw11958Labels permutation169 permutation5
    mixedMoment B raw11958step0 raw11958step0Labels = mixedMoment B raw11958step1 raw11958step1Labels := by
      have ha : raw11958step1 = -raw11958step0 := by apply Matrix.ext; change ∀ i j, raw11958step1 i j = -(raw11958step0 i j); unfold raw11958step1 raw11958step0; decide +kernel
      have hl : raw11958step1Labels = raw11958step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11958step1 raw11958step1Labels = mixedMoment B raw11958step2 raw11958step2Labels := by
      have ha : raw11958step2 = raw11958step1 := by apply Matrix.ext; unfold raw11958step2 raw11958step1; decide +kernel
      have hl : raw11958step1Labels = labelEmbedding1 ∘ raw11958step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11958step1 raw11958step1Labels raw11958step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3342 node3342Labels := by rfl

def raw11959 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11959Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11959step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw11959step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11959step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11959step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11959step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11959step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11959 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11959 raw11959Labels = mixedMoment B node3529 node3529Labels := by
  calc
    mixedMoment B raw11959 raw11959Labels = mixedMoment B raw11959step0 raw11959step0Labels := by
      have ha : raw11959step0 = (fun i j => raw11959 (permutation165 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11959step0 raw11959; decide +kernel
      have hl : raw11959step0Labels = raw11959Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11959 raw11959Labels permutation165 permutation5
    mixedMoment B raw11959step0 raw11959step0Labels = mixedMoment B raw11959step1 raw11959step1Labels := by
      have ha : raw11959step1 = -raw11959step0 := by apply Matrix.ext; change ∀ i j, raw11959step1 i j = -(raw11959step0 i j); unfold raw11959step1 raw11959step0; decide +kernel
      have hl : raw11959step1Labels = raw11959step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11959step1 raw11959step1Labels = mixedMoment B raw11959step2 raw11959step2Labels := by
      have ha : raw11959step2 = raw11959step1 := by apply Matrix.ext; unfold raw11959step2 raw11959step1; decide +kernel
      have hl : raw11959step1Labels = labelEmbedding1 ∘ raw11959step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11959step1 raw11959step1Labels raw11959step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3529 node3529Labels := by rfl

def raw11960 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1], ![0, 1, -1], ![1, -1, 0]]
def raw11960Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11960step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw11960step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11960step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11960step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11960step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11960step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11960 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11960 raw11960Labels = mixedMoment B node3497 node3497Labels := by
  calc
    mixedMoment B raw11960 raw11960Labels = mixedMoment B raw11960step0 raw11960step0Labels := by
      have ha : raw11960step0 = (fun i j => raw11960 (permutation169 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11960step0 raw11960; decide +kernel
      have hl : raw11960step0Labels = raw11960Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11960 raw11960Labels permutation169 permutation5
    mixedMoment B raw11960step0 raw11960step0Labels = mixedMoment B raw11960step1 raw11960step1Labels := by
      have ha : raw11960step1 = -raw11960step0 := by apply Matrix.ext; change ∀ i j, raw11960step1 i j = -(raw11960step0 i j); unfold raw11960step1 raw11960step0; decide +kernel
      have hl : raw11960step1Labels = raw11960step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11960step1 raw11960step1Labels = mixedMoment B raw11960step2 raw11960step2Labels := by
      have ha : raw11960step2 = raw11960step1 := by apply Matrix.ext; unfold raw11960step2 raw11960step1; decide +kernel
      have hl : raw11960step1Labels = labelEmbedding1 ∘ raw11960step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11960step1 raw11960step1Labels raw11960step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3497 node3497Labels := by rfl

def raw11961 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![0, 0, 0]]
def raw11961Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11961step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1]]
def raw11961step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11961step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw11961step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11961step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11961step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11961step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11961step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11961 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11961 raw11961Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw11961 raw11961Labels = mixedMoment B raw11961step0 raw11961step0Labels := by
      have hz : ∀ j, raw11961 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw11961step0 = (fun i j => raw11961 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw11961step0 raw11961; decide +kernel
      have hl : raw11961step0Labels = raw11961Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11961 raw11961Labels permutation590 hz
    mixedMoment B raw11961step0 raw11961step0Labels = mixedMoment B raw11961step1 raw11961step1Labels := by
      have ha : raw11961step1 = (fun i j => raw11961step0 (permutation37 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11961step1 raw11961step0; decide +kernel
      have hl : raw11961step1Labels = raw11961step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11961step0 raw11961step0Labels permutation37 permutation5
    mixedMoment B raw11961step1 raw11961step1Labels = mixedMoment B raw11961step2 raw11961step2Labels := by
      have ha : raw11961step2 = -raw11961step1 := by apply Matrix.ext; change ∀ i j, raw11961step2 i j = -(raw11961step1 i j); unfold raw11961step2 raw11961step1; decide +kernel
      have hl : raw11961step2Labels = raw11961step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11961step2 raw11961step2Labels = mixedMoment B raw11961step3 raw11961step3Labels := by
      have ha : raw11961step3 = raw11961step2 := by apply Matrix.ext; unfold raw11961step3 raw11961step2; decide +kernel
      have hl : raw11961step2Labels = labelEmbedding1 ∘ raw11961step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11961step2 raw11961step2Labels raw11961step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3535 node3535Labels := by rfl

def raw11962 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw11962Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11962step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw11962step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11962step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11962step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11962step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11962step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11962 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11962 raw11962Labels = mixedMoment B node1601 node1601Labels := by
  calc
    mixedMoment B raw11962 raw11962Labels = mixedMoment B raw11962step0 raw11962step0Labels := by
      have ha : raw11962step0 = (fun i j => raw11962 (permutation163 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11962step0 raw11962; decide +kernel
      have hl : raw11962step0Labels = raw11962Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11962 raw11962Labels permutation163 permutation5
    mixedMoment B raw11962step0 raw11962step0Labels = mixedMoment B raw11962step1 raw11962step1Labels := by
      have ha : raw11962step1 = -raw11962step0 := by apply Matrix.ext; change ∀ i j, raw11962step1 i j = -(raw11962step0 i j); unfold raw11962step1 raw11962step0; decide +kernel
      have hl : raw11962step1Labels = raw11962step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11962step1 raw11962step1Labels = mixedMoment B raw11962step2 raw11962step2Labels := by
      have ha : raw11962step2 = raw11962step1 := by apply Matrix.ext; unfold raw11962step2 raw11962step1; decide +kernel
      have hl : raw11962step1Labels = labelEmbedding1 ∘ raw11962step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11962step1 raw11962step1Labels raw11962step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1601 node1601Labels := by rfl

def raw11963 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw11963Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11963step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -1, 1], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw11963step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11963step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11963step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11963step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11963step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11963 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11963 raw11963Labels = mixedMoment B node3342 node3342Labels := by
  calc
    mixedMoment B raw11963 raw11963Labels = mixedMoment B raw11963step0 raw11963step0Labels := by
      have ha : raw11963step0 = (fun i j => raw11963 (permutation163 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11963step0 raw11963; decide +kernel
      have hl : raw11963step0Labels = raw11963Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11963 raw11963Labels permutation163 permutation5
    mixedMoment B raw11963step0 raw11963step0Labels = mixedMoment B raw11963step1 raw11963step1Labels := by
      have ha : raw11963step1 = -raw11963step0 := by apply Matrix.ext; change ∀ i j, raw11963step1 i j = -(raw11963step0 i j); unfold raw11963step1 raw11963step0; decide +kernel
      have hl : raw11963step1Labels = raw11963step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11963step1 raw11963step1Labels = mixedMoment B raw11963step2 raw11963step2Labels := by
      have ha : raw11963step2 = raw11963step1 := by apply Matrix.ext; unfold raw11963step2 raw11963step1; decide +kernel
      have hl : raw11963step1Labels = labelEmbedding1 ∘ raw11963step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11963step1 raw11963step1Labels raw11963step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3342 node3342Labels := by rfl

def raw11964 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw11964Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11964step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, -1, 2]]
def raw11964step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11964step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11964step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11964step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 1, -2]]
def raw11964step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11964 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11964 raw11964Labels = mixedMoment B node3529 node3529Labels := by
  calc
    mixedMoment B raw11964 raw11964Labels = mixedMoment B raw11964step0 raw11964step0Labels := by
      have ha : raw11964step0 = (fun i j => raw11964 (permutation159 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11964step0 raw11964; decide +kernel
      have hl : raw11964step0Labels = raw11964Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11964 raw11964Labels permutation159 permutation5
    mixedMoment B raw11964step0 raw11964step0Labels = mixedMoment B raw11964step1 raw11964step1Labels := by
      have ha : raw11964step1 = -raw11964step0 := by apply Matrix.ext; change ∀ i j, raw11964step1 i j = -(raw11964step0 i j); unfold raw11964step1 raw11964step0; decide +kernel
      have hl : raw11964step1Labels = raw11964step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11964step1 raw11964step1Labels = mixedMoment B raw11964step2 raw11964step2Labels := by
      have ha : raw11964step2 = raw11964step1 := by apply Matrix.ext; unfold raw11964step2 raw11964step1; decide +kernel
      have hl : raw11964step1Labels = labelEmbedding1 ∘ raw11964step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11964step1 raw11964step1Labels raw11964step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3529 node3529Labels := by rfl

def raw11965 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw11965Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11965step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw11965step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11965step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11965step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11965step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![1, 0, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11965step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11965 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11965 raw11965Labels = mixedMoment B node3497 node3497Labels := by
  calc
    mixedMoment B raw11965 raw11965Labels = mixedMoment B raw11965step0 raw11965step0Labels := by
      have ha : raw11965step0 = (fun i j => raw11965 (permutation163 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11965step0 raw11965; decide +kernel
      have hl : raw11965step0Labels = raw11965Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11965 raw11965Labels permutation163 permutation5
    mixedMoment B raw11965step0 raw11965step0Labels = mixedMoment B raw11965step1 raw11965step1Labels := by
      have ha : raw11965step1 = -raw11965step0 := by apply Matrix.ext; change ∀ i j, raw11965step1 i j = -(raw11965step0 i j); unfold raw11965step1 raw11965step0; decide +kernel
      have hl : raw11965step1Labels = raw11965step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11965step1 raw11965step1Labels = mixedMoment B raw11965step2 raw11965step2Labels := by
      have ha : raw11965step2 = raw11965step1 := by apply Matrix.ext; unfold raw11965step2 raw11965step1; decide +kernel
      have hl : raw11965step1Labels = labelEmbedding1 ∘ raw11965step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11965step1 raw11965step1Labels raw11965step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3497 node3497Labels := by rfl

def raw11966 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![0, 0, 0]]
def raw11966Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11966step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1]]
def raw11966step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11966step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw11966step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11966step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11966step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11966step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw11966step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11966 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11966 raw11966Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw11966 raw11966Labels = mixedMoment B raw11966step0 raw11966step0Labels := by
      have hz : ∀ j, raw11966 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw11966step0 = (fun i j => raw11966 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw11966step0 raw11966; decide +kernel
      have hl : raw11966step0Labels = raw11966Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11966 raw11966Labels permutation590 hz
    mixedMoment B raw11966step0 raw11966step0Labels = mixedMoment B raw11966step1 raw11966step1Labels := by
      have ha : raw11966step1 = (fun i j => raw11966step0 (permutation35 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11966step1 raw11966step0; decide +kernel
      have hl : raw11966step1Labels = raw11966step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11966step0 raw11966step0Labels permutation35 permutation5
    mixedMoment B raw11966step1 raw11966step1Labels = mixedMoment B raw11966step2 raw11966step2Labels := by
      have ha : raw11966step2 = -raw11966step1 := by apply Matrix.ext; change ∀ i j, raw11966step2 i j = -(raw11966step1 i j); unfold raw11966step2 raw11966step1; decide +kernel
      have hl : raw11966step2Labels = raw11966step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11966step2 raw11966step2Labels = mixedMoment B raw11966step3 raw11966step3Labels := by
      have ha : raw11966step3 = raw11966step2 := by apply Matrix.ext; unfold raw11966step3 raw11966step2; decide +kernel
      have hl : raw11966step2Labels = labelEmbedding1 ∘ raw11966step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11966step2 raw11966step2Labels raw11966step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3535 node3535Labels := by rfl

def raw11967 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11967Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11967step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 1, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw11967step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11967step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw11967step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11967step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, -1, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw11967step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11967 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11967 raw11967Labels = mixedMoment B node1594 node1594Labels := by
  calc
    mixedMoment B raw11967 raw11967Labels = mixedMoment B raw11967step0 raw11967step0Labels := by
      have ha : raw11967step0 = (fun i j => raw11967 (permutation160 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11967step0 raw11967; decide +kernel
      have hl : raw11967step0Labels = raw11967Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11967 raw11967Labels permutation160 permutation5
    mixedMoment B raw11967step0 raw11967step0Labels = mixedMoment B raw11967step1 raw11967step1Labels := by
      have ha : raw11967step1 = -raw11967step0 := by apply Matrix.ext; change ∀ i j, raw11967step1 i j = -(raw11967step0 i j); unfold raw11967step1 raw11967step0; decide +kernel
      have hl : raw11967step1Labels = raw11967step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11967step1 raw11967step1Labels = mixedMoment B raw11967step2 raw11967step2Labels := by
      have ha : raw11967step2 = raw11967step1 := by apply Matrix.ext; unfold raw11967step2 raw11967step1; decide +kernel
      have hl : raw11967step1Labels = labelEmbedding1 ∘ raw11967step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11967step1 raw11967step1Labels raw11967step2Labels labelEmbedding1 hl
    _ = mixedMoment B node1594 node1594Labels := by rfl

def raw11968 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11968Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11968step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![2, -1, -1], ![0, -1, 1], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw11968step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11968step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw11968step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11968step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-2, 1, 1], ![0, 1, -1], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw11968step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11968 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11968 raw11968Labels = mixedMoment B node3337 node3337Labels := by
  calc
    mixedMoment B raw11968 raw11968Labels = mixedMoment B raw11968step0 raw11968step0Labels := by
      have ha : raw11968step0 = (fun i j => raw11968 (permutation160 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11968step0 raw11968; decide +kernel
      have hl : raw11968step0Labels = raw11968Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11968 raw11968Labels permutation160 permutation5
    mixedMoment B raw11968step0 raw11968step0Labels = mixedMoment B raw11968step1 raw11968step1Labels := by
      have ha : raw11968step1 = -raw11968step0 := by apply Matrix.ext; change ∀ i j, raw11968step1 i j = -(raw11968step0 i j); unfold raw11968step1 raw11968step0; decide +kernel
      have hl : raw11968step1Labels = raw11968step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11968step1 raw11968step1Labels = mixedMoment B raw11968step2 raw11968step2Labels := by
      have ha : raw11968step2 = raw11968step1 := by apply Matrix.ext; unfold raw11968step2 raw11968step1; decide +kernel
      have hl : raw11968step1Labels = labelEmbedding1 ∘ raw11968step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11968step1 raw11968step1Labels raw11968step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3337 node3337Labels := by rfl

def raw11969 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11969Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11969step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 2, -1], ![-2, 0, 2]]
def raw11969step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11969step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw11969step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11969step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, 0, -2]]
def raw11969step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11969 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11969 raw11969Labels = mixedMoment B node3524 node3524Labels := by
  calc
    mixedMoment B raw11969 raw11969Labels = mixedMoment B raw11969step0 raw11969step0Labels := by
      have ha : raw11969step0 = (fun i j => raw11969 (permutation160 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11969step0 raw11969; decide +kernel
      have hl : raw11969step0Labels = raw11969Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11969 raw11969Labels permutation160 permutation5
    mixedMoment B raw11969step0 raw11969step0Labels = mixedMoment B raw11969step1 raw11969step1Labels := by
      have ha : raw11969step1 = -raw11969step0 := by apply Matrix.ext; change ∀ i j, raw11969step1 i j = -(raw11969step0 i j); unfold raw11969step1 raw11969step0; decide +kernel
      have hl : raw11969step1Labels = raw11969step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11969step1 raw11969step1Labels = mixedMoment B raw11969step2 raw11969step2Labels := by
      have ha : raw11969step2 = raw11969step1 := by apply Matrix.ext; unfold raw11969step2 raw11969step1; decide +kernel
      have hl : raw11969step1Labels = labelEmbedding1 ∘ raw11969step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11969step1 raw11969step1Labels raw11969step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3524 node3524Labels := by rfl

def raw11970 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11970Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11970step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw11970step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11970step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw11970step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11970step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw11970step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11970 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11970 raw11970Labels = mixedMoment B node3488 node3488Labels := by
  calc
    mixedMoment B raw11970 raw11970Labels = mixedMoment B raw11970step0 raw11970step0Labels := by
      have ha : raw11970step0 = (fun i j => raw11970 (permutation160 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11970step0 raw11970; decide +kernel
      have hl : raw11970step0Labels = raw11970Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11970 raw11970Labels permutation160 permutation5
    mixedMoment B raw11970step0 raw11970step0Labels = mixedMoment B raw11970step1 raw11970step1Labels := by
      have ha : raw11970step1 = -raw11970step0 := by apply Matrix.ext; change ∀ i j, raw11970step1 i j = -(raw11970step0 i j); unfold raw11970step1 raw11970step0; decide +kernel
      have hl : raw11970step1Labels = raw11970step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11970step1 raw11970step1Labels = mixedMoment B raw11970step2 raw11970step2Labels := by
      have ha : raw11970step2 = raw11970step1 := by apply Matrix.ext; unfold raw11970step2 raw11970step1; decide +kernel
      have hl : raw11970step1Labels = labelEmbedding1 ∘ raw11970step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11970step1 raw11970step1Labels raw11970step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3488 node3488Labels := by rfl

def raw11971 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![2, -2, 0]]
def raw11971Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw11971step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 2, 0], ![-2, 0, 2]]
def raw11971step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11971step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw11971step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw11971step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -2, 0], ![2, 0, -2]]
def raw11971step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11971 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11971 raw11971Labels = mixedMoment B node3488 node3488Labels := by
  calc
    mixedMoment B raw11971 raw11971Labels = mixedMoment B raw11971step0 raw11971step0Labels := by
      have ha : raw11971step0 = (fun i j => raw11971 (permutation166 i) (permutation5 j)) := by apply Matrix.ext; unfold raw11971step0 raw11971; decide +kernel
      have hl : raw11971step0Labels = raw11971Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11971 raw11971Labels permutation166 permutation5
    mixedMoment B raw11971step0 raw11971step0Labels = mixedMoment B raw11971step1 raw11971step1Labels := by
      have ha : raw11971step1 = -raw11971step0 := by apply Matrix.ext; change ∀ i j, raw11971step1 i j = -(raw11971step0 i j); unfold raw11971step1 raw11971step0; decide +kernel
      have hl : raw11971step1Labels = raw11971step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw11971step1 raw11971step1Labels = mixedMoment B raw11971step2 raw11971step2Labels := by
      have ha : raw11971step2 = raw11971step1 := by apply Matrix.ext; unfold raw11971step2 raw11971step1; decide +kernel
      have hl : raw11971step1Labels = labelEmbedding1 ∘ raw11971step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11971step1 raw11971step1Labels raw11971step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3488 node3488Labels := by rfl

def raw11972 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11972Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11972step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11972step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11972 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11972 raw11972Labels = mixedMoment B node3037 node3037Labels := by
  calc
    mixedMoment B raw11972 raw11972Labels = mixedMoment B raw11972step0 raw11972step0Labels := by
      have ha : raw11972step0 = (fun i j => raw11972 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11972step0 raw11972; decide +kernel
      have hl : raw11972step0Labels = raw11972Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11972 raw11972Labels permutation180 permutation2
    _ = mixedMoment B node3037 node3037Labels := by rfl

def raw11973 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11973Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11973step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw11973step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11973 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11973 raw11973Labels = mixedMoment B node3846 node3846Labels := by
  calc
    mixedMoment B raw11973 raw11973Labels = mixedMoment B raw11973step0 raw11973step0Labels := by
      have ha : raw11973step0 = (fun i j => raw11973 (permutation426 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11973step0 raw11973; decide +kernel
      have hl : raw11973step0Labels = raw11973Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11973 raw11973Labels permutation426 permutation4
    _ = mixedMoment B node3846 node3846Labels := by rfl

def raw11974 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11974Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11974step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11974step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11974 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11974 raw11974Labels = mixedMoment B node3957 node3957Labels := by
  calc
    mixedMoment B raw11974 raw11974Labels = mixedMoment B raw11974step0 raw11974step0Labels := by
      have ha : raw11974step0 = (fun i j => raw11974 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11974step0 raw11974; decide +kernel
      have hl : raw11974step0Labels = raw11974Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11974 raw11974Labels permutation180 permutation2
    _ = mixedMoment B node3957 node3957Labels := by rfl

def raw11975 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11975Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11975step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11975step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11975 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11975 raw11975Labels = mixedMoment B node3849 node3849Labels := by
  calc
    mixedMoment B raw11975 raw11975Labels = mixedMoment B raw11975step0 raw11975step0Labels := by
      have ha : raw11975step0 = (fun i j => raw11975 (permutation428 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11975step0 raw11975; decide +kernel
      have hl : raw11975step0Labels = raw11975Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11975 raw11975Labels permutation428 permutation4
    _ = mixedMoment B node3849 node3849Labels := by rfl

def raw11976 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw11976Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11976step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw11976step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11976 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11976 raw11976Labels = mixedMoment B node3849 node3849Labels := by
  calc
    mixedMoment B raw11976 raw11976Labels = mixedMoment B raw11976step0 raw11976step0Labels := by
      have ha : raw11976step0 = (fun i j => raw11976 (permutation424 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11976step0 raw11976; decide +kernel
      have hl : raw11976step0Labels = raw11976Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11976 raw11976Labels permutation424 permutation4
    _ = mixedMoment B node3849 node3849Labels := by rfl

def raw11977 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw11977Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11977step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw11977step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11977step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw11977step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11977 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11977 raw11977Labels = mixedMoment B node3910 node3910Labels := by
  calc
    mixedMoment B raw11977 raw11977Labels = mixedMoment B raw11977step0 raw11977step0Labels := by
      have hz : ∀ j, raw11977 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw11977step0 = (fun i j => raw11977 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw11977step0 raw11977; decide +kernel
      have hl : raw11977step0Labels = raw11977Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11977 raw11977Labels permutation590 hz
    mixedMoment B raw11977step0 raw11977step0Labels = mixedMoment B raw11977step1 raw11977step1Labels := by
      have ha : raw11977step1 = (fun i j => raw11977step0 (permutation96 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11977step1 raw11977step0; decide +kernel
      have hl : raw11977step1Labels = raw11977step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11977step0 raw11977step0Labels permutation96 permutation4
    _ = mixedMoment B node3910 node3910Labels := by rfl

def raw11978 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-2, 2], ![1, -1], ![1, -1], ![0, 0]]
def raw11978Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11978step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![1, -1], ![-2, 2], ![1, -1], ![1, -1]]
def raw11978step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw11978step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw11978step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical11978 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11978 raw11978Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw11978 raw11978Labels = mixedMoment B raw11978step0 raw11978step0Labels := by
      have hz : ∀ j, raw11978 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw11978step0 = (fun i j => raw11978 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw11978step0 raw11978; decide +kernel
      have hl : raw11978step0Labels = raw11978Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11978 raw11978Labels permutation590 hz
    mixedMoment B raw11978step0 raw11978step0Labels = mixedMoment B raw11978step1 raw11978step1Labels := by
      have ha : raw11978step1 = (fun i j => raw11978step0 (permutation80 i) (permutation0 j)) := by apply Matrix.ext; unfold raw11978step1 raw11978step0; decide +kernel
      have hl : raw11978step1Labels = raw11978step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11978step0 raw11978step0Labels permutation80 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw11979 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![1, 0, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11979Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11979step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw11979step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11979 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11979 raw11979Labels = mixedMoment B node1366 node1366Labels := by
  calc
    mixedMoment B raw11979 raw11979Labels = mixedMoment B raw11979step0 raw11979step0Labels := by
      have ha : raw11979step0 = (fun i j => raw11979 (permutation194 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11979step0 raw11979; decide +kernel
      have hl : raw11979step0Labels = raw11979Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11979 raw11979Labels permutation194 permutation2
    _ = mixedMoment B node1366 node1366Labels := by rfl

def raw11980 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11980Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11980step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![1, -3, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11980step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11980 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11980 raw11980Labels = mixedMoment B node1421 node1421Labels := by
  calc
    mixedMoment B raw11980 raw11980Labels = mixedMoment B raw11980step0 raw11980step0Labels := by
      have ha : raw11980step0 = (fun i j => raw11980 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11980step0 raw11980; decide +kernel
      have hl : raw11980step0Labels = raw11980Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11980 raw11980Labels permutation156 permutation2
    _ = mixedMoment B node1421 node1421Labels := by rfl

def raw11981 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11981Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11981step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11981step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11981 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11981 raw11981Labels = mixedMoment B node1358 node1358Labels := by
  calc
    mixedMoment B raw11981 raw11981Labels = mixedMoment B raw11981step0 raw11981step0Labels := by
      have ha : raw11981step0 = (fun i j => raw11981 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11981step0 raw11981; decide +kernel
      have hl : raw11981step0Labels = raw11981Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11981 raw11981Labels permutation181 permutation2
    _ = mixedMoment B node1358 node1358Labels := by rfl

def raw11982 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw11982Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11982step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11982step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11982 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11982 raw11982Labels = mixedMoment B node1358 node1358Labels := by
  calc
    mixedMoment B raw11982 raw11982Labels = mixedMoment B raw11982step0 raw11982step0Labels := by
      have ha : raw11982step0 = (fun i j => raw11982 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11982step0 raw11982; decide +kernel
      have hl : raw11982step0Labels = raw11982Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11982 raw11982Labels permutation180 permutation2
    _ = mixedMoment B node1358 node1358Labels := by rfl

def raw11983 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, 1, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11983Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11983step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 3, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11983step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11983 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11983 raw11983Labels = mixedMoment B node1360 node1360Labels := by
  calc
    mixedMoment B raw11983 raw11983Labels = mixedMoment B raw11983step0 raw11983step0Labels := by
      have ha : raw11983step0 = (fun i j => raw11983 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11983step0 raw11983; decide +kernel
      have hl : raw11983step0Labels = raw11983Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11983 raw11983Labels permutation176 permutation2
    _ = mixedMoment B node1360 node1360Labels := by rfl

def raw11984 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11984Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11984step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw11984step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11984 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11984 raw11984Labels = mixedMoment B node2880 node2880Labels := by
  calc
    mixedMoment B raw11984 raw11984Labels = mixedMoment B raw11984step0 raw11984step0Labels := by
      have ha : raw11984step0 = (fun i j => raw11984 (permutation194 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11984step0 raw11984; decide +kernel
      have hl : raw11984step0Labels = raw11984Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11984 raw11984Labels permutation194 permutation2
    _ = mixedMoment B node2880 node2880Labels := by rfl

def raw11985 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11985Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11985step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11985step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11985 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11985 raw11985Labels = mixedMoment B node3037 node3037Labels := by
  calc
    mixedMoment B raw11985 raw11985Labels = mixedMoment B raw11985step0 raw11985step0Labels := by
      have ha : raw11985step0 = (fun i j => raw11985 (permutation186 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11985step0 raw11985; decide +kernel
      have hl : raw11985step0Labels = raw11985Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11985 raw11985Labels permutation186 permutation2
    _ = mixedMoment B node3037 node3037Labels := by rfl

def raw11986 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![1, -1, 0]]
def raw11986Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11986step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11986step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11986 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11986 raw11986Labels = mixedMoment B node3037 node3037Labels := by
  calc
    mixedMoment B raw11986 raw11986Labels = mixedMoment B raw11986step0 raw11986step0Labels := by
      have ha : raw11986step0 = (fun i j => raw11986 (permutation192 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11986step0 raw11986; decide +kernel
      have hl : raw11986step0Labels = raw11986Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11986 raw11986Labels permutation192 permutation2
    _ = mixedMoment B node3037 node3037Labels := by rfl

def raw11987 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![0, 0, 0]]
def raw11987Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11987step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![1, 0, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1]]
def raw11987step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11987step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw11987step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11987 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11987 raw11987Labels = mixedMoment B node3053 node3053Labels := by
  calc
    mixedMoment B raw11987 raw11987Labels = mixedMoment B raw11987step0 raw11987step0Labels := by
      have hz : ∀ j, raw11987 (permutation590 0) j = 0 := by decide +kernel
      have ha : raw11987step0 = (fun i j => raw11987 (permutation590 i.succ) j) := by apply Matrix.ext; unfold raw11987step0 raw11987; decide +kernel
      have hl : raw11987step0Labels = raw11987Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw11987 raw11987Labels permutation590 hz
    mixedMoment B raw11987step0 raw11987step0Labels = mixedMoment B raw11987step1 raw11987step1Labels := by
      have ha : raw11987step1 = (fun i j => raw11987step0 (permutation38 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11987step1 raw11987step0; decide +kernel
      have hl : raw11987step1Labels = raw11987step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11987step0 raw11987step0Labels permutation38 permutation2
    _ = mixedMoment B node3053 node3053Labels := by rfl

def raw11988 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11988Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11988step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, -1, -1]]
def raw11988step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11988 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11988 raw11988Labels = mixedMoment B node2564 node2564Labels := by
  calc
    mixedMoment B raw11988 raw11988Labels = mixedMoment B raw11988step0 raw11988step0Labels := by
      have ha : raw11988step0 = (fun i j => raw11988 (permutation426 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11988step0 raw11988; decide +kernel
      have hl : raw11988step0Labels = raw11988Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11988 raw11988Labels permutation426 permutation4
    _ = mixedMoment B node2564 node2564Labels := by rfl

def raw11989 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11989Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11989step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11989step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11989 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11989 raw11989Labels = mixedMoment B node3008 node3008Labels := by
  calc
    mixedMoment B raw11989 raw11989Labels = mixedMoment B raw11989step0 raw11989step0Labels := by
      have ha : raw11989step0 = (fun i j => raw11989 (permutation157 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11989step0 raw11989; decide +kernel
      have hl : raw11989step0Labels = raw11989Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11989 raw11989Labels permutation157 permutation2
    _ = mixedMoment B node3008 node3008Labels := by rfl

def raw11990 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw11990Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11990step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11990step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11990 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11990 raw11990Labels = mixedMoment B node3008 node3008Labels := by
  calc
    mixedMoment B raw11990 raw11990Labels = mixedMoment B raw11990step0 raw11990step0Labels := by
      have ha : raw11990step0 = (fun i j => raw11990 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11990step0 raw11990; decide +kernel
      have hl : raw11990step0Labels = raw11990Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11990 raw11990Labels permutation156 permutation2
    _ = mixedMoment B node3008 node3008Labels := by rfl

def raw11991 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 2, -1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11991Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11991 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11991 raw11991Labels = mixedMoment B node3009 node3009Labels := by
  calc
    _ = mixedMoment B node3009 node3009Labels := by rfl

def raw11992 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, -1, 2], ![2, -1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11992Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11992step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11992step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11992 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11992 raw11992Labels = mixedMoment B node2862 node2862Labels := by
  calc
    mixedMoment B raw11992 raw11992Labels = mixedMoment B raw11992step0 raw11992step0Labels := by
      have ha : raw11992step0 = (fun i j => raw11992 (permutation181 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11992step0 raw11992; decide +kernel
      have hl : raw11992step0Labels = raw11992Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11992 raw11992Labels permutation181 permutation2
    _ = mixedMoment B node2862 node2862Labels := by rfl

def raw11993 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, -1, 2], ![1, 0, -1], ![2, -1, -1], ![1, -1, 0]]
def raw11993Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11993step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw11993step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11993 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11993 raw11993Labels = mixedMoment B node2862 node2862Labels := by
  calc
    mixedMoment B raw11993 raw11993Labels = mixedMoment B raw11993step0 raw11993step0Labels := by
      have ha : raw11993step0 = (fun i j => raw11993 (permutation180 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11993step0 raw11993; decide +kernel
      have hl : raw11993step0Labels = raw11993Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11993 raw11993Labels permutation180 permutation2
    _ = mixedMoment B node2862 node2862Labels := by rfl

def raw11994 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11994Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11994step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11994step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11994 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11994 raw11994Labels = mixedMoment B node2864 node2864Labels := by
  calc
    mixedMoment B raw11994 raw11994Labels = mixedMoment B raw11994step0 raw11994step0Labels := by
      have ha : raw11994step0 = (fun i j => raw11994 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11994step0 raw11994; decide +kernel
      have hl : raw11994step0Labels = raw11994Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11994 raw11994Labels permutation176 permutation2
    _ = mixedMoment B node2864 node2864Labels := by rfl

def raw11995 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![1, -3, 2], ![0, 1, -1], ![1, 0, -1], ![1, -1, 0]]
def raw11995Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11995step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -3, 1]]
def raw11995step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11995 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11995 raw11995Labels = mixedMoment B node2573 node2573Labels := by
  calc
    mixedMoment B raw11995 raw11995Labels = mixedMoment B raw11995step0 raw11995step0Labels := by
      have ha : raw11995step0 = (fun i j => raw11995 (permutation431 i) (permutation4 j)) := by apply Matrix.ext; unfold raw11995step0 raw11995; decide +kernel
      have hl : raw11995step0Labels = raw11995Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11995 raw11995Labels permutation431 permutation4
    _ = mixedMoment B node2573 node2573Labels := by rfl

def raw11996 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![0, 1, -1], ![2, -1, -1], ![1, -1, 0]]
def raw11996Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11996step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw11996step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11996 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11996 raw11996Labels = mixedMoment B node3029 node3029Labels := by
  calc
    mixedMoment B raw11996 raw11996Labels = mixedMoment B raw11996step0 raw11996step0Labels := by
      have ha : raw11996step0 = (fun i j => raw11996 (permutation177 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11996step0 raw11996; decide +kernel
      have hl : raw11996step0Labels = raw11996Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11996 raw11996Labels permutation177 permutation2
    _ = mixedMoment B node3029 node3029Labels := by rfl

def raw11997 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 1, -1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11997Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw11997step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw11997step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical11997 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11997 raw11997Labels = mixedMoment B node3030 node3030Labels := by
  calc
    mixedMoment B raw11997 raw11997Labels = mixedMoment B raw11997step0 raw11997step0Labels := by
      have ha : raw11997step0 = (fun i j => raw11997 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw11997step0 raw11997; decide +kernel
      have hl : raw11997step0Labels = raw11997Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11997 raw11997Labels permutation176 permutation2
    _ = mixedMoment B node3030 node3030Labels := by rfl

def raw11998 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw11998Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11998step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11998step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11998step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw11998step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11998 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11998 raw11998Labels = mixedMoment B node5231 node5231Labels := by
  calc
    mixedMoment B raw11998 raw11998Labels = mixedMoment B raw11998step0 raw11998step0Labels := by
      have ha : raw11998step0 = (fun i j => raw11998 (permutation180 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11998step0 raw11998; decide +kernel
      have hl : raw11998step0Labels = raw11998Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11998 raw11998Labels permutation180 permutation7
    mixedMoment B raw11998step0 raw11998step0Labels = mixedMoment B raw11998step1 raw11998step1Labels := by
      have ha : raw11998step1 = raw11998step0 := by apply Matrix.ext; unfold raw11998step1 raw11998step0; decide +kernel
      have hl : raw11998step0Labels = labelEmbedding10 ∘ raw11998step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11998step0 raw11998step0Labels raw11998step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5231 node5231Labels := by rfl

def raw11999 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw11999Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw11999step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11999step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw11999step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw11999step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical11999 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw11999 raw11999Labels = mixedMoment B node5226 node5226Labels := by
  calc
    mixedMoment B raw11999 raw11999Labels = mixedMoment B raw11999step0 raw11999step0Labels := by
      have ha : raw11999step0 = (fun i j => raw11999 (permutation181 i) (permutation7 j)) := by apply Matrix.ext; unfold raw11999step0 raw11999; decide +kernel
      have hl : raw11999step0Labels = raw11999Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw11999 raw11999Labels permutation181 permutation7
    mixedMoment B raw11999step0 raw11999step0Labels = mixedMoment B raw11999step1 raw11999step1Labels := by
      have ha : raw11999step1 = raw11999step0 := by apply Matrix.ext; unfold raw11999step1 raw11999step0; decide +kernel
      have hl : raw11999step0Labels = labelEmbedding10 ∘ raw11999step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw11999step0 raw11999step0Labels raw11999step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5226 node5226Labels := by rfl

def raw12000 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12000Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12000step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12000step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw12000step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw12000step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12000 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12000 raw12000Labels = mixedMoment B node5226 node5226Labels := by
  calc
    mixedMoment B raw12000 raw12000Labels = mixedMoment B raw12000step0 raw12000step0Labels := by
      have ha : raw12000step0 = (fun i j => raw12000 (permutation180 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12000step0 raw12000; decide +kernel
      have hl : raw12000step0Labels = raw12000Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12000 raw12000Labels permutation180 permutation7
    mixedMoment B raw12000step0 raw12000step0Labels = mixedMoment B raw12000step1 raw12000step1Labels := by
      have ha : raw12000step1 = raw12000step0 := by apply Matrix.ext; unfold raw12000step1 raw12000step0; decide +kernel
      have hl : raw12000step0Labels = labelEmbedding10 ∘ raw12000step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12000step0 raw12000step0Labels raw12000step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5226 node5226Labels := by rfl

def raw12001 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12001Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12001step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12001step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw12001step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw12001step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12001 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12001 raw12001Labels = mixedMoment B node5227 node5227Labels := by
  calc
    mixedMoment B raw12001 raw12001Labels = mixedMoment B raw12001step0 raw12001step0Labels := by
      have ha : raw12001step0 = (fun i j => raw12001 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw12001step0 raw12001; decide +kernel
      have hl : raw12001step0Labels = raw12001Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12001 raw12001Labels permutation176 permutation7
    mixedMoment B raw12001step0 raw12001step0Labels = mixedMoment B raw12001step1 raw12001step1Labels := by
      have ha : raw12001step1 = raw12001step0 := by apply Matrix.ext; unfold raw12001step1 raw12001step0; decide +kernel
      have hl : raw12001step0Labels = labelEmbedding10 ∘ raw12001step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12001step0 raw12001step0Labels raw12001step1Labels labelEmbedding10 hl
    _ = mixedMoment B node5227 node5227Labels := by rfl

def raw12002 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12002Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12002step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12002step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12002step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12002step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12002step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12002step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12002step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12002step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12002 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12002 raw12002Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw12002 raw12002Labels = mixedMoment B raw12002step0 raw12002step0Labels := by
      have hz : ∀ j, raw12002 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12002step0 = (fun i j => raw12002 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12002step0 raw12002; decide +kernel
      have hl : raw12002step0Labels = raw12002Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12002 raw12002Labels permutation265 hz
    mixedMoment B raw12002step0 raw12002step0Labels = mixedMoment B raw12002step1 raw12002step1Labels := by
      have ha : raw12002step1 = (fun i j => raw12002step0 (permutation41 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12002step1 raw12002step0; decide +kernel
      have hl : raw12002step1Labels = raw12002step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12002step0 raw12002step0Labels permutation41 permutation4
    mixedMoment B raw12002step1 raw12002step1Labels = mixedMoment B raw12002step2 raw12002step2Labels := by
      have ha : raw12002step2 = -raw12002step1 := by apply Matrix.ext; change ∀ i j, raw12002step2 i j = -(raw12002step1 i j); unfold raw12002step2 raw12002step1; decide +kernel
      have hl : raw12002step2Labels = raw12002step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12002step2 raw12002step2Labels = mixedMoment B raw12002step3 raw12002step3Labels := by
      have ha : raw12002step3 = raw12002step2 := by apply Matrix.ext; unfold raw12002step3 raw12002step2; decide +kernel
      have hl : raw12002step2Labels = labelEmbedding7 ∘ raw12002step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12002step2 raw12002step2Labels raw12002step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

def raw12003 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12003Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12003step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12003step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12003step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12003step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12003step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12003step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12003 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12003 raw12003Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw12003 raw12003Labels = mixedMoment B raw12003step0 raw12003step0Labels := by
      have hz : ∀ j, raw12003 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12003step0 = (fun i j => raw12003 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12003step0 raw12003; decide +kernel
      have hl : raw12003step0Labels = raw12003Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12003 raw12003Labels permutation265 hz
    mixedMoment B raw12003step0 raw12003step0Labels = mixedMoment B raw12003step1 raw12003step1Labels := by
      have ha : raw12003step1 = (fun i j => raw12003step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12003step1 raw12003step0; decide +kernel
      have hl : raw12003step1Labels = raw12003step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12003step0 raw12003step0Labels permutation32 permutation6
    mixedMoment B raw12003step1 raw12003step1Labels = mixedMoment B raw12003step2 raw12003step2Labels := by
      have ha : raw12003step2 = raw12003step1 := by apply Matrix.ext; unfold raw12003step2 raw12003step1; decide +kernel
      have hl : raw12003step1Labels = labelEmbedding9 ∘ raw12003step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12003step1 raw12003step1Labels raw12003step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw12004 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12004Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12004step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12004step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12004step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12004step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12004step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12004step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12004 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12004 raw12004Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw12004 raw12004Labels = mixedMoment B raw12004step0 raw12004step0Labels := by
      have hz : ∀ j, raw12004 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12004step0 = (fun i j => raw12004 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12004step0 raw12004; decide +kernel
      have hl : raw12004step0Labels = raw12004Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12004 raw12004Labels permutation265 hz
    mixedMoment B raw12004step0 raw12004step0Labels = mixedMoment B raw12004step1 raw12004step1Labels := by
      have ha : raw12004step1 = (fun i j => raw12004step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12004step1 raw12004step0; decide +kernel
      have hl : raw12004step1Labels = raw12004step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12004step0 raw12004step0Labels permutation34 permutation6
    mixedMoment B raw12004step1 raw12004step1Labels = mixedMoment B raw12004step2 raw12004step2Labels := by
      have ha : raw12004step2 = raw12004step1 := by apply Matrix.ext; unfold raw12004step2 raw12004step1; decide +kernel
      have hl : raw12004step1Labels = labelEmbedding9 ∘ raw12004step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12004step1 raw12004step1Labels raw12004step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw12005 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12005Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12005step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12005step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12005step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12005step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12005step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12005step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12005 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12005 raw12005Labels = mixedMoment B node5301 node5301Labels := by
  calc
    mixedMoment B raw12005 raw12005Labels = mixedMoment B raw12005step0 raw12005step0Labels := by
      have hz : ∀ j, raw12005 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12005step0 = (fun i j => raw12005 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12005step0 raw12005; decide +kernel
      have hl : raw12005step0Labels = raw12005Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12005 raw12005Labels permutation265 hz
    mixedMoment B raw12005step0 raw12005step0Labels = mixedMoment B raw12005step1 raw12005step1Labels := by
      have ha : raw12005step1 = (fun i j => raw12005step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12005step1 raw12005step0; decide +kernel
      have hl : raw12005step1Labels = raw12005step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12005step0 raw12005step0Labels permutation32 permutation6
    mixedMoment B raw12005step1 raw12005step1Labels = mixedMoment B raw12005step2 raw12005step2Labels := by
      have ha : raw12005step2 = raw12005step1 := by apply Matrix.ext; unfold raw12005step2 raw12005step1; decide +kernel
      have hl : raw12005step1Labels = labelEmbedding9 ∘ raw12005step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12005step1 raw12005step1Labels raw12005step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5301 node5301Labels := by rfl

def raw12006 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12006Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12006step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-3, 3, 0]]
def raw12006step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12006step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw12006step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12006step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![3, -3, 0]]
def raw12006step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12006 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12006 raw12006Labels = mixedMoment B node4793 node4793Labels := by
  calc
    mixedMoment B raw12006 raw12006Labels = mixedMoment B raw12006step0 raw12006step0Labels := by
      have ha : raw12006step0 = (fun i j => raw12006 (permutation161 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12006step0 raw12006; decide +kernel
      have hl : raw12006step0Labels = raw12006Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12006 raw12006Labels permutation161 permutation4
    mixedMoment B raw12006step0 raw12006step0Labels = mixedMoment B raw12006step1 raw12006step1Labels := by
      have ha : raw12006step1 = -raw12006step0 := by apply Matrix.ext; change ∀ i j, raw12006step1 i j = -(raw12006step0 i j); unfold raw12006step1 raw12006step0; decide +kernel
      have hl : raw12006step1Labels = raw12006step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12006step1 raw12006step1Labels = mixedMoment B raw12006step2 raw12006step2Labels := by
      have ha : raw12006step2 = raw12006step1 := by apply Matrix.ext; unfold raw12006step2 raw12006step1; decide +kernel
      have hl : raw12006step1Labels = labelEmbedding7 ∘ raw12006step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12006step1 raw12006step1Labels raw12006step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4793 node4793Labels := by rfl

def raw12007 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12007Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12007step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw12007step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw12007step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![2, 0, -2]]
def raw12007step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12007 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12007 raw12007Labels = mixedMoment B node4794 node4794Labels := by
  calc
    mixedMoment B raw12007 raw12007Labels = mixedMoment B raw12007step0 raw12007step0Labels := by
      have ha : raw12007step0 = (fun i j => raw12007 (permutation426 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12007step0 raw12007; decide +kernel
      have hl : raw12007step0Labels = raw12007Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12007 raw12007Labels permutation426 permutation5
    mixedMoment B raw12007step0 raw12007step0Labels = mixedMoment B raw12007step1 raw12007step1Labels := by
      have ha : raw12007step1 = raw12007step0 := by apply Matrix.ext; unfold raw12007step1 raw12007step0; decide +kernel
      have hl : raw12007step0Labels = labelEmbedding8 ∘ raw12007step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12007step0 raw12007step0Labels raw12007step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4794 node4794Labels := by rfl

def raw12008 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12008Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12008step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw12008step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw12008step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw12008step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12008 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12008 raw12008Labels = mixedMoment B node4806 node4806Labels := by
  calc
    mixedMoment B raw12008 raw12008Labels = mixedMoment B raw12008step0 raw12008step0Labels := by
      have ha : raw12008step0 = (fun i j => raw12008 (permutation431 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12008step0 raw12008; decide +kernel
      have hl : raw12008step0Labels = raw12008Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12008 raw12008Labels permutation431 permutation5
    mixedMoment B raw12008step0 raw12008step0Labels = mixedMoment B raw12008step1 raw12008step1Labels := by
      have ha : raw12008step1 = raw12008step0 := by apply Matrix.ext; unfold raw12008step1 raw12008step0; decide +kernel
      have hl : raw12008step0Labels = labelEmbedding8 ∘ raw12008step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12008step0 raw12008step0Labels raw12008step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4806 node4806Labels := by rfl

def raw12009 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12009Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12009step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw12009step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw12009step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 1, -2], ![2, -3, 1]]
def raw12009step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12009 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12009 raw12009Labels = mixedMoment B node4806 node4806Labels := by
  calc
    mixedMoment B raw12009 raw12009Labels = mixedMoment B raw12009step0 raw12009step0Labels := by
      have ha : raw12009step0 = (fun i j => raw12009 (permutation425 i) (permutation5 j)) := by apply Matrix.ext; unfold raw12009step0 raw12009; decide +kernel
      have hl : raw12009step0Labels = raw12009Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12009 raw12009Labels permutation425 permutation5
    mixedMoment B raw12009step0 raw12009step0Labels = mixedMoment B raw12009step1 raw12009step1Labels := by
      have ha : raw12009step1 = raw12009step0 := by apply Matrix.ext; unfold raw12009step1 raw12009step0; decide +kernel
      have hl : raw12009step0Labels = labelEmbedding8 ∘ raw12009step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12009step0 raw12009step0Labels raw12009step1Labels labelEmbedding8 hl
    _ = mixedMoment B node4806 node4806Labels := by rfl

def raw12010 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12010Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12010step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw12010step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12010step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12010step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw12010step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12010step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12010 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12010 raw12010Labels = mixedMoment B node4878 node4878Labels := by
  calc
    mixedMoment B raw12010 raw12010Labels = mixedMoment B raw12010step0 raw12010step0Labels := by
      have ha : raw12010step0 = (fun i j => raw12010 (permutation355 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12010step0 raw12010; decide +kernel
      have hl : raw12010step0Labels = raw12010Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12010 raw12010Labels permutation355 permutation3
    mixedMoment B raw12010step0 raw12010step0Labels = mixedMoment B raw12010step1 raw12010step1Labels := by
      have ha : raw12010step1 = -raw12010step0 := by apply Matrix.ext; change ∀ i j, raw12010step1 i j = -(raw12010step0 i j); unfold raw12010step1 raw12010step0; decide +kernel
      have hl : raw12010step1Labels = raw12010step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12010step1 raw12010step1Labels = mixedMoment B raw12010step2 raw12010step2Labels := by
      have ha : raw12010step2 = raw12010step1 := by apply Matrix.ext; unfold raw12010step2 raw12010step1; decide +kernel
      have hl : raw12010step1Labels = labelEmbedding6 ∘ raw12010step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12010step1 raw12010step1Labels raw12010step2Labels labelEmbedding6 hl
    _ = mixedMoment B node4878 node4878Labels := by rfl

def raw12011 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12011Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12011step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12011step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12011step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12011step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12011step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12011step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12011 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12011 raw12011Labels = mixedMoment B node4805 node4805Labels := by
  calc
    mixedMoment B raw12011 raw12011Labels = mixedMoment B raw12011step0 raw12011step0Labels := by
      have ha : raw12011step0 = (fun i j => raw12011 (permutation167 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12011step0 raw12011; decide +kernel
      have hl : raw12011step0Labels = raw12011Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12011 raw12011Labels permutation167 permutation4
    mixedMoment B raw12011step0 raw12011step0Labels = mixedMoment B raw12011step1 raw12011step1Labels := by
      have ha : raw12011step1 = -raw12011step0 := by apply Matrix.ext; change ∀ i j, raw12011step1 i j = -(raw12011step0 i j); unfold raw12011step1 raw12011step0; decide +kernel
      have hl : raw12011step1Labels = raw12011step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12011step1 raw12011step1Labels = mixedMoment B raw12011step2 raw12011step2Labels := by
      have ha : raw12011step2 = raw12011step1 := by apply Matrix.ext; unfold raw12011step2 raw12011step1; decide +kernel
      have hl : raw12011step1Labels = labelEmbedding7 ∘ raw12011step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12011step1 raw12011step1Labels raw12011step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4805 node4805Labels := by rfl

def raw12012 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12012Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12012step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12012step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12012step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12012step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12012 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12012 raw12012Labels = mixedMoment B node5231 node5231Labels := by
  calc
    mixedMoment B raw12012 raw12012Labels = mixedMoment B raw12012step0 raw12012step0Labels := by
      have ha : raw12012step0 = (fun i j => raw12012 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12012step0 raw12012; decide +kernel
      have hl : raw12012step0Labels = raw12012Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12012 raw12012Labels permutation154 permutation6
    mixedMoment B raw12012step0 raw12012step0Labels = mixedMoment B raw12012step1 raw12012step1Labels := by
      have ha : raw12012step1 = raw12012step0 := by apply Matrix.ext; unfold raw12012step1 raw12012step0; decide +kernel
      have hl : raw12012step0Labels = labelEmbedding9 ∘ raw12012step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12012step0 raw12012step0Labels raw12012step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5231 node5231Labels := by rfl

def raw12013 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12013Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12013step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12013step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12013step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12013step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12013 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12013 raw12013Labels = mixedMoment B node5263 node5263Labels := by
  calc
    mixedMoment B raw12013 raw12013Labels = mixedMoment B raw12013step0 raw12013step0Labels := by
      have ha : raw12013step0 = (fun i j => raw12013 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12013step0 raw12013; decide +kernel
      have hl : raw12013step0Labels = raw12013Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12013 raw12013Labels permutation154 permutation6
    mixedMoment B raw12013step0 raw12013step0Labels = mixedMoment B raw12013step1 raw12013step1Labels := by
      have ha : raw12013step1 = raw12013step0 := by apply Matrix.ext; unfold raw12013step1 raw12013step0; decide +kernel
      have hl : raw12013step0Labels = labelEmbedding9 ∘ raw12013step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12013step0 raw12013step0Labels raw12013step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5263 node5263Labels := by rfl

def raw12014 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12014Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12014step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12014step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12014step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12014step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12014 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12014 raw12014Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw12014 raw12014Labels = mixedMoment B raw12014step0 raw12014step0Labels := by
      have ha : raw12014step0 = (fun i j => raw12014 (permutation155 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12014step0 raw12014; decide +kernel
      have hl : raw12014step0Labels = raw12014Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12014 raw12014Labels permutation155 permutation6
    mixedMoment B raw12014step0 raw12014step0Labels = mixedMoment B raw12014step1 raw12014step1Labels := by
      have ha : raw12014step1 = raw12014step0 := by apply Matrix.ext; unfold raw12014step1 raw12014step0; decide +kernel
      have hl : raw12014step0Labels = labelEmbedding9 ∘ raw12014step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12014step0 raw12014step0Labels raw12014step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

def raw12015 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12015Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12015step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw12015step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12015step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12015step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw12015step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1], ![2, -2, 0]]
def raw12015step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12015 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12015 raw12015Labels = mixedMoment B node4805 node4805Labels := by
  calc
    mixedMoment B raw12015 raw12015Labels = mixedMoment B raw12015step0 raw12015step0Labels := by
      have ha : raw12015step0 = (fun i j => raw12015 (permutation161 i) (permutation4 j)) := by apply Matrix.ext; unfold raw12015step0 raw12015; decide +kernel
      have hl : raw12015step0Labels = raw12015Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12015 raw12015Labels permutation161 permutation4
    mixedMoment B raw12015step0 raw12015step0Labels = mixedMoment B raw12015step1 raw12015step1Labels := by
      have ha : raw12015step1 = -raw12015step0 := by apply Matrix.ext; change ∀ i j, raw12015step1 i j = -(raw12015step0 i j); unfold raw12015step1 raw12015step0; decide +kernel
      have hl : raw12015step1Labels = raw12015step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw12015step1 raw12015step1Labels = mixedMoment B raw12015step2 raw12015step2Labels := by
      have ha : raw12015step2 = raw12015step1 := by apply Matrix.ext; unfold raw12015step2 raw12015step1; decide +kernel
      have hl : raw12015step1Labels = labelEmbedding7 ∘ raw12015step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12015step1 raw12015step1Labels raw12015step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4805 node4805Labels := by rfl

def raw12016 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12016Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12016step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12016step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12016step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw12016step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12016 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12016 raw12016Labels = mixedMoment B node5231 node5231Labels := by
  calc
    mixedMoment B raw12016 raw12016Labels = mixedMoment B raw12016step0 raw12016step0Labels := by
      have ha : raw12016step0 = (fun i j => raw12016 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12016step0 raw12016; decide +kernel
      have hl : raw12016step0Labels = raw12016Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12016 raw12016Labels permutation152 permutation6
    mixedMoment B raw12016step0 raw12016step0Labels = mixedMoment B raw12016step1 raw12016step1Labels := by
      have ha : raw12016step1 = raw12016step0 := by apply Matrix.ext; unfold raw12016step1 raw12016step0; decide +kernel
      have hl : raw12016step0Labels = labelEmbedding9 ∘ raw12016step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12016step0 raw12016step0Labels raw12016step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5231 node5231Labels := by rfl

def raw12017 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![0, -1, 1], ![0, -1, 1]]
def raw12017Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12017step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12017step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12017step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw12017step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12017 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12017 raw12017Labels = mixedMoment B node5263 node5263Labels := by
  calc
    mixedMoment B raw12017 raw12017Labels = mixedMoment B raw12017step0 raw12017step0Labels := by
      have ha : raw12017step0 = (fun i j => raw12017 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12017step0 raw12017; decide +kernel
      have hl : raw12017step0Labels = raw12017Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12017 raw12017Labels permutation152 permutation6
    mixedMoment B raw12017step0 raw12017step0Labels = mixedMoment B raw12017step1 raw12017step1Labels := by
      have ha : raw12017step1 = raw12017step0 := by apply Matrix.ext; unfold raw12017step1 raw12017step0; decide +kernel
      have hl : raw12017step0Labels = labelEmbedding9 ∘ raw12017step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12017step0 raw12017step0Labels raw12017step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5263 node5263Labels := by rfl

def raw12018 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw12018Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12018step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12018step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12018step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12018step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12018 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12018 raw12018Labels = mixedMoment B node5265 node5265Labels := by
  calc
    mixedMoment B raw12018 raw12018Labels = mixedMoment B raw12018step0 raw12018step0Labels := by
      have ha : raw12018step0 = (fun i j => raw12018 (permutation153 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12018step0 raw12018; decide +kernel
      have hl : raw12018step0Labels = raw12018Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12018 raw12018Labels permutation153 permutation6
    mixedMoment B raw12018step0 raw12018step0Labels = mixedMoment B raw12018step1 raw12018step1Labels := by
      have ha : raw12018step1 = raw12018step0 := by apply Matrix.ext; unfold raw12018step1 raw12018step0; decide +kernel
      have hl : raw12018step0Labels = labelEmbedding9 ∘ raw12018step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12018step0 raw12018step0Labels raw12018step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5265 node5265Labels := by rfl

def raw12019 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![1, -2, 1]]
def raw12019Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw12019step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12019step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw12019step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw12019step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical12019 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12019 raw12019Labels = mixedMoment B node5256 node5256Labels := by
  calc
    mixedMoment B raw12019 raw12019Labels = mixedMoment B raw12019step0 raw12019step0Labels := by
      have ha : raw12019step0 = (fun i j => raw12019 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12019step0 raw12019; decide +kernel
      have hl : raw12019step0Labels = raw12019Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12019 raw12019Labels permutation152 permutation6
    mixedMoment B raw12019step0 raw12019step0Labels = mixedMoment B raw12019step1 raw12019step1Labels := by
      have ha : raw12019step1 = raw12019step0 := by apply Matrix.ext; unfold raw12019step1 raw12019step0; decide +kernel
      have hl : raw12019step0Labels = labelEmbedding9 ∘ raw12019step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw12019step0 raw12019step0Labels raw12019step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5256 node5256Labels := by rfl

def raw12020 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-2, 2, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12020Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12020step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12020step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12020 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12020 raw12020Labels = mixedMoment B node3043 node3043Labels := by
  calc
    mixedMoment B raw12020 raw12020Labels = mixedMoment B raw12020step0 raw12020step0Labels := by
      have ha : raw12020step0 = (fun i j => raw12020 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12020step0 raw12020; decide +kernel
      have hl : raw12020step0Labels = raw12020Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12020 raw12020Labels permutation152 permutation6
    _ = mixedMoment B node3043 node3043Labels := by rfl

def raw12021 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12021Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12021step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12021step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12021 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12021 raw12021Labels = mixedMoment B node3091 node3091Labels := by
  calc
    mixedMoment B raw12021 raw12021Labels = mixedMoment B raw12021step0 raw12021step0Labels := by
      have ha : raw12021step0 = (fun i j => raw12021 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12021step0 raw12021; decide +kernel
      have hl : raw12021step0Labels = raw12021Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12021 raw12021Labels permutation152 permutation6
    _ = mixedMoment B node3091 node3091Labels := by rfl

def raw12022 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12022Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12022step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12022step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12022 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12022 raw12022Labels = mixedMoment B node3091 node3091Labels := by
  calc
    mixedMoment B raw12022 raw12022Labels = mixedMoment B raw12022step0 raw12022step0Labels := by
      have ha : raw12022step0 = (fun i j => raw12022 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12022step0 raw12022; decide +kernel
      have hl : raw12022step0Labels = raw12022Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12022 raw12022Labels permutation154 permutation6
    _ = mixedMoment B node3091 node3091Labels := by rfl

def raw12023 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![-1, 1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12023Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12023step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12023step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12023 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12023 raw12023Labels = mixedMoment B node3093 node3093Labels := by
  calc
    mixedMoment B raw12023 raw12023Labels = mixedMoment B raw12023step0 raw12023step0Labels := by
      have ha : raw12023step0 = (fun i j => raw12023 (permutation152 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12023step0 raw12023; decide +kernel
      have hl : raw12023step0Labels = raw12023Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12023 raw12023Labels permutation152 permutation6
    _ = mixedMoment B node3093 node3093Labels := by rfl

def raw12024 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12024Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12024step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12024step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12024step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12024step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12024 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12024 raw12024Labels = mixedMoment B node2277 node2277Labels := by
  calc
    mixedMoment B raw12024 raw12024Labels = mixedMoment B raw12024step0 raw12024step0Labels := by
      have hz : ∀ j, raw12024 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12024step0 = (fun i j => raw12024 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12024step0 raw12024; decide +kernel
      have hl : raw12024step0Labels = raw12024Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12024 raw12024Labels permutation265 hz
    mixedMoment B raw12024step0 raw12024step0Labels = mixedMoment B raw12024step1 raw12024step1Labels := by
      have ha : raw12024step1 = (fun i j => raw12024step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12024step1 raw12024step0; decide +kernel
      have hl : raw12024step1Labels = raw12024step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12024step0 raw12024step0Labels permutation32 permutation6
    _ = mixedMoment B node2277 node2277Labels := by rfl

def raw12025 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12025Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12025step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12025step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12025step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12025step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12025 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12025 raw12025Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw12025 raw12025Labels = mixedMoment B raw12025step0 raw12025step0Labels := by
      have hz : ∀ j, raw12025 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12025step0 = (fun i j => raw12025 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12025step0 raw12025; decide +kernel
      have hl : raw12025step0Labels = raw12025Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12025 raw12025Labels permutation265 hz
    mixedMoment B raw12025step0 raw12025step0Labels = mixedMoment B raw12025step1 raw12025step1Labels := by
      have ha : raw12025step1 = (fun i j => raw12025step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12025step1 raw12025step0; decide +kernel
      have hl : raw12025step1Labels = raw12025step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12025step0 raw12025step0Labels permutation32 permutation6
    _ = mixedMoment B node2773 node2773Labels := by rfl

def raw12026 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12026Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12026step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12026step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12026step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw12026step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12026 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12026 raw12026Labels = mixedMoment B node2773 node2773Labels := by
  calc
    mixedMoment B raw12026 raw12026Labels = mixedMoment B raw12026step0 raw12026step0Labels := by
      have hz : ∀ j, raw12026 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12026step0 = (fun i j => raw12026 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12026step0 raw12026; decide +kernel
      have hl : raw12026step0Labels = raw12026Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12026 raw12026Labels permutation265 hz
    mixedMoment B raw12026step0 raw12026step0Labels = mixedMoment B raw12026step1 raw12026step1Labels := by
      have ha : raw12026step1 = (fun i j => raw12026step0 (permutation34 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12026step1 raw12026step0; decide +kernel
      have hl : raw12026step1Labels = raw12026step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12026step0 raw12026step0Labels permutation34 permutation6
    _ = mixedMoment B node2773 node2773Labels := by rfl

def raw12027 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12027Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12027step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw12027step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12027step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw12027step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12027 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12027 raw12027Labels = mixedMoment B node2775 node2775Labels := by
  calc
    mixedMoment B raw12027 raw12027Labels = mixedMoment B raw12027step0 raw12027step0Labels := by
      have hz : ∀ j, raw12027 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw12027step0 = (fun i j => raw12027 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw12027step0 raw12027; decide +kernel
      have hl : raw12027step0Labels = raw12027Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw12027 raw12027Labels permutation265 hz
    mixedMoment B raw12027step0 raw12027step0Labels = mixedMoment B raw12027step1 raw12027step1Labels := by
      have ha : raw12027step1 = (fun i j => raw12027step0 (permutation32 i) (permutation6 j)) := by apply Matrix.ext; unfold raw12027step1 raw12027step0; decide +kernel
      have hl : raw12027step1Labels = raw12027step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12027step0 raw12027step0Labels permutation32 permutation6
    _ = mixedMoment B node2775 node2775Labels := by rfl

def raw12028 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12028Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12028step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, 1, -1], ![0, -3, 3], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw12028step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12028step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, -1, 1], ![0, 3, -3], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw12028step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12028 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12028 raw12028Labels = mixedMoment B node2219 node2219Labels := by
  calc
    mixedMoment B raw12028 raw12028Labels = mixedMoment B raw12028step0 raw12028step0Labels := by
      have ha : raw12028step0 = (fun i j => raw12028 (permutation416 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12028step0 raw12028; decide +kernel
      have hl : raw12028step0Labels = raw12028Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12028 raw12028Labels permutation416 permutation3
    mixedMoment B raw12028step0 raw12028step0Labels = mixedMoment B raw12028step1 raw12028step1Labels := by
      have ha : raw12028step1 = -raw12028step0 := by apply Matrix.ext; change ∀ i j, raw12028step1 i j = -(raw12028step0 i j); unfold raw12028step1 raw12028step0; decide +kernel
      have hl : raw12028step1Labels = raw12028step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2219 node2219Labels := by rfl

def raw12029 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-2, 2, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12029Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12029step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![0, 1, -1], ![-1, 1, 0], ![-1, 1, 0], ![-2, 0, 2]]
def raw12029step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12029step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 0, -2]]
def raw12029step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12029 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12029 raw12029Labels = mixedMoment B node2117 node2117Labels := by
  calc
    mixedMoment B raw12029 raw12029Labels = mixedMoment B raw12029step0 raw12029step0Labels := by
      have ha : raw12029step0 = (fun i j => raw12029 (permutation364 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12029step0 raw12029; decide +kernel
      have hl : raw12029step0Labels = raw12029Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12029 raw12029Labels permutation364 permutation3
    mixedMoment B raw12029step0 raw12029step0Labels = mixedMoment B raw12029step1 raw12029step1Labels := by
      have ha : raw12029step1 = -raw12029step0 := by apply Matrix.ext; change ∀ i j, raw12029step1 i j = -(raw12029step0 i j); unfold raw12029step1 raw12029step0; decide +kernel
      have hl : raw12029step1Labels = raw12029step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2117 node2117Labels := by rfl

def raw12030 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-2, 1, 1], ![-1, 0, 1], ![0, -1, 1]]
def raw12030Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12030step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw12030step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12030step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12030step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12030 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12030 raw12030Labels = mixedMoment B node2118 node2118Labels := by
  calc
    mixedMoment B raw12030 raw12030Labels = mixedMoment B raw12030step0 raw12030step0Labels := by
      have ha : raw12030step0 = (fun i j => raw12030 (permutation365 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12030step0 raw12030; decide +kernel
      have hl : raw12030step0Labels = raw12030Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12030 raw12030Labels permutation365 permutation3
    mixedMoment B raw12030step0 raw12030step0Labels = mixedMoment B raw12030step1 raw12030step1Labels := by
      have ha : raw12030step1 = -raw12030step0 := by apply Matrix.ext; change ∀ i j, raw12030step1 i j = -(raw12030step0 i j); unfold raw12030step1 raw12030step0; decide +kernel
      have hl : raw12030step1Labels = raw12030step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2118 node2118Labels := by rfl

def raw12031 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![-1, 1, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, 1, 1], ![0, -1, 1]]
def raw12031Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw12031step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-2, 1, 1]]
def raw12031step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw12031step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, -1, -1]]
def raw12031step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical12031 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw12031 raw12031Labels = mixedMoment B node2118 node2118Labels := by
  calc
    mixedMoment B raw12031 raw12031Labels = mixedMoment B raw12031step0 raw12031step0Labels := by
      have ha : raw12031step0 = (fun i j => raw12031 (permutation363 i) (permutation3 j)) := by apply Matrix.ext; unfold raw12031step0 raw12031; decide +kernel
      have hl : raw12031step0Labels = raw12031Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw12031 raw12031Labels permutation363 permutation3
    mixedMoment B raw12031step0 raw12031step0Labels = mixedMoment B raw12031step1 raw12031step1Labels := by
      have ha : raw12031step1 = -raw12031step0 := by apply Matrix.ext; change ∀ i j, raw12031step1 i j = -(raw12031step0 i j); unfold raw12031step1 raw12031step0; decide +kernel
      have hl : raw12031step1Labels = raw12031step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node2118 node2118Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
