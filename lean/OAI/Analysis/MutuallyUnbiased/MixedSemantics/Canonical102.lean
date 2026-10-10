import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Rules
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Permutations
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes18
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes19
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes34
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes35
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes38
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes39
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes41
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes42
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes44
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes46
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes47
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes48
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes50
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes51
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes55
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes60
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes61
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes62
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes63
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes71
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes76
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes79
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes81
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes82
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes84
import OAI.Analysis.MutuallyUnbiased.MixedSemantics.Nodes85

namespace OAI

namespace MUB6.Certificate.MixedSemantics

def raw13056 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13056Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13056step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13056step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13056step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw13056step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13056step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13056step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13056step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13056step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13056 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13056 raw13056Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw13056 raw13056Labels = mixedMoment B raw13056step0 raw13056step0Labels := by
      have hz : ∀ j, raw13056 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13056step0 = (fun i j => raw13056 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13056step0 raw13056; decide +kernel
      have hl : raw13056step0Labels = raw13056Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13056 raw13056Labels permutation265 hz
    mixedMoment B raw13056step0 raw13056step0Labels = mixedMoment B raw13056step1 raw13056step1Labels := by
      have ha : raw13056step1 = (fun i j => raw13056step0 (permutation41 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13056step1 raw13056step0; decide +kernel
      have hl : raw13056step1Labels = raw13056step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13056step0 raw13056step0Labels permutation41 permutation5
    mixedMoment B raw13056step1 raw13056step1Labels = mixedMoment B raw13056step2 raw13056step2Labels := by
      have ha : raw13056step2 = -raw13056step1 := by apply Matrix.ext; change ∀ i j, raw13056step2 i j = -(raw13056step1 i j); unfold raw13056step2 raw13056step1; decide +kernel
      have hl : raw13056step2Labels = raw13056step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13056step2 raw13056step2Labels = mixedMoment B raw13056step3 raw13056step3Labels := by
      have ha : raw13056step3 = raw13056step2 := by apply Matrix.ext; unfold raw13056step3 raw13056step2; decide +kernel
      have hl : raw13056step2Labels = labelEmbedding1 ∘ raw13056step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13056step2 raw13056step2Labels raw13056step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3535 node3535Labels := by rfl

def raw13057 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw13057Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13057step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![2, -1, -1]]
def raw13057step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13057step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, -1, 2], ![-2, 2, 0]]
def raw13057step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13057step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13057step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13057step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, 1, -2], ![2, -2, 0]]
def raw13057step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13057 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13057 raw13057Labels = mixedMoment B node3535 node3535Labels := by
  calc
    mixedMoment B raw13057 raw13057Labels = mixedMoment B raw13057step0 raw13057step0Labels := by
      have hz : ∀ j, raw13057 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13057step0 = (fun i j => raw13057 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13057step0 raw13057; decide +kernel
      have hl : raw13057step0Labels = raw13057Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13057 raw13057Labels permutation265 hz
    mixedMoment B raw13057step0 raw13057step0Labels = mixedMoment B raw13057step1 raw13057step1Labels := by
      have ha : raw13057step1 = (fun i j => raw13057step0 (permutation47 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13057step1 raw13057step0; decide +kernel
      have hl : raw13057step1Labels = raw13057step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13057step0 raw13057step0Labels permutation47 permutation5
    mixedMoment B raw13057step1 raw13057step1Labels = mixedMoment B raw13057step2 raw13057step2Labels := by
      have ha : raw13057step2 = -raw13057step1 := by apply Matrix.ext; change ∀ i j, raw13057step2 i j = -(raw13057step1 i j); unfold raw13057step2 raw13057step1; decide +kernel
      have hl : raw13057step2Labels = raw13057step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13057step2 raw13057step2Labels = mixedMoment B raw13057step3 raw13057step3Labels := by
      have ha : raw13057step3 = raw13057step2 := by apply Matrix.ext; unfold raw13057step3 raw13057step2; decide +kernel
      have hl : raw13057step2Labels = labelEmbedding1 ∘ raw13057step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13057step2 raw13057step2Labels raw13057step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3535 node3535Labels := by rfl

def raw13058 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13058Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13058step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13058step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13058 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13058 raw13058Labels = mixedMoment B node3053 node3053Labels := by
  calc
    mixedMoment B raw13058 raw13058Labels = mixedMoment B raw13058step0 raw13058step0Labels := by
      have hz : ∀ j, raw13058 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13058step0 = (fun i j => raw13058 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13058step0 raw13058; decide +kernel
      have hl : raw13058step0Labels = raw13058Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13058 raw13058Labels permutation265 hz
    _ = mixedMoment B node3053 node3053Labels := by rfl

def raw13059 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13059Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13059step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0]]
def raw13059step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13059 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13059 raw13059Labels = mixedMoment B node3909 node3909Labels := by
  calc
    mixedMoment B raw13059 raw13059Labels = mixedMoment B raw13059step0 raw13059step0Labels := by
      have ha : raw13059step0 = (fun i j => raw13059 (permutation393 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13059step0 raw13059; decide +kernel
      have hl : raw13059step0Labels = raw13059Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13059 raw13059Labels permutation393 permutation4
    _ = mixedMoment B node3909 node3909Labels := by rfl

def raw13060 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13060Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13060step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![-1, -1, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13060step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13060 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13060 raw13060Labels = mixedMoment B node3962 node3962Labels := by
  calc
    mixedMoment B raw13060 raw13060Labels = mixedMoment B raw13060step0 raw13060step0Labels := by
      have hz : ∀ j, raw13060 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13060step0 = (fun i j => raw13060 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13060step0 raw13060; decide +kernel
      have hl : raw13060step0Labels = raw13060Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13060 raw13060Labels permutation265 hz
    _ = mixedMoment B node3962 node3962Labels := by rfl

def raw13061 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13061Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13061step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![0, 1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13061step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13061step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw13061step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13061 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13061 raw13061Labels = mixedMoment B node3910 node3910Labels := by
  calc
    mixedMoment B raw13061 raw13061Labels = mixedMoment B raw13061step0 raw13061step0Labels := by
      have hz : ∀ j, raw13061 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13061step0 = (fun i j => raw13061 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13061step0 raw13061; decide +kernel
      have hl : raw13061step0Labels = raw13061Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13061 raw13061Labels permutation265 hz
    mixedMoment B raw13061step0 raw13061step0Labels = mixedMoment B raw13061step1 raw13061step1Labels := by
      have ha : raw13061step1 = (fun i j => raw13061step0 (permutation72 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13061step1 raw13061step0; decide +kernel
      have hl : raw13061step1Labels = raw13061step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13061step0 raw13061step0Labels permutation72 permutation4
    _ = mixedMoment B node3910 node3910Labels := by rfl

def raw13062 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw13062Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13062step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![0, 1, -1], ![1, 0, -1]]
def raw13062step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13062step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw13062step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13062 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13062 raw13062Labels = mixedMoment B node3910 node3910Labels := by
  calc
    mixedMoment B raw13062 raw13062Labels = mixedMoment B raw13062step0 raw13062step0Labels := by
      have hz : ∀ j, raw13062 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13062step0 = (fun i j => raw13062 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13062step0 raw13062; decide +kernel
      have hl : raw13062step0Labels = raw13062Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13062 raw13062Labels permutation265 hz
    mixedMoment B raw13062step0 raw13062step0Labels = mixedMoment B raw13062step1 raw13062step1Labels := by
      have ha : raw13062step1 = (fun i j => raw13062step0 (permutation66 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13062step1 raw13062step0; decide +kernel
      have hl : raw13062step1Labels = raw13062step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13062step0 raw13062step0Labels permutation66 permutation4
    _ = mixedMoment B node3910 node3910Labels := by rfl

def raw13063 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 1, 1], ![0, 0, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw13063Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13063step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 1, 1], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![0, 1, -1]]
def raw13063step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13063step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw13063step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13063 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13063 raw13063Labels = mixedMoment B node3910 node3910Labels := by
  calc
    mixedMoment B raw13063 raw13063Labels = mixedMoment B raw13063step0 raw13063step0Labels := by
      have hz : ∀ j, raw13063 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13063step0 = (fun i j => raw13063 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13063step0 raw13063; decide +kernel
      have hl : raw13063step0Labels = raw13063Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13063 raw13063Labels permutation265 hz
    mixedMoment B raw13063step0 raw13063step0Labels = mixedMoment B raw13063step1 raw13063step1Labels := by
      have ha : raw13063step1 = (fun i j => raw13063step0 (permutation64 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13063step1 raw13063step0; decide +kernel
      have hl : raw13063step1Labels = raw13063step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13063step0 raw13063step0Labels permutation64 permutation4
    _ = mixedMoment B node3910 node3910Labels := by rfl

def raw13064 : Matrix (Fin 6) (Fin 2) ℤ := ![![-1, 1], ![0, 0], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]
def raw13064Labels : Fin 2 → Fin 2 := ![0, 1]

def raw13064step0 : Matrix (Fin 5) (Fin 2) ℤ := ![![-1, 1], ![-2, 2], ![1, -1], ![1, -1], ![1, -1]]
def raw13064step0Labels : Fin 2 → Fin 2 := ![0, 1]

def raw13064step1 : Matrix (Fin 5) (Fin 2) ℤ := ![![-2, 2], ![-1, 1], ![1, -1], ![1, -1], ![1, -1]]
def raw13064step1Labels : Fin 2 → Fin 2 := ![0, 1]

theorem canonical13064 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13064 raw13064Labels = mixedMoment B node4091 node4091Labels := by
  calc
    mixedMoment B raw13064 raw13064Labels = mixedMoment B raw13064step0 raw13064step0Labels := by
      have hz : ∀ j, raw13064 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13064step0 = (fun i j => raw13064 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13064step0 raw13064; decide +kernel
      have hl : raw13064step0Labels = raw13064Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13064 raw13064Labels permutation265 hz
    mixedMoment B raw13064step0 raw13064step0Labels = mixedMoment B raw13064step1 raw13064step1Labels := by
      have ha : raw13064step1 = (fun i j => raw13064step0 (permutation56 i) (permutation0 j)) := by apply Matrix.ext; unfold raw13064step1 raw13064step0; decide +kernel
      have hl : raw13064step1Labels = raw13064step0Labels ∘ permutation0 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13064step0 raw13064step0Labels permutation56 permutation0
    _ = mixedMoment B node4091 node4091Labels := by rfl

def raw13065 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![1, -3, 2], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13065Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13065step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -3, 1]]
def raw13065step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13065 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13065 raw13065Labels = mixedMoment B node2746 node2746Labels := by
  calc
    mixedMoment B raw13065 raw13065Labels = mixedMoment B raw13065step0 raw13065step0Labels := by
      have ha : raw13065step0 = (fun i j => raw13065 (permutation394 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13065step0 raw13065; decide +kernel
      have hl : raw13065step0Labels = raw13065Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13065 raw13065Labels permutation394 permutation4
    _ = mixedMoment B node2746 node2746Labels := by rfl

def raw13066 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![2, -1, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13066Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13066step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13066step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13066 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13066 raw13066Labels = mixedMoment B node2976 node2976Labels := by
  calc
    mixedMoment B raw13066 raw13066Labels = mixedMoment B raw13066step0 raw13066step0Labels := by
      have ha : raw13066step0 = (fun i j => raw13066 (permutation155 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13066step0 raw13066; decide +kernel
      have hl : raw13066step0Labels = raw13066Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13066 raw13066Labels permutation155 permutation2
    _ = mixedMoment B node2976 node2976Labels := by rfl

def raw13067 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![2, -1, -1], ![1, 0, -1]]
def raw13067Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13067step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13067step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13067 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13067 raw13067Labels = mixedMoment B node2976 node2976Labels := by
  calc
    mixedMoment B raw13067 raw13067Labels = mixedMoment B raw13067step0 raw13067step0Labels := by
      have ha : raw13067step0 = (fun i j => raw13067 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13067step0 raw13067; decide +kernel
      have hl : raw13067step0Labels = raw13067Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13067 raw13067Labels permutation153 permutation2
    _ = mixedMoment B node2976 node2976Labels := by rfl

def raw13068 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, 1, 0], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13068Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13068 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13068 raw13068Labels = mixedMoment B node2976 node2976Labels := by
  calc
    _ = mixedMoment B node2976 node2976Labels := by rfl

def raw13069 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw13069Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13069step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw13069step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13069step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13069step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13069step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13069step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13069 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13069 raw13069Labels = mixedMoment B node5237 node5237Labels := by
  calc
    mixedMoment B raw13069 raw13069Labels = mixedMoment B raw13069step0 raw13069step0Labels := by
      have hz : ∀ j, raw13069 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13069step0 = (fun i j => raw13069 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13069step0 raw13069; decide +kernel
      have hl : raw13069step0Labels = raw13069Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13069 raw13069Labels permutation265 hz
    mixedMoment B raw13069step0 raw13069step0Labels = mixedMoment B raw13069step1 raw13069step1Labels := by
      have ha : raw13069step1 = (fun i j => raw13069step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13069step1 raw13069step0; decide +kernel
      have hl : raw13069step1Labels = raw13069step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13069step0 raw13069step0Labels permutation33 permutation7
    mixedMoment B raw13069step1 raw13069step1Labels = mixedMoment B raw13069step2 raw13069step2Labels := by
      have ha : raw13069step2 = raw13069step1 := by apply Matrix.ext; unfold raw13069step2 raw13069step1; decide +kernel
      have hl : raw13069step1Labels = labelEmbedding10 ∘ raw13069step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13069step1 raw13069step1Labels raw13069step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5237 node5237Labels := by rfl

def raw13070 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13070Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13070step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13070step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13070step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13070step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13070step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13070step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13070 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13070 raw13070Labels = mixedMoment B node5237 node5237Labels := by
  calc
    mixedMoment B raw13070 raw13070Labels = mixedMoment B raw13070step0 raw13070step0Labels := by
      have hz : ∀ j, raw13070 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13070step0 = (fun i j => raw13070 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13070step0 raw13070; decide +kernel
      have hl : raw13070step0Labels = raw13070Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13070 raw13070Labels permutation265 hz
    mixedMoment B raw13070step0 raw13070step0Labels = mixedMoment B raw13070step1 raw13070step1Labels := by
      have ha : raw13070step1 = (fun i j => raw13070step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13070step1 raw13070step0; decide +kernel
      have hl : raw13070step1Labels = raw13070step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13070step0 raw13070step0Labels permutation32 permutation7
    mixedMoment B raw13070step1 raw13070step1Labels = mixedMoment B raw13070step2 raw13070step2Labels := by
      have ha : raw13070step2 = raw13070step1 := by apply Matrix.ext; unfold raw13070step2 raw13070step1; decide +kernel
      have hl : raw13070step1Labels = labelEmbedding10 ∘ raw13070step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13070step1 raw13070step1Labels raw13070step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5237 node5237Labels := by rfl

def raw13071 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13071Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13071step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-1, 1, 0], ![-2, 2, 0]]
def raw13071step0Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13071step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw13071step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13071step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -2, 0]]
def raw13071step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13071 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13071 raw13071Labels = mixedMoment B node4885 node4885Labels := by
  calc
    mixedMoment B raw13071 raw13071Labels = mixedMoment B raw13071step0 raw13071step0Labels := by
      have ha : raw13071step0 = (fun i j => raw13071 (permutation216 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13071step0 raw13071; decide +kernel
      have hl : raw13071step0Labels = raw13071Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13071 raw13071Labels permutation216 permutation4
    mixedMoment B raw13071step0 raw13071step0Labels = mixedMoment B raw13071step1 raw13071step1Labels := by
      have ha : raw13071step1 = -raw13071step0 := by apply Matrix.ext; change ∀ i j, raw13071step1 i j = -(raw13071step0 i j); unfold raw13071step1 raw13071step0; decide +kernel
      have hl : raw13071step1Labels = raw13071step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13071step1 raw13071step1Labels = mixedMoment B raw13071step2 raw13071step2Labels := by
      have ha : raw13071step2 = raw13071step1 := by apply Matrix.ext; unfold raw13071step2 raw13071step1; decide +kernel
      have hl : raw13071step1Labels = labelEmbedding7 ∘ raw13071step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13071step1 raw13071step1Labels raw13071step2Labels labelEmbedding7 hl
    _ = mixedMoment B node4885 node4885Labels := by rfl

def raw13072 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw13072Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13072step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw13072step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13072step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw13072step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13072 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13072 raw13072Labels = mixedMoment B node5286 node5286Labels := by
  calc
    mixedMoment B raw13072 raw13072Labels = mixedMoment B raw13072step0 raw13072step0Labels := by
      have ha : raw13072step0 = (fun i j => raw13072 (permutation154 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13072step0 raw13072; decide +kernel
      have hl : raw13072step0Labels = raw13072Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13072 raw13072Labels permutation154 permutation6
    mixedMoment B raw13072step0 raw13072step0Labels = mixedMoment B raw13072step1 raw13072step1Labels := by
      have ha : raw13072step1 = raw13072step0 := by apply Matrix.ext; unfold raw13072step1 raw13072step0; decide +kernel
      have hl : raw13072step0Labels = labelEmbedding9 ∘ raw13072step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13072step0 raw13072step0Labels raw13072step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5286 node5286Labels := by rfl

def raw13073 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13073Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13073step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw13073step0Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13073step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, -1, 0]]
def raw13073step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13073 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13073 raw13073Labels = mixedMoment B node5286 node5286Labels := by
  calc
    mixedMoment B raw13073 raw13073Labels = mixedMoment B raw13073step0 raw13073step0Labels := by
      have ha : raw13073step0 = (fun i j => raw13073 (permutation156 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13073step0 raw13073; decide +kernel
      have hl : raw13073step0Labels = raw13073Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13073 raw13073Labels permutation156 permutation6
    mixedMoment B raw13073step0 raw13073step0Labels = mixedMoment B raw13073step1 raw13073step1Labels := by
      have ha : raw13073step1 = raw13073step0 := by apply Matrix.ext; unfold raw13073step1 raw13073step0; decide +kernel
      have hl : raw13073step0Labels = labelEmbedding9 ∘ raw13073step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13073step0 raw13073step0Labels raw13073step1Labels labelEmbedding9 hl
    _ = mixedMoment B node5286 node5286Labels := by rfl

def raw13074 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13074Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13074step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13074step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13074step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![-3, 3, 0]]
def raw13074step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13074step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw13074step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13074step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw13074step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13074 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13074 raw13074Labels = mixedMoment B node4886 node4886Labels := by
  calc
    mixedMoment B raw13074 raw13074Labels = mixedMoment B raw13074step0 raw13074step0Labels := by
      have hz : ∀ j, raw13074 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13074step0 = (fun i j => raw13074 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13074step0 raw13074; decide +kernel
      have hl : raw13074step0Labels = raw13074Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13074 raw13074Labels permutation265 hz
    mixedMoment B raw13074step0 raw13074step0Labels = mixedMoment B raw13074step1 raw13074step1Labels := by
      have ha : raw13074step1 = (fun i j => raw13074step0 (permutation41 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13074step1 raw13074step0; decide +kernel
      have hl : raw13074step1Labels = raw13074step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13074step0 raw13074step0Labels permutation41 permutation4
    mixedMoment B raw13074step1 raw13074step1Labels = mixedMoment B raw13074step2 raw13074step2Labels := by
      have ha : raw13074step2 = -raw13074step1 := by apply Matrix.ext; change ∀ i j, raw13074step2 i j = -(raw13074step1 i j); unfold raw13074step2 raw13074step1; decide +kernel
      have hl : raw13074step2Labels = raw13074step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13074step2 raw13074step2Labels = mixedMoment B raw13074step3 raw13074step3Labels := by
      have ha : raw13074step3 = raw13074step2 := by apply Matrix.ext; unfold raw13074step3 raw13074step2; decide +kernel
      have hl : raw13074step2Labels = labelEmbedding7 ∘ raw13074step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13074step2 raw13074step2Labels raw13074step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4886 node4886Labels := by rfl

def raw13075 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw13075Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13075step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![3, -3, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw13075step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13075step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw13075step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13075step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13075step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13075step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13075step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13075 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13075 raw13075Labels = mixedMoment B node4879 node4879Labels := by
  calc
    mixedMoment B raw13075 raw13075Labels = mixedMoment B raw13075step0 raw13075step0Labels := by
      have hz : ∀ j, raw13075 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13075step0 = (fun i j => raw13075 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13075step0 raw13075; decide +kernel
      have hl : raw13075step0Labels = raw13075Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13075 raw13075Labels permutation265 hz
    mixedMoment B raw13075step0 raw13075step0Labels = mixedMoment B raw13075step1 raw13075step1Labels := by
      have ha : raw13075step1 = (fun i j => raw13075step0 (permutation57 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13075step1 raw13075step0; decide +kernel
      have hl : raw13075step1Labels = raw13075step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13075step0 raw13075step0Labels permutation57 permutation3
    mixedMoment B raw13075step1 raw13075step1Labels = mixedMoment B raw13075step2 raw13075step2Labels := by
      have ha : raw13075step2 = -raw13075step1 := by apply Matrix.ext; change ∀ i j, raw13075step2 i j = -(raw13075step1 i j); unfold raw13075step2 raw13075step1; decide +kernel
      have hl : raw13075step2Labels = raw13075step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13075step2 raw13075step2Labels = mixedMoment B raw13075step3 raw13075step3Labels := by
      have ha : raw13075step3 = raw13075step2 := by apply Matrix.ext; unfold raw13075step3 raw13075step2; decide +kernel
      have hl : raw13075step2Labels = labelEmbedding6 ∘ raw13075step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13075step2 raw13075step2Labels raw13075step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4879 node4879Labels := by rfl

def raw13076 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13076Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13076step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![3, -3, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13076step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13076step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![1, -3, 2], ![-1, 1, 0], ![-1, 1, 0], ![-2, 1, 1]]
def raw13076step1Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13076step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13076step2Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13076step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![-1, 3, -2], ![1, -1, 0], ![1, -1, 0], ![2, -1, -1]]
def raw13076step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13076 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13076 raw13076Labels = mixedMoment B node4879 node4879Labels := by
  calc
    mixedMoment B raw13076 raw13076Labels = mixedMoment B raw13076step0 raw13076step0Labels := by
      have hz : ∀ j, raw13076 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13076step0 = (fun i j => raw13076 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13076step0 raw13076; decide +kernel
      have hl : raw13076step0Labels = raw13076Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13076 raw13076Labels permutation265 hz
    mixedMoment B raw13076step0 raw13076step0Labels = mixedMoment B raw13076step1 raw13076step1Labels := by
      have ha : raw13076step1 = (fun i j => raw13076step0 (permutation56 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13076step1 raw13076step0; decide +kernel
      have hl : raw13076step1Labels = raw13076step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13076step0 raw13076step0Labels permutation56 permutation3
    mixedMoment B raw13076step1 raw13076step1Labels = mixedMoment B raw13076step2 raw13076step2Labels := by
      have ha : raw13076step2 = -raw13076step1 := by apply Matrix.ext; change ∀ i j, raw13076step2 i j = -(raw13076step1 i j); unfold raw13076step2 raw13076step1; decide +kernel
      have hl : raw13076step2Labels = raw13076step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13076step2 raw13076step2Labels = mixedMoment B raw13076step3 raw13076step3Labels := by
      have ha : raw13076step3 = raw13076step2 := by apply Matrix.ext; unfold raw13076step3 raw13076step2; decide +kernel
      have hl : raw13076step2Labels = labelEmbedding6 ∘ raw13076step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13076step2 raw13076step2Labels raw13076step3Labels labelEmbedding6 hl
    _ = mixedMoment B node4879 node4879Labels := by rfl

def raw13077 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13077Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13077step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13077step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13077step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw13077step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13077step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13077step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13077step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13077step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13077 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13077 raw13077Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw13077 raw13077Labels = mixedMoment B raw13077step0 raw13077step0Labels := by
      have hz : ∀ j, raw13077 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13077step0 = (fun i j => raw13077 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13077step0 raw13077; decide +kernel
      have hl : raw13077step0Labels = raw13077Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13077 raw13077Labels permutation265 hz
    mixedMoment B raw13077step0 raw13077step0Labels = mixedMoment B raw13077step1 raw13077step1Labels := by
      have ha : raw13077step1 = (fun i j => raw13077step0 (permutation49 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13077step1 raw13077step0; decide +kernel
      have hl : raw13077step1Labels = raw13077step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13077step0 raw13077step0Labels permutation49 permutation4
    mixedMoment B raw13077step1 raw13077step1Labels = mixedMoment B raw13077step2 raw13077step2Labels := by
      have ha : raw13077step2 = -raw13077step1 := by apply Matrix.ext; change ∀ i j, raw13077step2 i j = -(raw13077step1 i j); unfold raw13077step2 raw13077step1; decide +kernel
      have hl : raw13077step2Labels = raw13077step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13077step2 raw13077step2Labels = mixedMoment B raw13077step3 raw13077step3Labels := by
      have ha : raw13077step3 = raw13077step2 := by apply Matrix.ext; unfold raw13077step3 raw13077step2; decide +kernel
      have hl : raw13077step2Labels = labelEmbedding7 ∘ raw13077step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13077step2 raw13077step2Labels raw13077step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

def raw13078 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw13078Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13078step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw13078step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13078step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13078step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13078step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13078step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13078 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13078 raw13078Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw13078 raw13078Labels = mixedMoment B raw13078step0 raw13078step0Labels := by
      have hz : ∀ j, raw13078 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13078step0 = (fun i j => raw13078 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13078step0 raw13078; decide +kernel
      have hl : raw13078step0Labels = raw13078Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13078 raw13078Labels permutation265 hz
    mixedMoment B raw13078step0 raw13078step0Labels = mixedMoment B raw13078step1 raw13078step1Labels := by
      have ha : raw13078step1 = (fun i j => raw13078step0 (permutation35 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13078step1 raw13078step0; decide +kernel
      have hl : raw13078step1Labels = raw13078step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13078step0 raw13078step0Labels permutation35 permutation6
    mixedMoment B raw13078step1 raw13078step1Labels = mixedMoment B raw13078step2 raw13078step2Labels := by
      have ha : raw13078step2 = raw13078step1 := by apply Matrix.ext; unfold raw13078step2 raw13078step1; decide +kernel
      have hl : raw13078step1Labels = labelEmbedding9 ∘ raw13078step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13078step1 raw13078step1Labels raw13078step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw13079 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13079Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13079step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13079step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13079step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13079step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13079step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13079step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13079 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13079 raw13079Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw13079 raw13079Labels = mixedMoment B raw13079step0 raw13079step0Labels := by
      have hz : ∀ j, raw13079 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13079step0 = (fun i j => raw13079 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13079step0 raw13079; decide +kernel
      have hl : raw13079step0Labels = raw13079Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13079 raw13079Labels permutation265 hz
    mixedMoment B raw13079step0 raw13079step0Labels = mixedMoment B raw13079step1 raw13079step1Labels := by
      have ha : raw13079step1 = (fun i j => raw13079step0 (permutation37 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13079step1 raw13079step0; decide +kernel
      have hl : raw13079step1Labels = raw13079step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13079step0 raw13079step0Labels permutation37 permutation6
    mixedMoment B raw13079step1 raw13079step1Labels = mixedMoment B raw13079step2 raw13079step2Labels := by
      have ha : raw13079step2 = raw13079step1 := by apply Matrix.ext; unfold raw13079step2 raw13079step1; decide +kernel
      have hl : raw13079step1Labels = labelEmbedding9 ∘ raw13079step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13079step1 raw13079step1Labels raw13079step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw13080 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13080Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13080step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13080step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13080step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![3, 0, -3], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 2, 0]]
def raw13080step1Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13080step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13080step2Labels : Fin 3 → Fin 3 := ![1, 0, 2]

def raw13080step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13080step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13080 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13080 raw13080Labels = mixedMoment B node4889 node4889Labels := by
  calc
    mixedMoment B raw13080 raw13080Labels = mixedMoment B raw13080step0 raw13080step0Labels := by
      have hz : ∀ j, raw13080 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13080step0 = (fun i j => raw13080 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13080step0 raw13080; decide +kernel
      have hl : raw13080step0Labels = raw13080Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13080 raw13080Labels permutation265 hz
    mixedMoment B raw13080step0 raw13080step0Labels = mixedMoment B raw13080step1 raw13080step1Labels := by
      have ha : raw13080step1 = (fun i j => raw13080step0 (permutation43 i) (permutation4 j)) := by apply Matrix.ext; unfold raw13080step1 raw13080step0; decide +kernel
      have hl : raw13080step1Labels = raw13080step0Labels ∘ permutation4 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13080step0 raw13080step0Labels permutation43 permutation4
    mixedMoment B raw13080step1 raw13080step1Labels = mixedMoment B raw13080step2 raw13080step2Labels := by
      have ha : raw13080step2 = -raw13080step1 := by apply Matrix.ext; change ∀ i j, raw13080step2 i j = -(raw13080step1 i j); unfold raw13080step2 raw13080step1; decide +kernel
      have hl : raw13080step2Labels = raw13080step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13080step2 raw13080step2Labels = mixedMoment B raw13080step3 raw13080step3Labels := by
      have ha : raw13080step3 = raw13080step2 := by apply Matrix.ext; unfold raw13080step3 raw13080step2; decide +kernel
      have hl : raw13080step2Labels = labelEmbedding7 ∘ raw13080step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13080step2 raw13080step2Labels raw13080step3Labels labelEmbedding7 hl
    _ = mixedMoment B node4889 node4889Labels := by rfl

def raw13081 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13081Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13081step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13081step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13081step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13081step1Labels : Fin 3 → Fin 3 := ![2, 0, 1]

def raw13081step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13081step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13081 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13081 raw13081Labels = mixedMoment B node5299 node5299Labels := by
  calc
    mixedMoment B raw13081 raw13081Labels = mixedMoment B raw13081step0 raw13081step0Labels := by
      have hz : ∀ j, raw13081 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13081step0 = (fun i j => raw13081 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13081step0 raw13081; decide +kernel
      have hl : raw13081step0Labels = raw13081Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13081 raw13081Labels permutation265 hz
    mixedMoment B raw13081step0 raw13081step0Labels = mixedMoment B raw13081step1 raw13081step1Labels := by
      have ha : raw13081step1 = (fun i j => raw13081step0 (permutation36 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13081step1 raw13081step0; decide +kernel
      have hl : raw13081step1Labels = raw13081step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13081step0 raw13081step0Labels permutation36 permutation6
    mixedMoment B raw13081step1 raw13081step1Labels = mixedMoment B raw13081step2 raw13081step2Labels := by
      have ha : raw13081step2 = raw13081step1 := by apply Matrix.ext; unfold raw13081step2 raw13081step1; decide +kernel
      have hl : raw13081step1Labels = labelEmbedding9 ∘ raw13081step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13081step1 raw13081step1Labels raw13081step2Labels labelEmbedding9 hl
    _ = mixedMoment B node5299 node5299Labels := by rfl

def raw13082 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13082Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13082step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13082step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13082step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13082step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13082step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13082step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13082 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13082 raw13082Labels = mixedMoment B node2741 node2741Labels := by
  calc
    mixedMoment B raw13082 raw13082Labels = mixedMoment B raw13082step0 raw13082step0Labels := by
      have hz : ∀ j, raw13082 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13082step0 = (fun i j => raw13082 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13082step0 raw13082; decide +kernel
      have hl : raw13082step0Labels = raw13082Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13082 raw13082Labels permutation265 hz
    mixedMoment B raw13082step0 raw13082step0Labels = mixedMoment B raw13082step1 raw13082step1Labels := by
      have ha : raw13082step1 = (fun i j => raw13082step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13082step1 raw13082step0; decide +kernel
      have hl : raw13082step1Labels = raw13082step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13082step0 raw13082step0Labels permutation32 permutation7
    mixedMoment B raw13082step1 raw13082step1Labels = mixedMoment B raw13082step2 raw13082step2Labels := by
      have ha : raw13082step2 = raw13082step1 := by apply Matrix.ext; unfold raw13082step2 raw13082step1; decide +kernel
      have hl : raw13082step1Labels = labelEmbedding1 ∘ raw13082step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13082step1 raw13082step1Labels raw13082step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2741 node2741Labels := by rfl

def raw13083 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw13083Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13083step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw13083step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13083step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13083step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13083step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13083step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13083 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13083 raw13083Labels = mixedMoment B node2684 node2684Labels := by
  calc
    mixedMoment B raw13083 raw13083Labels = mixedMoment B raw13083step0 raw13083step0Labels := by
      have hz : ∀ j, raw13083 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13083step0 = (fun i j => raw13083 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13083step0 raw13083; decide +kernel
      have hl : raw13083step0Labels = raw13083Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13083 raw13083Labels permutation265 hz
    mixedMoment B raw13083step0 raw13083step0Labels = mixedMoment B raw13083step1 raw13083step1Labels := by
      have ha : raw13083step1 = (fun i j => raw13083step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13083step1 raw13083step0; decide +kernel
      have hl : raw13083step1Labels = raw13083step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13083step0 raw13083step0Labels permutation33 permutation7
    mixedMoment B raw13083step1 raw13083step1Labels = mixedMoment B raw13083step2 raw13083step2Labels := by
      have ha : raw13083step2 = raw13083step1 := by apply Matrix.ext; unfold raw13083step2 raw13083step1; decide +kernel
      have hl : raw13083step1Labels = labelEmbedding1 ∘ raw13083step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13083step1 raw13083step1Labels raw13083step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2684 node2684Labels := by rfl

def raw13084 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13084Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13084step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13084step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13084step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13084step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13084step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -2, 2], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13084step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13084 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13084 raw13084Labels = mixedMoment B node2684 node2684Labels := by
  calc
    mixedMoment B raw13084 raw13084Labels = mixedMoment B raw13084step0 raw13084step0Labels := by
      have hz : ∀ j, raw13084 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13084step0 = (fun i j => raw13084 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13084step0 raw13084; decide +kernel
      have hl : raw13084step0Labels = raw13084Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13084 raw13084Labels permutation265 hz
    mixedMoment B raw13084step0 raw13084step0Labels = mixedMoment B raw13084step1 raw13084step1Labels := by
      have ha : raw13084step1 = (fun i j => raw13084step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13084step1 raw13084step0; decide +kernel
      have hl : raw13084step1Labels = raw13084step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13084step0 raw13084step0Labels permutation32 permutation7
    mixedMoment B raw13084step1 raw13084step1Labels = mixedMoment B raw13084step2 raw13084step2Labels := by
      have ha : raw13084step2 = raw13084step1 := by apply Matrix.ext; unfold raw13084step2 raw13084step1; decide +kernel
      have hl : raw13084step1Labels = labelEmbedding1 ∘ raw13084step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13084step1 raw13084step1Labels raw13084step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2684 node2684Labels := by rfl

def raw13085 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13085Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13085step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13085step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13085step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13085step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13085 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13085 raw13085Labels = mixedMoment B node3221 node3221Labels := by
  calc
    mixedMoment B raw13085 raw13085Labels = mixedMoment B raw13085step0 raw13085step0Labels := by
      have ha : raw13085step0 = (fun i j => raw13085 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13085step0 raw13085; decide +kernel
      have hl : raw13085step0Labels = raw13085Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13085 raw13085Labels permutation176 permutation7
    mixedMoment B raw13085step0 raw13085step0Labels = mixedMoment B raw13085step1 raw13085step1Labels := by
      have ha : raw13085step1 = raw13085step0 := by apply Matrix.ext; unfold raw13085step1 raw13085step0; decide +kernel
      have hl : raw13085step0Labels = labelEmbedding1 ∘ raw13085step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13085step0 raw13085step0Labels raw13085step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3221 node3221Labels := by rfl

def raw13086 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![1, -1, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13086Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13086step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13086step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13086step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13086step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13086 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13086 raw13086Labels = mixedMoment B node3076 node3076Labels := by
  calc
    mixedMoment B raw13086 raw13086Labels = mixedMoment B raw13086step0 raw13086step0Labels := by
      have ha : raw13086step0 = (fun i j => raw13086 (permutation152 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13086step0 raw13086; decide +kernel
      have hl : raw13086step0Labels = raw13086Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13086 raw13086Labels permutation152 permutation7
    mixedMoment B raw13086step0 raw13086step0Labels = mixedMoment B raw13086step1 raw13086step1Labels := by
      have ha : raw13086step1 = raw13086step0 := by apply Matrix.ext; unfold raw13086step1 raw13086step0; decide +kernel
      have hl : raw13086step0Labels = labelEmbedding1 ∘ raw13086step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13086step0 raw13086step0Labels raw13086step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3076 node3076Labels := by rfl

def raw13087 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw13087Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13087step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13087step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13087step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13087step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13087 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13087 raw13087Labels = mixedMoment B node3023 node3023Labels := by
  calc
    mixedMoment B raw13087 raw13087Labels = mixedMoment B raw13087step0 raw13087step0Labels := by
      have ha : raw13087step0 = (fun i j => raw13087 (permutation177 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13087step0 raw13087; decide +kernel
      have hl : raw13087step0Labels = raw13087Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13087 raw13087Labels permutation177 permutation7
    mixedMoment B raw13087step0 raw13087step0Labels = mixedMoment B raw13087step1 raw13087step1Labels := by
      have ha : raw13087step1 = raw13087step0 := by apply Matrix.ext; unfold raw13087step1 raw13087step0; decide +kernel
      have hl : raw13087step0Labels = labelEmbedding1 ∘ raw13087step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13087step0 raw13087step0Labels raw13087step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3023 node3023Labels := by rfl

def raw13088 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![2, -2, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13088Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13088step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13088step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13088step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 1, -2]]
def raw13088step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13088 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13088 raw13088Labels = mixedMoment B node3023 node3023Labels := by
  calc
    mixedMoment B raw13088 raw13088Labels = mixedMoment B raw13088step0 raw13088step0Labels := by
      have ha : raw13088step0 = (fun i j => raw13088 (permutation176 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13088step0 raw13088; decide +kernel
      have hl : raw13088step0Labels = raw13088Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13088 raw13088Labels permutation176 permutation7
    mixedMoment B raw13088step0 raw13088step0Labels = mixedMoment B raw13088step1 raw13088step1Labels := by
      have ha : raw13088step1 = raw13088step0 := by apply Matrix.ext; unfold raw13088step1 raw13088step0; decide +kernel
      have hl : raw13088step0Labels = labelEmbedding1 ∘ raw13088step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13088step0 raw13088step0Labels raw13088step1Labels labelEmbedding1 hl
    _ = mixedMoment B node3023 node3023Labels := by rfl

def raw13089 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13089Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13089step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![3, -3, 0], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13089step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13089step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw13089step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13089step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![3, -3, 0]]
def raw13089step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13089 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13089 raw13089Labels = mixedMoment B node2235 node2235Labels := by
  calc
    mixedMoment B raw13089 raw13089Labels = mixedMoment B raw13089step0 raw13089step0Labels := by
      have hz : ∀ j, raw13089 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13089step0 = (fun i j => raw13089 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13089step0 raw13089; decide +kernel
      have hl : raw13089step0Labels = raw13089Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13089 raw13089Labels permutation265 hz
    mixedMoment B raw13089step0 raw13089step0Labels = mixedMoment B raw13089step1 raw13089step1Labels := by
      have ha : raw13089step1 = (fun i j => raw13089step0 (permutation65 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13089step1 raw13089step0; decide +kernel
      have hl : raw13089step1Labels = raw13089step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13089step0 raw13089step0Labels permutation65 permutation5
    mixedMoment B raw13089step1 raw13089step1Labels = mixedMoment B raw13089step2 raw13089step2Labels := by
      have ha : raw13089step2 = raw13089step1 := by apply Matrix.ext; unfold raw13089step2 raw13089step1; decide +kernel
      have hl : raw13089step1Labels = labelEmbedding1 ∘ raw13089step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13089step1 raw13089step1Labels raw13089step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2235 node2235Labels := by rfl

def raw13090 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw13090Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13090step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![3, -3, 0], ![-1, 0, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw13090step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13090step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw13090step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13090step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw13090step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13090 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13090 raw13090Labels = mixedMoment B node2246 node2246Labels := by
  calc
    mixedMoment B raw13090 raw13090Labels = mixedMoment B raw13090step0 raw13090step0Labels := by
      have hz : ∀ j, raw13090 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13090step0 = (fun i j => raw13090 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13090step0 raw13090; decide +kernel
      have hl : raw13090step0Labels = raw13090Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13090 raw13090Labels permutation265 hz
    mixedMoment B raw13090step0 raw13090step0Labels = mixedMoment B raw13090step1 raw13090step1Labels := by
      have ha : raw13090step1 = (fun i j => raw13090step0 (permutation67 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13090step1 raw13090step0; decide +kernel
      have hl : raw13090step1Labels = raw13090step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13090step0 raw13090step0Labels permutation67 permutation5
    mixedMoment B raw13090step1 raw13090step1Labels = mixedMoment B raw13090step2 raw13090step2Labels := by
      have ha : raw13090step2 = raw13090step1 := by apply Matrix.ext; unfold raw13090step2 raw13090step1; decide +kernel
      have hl : raw13090step1Labels = labelEmbedding1 ∘ raw13090step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13090step1 raw13090step1Labels raw13090step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2246 node2246Labels := by rfl

def raw13091 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![3, -3, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13091Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13091step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![3, -3, 0], ![-1, 0, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13091step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13091step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw13091step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13091step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 0, 3], ![0, 1, -1], ![0, 1, -1], ![1, 1, -2], ![2, -3, 1]]
def raw13091step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13091 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13091 raw13091Labels = mixedMoment B node2246 node2246Labels := by
  calc
    mixedMoment B raw13091 raw13091Labels = mixedMoment B raw13091step0 raw13091step0Labels := by
      have hz : ∀ j, raw13091 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13091step0 = (fun i j => raw13091 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13091step0 raw13091; decide +kernel
      have hl : raw13091step0Labels = raw13091Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13091 raw13091Labels permutation265 hz
    mixedMoment B raw13091step0 raw13091step0Labels = mixedMoment B raw13091step1 raw13091step1Labels := by
      have ha : raw13091step1 = (fun i j => raw13091step0 (permutation65 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13091step1 raw13091step0; decide +kernel
      have hl : raw13091step1Labels = raw13091step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13091step0 raw13091step0Labels permutation65 permutation5
    mixedMoment B raw13091step1 raw13091step1Labels = mixedMoment B raw13091step2 raw13091step2Labels := by
      have ha : raw13091step2 = raw13091step1 := by apply Matrix.ext; unfold raw13091step2 raw13091step1; decide +kernel
      have hl : raw13091step1Labels = labelEmbedding1 ∘ raw13091step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13091step1 raw13091step1Labels raw13091step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2246 node2246Labels := by rfl

def raw13092 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13092Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13092step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13092step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13092step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13092step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13092step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13092step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13092 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13092 raw13092Labels = mixedMoment B node3223 node3223Labels := by
  calc
    mixedMoment B raw13092 raw13092Labels = mixedMoment B raw13092step0 raw13092step0Labels := by
      have hz : ∀ j, raw13092 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13092step0 = (fun i j => raw13092 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13092step0 raw13092; decide +kernel
      have hl : raw13092step0Labels = raw13092Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13092 raw13092Labels permutation265 hz
    mixedMoment B raw13092step0 raw13092step0Labels = mixedMoment B raw13092step1 raw13092step1Labels := by
      have ha : raw13092step1 = (fun i j => raw13092step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13092step1 raw13092step0; decide +kernel
      have hl : raw13092step1Labels = raw13092step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13092step0 raw13092step0Labels permutation32 permutation7
    mixedMoment B raw13092step1 raw13092step1Labels = mixedMoment B raw13092step2 raw13092step2Labels := by
      have ha : raw13092step2 = raw13092step1 := by apply Matrix.ext; unfold raw13092step2 raw13092step1; decide +kernel
      have hl : raw13092step1Labels = labelEmbedding1 ∘ raw13092step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13092step1 raw13092step1Labels raw13092step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3223 node3223Labels := by rfl

def raw13093 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13093Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13093step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13093step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13093step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13093step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13093step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13093step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13093 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13093 raw13093Labels = mixedMoment B node3100 node3100Labels := by
  calc
    mixedMoment B raw13093 raw13093Labels = mixedMoment B raw13093step0 raw13093step0Labels := by
      have hz : ∀ j, raw13093 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13093step0 = (fun i j => raw13093 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13093step0 raw13093; decide +kernel
      have hl : raw13093step0Labels = raw13093Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13093 raw13093Labels permutation265 hz
    mixedMoment B raw13093step0 raw13093step0Labels = mixedMoment B raw13093step1 raw13093step1Labels := by
      have ha : raw13093step1 = (fun i j => raw13093step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13093step1 raw13093step0; decide +kernel
      have hl : raw13093step1Labels = raw13093step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13093step0 raw13093step0Labels permutation32 permutation7
    mixedMoment B raw13093step1 raw13093step1Labels = mixedMoment B raw13093step2 raw13093step2Labels := by
      have ha : raw13093step2 = raw13093step1 := by apply Matrix.ext; unfold raw13093step2 raw13093step1; decide +kernel
      have hl : raw13093step1Labels = labelEmbedding1 ∘ raw13093step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13093step1 raw13093step1Labels raw13093step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3100 node3100Labels := by rfl

def raw13094 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw13094Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13094step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, -1, 1], ![-2, 1, 1], ![-1, 0, 1]]
def raw13094step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13094step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13094step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13094step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13094step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13094 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13094 raw13094Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw13094 raw13094Labels = mixedMoment B raw13094step0 raw13094step0Labels := by
      have hz : ∀ j, raw13094 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13094step0 = (fun i j => raw13094 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13094step0 raw13094; decide +kernel
      have hl : raw13094step0Labels = raw13094Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13094 raw13094Labels permutation265 hz
    mixedMoment B raw13094step0 raw13094step0Labels = mixedMoment B raw13094step1 raw13094step1Labels := by
      have ha : raw13094step1 = (fun i j => raw13094step0 (permutation33 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13094step1 raw13094step0; decide +kernel
      have hl : raw13094step1Labels = raw13094step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13094step0 raw13094step0Labels permutation33 permutation7
    mixedMoment B raw13094step1 raw13094step1Labels = mixedMoment B raw13094step2 raw13094step2Labels := by
      have ha : raw13094step2 = raw13094step1 := by apply Matrix.ext; unfold raw13094step2 raw13094step1; decide +kernel
      have hl : raw13094step1Labels = labelEmbedding1 ∘ raw13094step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13094step1 raw13094step1Labels raw13094step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3051 node3051Labels := by rfl

def raw13095 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13095Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13095step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13095step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13095step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13095step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13095step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13095step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13095 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13095 raw13095Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw13095 raw13095Labels = mixedMoment B raw13095step0 raw13095step0Labels := by
      have hz : ∀ j, raw13095 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13095step0 = (fun i j => raw13095 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13095step0 raw13095; decide +kernel
      have hl : raw13095step0Labels = raw13095Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13095 raw13095Labels permutation265 hz
    mixedMoment B raw13095step0 raw13095step0Labels = mixedMoment B raw13095step1 raw13095step1Labels := by
      have ha : raw13095step1 = (fun i j => raw13095step0 (permutation32 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13095step1 raw13095step0; decide +kernel
      have hl : raw13095step1Labels = raw13095step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13095step0 raw13095step0Labels permutation32 permutation7
    mixedMoment B raw13095step1 raw13095step1Labels = mixedMoment B raw13095step2 raw13095step2Labels := by
      have ha : raw13095step2 = raw13095step1 := by apply Matrix.ext; unfold raw13095step2 raw13095step1; decide +kernel
      have hl : raw13095step1Labels = labelEmbedding1 ∘ raw13095step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13095step1 raw13095step1Labels raw13095step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3051 node3051Labels := by rfl

def raw13096 : Matrix (Fin 6) (Fin 3) ℤ := ![![0, 3, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13096Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13096step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![0, 3, -3], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13096step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13096step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13096step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13096step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 3, 0], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13096step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13096 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13096 raw13096Labels = mixedMoment B node3223 node3223Labels := by
  calc
    mixedMoment B raw13096 raw13096Labels = mixedMoment B raw13096step0 raw13096step0Labels := by
      have hz : ∀ j, raw13096 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13096step0 = (fun i j => raw13096 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13096step0 raw13096; decide +kernel
      have hl : raw13096step0Labels = raw13096Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13096 raw13096Labels permutation265 hz
    mixedMoment B raw13096step0 raw13096step0Labels = mixedMoment B raw13096step1 raw13096step1Labels := by
      have ha : raw13096step1 = (fun i j => raw13096step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13096step1 raw13096step0; decide +kernel
      have hl : raw13096step1Labels = raw13096step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13096step0 raw13096step0Labels permutation34 permutation7
    mixedMoment B raw13096step1 raw13096step1Labels = mixedMoment B raw13096step2 raw13096step2Labels := by
      have ha : raw13096step2 = raw13096step1 := by apply Matrix.ext; unfold raw13096step2 raw13096step1; decide +kernel
      have hl : raw13096step1Labels = labelEmbedding1 ∘ raw13096step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13096step1 raw13096step1Labels raw13096step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3223 node3223Labels := by rfl

def raw13097 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13097Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13097step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![1, -1, 0], ![-1, 0, 1], ![0, -1, 1], ![-1, 0, 1]]
def raw13097step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13097step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13097step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13097step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13097step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13097 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13097 raw13097Labels = mixedMoment B node3100 node3100Labels := by
  calc
    mixedMoment B raw13097 raw13097Labels = mixedMoment B raw13097step0 raw13097step0Labels := by
      have hz : ∀ j, raw13097 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13097step0 = (fun i j => raw13097 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13097step0 raw13097; decide +kernel
      have hl : raw13097step0Labels = raw13097Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13097 raw13097Labels permutation265 hz
    mixedMoment B raw13097step0 raw13097step0Labels = mixedMoment B raw13097step1 raw13097step1Labels := by
      have ha : raw13097step1 = (fun i j => raw13097step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13097step1 raw13097step0; decide +kernel
      have hl : raw13097step1Labels = raw13097step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13097step0 raw13097step0Labels permutation34 permutation7
    mixedMoment B raw13097step1 raw13097step1Labels = mixedMoment B raw13097step2 raw13097step2Labels := by
      have ha : raw13097step2 = raw13097step1 := by apply Matrix.ext; unfold raw13097step2 raw13097step1; decide +kernel
      have hl : raw13097step1Labels = labelEmbedding1 ∘ raw13097step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13097step1 raw13097step1Labels raw13097step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3100 node3100Labels := by rfl

def raw13098 : Matrix (Fin 6) (Fin 3) ℤ := ![![1, 2, -3], ![0, 0, 0], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13098Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13098step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![1, 2, -3], ![2, -2, 0], ![-1, 0, 1], ![0, -1, 1], ![-2, 1, 1]]
def raw13098step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13098step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13098step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13098step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -2, 2], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13098step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13098 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13098 raw13098Labels = mixedMoment B node3051 node3051Labels := by
  calc
    mixedMoment B raw13098 raw13098Labels = mixedMoment B raw13098step0 raw13098step0Labels := by
      have hz : ∀ j, raw13098 (permutation265 0) j = 0 := by decide +kernel
      have ha : raw13098step0 = (fun i j => raw13098 (permutation265 i.succ) j) := by apply Matrix.ext; unfold raw13098step0 raw13098; decide +kernel
      have hl : raw13098step0Labels = raw13098Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13098 raw13098Labels permutation265 hz
    mixedMoment B raw13098step0 raw13098step0Labels = mixedMoment B raw13098step1 raw13098step1Labels := by
      have ha : raw13098step1 = (fun i j => raw13098step0 (permutation34 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13098step1 raw13098step0; decide +kernel
      have hl : raw13098step1Labels = raw13098step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13098step0 raw13098step0Labels permutation34 permutation7
    mixedMoment B raw13098step1 raw13098step1Labels = mixedMoment B raw13098step2 raw13098step2Labels := by
      have ha : raw13098step2 = raw13098step1 := by apply Matrix.ext; unfold raw13098step2 raw13098step1; decide +kernel
      have hl : raw13098step1Labels = labelEmbedding1 ∘ raw13098step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13098step1 raw13098step1Labels raw13098step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3051 node3051Labels := by rfl

def raw13099 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13099Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13099 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13099 raw13099Labels = mixedMoment B node5445 node5445Labels := by
  calc
    _ = mixedMoment B node5445 node5445Labels := by rfl

def raw13100 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13100Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13100step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13100step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13100 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13100 raw13100Labels = mixedMoment B node5445 node5445Labels := by
  calc
    mixedMoment B raw13100 raw13100Labels = mixedMoment B raw13100step0 raw13100step0Labels := by
      have ha : raw13100step0 = (fun i j => raw13100 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13100step0 raw13100; decide +kernel
      have hl : raw13100step0Labels = raw13100Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13100 raw13100Labels permutation176 permutation2
    _ = mixedMoment B node5445 node5445Labels := by rfl

def raw13101 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13101Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13101step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13101step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13101step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13101step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13101step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13101step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13101 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13101 raw13101Labels = mixedMoment B node5433 node5433Labels := by
  calc
    mixedMoment B raw13101 raw13101Labels = mixedMoment B raw13101step0 raw13101step0Labels := by
      have ha : raw13101step0 = (fun i j => raw13101 (permutation212 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13101step0 raw13101; decide +kernel
      have hl : raw13101step0Labels = raw13101Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13101 raw13101Labels permutation212 permutation7
    mixedMoment B raw13101step0 raw13101step0Labels = mixedMoment B raw13101step1 raw13101step1Labels := by
      have ha : raw13101step1 = -raw13101step0 := by apply Matrix.ext; change ∀ i j, raw13101step1 i j = -(raw13101step0 i j); unfold raw13101step1 raw13101step0; decide +kernel
      have hl : raw13101step1Labels = raw13101step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13101step1 raw13101step1Labels = mixedMoment B raw13101step2 raw13101step2Labels := by
      have ha : raw13101step2 = raw13101step1 := by apply Matrix.ext; unfold raw13101step2 raw13101step1; decide +kernel
      have hl : raw13101step1Labels = labelEmbedding10 ∘ raw13101step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13101step1 raw13101step1Labels raw13101step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5433 node5433Labels := by rfl

def raw13102 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1]]
def raw13102Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13102step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw13102step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13102step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13102step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13102step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13102step2Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13102step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13102step3Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13102 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13102 raw13102Labels = mixedMoment B node5450 node5450Labels := by
  calc
    mixedMoment B raw13102 raw13102Labels = mixedMoment B raw13102step0 raw13102step0Labels := by
      have hz : ∀ j, raw13102 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13102step0 = (fun i j => raw13102 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13102step0 raw13102; decide +kernel
      have hl : raw13102step0Labels = raw13102Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13102 raw13102Labels permutation520 hz
    mixedMoment B raw13102step0 raw13102step0Labels = mixedMoment B raw13102step1 raw13102step1Labels := by
      have ha : raw13102step1 = (fun i j => raw13102step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13102step1 raw13102step0; decide +kernel
      have hl : raw13102step1Labels = raw13102step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13102step0 raw13102step0Labels permutation44 permutation7
    mixedMoment B raw13102step1 raw13102step1Labels = mixedMoment B raw13102step2 raw13102step2Labels := by
      have ha : raw13102step2 = -raw13102step1 := by apply Matrix.ext; change ∀ i j, raw13102step2 i j = -(raw13102step1 i j); unfold raw13102step2 raw13102step1; decide +kernel
      have hl : raw13102step2Labels = raw13102step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13102step2 raw13102step2Labels = mixedMoment B raw13102step3 raw13102step3Labels := by
      have ha : raw13102step3 = raw13102step2 := by apply Matrix.ext; unfold raw13102step3 raw13102step2; decide +kernel
      have hl : raw13102step2Labels = labelEmbedding10 ∘ raw13102step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13102step2 raw13102step2Labels raw13102step3Labels labelEmbedding10 hl
    _ = mixedMoment B node5450 node5450Labels := by rfl

def raw13103 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw13103Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13103step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw13103step0Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13103step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13103step1Labels : Fin 3 → Fin 3 := ![2, 1, 0]

def raw13103step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13103step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13103 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13103 raw13103Labels = mixedMoment B node5447 node5447Labels := by
  calc
    mixedMoment B raw13103 raw13103Labels = mixedMoment B raw13103step0 raw13103step0Labels := by
      have ha : raw13103step0 = (fun i j => raw13103 (permutation212 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13103step0 raw13103; decide +kernel
      have hl : raw13103step0Labels = raw13103Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13103 raw13103Labels permutation212 permutation7
    mixedMoment B raw13103step0 raw13103step0Labels = mixedMoment B raw13103step1 raw13103step1Labels := by
      have ha : raw13103step1 = -raw13103step0 := by apply Matrix.ext; change ∀ i j, raw13103step1 i j = -(raw13103step0 i j); unfold raw13103step1 raw13103step0; decide +kernel
      have hl : raw13103step1Labels = raw13103step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13103step1 raw13103step1Labels = mixedMoment B raw13103step2 raw13103step2Labels := by
      have ha : raw13103step2 = raw13103step1 := by apply Matrix.ext; unfold raw13103step2 raw13103step1; decide +kernel
      have hl : raw13103step1Labels = labelEmbedding10 ∘ raw13103step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13103step1 raw13103step1Labels raw13103step2Labels labelEmbedding10 hl
    _ = mixedMoment B node5447 node5447Labels := by rfl

def raw13104 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13104Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13104step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13104step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13104step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13104step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13104 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13104 raw13104Labels = mixedMoment B node4599 node4599Labels := by
  calc
    mixedMoment B raw13104 raw13104Labels = mixedMoment B raw13104step0 raw13104step0Labels := by
      have ha : raw13104step0 = (fun i j => raw13104 (permutation181 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13104step0 raw13104; decide +kernel
      have hl : raw13104step0Labels = raw13104Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13104 raw13104Labels permutation181 permutation3
    mixedMoment B raw13104step0 raw13104step0Labels = mixedMoment B raw13104step1 raw13104step1Labels := by
      have ha : raw13104step1 = raw13104step0 := by apply Matrix.ext; unfold raw13104step1 raw13104step0; decide +kernel
      have hl : raw13104step0Labels = labelEmbedding6 ∘ raw13104step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13104step0 raw13104step0Labels raw13104step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4599 node4599Labels := by rfl

def raw13105 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13105Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13105step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13105step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13105 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13105 raw13105Labels = mixedMoment B node5197 node5197Labels := by
  calc
    mixedMoment B raw13105 raw13105Labels = mixedMoment B raw13105step0 raw13105step0Labels := by
      have ha : raw13105step0 = (fun i j => raw13105 (permutation184 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13105step0 raw13105; decide +kernel
      have hl : raw13105step0Labels = raw13105Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13105 raw13105Labels permutation184 permutation2
    _ = mixedMoment B node5197 node5197Labels := by rfl

def raw13106 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13106Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13106step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13106step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13106 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13106 raw13106Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw13106 raw13106Labels = mixedMoment B raw13106step0 raw13106step0Labels := by
      have ha : raw13106step0 = (fun i j => raw13106 (permutation208 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13106step0 raw13106; decide +kernel
      have hl : raw13106step0Labels = raw13106Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13106 raw13106Labels permutation208 permutation2
    _ = mixedMoment B node5257 node5257Labels := by rfl

def raw13107 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1]]
def raw13107Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13107step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw13107step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13107step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13107step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13107 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13107 raw13107Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw13107 raw13107Labels = mixedMoment B raw13107step0 raw13107step0Labels := by
      have hz : ∀ j, raw13107 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13107step0 = (fun i j => raw13107 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13107step0 raw13107; decide +kernel
      have hl : raw13107step0Labels = raw13107Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13107 raw13107Labels permutation520 hz
    mixedMoment B raw13107step0 raw13107step0Labels = mixedMoment B raw13107step1 raw13107step1Labels := by
      have ha : raw13107step1 = (fun i j => raw13107step0 (permutation40 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13107step1 raw13107step0; decide +kernel
      have hl : raw13107step1Labels = raw13107step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13107step0 raw13107step0Labels permutation40 permutation2
    _ = mixedMoment B node5290 node5290Labels := by rfl

def raw13108 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw13108Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13108step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13108step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13108 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13108 raw13108Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw13108 raw13108Labels = mixedMoment B raw13108step0 raw13108step0Labels := by
      have ha : raw13108step0 = (fun i j => raw13108 (permutation197 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13108step0 raw13108; decide +kernel
      have hl : raw13108step0Labels = raw13108Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13108 raw13108Labels permutation197 permutation2
    _ = mixedMoment B node5281 node5281Labels := by rfl

def raw13109 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13109Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13109step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13109step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13109step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13109step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13109 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13109 raw13109Labels = mixedMoment B node4599 node4599Labels := by
  calc
    mixedMoment B raw13109 raw13109Labels = mixedMoment B raw13109step0 raw13109step0Labels := by
      have ha : raw13109step0 = (fun i j => raw13109 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13109step0 raw13109; decide +kernel
      have hl : raw13109step0Labels = raw13109Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13109 raw13109Labels permutation157 permutation3
    mixedMoment B raw13109step0 raw13109step0Labels = mixedMoment B raw13109step1 raw13109step1Labels := by
      have ha : raw13109step1 = raw13109step0 := by apply Matrix.ext; unfold raw13109step1 raw13109step0; decide +kernel
      have hl : raw13109step0Labels = labelEmbedding6 ∘ raw13109step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13109step0 raw13109step0Labels raw13109step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4599 node4599Labels := by rfl

def raw13110 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13110Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13110step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13110step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13110 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13110 raw13110Labels = mixedMoment B node5197 node5197Labels := by
  calc
    mixedMoment B raw13110 raw13110Labels = mixedMoment B raw13110step0 raw13110step0Labels := by
      have ha : raw13110step0 = (fun i j => raw13110 (permutation160 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13110step0 raw13110; decide +kernel
      have hl : raw13110step0Labels = raw13110Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13110 raw13110Labels permutation160 permutation2
    _ = mixedMoment B node5197 node5197Labels := by rfl

def raw13111 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13111Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13111step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13111step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13111 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13111 raw13111Labels = mixedMoment B node5257 node5257Labels := by
  calc
    mixedMoment B raw13111 raw13111Labels = mixedMoment B raw13111step0 raw13111step0Labels := by
      have ha : raw13111step0 = (fun i j => raw13111 (permutation202 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13111step0 raw13111; decide +kernel
      have hl : raw13111step0Labels = raw13111Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13111 raw13111Labels permutation202 permutation2
    _ = mixedMoment B node5257 node5257Labels := by rfl

def raw13112 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1]]
def raw13112Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13112step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw13112step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13112step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13112step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13112 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13112 raw13112Labels = mixedMoment B node5290 node5290Labels := by
  calc
    mixedMoment B raw13112 raw13112Labels = mixedMoment B raw13112step0 raw13112step0Labels := by
      have hz : ∀ j, raw13112 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13112step0 = (fun i j => raw13112 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13112step0 raw13112; decide +kernel
      have hl : raw13112step0Labels = raw13112Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13112 raw13112Labels permutation520 hz
    mixedMoment B raw13112step0 raw13112step0Labels = mixedMoment B raw13112step1 raw13112step1Labels := by
      have ha : raw13112step1 = (fun i j => raw13112step0 (permutation34 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13112step1 raw13112step0; decide +kernel
      have hl : raw13112step1Labels = raw13112step0Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13112step0 raw13112step0Labels permutation34 permutation2
    _ = mixedMoment B node5290 node5290Labels := by rfl

def raw13113 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw13113Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13113step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13113step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13113 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13113 raw13113Labels = mixedMoment B node5281 node5281Labels := by
  calc
    mixedMoment B raw13113 raw13113Labels = mixedMoment B raw13113step0 raw13113step0Labels := by
      have ha : raw13113step0 = (fun i j => raw13113 (permutation173 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13113step0 raw13113; decide +kernel
      have hl : raw13113step0Labels = raw13113Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13113 raw13113Labels permutation173 permutation2
    _ = mixedMoment B node5281 node5281Labels := by rfl

def raw13114 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13114Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13114step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw13114step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13114step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw13114step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13114 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13114 raw13114Labels = mixedMoment B node4579 node4579Labels := by
  calc
    mixedMoment B raw13114 raw13114Labels = mixedMoment B raw13114step0 raw13114step0Labels := by
      have ha : raw13114step0 = (fun i j => raw13114 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13114step0 raw13114; decide +kernel
      have hl : raw13114step0Labels = raw13114Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13114 raw13114Labels permutation157 permutation3
    mixedMoment B raw13114step0 raw13114step0Labels = mixedMoment B raw13114step1 raw13114step1Labels := by
      have ha : raw13114step1 = raw13114step0 := by apply Matrix.ext; unfold raw13114step1 raw13114step0; decide +kernel
      have hl : raw13114step0Labels = labelEmbedding6 ∘ raw13114step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13114step0 raw13114step0Labels raw13114step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4579 node4579Labels := by rfl

def raw13115 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13115Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13115step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw13115step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw13115step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw13115step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13115 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13115 raw13115Labels = mixedMoment B node5057 node5057Labels := by
  calc
    mixedMoment B raw13115 raw13115Labels = mixedMoment B raw13115step0 raw13115step0Labels := by
      have ha : raw13115step0 = (fun i j => raw13115 (permutation503 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13115step0 raw13115; decide +kernel
      have hl : raw13115step0Labels = raw13115Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13115 raw13115Labels permutation503 permutation5
    mixedMoment B raw13115step0 raw13115step0Labels = mixedMoment B raw13115step1 raw13115step1Labels := by
      have ha : raw13115step1 = raw13115step0 := by apply Matrix.ext; unfold raw13115step1 raw13115step0; decide +kernel
      have hl : raw13115step0Labels = labelEmbedding8 ∘ raw13115step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13115step0 raw13115step0Labels raw13115step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5057 node5057Labels := by rfl

def raw13116 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13116Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13116step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw13116step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw13116step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw13116step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13116 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13116 raw13116Labels = mixedMoment B node5057 node5057Labels := by
  calc
    mixedMoment B raw13116 raw13116Labels = mixedMoment B raw13116step0 raw13116step0Labels := by
      have ha : raw13116step0 = (fun i j => raw13116 (permutation501 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13116step0 raw13116; decide +kernel
      have hl : raw13116step0Labels = raw13116Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13116 raw13116Labels permutation501 permutation5
    mixedMoment B raw13116step0 raw13116step0Labels = mixedMoment B raw13116step1 raw13116step1Labels := by
      have ha : raw13116step1 = raw13116step0 := by apply Matrix.ext; unfold raw13116step1 raw13116step0; decide +kernel
      have hl : raw13116step0Labels = labelEmbedding8 ∘ raw13116step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13116step0 raw13116step0Labels raw13116step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5057 node5057Labels := by rfl

def raw13117 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![0, 0, 0], ![1, 0, -1]]
def raw13117Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13117step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw13117step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13117step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13117step1Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw13117step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13117step2Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13117 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13117 raw13117Labels = mixedMoment B node5270 node5270Labels := by
  calc
    mixedMoment B raw13117 raw13117Labels = mixedMoment B raw13117step0 raw13117step0Labels := by
      have hz : ∀ j, raw13117 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13117step0 = (fun i j => raw13117 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13117step0 raw13117; decide +kernel
      have hl : raw13117step0Labels = raw13117Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13117 raw13117Labels permutation520 hz
    mixedMoment B raw13117step0 raw13117step0Labels = mixedMoment B raw13117step1 raw13117step1Labels := by
      have ha : raw13117step1 = (fun i j => raw13117step0 (permutation125 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13117step1 raw13117step0; decide +kernel
      have hl : raw13117step1Labels = raw13117step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13117step0 raw13117step0Labels permutation125 permutation5
    mixedMoment B raw13117step1 raw13117step1Labels = mixedMoment B raw13117step2 raw13117step2Labels := by
      have ha : raw13117step2 = raw13117step1 := by apply Matrix.ext; unfold raw13117step2 raw13117step1; decide +kernel
      have hl : raw13117step1Labels = labelEmbedding8 ∘ raw13117step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13117step1 raw13117step1Labels raw13117step2Labels labelEmbedding8 hl
    _ = mixedMoment B node5270 node5270Labels := by rfl

def raw13118 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![0, 1, -1]]
def raw13118Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13118step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13118step0Labels : Fin 3 → Fin 3 := ![1, 2, 0]

def raw13118step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13118step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13118 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13118 raw13118Labels = mixedMoment B node5097 node5097Labels := by
  calc
    mixedMoment B raw13118 raw13118Labels = mixedMoment B raw13118step0 raw13118step0Labels := by
      have ha : raw13118step0 = (fun i j => raw13118 (permutation492 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13118step0 raw13118; decide +kernel
      have hl : raw13118step0Labels = raw13118Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13118 raw13118Labels permutation492 permutation5
    mixedMoment B raw13118step0 raw13118step0Labels = mixedMoment B raw13118step1 raw13118step1Labels := by
      have ha : raw13118step1 = raw13118step0 := by apply Matrix.ext; unfold raw13118step1 raw13118step0; decide +kernel
      have hl : raw13118step0Labels = labelEmbedding8 ∘ raw13118step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13118step0 raw13118step0Labels raw13118step1Labels labelEmbedding8 hl
    _ = mixedMoment B node5097 node5097Labels := by rfl

def raw13119 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw13119Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13119step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw13119step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13119step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw13119step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13119 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13119 raw13119Labels = mixedMoment B node4580 node4580Labels := by
  calc
    mixedMoment B raw13119 raw13119Labels = mixedMoment B raw13119step0 raw13119step0Labels := by
      have ha : raw13119step0 = (fun i j => raw13119 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13119step0 raw13119; decide +kernel
      have hl : raw13119step0Labels = raw13119Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13119 raw13119Labels permutation156 permutation3
    mixedMoment B raw13119step0 raw13119step0Labels = mixedMoment B raw13119step1 raw13119step1Labels := by
      have ha : raw13119step1 = raw13119step0 := by apply Matrix.ext; unfold raw13119step1 raw13119step0; decide +kernel
      have hl : raw13119step0Labels = labelEmbedding6 ∘ raw13119step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13119step0 raw13119step0Labels raw13119step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4580 node4580Labels := by rfl

def raw13120 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw13120Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13120step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw13120step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13120 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13120 raw13120Labels = mixedMoment B node5191 node5191Labels := by
  calc
    mixedMoment B raw13120 raw13120Labels = mixedMoment B raw13120step0 raw13120step0Labels := by
      have ha : raw13120step0 = (fun i j => raw13120 (permutation153 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13120step0 raw13120; decide +kernel
      have hl : raw13120step0Labels = raw13120Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13120 raw13120Labels permutation153 permutation2
    _ = mixedMoment B node5191 node5191Labels := by rfl

def raw13121 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw13121Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13121step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![2, -2, 0]]
def raw13121step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13121 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13121 raw13121Labels = mixedMoment B node5191 node5191Labels := by
  calc
    mixedMoment B raw13121 raw13121Labels = mixedMoment B raw13121step0 raw13121step0Labels := by
      have ha : raw13121step0 = (fun i j => raw13121 (permutation177 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13121step0 raw13121; decide +kernel
      have hl : raw13121step0Labels = raw13121Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13121 raw13121Labels permutation177 permutation2
    _ = mixedMoment B node5191 node5191Labels := by rfl

def raw13122 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1]]
def raw13122Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13122step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -2, 0]]
def raw13122step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13122 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13122 raw13122Labels = mixedMoment B node5251 node5251Labels := by
  calc
    mixedMoment B raw13122 raw13122Labels = mixedMoment B raw13122step0 raw13122step0Labels := by
      have ha : raw13122step0 = (fun i j => raw13122 (permutation201 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13122step0 raw13122; decide +kernel
      have hl : raw13122step0Labels = raw13122Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13122 raw13122Labels permutation201 permutation2
    _ = mixedMoment B node5251 node5251Labels := by rfl

def raw13123 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![0, 1, -1]]
def raw13123Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13123step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0]]
def raw13123step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13123 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13123 raw13123Labels = mixedMoment B node5277 node5277Labels := by
  calc
    mixedMoment B raw13123 raw13123Labels = mixedMoment B raw13123step0 raw13123step0Labels := by
      have ha : raw13123step0 = (fun i j => raw13123 (permutation156 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13123step0 raw13123; decide +kernel
      have hl : raw13123step0Labels = raw13123Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13123 raw13123Labels permutation156 permutation2
    _ = mixedMoment B node5277 node5277Labels := by rfl

def raw13124 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw13124Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13124step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw13124step0Labels : Fin 3 → Fin 3 := ![0, 2, 1]

def raw13124step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw13124step1Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13124 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13124 raw13124Labels = mixedMoment B node4582 node4582Labels := by
  calc
    mixedMoment B raw13124 raw13124Labels = mixedMoment B raw13124step0 raw13124step0Labels := by
      have ha : raw13124step0 = (fun i j => raw13124 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13124step0 raw13124; decide +kernel
      have hl : raw13124step0Labels = raw13124Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13124 raw13124Labels permutation154 permutation3
    mixedMoment B raw13124step0 raw13124step0Labels = mixedMoment B raw13124step1 raw13124step1Labels := by
      have ha : raw13124step1 = raw13124step0 := by apply Matrix.ext; unfold raw13124step1 raw13124step0; decide +kernel
      have hl : raw13124step0Labels = labelEmbedding6 ∘ raw13124step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13124step0 raw13124step0Labels raw13124step1Labels labelEmbedding6 hl
    _ = mixedMoment B node4582 node4582Labels := by rfl

def raw13125 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw13125Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13125 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13125 raw13125Labels = mixedMoment B node5190 node5190Labels := by
  calc
    _ = mixedMoment B node5190 node5190Labels := by rfl

def raw13126 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw13126Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13126step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw13126step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13126 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13126 raw13126Labels = mixedMoment B node5190 node5190Labels := by
  calc
    mixedMoment B raw13126 raw13126Labels = mixedMoment B raw13126step0 raw13126step0Labels := by
      have ha : raw13126step0 = (fun i j => raw13126 (permutation176 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13126step0 raw13126; decide +kernel
      have hl : raw13126step0Labels = raw13126Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13126 raw13126Labels permutation176 permutation2
    _ = mixedMoment B node5190 node5190Labels := by rfl

def raw13127 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw13127Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13127step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![0, 1, -1], ![0, 1, -1], ![1, -1, 0], ![2, -1, -1]]
def raw13127step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13127 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13127 raw13127Labels = mixedMoment B node5250 node5250Labels := by
  calc
    mixedMoment B raw13127 raw13127Labels = mixedMoment B raw13127step0 raw13127step0Labels := by
      have ha : raw13127step0 = (fun i j => raw13127 (permutation200 i) (permutation2 j)) := by apply Matrix.ext; unfold raw13127step0 raw13127; decide +kernel
      have hl : raw13127step0Labels = raw13127Labels ∘ permutation2 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13127 raw13127Labels permutation200 permutation2
    _ = mixedMoment B node5250 node5250Labels := by rfl

def raw13128 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![2, -1, -1]]
def raw13128Labels : Fin 3 → Fin 3 := ![0, 1, 2]

def raw13128step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw13128step0Labels : Fin 3 → Fin 3 := ![0, 1, 2]

theorem canonical13128 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13128 raw13128Labels = mixedMoment B node5282 node5282Labels := by
  calc
    mixedMoment B raw13128 raw13128Labels = mixedMoment B raw13128step0 raw13128step0Labels := by
      have hz : ∀ j, raw13128 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13128step0 = (fun i j => raw13128 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13128step0 raw13128; decide +kernel
      have hl : raw13128step0Labels = raw13128Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13128 raw13128Labels permutation520 hz
    _ = mixedMoment B node5282 node5282Labels := by rfl

def raw13129 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13129Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13129step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13129step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13129 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13129 raw13129Labels = mixedMoment B node4024 node4024Labels := by
  calc
    mixedMoment B raw13129 raw13129Labels = mixedMoment B raw13129step0 raw13129step0Labels := by
      have ha : raw13129step0 = (fun i j => raw13129 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13129step0 raw13129; decide +kernel
      have hl : raw13129step0Labels = raw13129Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13129 raw13129Labels permutation157 permutation3
    _ = mixedMoment B node4024 node4024Labels := by rfl

def raw13130 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13130Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13130step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13130step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13130 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13130 raw13130Labels = mixedMoment B node4024 node4024Labels := by
  calc
    mixedMoment B raw13130 raw13130Labels = mixedMoment B raw13130step0 raw13130step0Labels := by
      have ha : raw13130step0 = (fun i j => raw13130 (permutation181 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13130step0 raw13130; decide +kernel
      have hl : raw13130step0Labels = raw13130Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13130 raw13130Labels permutation181 permutation3
    _ = mixedMoment B node4024 node4024Labels := by rfl

def raw13131 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13131Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13131step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 0, -1], ![0, 1, -1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13131step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13131step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13131step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13131 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13131 raw13131Labels = mixedMoment B node4033 node4033Labels := by
  calc
    mixedMoment B raw13131 raw13131Labels = mixedMoment B raw13131step0 raw13131step0Labels := by
      have ha : raw13131step0 = (fun i j => raw13131 (permutation216 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13131step0 raw13131; decide +kernel
      have hl : raw13131step0Labels = raw13131Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13131 raw13131Labels permutation216 permutation6
    mixedMoment B raw13131step0 raw13131step0Labels = mixedMoment B raw13131step1 raw13131step1Labels := by
      have ha : raw13131step1 = -raw13131step0 := by apply Matrix.ext; change ∀ i j, raw13131step1 i j = -(raw13131step0 i j); unfold raw13131step1 raw13131step0; decide +kernel
      have hl : raw13131step1Labels = raw13131step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4033 node4033Labels := by rfl

def raw13132 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1]]
def raw13132Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13132step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw13132step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13132step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13132step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13132step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13132step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13132 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13132 raw13132Labels = mixedMoment B node4029 node4029Labels := by
  calc
    mixedMoment B raw13132 raw13132Labels = mixedMoment B raw13132step0 raw13132step0Labels := by
      have hz : ∀ j, raw13132 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13132step0 = (fun i j => raw13132 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13132step0 raw13132; decide +kernel
      have hl : raw13132step0Labels = raw13132Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13132 raw13132Labels permutation520 hz
    mixedMoment B raw13132step0 raw13132step0Labels = mixedMoment B raw13132step1 raw13132step1Labels := by
      have ha : raw13132step1 = (fun i j => raw13132step0 (permutation48 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13132step1 raw13132step0; decide +kernel
      have hl : raw13132step1Labels = raw13132step0Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13132step0 raw13132step0Labels permutation48 permutation6
    mixedMoment B raw13132step1 raw13132step1Labels = mixedMoment B raw13132step2 raw13132step2Labels := by
      have ha : raw13132step2 = -raw13132step1 := by apply Matrix.ext; change ∀ i j, raw13132step2 i j = -(raw13132step1 i j); unfold raw13132step2 raw13132step1; decide +kernel
      have hl : raw13132step2Labels = raw13132step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4029 node4029Labels := by rfl

def raw13133 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw13133Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13133step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, -2, 0], ![1, 1, -2], ![0, 1, -1], ![-1, 0, 1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13133step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

def raw13133step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 2, 0], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 0, -1], ![1, 0, -1]]
def raw13133step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13133 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13133 raw13133Labels = mixedMoment B node4025 node4025Labels := by
  calc
    mixedMoment B raw13133 raw13133Labels = mixedMoment B raw13133step0 raw13133step0Labels := by
      have ha : raw13133step0 = (fun i j => raw13133 (permutation212 i) (permutation6 j)) := by apply Matrix.ext; unfold raw13133step0 raw13133; decide +kernel
      have hl : raw13133step0Labels = raw13133Labels ∘ permutation6 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13133 raw13133Labels permutation212 permutation6
    mixedMoment B raw13133step0 raw13133step0Labels = mixedMoment B raw13133step1 raw13133step1Labels := by
      have ha : raw13133step1 = -raw13133step0 := by apply Matrix.ext; change ∀ i j, raw13133step1 i j = -(raw13133step0 i j); unfold raw13133step1 raw13133step0; decide +kernel
      have hl : raw13133step1Labels = raw13133step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    _ = mixedMoment B node4025 node4025Labels := by rfl

def raw13134 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13134Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13134step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13134step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13134 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13134 raw13134Labels = mixedMoment B node1233 node1233Labels := by
  calc
    mixedMoment B raw13134 raw13134Labels = mixedMoment B raw13134step0 raw13134step0Labels := by
      have ha : raw13134step0 = (fun i j => raw13134 (permutation181 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13134step0 raw13134; decide +kernel
      have hl : raw13134step0Labels = raw13134Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13134 raw13134Labels permutation181 permutation3
    _ = mixedMoment B node1233 node1233Labels := by rfl

def raw13135 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13135Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13135step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13135step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13135 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13135 raw13135Labels = mixedMoment B node2878 node2878Labels := by
  calc
    mixedMoment B raw13135 raw13135Labels = mixedMoment B raw13135step0 raw13135step0Labels := by
      have ha : raw13135step0 = (fun i j => raw13135 (permutation181 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13135step0 raw13135; decide +kernel
      have hl : raw13135step0Labels = raw13135Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13135 raw13135Labels permutation181 permutation3
    _ = mixedMoment B node2878 node2878Labels := by rfl

def raw13136 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13136Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13136step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13136step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13136 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13136 raw13136Labels = mixedMoment B node3087 node3087Labels := by
  calc
    mixedMoment B raw13136 raw13136Labels = mixedMoment B raw13136step0 raw13136step0Labels := by
      have ha : raw13136step0 = (fun i j => raw13136 (permutation183 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13136step0 raw13136; decide +kernel
      have hl : raw13136step0Labels = raw13136Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13136 raw13136Labels permutation183 permutation3
    _ = mixedMoment B node3087 node3087Labels := by rfl

def raw13137 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1]]
def raw13137Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13137step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw13137step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13137step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13137step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13137 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13137 raw13137Labels = mixedMoment B node3099 node3099Labels := by
  calc
    mixedMoment B raw13137 raw13137Labels = mixedMoment B raw13137step0 raw13137step0Labels := by
      have hz : ∀ j, raw13137 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13137step0 = (fun i j => raw13137 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13137step0 raw13137; decide +kernel
      have hl : raw13137step0Labels = raw13137Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13137 raw13137Labels permutation520 hz
    mixedMoment B raw13137step0 raw13137step0Labels = mixedMoment B raw13137step1 raw13137step1Labels := by
      have ha : raw13137step1 = (fun i j => raw13137step0 (permutation39 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13137step1 raw13137step0; decide +kernel
      have hl : raw13137step1Labels = raw13137step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13137step0 raw13137step0Labels permutation39 permutation3
    _ = mixedMoment B node3099 node3099Labels := by rfl

def raw13138 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw13138Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13138step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13138step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13138 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13138 raw13138Labels = mixedMoment B node3074 node3074Labels := by
  calc
    mixedMoment B raw13138 raw13138Labels = mixedMoment B raw13138step0 raw13138step0Labels := by
      have ha : raw13138step0 = (fun i j => raw13138 (permutation195 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13138step0 raw13138; decide +kernel
      have hl : raw13138step0Labels = raw13138Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13138 raw13138Labels permutation195 permutation3
    _ = mixedMoment B node3074 node3074Labels := by rfl

def raw13139 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13139Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13139step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13139step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13139 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13139 raw13139Labels = mixedMoment B node1233 node1233Labels := by
  calc
    mixedMoment B raw13139 raw13139Labels = mixedMoment B raw13139step0 raw13139step0Labels := by
      have ha : raw13139step0 = (fun i j => raw13139 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13139step0 raw13139; decide +kernel
      have hl : raw13139step0Labels = raw13139Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13139 raw13139Labels permutation157 permutation3
    _ = mixedMoment B node1233 node1233Labels := by rfl

def raw13140 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13140Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13140step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13140step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13140 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13140 raw13140Labels = mixedMoment B node2878 node2878Labels := by
  calc
    mixedMoment B raw13140 raw13140Labels = mixedMoment B raw13140step0 raw13140step0Labels := by
      have ha : raw13140step0 = (fun i j => raw13140 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13140step0 raw13140; decide +kernel
      have hl : raw13140step0Labels = raw13140Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13140 raw13140Labels permutation157 permutation3
    _ = mixedMoment B node2878 node2878Labels := by rfl

def raw13141 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13141Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13141step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13141step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13141 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13141 raw13141Labels = mixedMoment B node3087 node3087Labels := by
  calc
    mixedMoment B raw13141 raw13141Labels = mixedMoment B raw13141step0 raw13141step0Labels := by
      have ha : raw13141step0 = (fun i j => raw13141 (permutation159 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13141step0 raw13141; decide +kernel
      have hl : raw13141step0Labels = raw13141Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13141 raw13141Labels permutation159 permutation3
    _ = mixedMoment B node3087 node3087Labels := by rfl

def raw13142 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1]]
def raw13142Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13142step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw13142step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13142step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 1, -2]]
def raw13142step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13142 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13142 raw13142Labels = mixedMoment B node3099 node3099Labels := by
  calc
    mixedMoment B raw13142 raw13142Labels = mixedMoment B raw13142step0 raw13142step0Labels := by
      have hz : ∀ j, raw13142 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13142step0 = (fun i j => raw13142 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13142step0 raw13142; decide +kernel
      have hl : raw13142step0Labels = raw13142Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13142 raw13142Labels permutation520 hz
    mixedMoment B raw13142step0 raw13142step0Labels = mixedMoment B raw13142step1 raw13142step1Labels := by
      have ha : raw13142step1 = (fun i j => raw13142step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13142step1 raw13142step0; decide +kernel
      have hl : raw13142step1Labels = raw13142step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13142step0 raw13142step0Labels permutation33 permutation3
    _ = mixedMoment B node3099 node3099Labels := by rfl

def raw13143 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw13143Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13143step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![1, 1, -2]]
def raw13143step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13143 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13143 raw13143Labels = mixedMoment B node3074 node3074Labels := by
  calc
    mixedMoment B raw13143 raw13143Labels = mixedMoment B raw13143step0 raw13143step0Labels := by
      have ha : raw13143step0 = (fun i j => raw13143 (permutation171 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13143step0 raw13143; decide +kernel
      have hl : raw13143step0Labels = raw13143Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13143 raw13143Labels permutation171 permutation3
    _ = mixedMoment B node3074 node3074Labels := by rfl

def raw13144 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13144Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13144step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw13144step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13144 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13144 raw13144Labels = mixedMoment B node1197 node1197Labels := by
  calc
    mixedMoment B raw13144 raw13144Labels = mixedMoment B raw13144step0 raw13144step0Labels := by
      have ha : raw13144step0 = (fun i j => raw13144 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13144step0 raw13144; decide +kernel
      have hl : raw13144step0Labels = raw13144Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13144 raw13144Labels permutation157 permutation3
    _ = mixedMoment B node1197 node1197Labels := by rfl

def raw13145 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13145Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13145step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw13145step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13145 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13145 raw13145Labels = mixedMoment B node2851 node2851Labels := by
  calc
    mixedMoment B raw13145 raw13145Labels = mixedMoment B raw13145step0 raw13145step0Labels := by
      have ha : raw13145step0 = (fun i j => raw13145 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13145step0 raw13145; decide +kernel
      have hl : raw13145step0Labels = raw13145Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13145 raw13145Labels permutation157 permutation3
    _ = mixedMoment B node2851 node2851Labels := by rfl

def raw13146 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13146Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13146step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1], ![2, 1, -3]]
def raw13146step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13146 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13146 raw13146Labels = mixedMoment B node2851 node2851Labels := by
  calc
    mixedMoment B raw13146 raw13146Labels = mixedMoment B raw13146step0 raw13146step0Labels := by
      have ha : raw13146step0 = (fun i j => raw13146 (permutation181 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13146step0 raw13146; decide +kernel
      have hl : raw13146step0Labels = raw13146Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13146 raw13146Labels permutation181 permutation3
    _ = mixedMoment B node2851 node2851Labels := by rfl

def raw13147 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![0, 0, 0], ![1, 0, -1]]
def raw13147Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13147step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw13147step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13147step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![2, 1, -3]]
def raw13147step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13147 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13147 raw13147Labels = mixedMoment B node3075 node3075Labels := by
  calc
    mixedMoment B raw13147 raw13147Labels = mixedMoment B raw13147step0 raw13147step0Labels := by
      have hz : ∀ j, raw13147 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13147step0 = (fun i j => raw13147 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13147step0 raw13147; decide +kernel
      have hl : raw13147step0Labels = raw13147Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13147 raw13147Labels permutation520 hz
    mixedMoment B raw13147step0 raw13147step0Labels = mixedMoment B raw13147step1 raw13147step1Labels := by
      have ha : raw13147step1 = (fun i j => raw13147step0 (permutation33 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13147step1 raw13147step0; decide +kernel
      have hl : raw13147step1Labels = raw13147step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13147step0 raw13147step0Labels permutation33 permutation3
    _ = mixedMoment B node3075 node3075Labels := by rfl

def raw13148 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![0, 1, -1]]
def raw13148Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13148step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![2, 1, -3]]
def raw13148step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13148 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13148 raw13148Labels = mixedMoment B node3058 node3058Labels := by
  calc
    mixedMoment B raw13148 raw13148Labels = mixedMoment B raw13148step0 raw13148step0Labels := by
      have ha : raw13148step0 = (fun i j => raw13148 (permutation157 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13148step0 raw13148; decide +kernel
      have hl : raw13148step0Labels = raw13148Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13148 raw13148Labels permutation157 permutation3
    _ = mixedMoment B node3058 node3058Labels := by rfl

def raw13149 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw13149Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13149step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw13149step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13149 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13149 raw13149Labels = mixedMoment B node1198 node1198Labels := by
  calc
    mixedMoment B raw13149 raw13149Labels = mixedMoment B raw13149step0 raw13149step0Labels := by
      have ha : raw13149step0 = (fun i j => raw13149 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13149step0 raw13149; decide +kernel
      have hl : raw13149step0Labels = raw13149Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13149 raw13149Labels permutation156 permutation3
    _ = mixedMoment B node1198 node1198Labels := by rfl

def raw13150 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw13150Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13150step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw13150step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13150 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13150 raw13150Labels = mixedMoment B node2852 node2852Labels := by
  calc
    mixedMoment B raw13150 raw13150Labels = mixedMoment B raw13150step0 raw13150step0Labels := by
      have ha : raw13150step0 = (fun i j => raw13150 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13150step0 raw13150; decide +kernel
      have hl : raw13150step0Labels = raw13150Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13150 raw13150Labels permutation156 permutation3
    _ = mixedMoment B node2852 node2852Labels := by rfl

def raw13151 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw13151Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13151step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, -1, 0], ![1, 1, -2], ![2, 0, -2]]
def raw13151step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13151 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13151 raw13151Labels = mixedMoment B node2852 node2852Labels := by
  calc
    mixedMoment B raw13151 raw13151Labels = mixedMoment B raw13151step0 raw13151step0Labels := by
      have ha : raw13151step0 = (fun i j => raw13151 (permutation180 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13151step0 raw13151; decide +kernel
      have hl : raw13151step0Labels = raw13151Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13151 raw13151Labels permutation180 permutation3
    _ = mixedMoment B node2852 node2852Labels := by rfl

def raw13152 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1]]
def raw13152Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13152step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, -1, 0], ![2, 0, -2]]
def raw13152step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13152 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13152 raw13152Labels = mixedMoment B node3064 node3064Labels := by
  calc
    mixedMoment B raw13152 raw13152Labels = mixedMoment B raw13152step0 raw13152step0Labels := by
      have ha : raw13152step0 = (fun i j => raw13152 (permutation153 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13152step0 raw13152; decide +kernel
      have hl : raw13152step0Labels = raw13152Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13152 raw13152Labels permutation153 permutation3
    _ = mixedMoment B node3064 node3064Labels := by rfl

def raw13153 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![0, 1, -1]]
def raw13153Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13153step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, 0, -2]]
def raw13153step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13153 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13153 raw13153Labels = mixedMoment B node3059 node3059Labels := by
  calc
    mixedMoment B raw13153 raw13153Labels = mixedMoment B raw13153step0 raw13153step0Labels := by
      have ha : raw13153step0 = (fun i j => raw13153 (permutation156 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13153step0 raw13153; decide +kernel
      have hl : raw13153step0Labels = raw13153Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13153 raw13153Labels permutation156 permutation3
    _ = mixedMoment B node3059 node3059Labels := by rfl

def raw13154 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw13154Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13154step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, -1, 1], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw13154step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13154 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13154 raw13154Labels = mixedMoment B node1201 node1201Labels := by
  calc
    mixedMoment B raw13154 raw13154Labels = mixedMoment B raw13154step0 raw13154step0Labels := by
      have ha : raw13154step0 = (fun i j => raw13154 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13154step0 raw13154; decide +kernel
      have hl : raw13154step0Labels = raw13154Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13154 raw13154Labels permutation154 permutation3
    _ = mixedMoment B node1201 node1201Labels := by rfl

def raw13155 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw13155Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13155step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw13155step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13155 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13155 raw13155Labels = mixedMoment B node2854 node2854Labels := by
  calc
    mixedMoment B raw13155 raw13155Labels = mixedMoment B raw13155step0 raw13155step0Labels := by
      have ha : raw13155step0 = (fun i j => raw13155 (permutation154 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13155step0 raw13155; decide +kernel
      have hl : raw13155step0Labels = raw13155Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13155 raw13155Labels permutation154 permutation3
    _ = mixedMoment B node2854 node2854Labels := by rfl

def raw13156 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![2, -1, -1]]
def raw13156Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13156step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![-1, -1, 2], ![0, -1, 1], ![1, 0, -1], ![1, 1, -2], ![2, -1, -1]]
def raw13156step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13156 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13156 raw13156Labels = mixedMoment B node2854 node2854Labels := by
  calc
    mixedMoment B raw13156 raw13156Labels = mixedMoment B raw13156step0 raw13156step0Labels := by
      have ha : raw13156step0 = (fun i j => raw13156 (permutation178 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13156step0 raw13156; decide +kernel
      have hl : raw13156step0Labels = raw13156Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13156 raw13156Labels permutation178 permutation3
    _ = mixedMoment B node2854 node2854Labels := by rfl

def raw13157 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![2, -1, -1]]
def raw13157Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13157step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13157step0Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13157 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13157 raw13157Labels = mixedMoment B node3065 node3065Labels := by
  calc
    mixedMoment B raw13157 raw13157Labels = mixedMoment B raw13157step0 raw13157step0Labels := by
      have ha : raw13157step0 = (fun i j => raw13157 (permutation152 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13157step0 raw13157; decide +kernel
      have hl : raw13157step0Labels = raw13157Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13157 raw13157Labels permutation152 permutation3
    _ = mixedMoment B node3065 node3065Labels := by rfl

def raw13158 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![2, -1, -1]]
def raw13158Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13158step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -1, -1]]
def raw13158step0Labels : Fin 3 → Fin 2 := ![0, 1, 0]

def raw13158step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 2, 1], ![0, -1, 1], ![0, -1, 1], ![1, 1, -2], ![2, -1, -1]]
def raw13158step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13158 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13158 raw13158Labels = mixedMoment B node3078 node3078Labels := by
  calc
    mixedMoment B raw13158 raw13158Labels = mixedMoment B raw13158step0 raw13158step0Labels := by
      have hz : ∀ j, raw13158 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13158step0 = (fun i j => raw13158 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13158step0 raw13158; decide +kernel
      have hl : raw13158step0Labels = raw13158Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13158 raw13158Labels permutation520 hz
    mixedMoment B raw13158step0 raw13158step0Labels = mixedMoment B raw13158step1 raw13158step1Labels := by
      have ha : raw13158step1 = (fun i j => raw13158step0 (permutation32 i) (permutation3 j)) := by apply Matrix.ext; unfold raw13158step1 raw13158step0; decide +kernel
      have hl : raw13158step1Labels = raw13158step0Labels ∘ permutation3 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13158step0 raw13158step0Labels permutation32 permutation3
    _ = mixedMoment B node3078 node3078Labels := by rfl

def raw13159 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13159Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13159step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw13159step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13159step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13159step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13159step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13159step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13159 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13159 raw13159Labels = mixedMoment B node3880 node3880Labels := by
  calc
    mixedMoment B raw13159 raw13159Labels = mixedMoment B raw13159step0 raw13159step0Labels := by
      have ha : raw13159step0 = (fun i j => raw13159 (permutation212 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13159step0 raw13159; decide +kernel
      have hl : raw13159step0Labels = raw13159Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13159 raw13159Labels permutation212 permutation7
    mixedMoment B raw13159step0 raw13159step0Labels = mixedMoment B raw13159step1 raw13159step1Labels := by
      have ha : raw13159step1 = -raw13159step0 := by apply Matrix.ext; change ∀ i j, raw13159step1 i j = -(raw13159step0 i j); unfold raw13159step1 raw13159step0; decide +kernel
      have hl : raw13159step1Labels = raw13159step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13159step1 raw13159step1Labels = mixedMoment B raw13159step2 raw13159step2Labels := by
      have ha : raw13159step2 = raw13159step1 := by apply Matrix.ext; unfold raw13159step2 raw13159step1; decide +kernel
      have hl : raw13159step1Labels = labelEmbedding1 ∘ raw13159step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13159step1 raw13159step1Labels raw13159step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3880 node3880Labels := by rfl

def raw13160 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13160Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13160step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw13160step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13160step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13160step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13160step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13160step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13160 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13160 raw13160Labels = mixedMoment B node3880 node3880Labels := by
  calc
    mixedMoment B raw13160 raw13160Labels = mixedMoment B raw13160step0 raw13160step0Labels := by
      have ha : raw13160step0 = (fun i j => raw13160 (permutation214 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13160step0 raw13160; decide +kernel
      have hl : raw13160step0Labels = raw13160Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13160 raw13160Labels permutation214 permutation7
    mixedMoment B raw13160step0 raw13160step0Labels = mixedMoment B raw13160step1 raw13160step1Labels := by
      have ha : raw13160step1 = -raw13160step0 := by apply Matrix.ext; change ∀ i j, raw13160step1 i j = -(raw13160step0 i j); unfold raw13160step1 raw13160step0; decide +kernel
      have hl : raw13160step1Labels = raw13160step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13160step1 raw13160step1Labels = mixedMoment B raw13160step2 raw13160step2Labels := by
      have ha : raw13160step2 = raw13160step1 := by apply Matrix.ext; unfold raw13160step2 raw13160step1; decide +kernel
      have hl : raw13160step1Labels = labelEmbedding1 ∘ raw13160step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13160step1 raw13160step1Labels raw13160step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3880 node3880Labels := by rfl

def raw13161 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13161Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13161step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13161step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13161step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13161step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13161step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13161step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13161 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13161 raw13161Labels = mixedMoment B node3851 node3851Labels := by
  calc
    mixedMoment B raw13161 raw13161Labels = mixedMoment B raw13161step0 raw13161step0Labels := by
      have ha : raw13161step0 = (fun i j => raw13161 (permutation212 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13161step0 raw13161; decide +kernel
      have hl : raw13161step0Labels = raw13161Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13161 raw13161Labels permutation212 permutation7
    mixedMoment B raw13161step0 raw13161step0Labels = mixedMoment B raw13161step1 raw13161step1Labels := by
      have ha : raw13161step1 = -raw13161step0 := by apply Matrix.ext; change ∀ i j, raw13161step1 i j = -(raw13161step0 i j); unfold raw13161step1 raw13161step0; decide +kernel
      have hl : raw13161step1Labels = raw13161step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13161step1 raw13161step1Labels = mixedMoment B raw13161step2 raw13161step2Labels := by
      have ha : raw13161step2 = raw13161step1 := by apply Matrix.ext; unfold raw13161step2 raw13161step1; decide +kernel
      have hl : raw13161step1Labels = labelEmbedding1 ∘ raw13161step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13161step1 raw13161step1Labels raw13161step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3851 node3851Labels := by rfl

def raw13162 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1]]
def raw13162Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13162step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw13162step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13162step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13162step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13162step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13162step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13162step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13162step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13162 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13162 raw13162Labels = mixedMoment B node3887 node3887Labels := by
  calc
    mixedMoment B raw13162 raw13162Labels = mixedMoment B raw13162step0 raw13162step0Labels := by
      have hz : ∀ j, raw13162 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13162step0 = (fun i j => raw13162 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13162step0 raw13162; decide +kernel
      have hl : raw13162step0Labels = raw13162Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13162 raw13162Labels permutation520 hz
    mixedMoment B raw13162step0 raw13162step0Labels = mixedMoment B raw13162step1 raw13162step1Labels := by
      have ha : raw13162step1 = (fun i j => raw13162step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13162step1 raw13162step0; decide +kernel
      have hl : raw13162step1Labels = raw13162step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13162step0 raw13162step0Labels permutation44 permutation7
    mixedMoment B raw13162step1 raw13162step1Labels = mixedMoment B raw13162step2 raw13162step2Labels := by
      have ha : raw13162step2 = -raw13162step1 := by apply Matrix.ext; change ∀ i j, raw13162step2 i j = -(raw13162step1 i j); unfold raw13162step2 raw13162step1; decide +kernel
      have hl : raw13162step2Labels = raw13162step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13162step2 raw13162step2Labels = mixedMoment B raw13162step3 raw13162step3Labels := by
      have ha : raw13162step3 = raw13162step2 := by apply Matrix.ext; unfold raw13162step3 raw13162step2; decide +kernel
      have hl : raw13162step2Labels = labelEmbedding1 ∘ raw13162step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13162step2 raw13162step2Labels raw13162step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3887 node3887Labels := by rfl

def raw13163 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw13163Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13163step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 0, -2], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw13163step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13163step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13163step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13163step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, 0, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13163step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13163 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13163 raw13163Labels = mixedMoment B node3882 node3882Labels := by
  calc
    mixedMoment B raw13163 raw13163Labels = mixedMoment B raw13163step0 raw13163step0Labels := by
      have ha : raw13163step0 = (fun i j => raw13163 (permutation212 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13163step0 raw13163; decide +kernel
      have hl : raw13163step0Labels = raw13163Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13163 raw13163Labels permutation212 permutation7
    mixedMoment B raw13163step0 raw13163step0Labels = mixedMoment B raw13163step1 raw13163step1Labels := by
      have ha : raw13163step1 = -raw13163step0 := by apply Matrix.ext; change ∀ i j, raw13163step1 i j = -(raw13163step0 i j); unfold raw13163step1 raw13163step0; decide +kernel
      have hl : raw13163step1Labels = raw13163step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13163step1 raw13163step1Labels = mixedMoment B raw13163step2 raw13163step2Labels := by
      have ha : raw13163step2 = raw13163step1 := by apply Matrix.ext; unfold raw13163step2 raw13163step1; decide +kernel
      have hl : raw13163step1Labels = labelEmbedding1 ∘ raw13163step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13163step1 raw13163step1Labels raw13163step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3882 node3882Labels := by rfl

def raw13164 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13164Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13164step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13164step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13164step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13164step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13164step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13164step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13164 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13164 raw13164Labels = mixedMoment B node3289 node3289Labels := by
  calc
    mixedMoment B raw13164 raw13164Labels = mixedMoment B raw13164step0 raw13164step0Labels := by
      have ha : raw13164step0 = (fun i j => raw13164 (permutation181 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13164step0 raw13164; decide +kernel
      have hl : raw13164step0Labels = raw13164Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13164 raw13164Labels permutation181 permutation5
    mixedMoment B raw13164step0 raw13164step0Labels = mixedMoment B raw13164step1 raw13164step1Labels := by
      have ha : raw13164step1 = -raw13164step0 := by apply Matrix.ext; change ∀ i j, raw13164step1 i j = -(raw13164step0 i j); unfold raw13164step1 raw13164step0; decide +kernel
      have hl : raw13164step1Labels = raw13164step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13164step1 raw13164step1Labels = mixedMoment B raw13164step2 raw13164step2Labels := by
      have ha : raw13164step2 = raw13164step1 := by apply Matrix.ext; unfold raw13164step2 raw13164step1; decide +kernel
      have hl : raw13164step1Labels = labelEmbedding1 ∘ raw13164step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13164step1 raw13164step1Labels raw13164step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3289 node3289Labels := by rfl

def raw13165 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![-1, 2, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13165Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13165step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13165step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13165step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13165step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13165step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13165step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13165 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13165 raw13165Labels = mixedMoment B node3569 node3569Labels := by
  calc
    mixedMoment B raw13165 raw13165Labels = mixedMoment B raw13165step0 raw13165step0Labels := by
      have ha : raw13165step0 = (fun i j => raw13165 (permutation214 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13165step0 raw13165; decide +kernel
      have hl : raw13165step0Labels = raw13165Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13165 raw13165Labels permutation214 permutation7
    mixedMoment B raw13165step0 raw13165step0Labels = mixedMoment B raw13165step1 raw13165step1Labels := by
      have ha : raw13165step1 = -raw13165step0 := by apply Matrix.ext; change ∀ i j, raw13165step1 i j = -(raw13165step0 i j); unfold raw13165step1 raw13165step0; decide +kernel
      have hl : raw13165step1Labels = raw13165step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13165step1 raw13165step1Labels = mixedMoment B raw13165step2 raw13165step2Labels := by
      have ha : raw13165step2 = raw13165step1 := by apply Matrix.ext; unfold raw13165step2 raw13165step1; decide +kernel
      have hl : raw13165step1Labels = labelEmbedding1 ∘ raw13165step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13165step1 raw13165step1Labels raw13165step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3569 node3569Labels := by rfl

def raw13166 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13166Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13166step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13166step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13166step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13166step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13166step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13166step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13166 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13166 raw13166Labels = mixedMoment B node3532 node3532Labels := by
  calc
    mixedMoment B raw13166 raw13166Labels = mixedMoment B raw13166step0 raw13166step0Labels := by
      have ha : raw13166step0 = (fun i j => raw13166 (permutation214 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13166step0 raw13166; decide +kernel
      have hl : raw13166step0Labels = raw13166Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13166 raw13166Labels permutation214 permutation7
    mixedMoment B raw13166step0 raw13166step0Labels = mixedMoment B raw13166step1 raw13166step1Labels := by
      have ha : raw13166step1 = -raw13166step0 := by apply Matrix.ext; change ∀ i j, raw13166step1 i j = -(raw13166step0 i j); unfold raw13166step1 raw13166step0; decide +kernel
      have hl : raw13166step1Labels = raw13166step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13166step1 raw13166step1Labels = mixedMoment B raw13166step2 raw13166step2Labels := by
      have ha : raw13166step2 = raw13166step1 := by apply Matrix.ext; unfold raw13166step2 raw13166step1; decide +kernel
      have hl : raw13166step1Labels = labelEmbedding1 ∘ raw13166step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13166step1 raw13166step1Labels raw13166step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3532 node3532Labels := by rfl

def raw13167 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1]]
def raw13167Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13167step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1]]
def raw13167step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13167step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13167step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13167step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13167step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13167step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13167step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13167 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13167 raw13167Labels = mixedMoment B node3581 node3581Labels := by
  calc
    mixedMoment B raw13167 raw13167Labels = mixedMoment B raw13167step0 raw13167step0Labels := by
      have hz : ∀ j, raw13167 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13167step0 = (fun i j => raw13167 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13167step0 raw13167; decide +kernel
      have hl : raw13167step0Labels = raw13167Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13167 raw13167Labels permutation520 hz
    mixedMoment B raw13167step0 raw13167step0Labels = mixedMoment B raw13167step1 raw13167step1Labels := by
      have ha : raw13167step1 = (fun i j => raw13167step0 (permutation46 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13167step1 raw13167step0; decide +kernel
      have hl : raw13167step1Labels = raw13167step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13167step0 raw13167step0Labels permutation46 permutation7
    mixedMoment B raw13167step1 raw13167step1Labels = mixedMoment B raw13167step2 raw13167step2Labels := by
      have ha : raw13167step2 = -raw13167step1 := by apply Matrix.ext; change ∀ i j, raw13167step2 i j = -(raw13167step1 i j); unfold raw13167step2 raw13167step1; decide +kernel
      have hl : raw13167step2Labels = raw13167step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13167step2 raw13167step2Labels = mixedMoment B raw13167step3 raw13167step3Labels := by
      have ha : raw13167step3 = raw13167step2 := by apply Matrix.ext; unfold raw13167step3 raw13167step2; decide +kernel
      have hl : raw13167step2Labels = labelEmbedding1 ∘ raw13167step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13167step2 raw13167step2Labels raw13167step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3581 node3581Labels := by rfl

def raw13168 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![1, 0, -1], ![0, 1, -1], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw13168Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13168step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13168step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13168step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13168step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13168step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13168step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13168 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13168 raw13168Labels = mixedMoment B node3571 node3571Labels := by
  calc
    mixedMoment B raw13168 raw13168Labels = mixedMoment B raw13168step0 raw13168step0Labels := by
      have ha : raw13168step0 = (fun i j => raw13168 (permutation215 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13168step0 raw13168; decide +kernel
      have hl : raw13168step0Labels = raw13168Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13168 raw13168Labels permutation215 permutation7
    mixedMoment B raw13168step0 raw13168step0Labels = mixedMoment B raw13168step1 raw13168step1Labels := by
      have ha : raw13168step1 = -raw13168step0 := by apply Matrix.ext; change ∀ i j, raw13168step1 i j = -(raw13168step0 i j); unfold raw13168step1 raw13168step0; decide +kernel
      have hl : raw13168step1Labels = raw13168step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13168step1 raw13168step1Labels = mixedMoment B raw13168step2 raw13168step2Labels := by
      have ha : raw13168step2 = raw13168step1 := by apply Matrix.ext; unfold raw13168step2 raw13168step1; decide +kernel
      have hl : raw13168step1Labels = labelEmbedding1 ∘ raw13168step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13168step1 raw13168step1Labels raw13168step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3571 node3571Labels := by rfl

def raw13169 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13169Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13169step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![0, -1, 1], ![0, -1, 1], ![-1, 0, 1], ![-2, 1, 1]]
def raw13169step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13169step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13169step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13169step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![0, 1, -1], ![0, 1, -1], ![1, 0, -1], ![2, -1, -1]]
def raw13169step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13169 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13169 raw13169Labels = mixedMoment B node3289 node3289Labels := by
  calc
    mixedMoment B raw13169 raw13169Labels = mixedMoment B raw13169step0 raw13169step0Labels := by
      have ha : raw13169step0 = (fun i j => raw13169 (permutation157 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13169step0 raw13169; decide +kernel
      have hl : raw13169step0Labels = raw13169Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13169 raw13169Labels permutation157 permutation5
    mixedMoment B raw13169step0 raw13169step0Labels = mixedMoment B raw13169step1 raw13169step1Labels := by
      have ha : raw13169step1 = -raw13169step0 := by apply Matrix.ext; change ∀ i j, raw13169step1 i j = -(raw13169step0 i j); unfold raw13169step1 raw13169step0; decide +kernel
      have hl : raw13169step1Labels = raw13169step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13169step1 raw13169step1Labels = mixedMoment B raw13169step2 raw13169step2Labels := by
      have ha : raw13169step2 = raw13169step1 := by apply Matrix.ext; unfold raw13169step2 raw13169step1; decide +kernel
      have hl : raw13169step1Labels = labelEmbedding1 ∘ raw13169step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13169step1 raw13169step1Labels raw13169step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3289 node3289Labels := by rfl

def raw13170 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13170Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13170step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 2, -1], ![-1, 0, 1], ![-1, 0, 1]]
def raw13170step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13170step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13170step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13170step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![1, 0, -1], ![1, 0, -1]]
def raw13170step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13170 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13170 raw13170Labels = mixedMoment B node3569 node3569Labels := by
  calc
    mixedMoment B raw13170 raw13170Labels = mixedMoment B raw13170step0 raw13170step0Labels := by
      have ha : raw13170step0 = (fun i j => raw13170 (permutation212 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13170step0 raw13170; decide +kernel
      have hl : raw13170step0Labels = raw13170Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13170 raw13170Labels permutation212 permutation7
    mixedMoment B raw13170step0 raw13170step0Labels = mixedMoment B raw13170step1 raw13170step1Labels := by
      have ha : raw13170step1 = -raw13170step0 := by apply Matrix.ext; change ∀ i j, raw13170step1 i j = -(raw13170step0 i j); unfold raw13170step1 raw13170step0; decide +kernel
      have hl : raw13170step1Labels = raw13170step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13170step1 raw13170step1Labels = mixedMoment B raw13170step2 raw13170step2Labels := by
      have ha : raw13170step2 = raw13170step1 := by apply Matrix.ext; unfold raw13170step2 raw13170step1; decide +kernel
      have hl : raw13170step1Labels = labelEmbedding1 ∘ raw13170step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13170step1 raw13170step1Labels raw13170step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3569 node3569Labels := by rfl

def raw13171 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![0, -1, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13171Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13171step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -1, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13171step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13171step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13171step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13171step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 1, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13171step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13171 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13171 raw13171Labels = mixedMoment B node3532 node3532Labels := by
  calc
    mixedMoment B raw13171 raw13171Labels = mixedMoment B raw13171step0 raw13171step0Labels := by
      have ha : raw13171step0 = (fun i j => raw13171 (permutation212 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13171step0 raw13171; decide +kernel
      have hl : raw13171step0Labels = raw13171Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13171 raw13171Labels permutation212 permutation7
    mixedMoment B raw13171step0 raw13171step0Labels = mixedMoment B raw13171step1 raw13171step1Labels := by
      have ha : raw13171step1 = -raw13171step0 := by apply Matrix.ext; change ∀ i j, raw13171step1 i j = -(raw13171step0 i j); unfold raw13171step1 raw13171step0; decide +kernel
      have hl : raw13171step1Labels = raw13171step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13171step1 raw13171step1Labels = mixedMoment B raw13171step2 raw13171step2Labels := by
      have ha : raw13171step2 = raw13171step1 := by apply Matrix.ext; unfold raw13171step2 raw13171step1; decide +kernel
      have hl : raw13171step1Labels = labelEmbedding1 ∘ raw13171step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13171step1 raw13171step1Labels raw13171step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3532 node3532Labels := by rfl

def raw13172 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![0, 0, 0], ![1, 0, -1]]
def raw13172Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13172step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![1, 0, -1]]
def raw13172step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13172step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![-1, 1, 0], ![-1, 0, 1], ![-1, 0, 1]]
def raw13172step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13172step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13172step2Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13172step3 : Matrix (Fin 5) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![1, -1, 0], ![1, 0, -1], ![1, 0, -1]]
def raw13172step3Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13172 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13172 raw13172Labels = mixedMoment B node3581 node3581Labels := by
  calc
    mixedMoment B raw13172 raw13172Labels = mixedMoment B raw13172step0 raw13172step0Labels := by
      have hz : ∀ j, raw13172 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13172step0 = (fun i j => raw13172 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13172step0 raw13172; decide +kernel
      have hl : raw13172step0Labels = raw13172Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13172 raw13172Labels permutation520 hz
    mixedMoment B raw13172step0 raw13172step0Labels = mixedMoment B raw13172step1 raw13172step1Labels := by
      have ha : raw13172step1 = (fun i j => raw13172step0 (permutation44 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13172step1 raw13172step0; decide +kernel
      have hl : raw13172step1Labels = raw13172step0Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13172step0 raw13172step0Labels permutation44 permutation7
    mixedMoment B raw13172step1 raw13172step1Labels = mixedMoment B raw13172step2 raw13172step2Labels := by
      have ha : raw13172step2 = -raw13172step1 := by apply Matrix.ext; change ∀ i j, raw13172step2 i j = -(raw13172step1 i j); unfold raw13172step2 raw13172step1; decide +kernel
      have hl : raw13172step2Labels = raw13172step1Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13172step2 raw13172step2Labels = mixedMoment B raw13172step3 raw13172step3Labels := by
      have ha : raw13172step3 = raw13172step2 := by apply Matrix.ext; unfold raw13172step3 raw13172step2; decide +kernel
      have hl : raw13172step2Labels = labelEmbedding1 ∘ raw13172step3Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13172step2 raw13172step2Labels raw13172step3Labels labelEmbedding1 hl
    _ = mixedMoment B node3581 node3581Labels := by rfl

def raw13173 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![1, 0, -1], ![1, -2, 1], ![1, -1, 0], ![0, 1, -1]]
def raw13173Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13173step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -1, 1], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13173step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13173step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13173step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13173step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 1, -1], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13173step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13173 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13173 raw13173Labels = mixedMoment B node3571 node3571Labels := by
  calc
    mixedMoment B raw13173 raw13173Labels = mixedMoment B raw13173step0 raw13173step0Labels := by
      have ha : raw13173step0 = (fun i j => raw13173 (permutation213 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13173step0 raw13173; decide +kernel
      have hl : raw13173step0Labels = raw13173Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13173 raw13173Labels permutation213 permutation7
    mixedMoment B raw13173step0 raw13173step0Labels = mixedMoment B raw13173step1 raw13173step1Labels := by
      have ha : raw13173step1 = -raw13173step0 := by apply Matrix.ext; change ∀ i j, raw13173step1 i j = -(raw13173step0 i j); unfold raw13173step1 raw13173step0; decide +kernel
      have hl : raw13173step1Labels = raw13173step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13173step1 raw13173step1Labels = mixedMoment B raw13173step2 raw13173step2Labels := by
      have ha : raw13173step2 = raw13173step1 := by apply Matrix.ext; unfold raw13173step2 raw13173step1; decide +kernel
      have hl : raw13173step1Labels = labelEmbedding1 ∘ raw13173step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13173step1 raw13173step1Labels raw13173step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3571 node3571Labels := by rfl

def raw13174 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13174Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13174step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw13174step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13174step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![2, 2, -4]]
def raw13174step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13174 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13174 raw13174Labels = mixedMoment B node2457 node2457Labels := by
  calc
    mixedMoment B raw13174 raw13174Labels = mixedMoment B raw13174step0 raw13174step0Labels := by
      have ha : raw13174step0 = (fun i j => raw13174 (permutation502 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13174step0 raw13174; decide +kernel
      have hl : raw13174step0Labels = raw13174Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13174 raw13174Labels permutation502 permutation5
    mixedMoment B raw13174step0 raw13174step0Labels = mixedMoment B raw13174step1 raw13174step1Labels := by
      have ha : raw13174step1 = raw13174step0 := by apply Matrix.ext; unfold raw13174step1 raw13174step0; decide +kernel
      have hl : raw13174step0Labels = labelEmbedding1 ∘ raw13174step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13174step0 raw13174step0Labels raw13174step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2457 node2457Labels := by rfl

def raw13175 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13175Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13175step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw13175step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13175step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw13175step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13175 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13175 raw13175Labels = mixedMoment B node2460 node2460Labels := by
  calc
    mixedMoment B raw13175 raw13175Labels = mixedMoment B raw13175step0 raw13175step0Labels := by
      have ha : raw13175step0 = (fun i j => raw13175 (permutation503 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13175step0 raw13175; decide +kernel
      have hl : raw13175step0Labels = raw13175Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13175 raw13175Labels permutation503 permutation5
    mixedMoment B raw13175step0 raw13175step0Labels = mixedMoment B raw13175step1 raw13175step1Labels := by
      have ha : raw13175step1 = raw13175step0 := by apply Matrix.ext; unfold raw13175step1 raw13175step0; decide +kernel
      have hl : raw13175step0Labels = labelEmbedding1 ∘ raw13175step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13175step0 raw13175step0Labels raw13175step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2460 node2460Labels := by rfl

def raw13176 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![2, -3, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13176Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13176step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw13176step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13176step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![0, -1, 1], ![1, -1, 0], ![1, 2, -3], ![2, -1, -1]]
def raw13176step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13176 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13176 raw13176Labels = mixedMoment B node2460 node2460Labels := by
  calc
    mixedMoment B raw13176 raw13176Labels = mixedMoment B raw13176step0 raw13176step0Labels := by
      have ha : raw13176step0 = (fun i j => raw13176 (permutation501 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13176step0 raw13176; decide +kernel
      have hl : raw13176step0Labels = raw13176Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13176 raw13176Labels permutation501 permutation5
    mixedMoment B raw13176step0 raw13176step0Labels = mixedMoment B raw13176step1 raw13176step1Labels := by
      have ha : raw13176step1 = raw13176step0 := by apply Matrix.ext; unfold raw13176step1 raw13176step0; decide +kernel
      have hl : raw13176step0Labels = labelEmbedding1 ∘ raw13176step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13176step0 raw13176step0Labels raw13176step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2460 node2460Labels := by rfl

def raw13177 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![0, 0, 0], ![1, 0, -1]]
def raw13177Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13177step0 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![1, 0, -1]]
def raw13177step0Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13177step1 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13177step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13177step2 : Matrix (Fin 5) (Fin 3) ℤ := ![![-3, 1, 2], ![0, -1, 1], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13177step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13177 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13177 raw13177Labels = mixedMoment B node2738 node2738Labels := by
  calc
    mixedMoment B raw13177 raw13177Labels = mixedMoment B raw13177step0 raw13177step0Labels := by
      have hz : ∀ j, raw13177 (permutation520 0) j = 0 := by decide +kernel
      have ha : raw13177step0 = (fun i j => raw13177 (permutation520 i.succ) j) := by apply Matrix.ext; unfold raw13177step0 raw13177; decide +kernel
      have hl : raw13177step0Labels = raw13177Labels := by decide +kernel
      rw [ha, hl]
      exact delete_zero_row (by decide) B raw13177 raw13177Labels permutation520 hz
    mixedMoment B raw13177step0 raw13177step0Labels = mixedMoment B raw13177step1 raw13177step1Labels := by
      have ha : raw13177step1 = (fun i j => raw13177step0 (permutation125 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13177step1 raw13177step0; decide +kernel
      have hl : raw13177step1Labels = raw13177step0Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13177step0 raw13177step0Labels permutation125 permutation5
    mixedMoment B raw13177step1 raw13177step1Labels = mixedMoment B raw13177step2 raw13177step2Labels := by
      have ha : raw13177step2 = raw13177step1 := by apply Matrix.ext; unfold raw13177step2 raw13177step1; decide +kernel
      have hl : raw13177step1Labels = labelEmbedding1 ∘ raw13177step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13177step1 raw13177step1Labels raw13177step2Labels labelEmbedding1 hl
    _ = mixedMoment B node2738 node2738Labels := by rfl

def raw13178 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![2, -3, 1], ![1, -1, 0], ![0, 1, -1]]
def raw13178Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13178step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13178step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13178step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 0, 1], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0], ![1, 2, -3]]
def raw13178step1Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13178 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13178 raw13178Labels = mixedMoment B node2507 node2507Labels := by
  calc
    mixedMoment B raw13178 raw13178Labels = mixedMoment B raw13178step0 raw13178step0Labels := by
      have ha : raw13178step0 = (fun i j => raw13178 (permutation492 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13178step0 raw13178; decide +kernel
      have hl : raw13178step0Labels = raw13178Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13178 raw13178Labels permutation492 permutation5
    mixedMoment B raw13178step0 raw13178step0Labels = mixedMoment B raw13178step1 raw13178step1Labels := by
      have ha : raw13178step1 = raw13178step0 := by apply Matrix.ext; unfold raw13178step1 raw13178step0; decide +kernel
      have hl : raw13178step0Labels = labelEmbedding1 ∘ raw13178step1Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13178step0 raw13178step0Labels raw13178step1Labels labelEmbedding1 hl
    _ = mixedMoment B node2507 node2507Labels := by rfl

def raw13179 : Matrix (Fin 6) (Fin 3) ℤ := ![![-4, 2, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw13179Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13179step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 2, -4], ![1, -1, 0], ![1, -1, 0], ![0, -1, 1], ![-2, 1, 1], ![-2, 0, 2]]
def raw13179step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13179step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw13179step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13179step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -2, 4], ![-1, 1, 0], ![-1, 1, 0], ![0, 1, -1], ![2, -1, -1], ![2, 0, -2]]
def raw13179step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13179 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13179 raw13179Labels = mixedMoment B node3278 node3278Labels := by
  calc
    mixedMoment B raw13179 raw13179Labels = mixedMoment B raw13179step0 raw13179step0Labels := by
      have ha : raw13179step0 = (fun i j => raw13179 (permutation156 i) (permutation5 j)) := by apply Matrix.ext; unfold raw13179step0 raw13179; decide +kernel
      have hl : raw13179step0Labels = raw13179Labels ∘ permutation5 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13179 raw13179Labels permutation156 permutation5
    mixedMoment B raw13179step0 raw13179step0Labels = mixedMoment B raw13179step1 raw13179step1Labels := by
      have ha : raw13179step1 = -raw13179step0 := by apply Matrix.ext; change ∀ i j, raw13179step1 i j = -(raw13179step0 i j); unfold raw13179step1 raw13179step0; decide +kernel
      have hl : raw13179step1Labels = raw13179step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13179step1 raw13179step1Labels = mixedMoment B raw13179step2 raw13179step2Labels := by
      have ha : raw13179step2 = raw13179step1 := by apply Matrix.ext; unfold raw13179step2 raw13179step1; decide +kernel
      have hl : raw13179step1Labels = labelEmbedding1 ∘ raw13179step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13179step1 raw13179step1Labels raw13179step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3278 node3278Labels := by rfl

def raw13180 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![-1, 2, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw13180Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13180step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw13180step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13180step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13180step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13180step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13180step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13180 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13180 raw13180Labels = mixedMoment B node3574 node3574Labels := by
  calc
    mixedMoment B raw13180 raw13180Labels = mixedMoment B raw13180step0 raw13180step0Labels := by
      have ha : raw13180step0 = (fun i j => raw13180 (permutation212 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13180step0 raw13180; decide +kernel
      have hl : raw13180step0Labels = raw13180Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13180 raw13180Labels permutation212 permutation7
    mixedMoment B raw13180step0 raw13180step0Labels = mixedMoment B raw13180step1 raw13180step1Labels := by
      have ha : raw13180step1 = -raw13180step0 := by apply Matrix.ext; change ∀ i j, raw13180step1 i j = -(raw13180step0 i j); unfold raw13180step1 raw13180step0; decide +kernel
      have hl : raw13180step1Labels = raw13180step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13180step1 raw13180step1Labels = mixedMoment B raw13180step2 raw13180step2Labels := by
      have ha : raw13180step2 = raw13180step1 := by apply Matrix.ext; unfold raw13180step2 raw13180step1; decide +kernel
      have hl : raw13180step1Labels = labelEmbedding1 ∘ raw13180step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13180step1 raw13180step1Labels raw13180step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3574 node3574Labels := by rfl

def raw13181 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![-1, 2, -1], ![1, -2, 1], ![2, -2, 0], ![1, 0, -1]]
def raw13181Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13181step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -2, 2], ![-1, 2, -1], ![-1, 1, 0], ![-1, 0, 1]]
def raw13181step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13181step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13181step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13181step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -2, 1], ![1, -1, 0], ![1, 0, -1]]
def raw13181step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13181 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13181 raw13181Labels = mixedMoment B node3574 node3574Labels := by
  calc
    mixedMoment B raw13181 raw13181Labels = mixedMoment B raw13181step0 raw13181step0Labels := by
      have ha : raw13181step0 = (fun i j => raw13181 (permutation214 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13181step0 raw13181; decide +kernel
      have hl : raw13181step0Labels = raw13181Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13181 raw13181Labels permutation214 permutation7
    mixedMoment B raw13181step0 raw13181step0Labels = mixedMoment B raw13181step1 raw13181step1Labels := by
      have ha : raw13181step1 = -raw13181step0 := by apply Matrix.ext; change ∀ i j, raw13181step1 i j = -(raw13181step0 i j); unfold raw13181step1 raw13181step0; decide +kernel
      have hl : raw13181step1Labels = raw13181step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13181step1 raw13181step1Labels = mixedMoment B raw13181step2 raw13181step2Labels := by
      have ha : raw13181step2 = raw13181step1 := by apply Matrix.ext; unfold raw13181step2 raw13181step1; decide +kernel
      have hl : raw13181step1Labels = labelEmbedding1 ∘ raw13181step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13181step1 raw13181step1Labels raw13181step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3574 node3574Labels := by rfl

def raw13182 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![0, -1, 1], ![2, -2, 0], ![1, 0, -1]]
def raw13182Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13182step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -1, 0], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 0, 1]]
def raw13182step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13182step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13182step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13182step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 1, 0], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, 0, -1]]
def raw13182step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13182 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13182 raw13182Labels = mixedMoment B node3539 node3539Labels := by
  calc
    mixedMoment B raw13182 raw13182Labels = mixedMoment B raw13182step0 raw13182step0Labels := by
      have ha : raw13182step0 = (fun i j => raw13182 (permutation212 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13182step0 raw13182; decide +kernel
      have hl : raw13182step0Labels = raw13182Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13182 raw13182Labels permutation212 permutation7
    mixedMoment B raw13182step0 raw13182step0Labels = mixedMoment B raw13182step1 raw13182step1Labels := by
      have ha : raw13182step1 = -raw13182step0 := by apply Matrix.ext; change ∀ i j, raw13182step1 i j = -(raw13182step0 i j); unfold raw13182step1 raw13182step0; decide +kernel
      have hl : raw13182step1Labels = raw13182step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13182step1 raw13182step1Labels = mixedMoment B raw13182step2 raw13182step2Labels := by
      have ha : raw13182step2 = raw13182step1 := by apply Matrix.ext; unfold raw13182step2 raw13182step1; decide +kernel
      have hl : raw13182step1Labels = labelEmbedding1 ∘ raw13182step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13182step1 raw13182step1Labels raw13182step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3539 node3539Labels := by rfl

def raw13183 : Matrix (Fin 6) (Fin 3) ℤ := ![![-3, 1, 2], ![0, 1, -1], ![0, 1, -1], ![1, -2, 1], ![2, -2, 0], ![0, 1, -1]]
def raw13183Labels : Fin 3 → Fin 2 := ![0, 1, 1]

def raw13183step0 : Matrix (Fin 6) (Fin 3) ℤ := ![![2, 1, -3], ![1, -2, 1], ![0, -2, 2], ![-1, 1, 0], ![-1, 1, 0], ![-1, 1, 0]]
def raw13183step0Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13183step1 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13183step1Labels : Fin 3 → Fin 2 := ![1, 1, 0]

def raw13183step2 : Matrix (Fin 6) (Fin 3) ℤ := ![![-2, -1, 3], ![-1, 2, -1], ![0, 2, -2], ![1, -1, 0], ![1, -1, 0], ![1, -1, 0]]
def raw13183step2Labels : Fin 3 → Fin 2 := ![0, 0, 1]

theorem canonical13183 (B : Fin 7 → Basis) (_hB : IsMUBFamily B) :
    mixedMoment B raw13183 raw13183Labels = mixedMoment B node3576 node3576Labels := by
  calc
    mixedMoment B raw13183 raw13183Labels = mixedMoment B raw13183step0 raw13183step0Labels := by
      have ha : raw13183step0 = (fun i j => raw13183 (permutation212 i) (permutation7 j)) := by apply Matrix.ext; unfold raw13183step0 raw13183; decide +kernel
      have hl : raw13183step0Labels = raw13183Labels ∘ permutation7 := by decide +kernel
      rw [ha, hl]
      exact permute B raw13183 raw13183Labels permutation212 permutation7
    mixedMoment B raw13183step0 raw13183step0Labels = mixedMoment B raw13183step1 raw13183step1Labels := by
      have ha : raw13183step1 = -raw13183step0 := by apply Matrix.ext; change ∀ i j, raw13183step1 i j = -(raw13183step0 i j); unfold raw13183step1 raw13183step0; decide +kernel
      have hl : raw13183step1Labels = raw13183step0Labels := by decide +kernel
      rw [ha, hl]
      exact (mixedMoment_neg B _hB _ _).symm
    mixedMoment B raw13183step1 raw13183step1Labels = mixedMoment B raw13183step2 raw13183step2Labels := by
      have ha : raw13183step2 = raw13183step1 := by apply Matrix.ext; unfold raw13183step2 raw13183step1; decide +kernel
      have hl : raw13183step1Labels = labelEmbedding1 ∘ raw13183step2Labels := by decide +kernel
      rw [ha]
      exact rename_labels (by decide) B raw13183step1 raw13183step1Labels raw13183step2Labels labelEmbedding1 hl
    _ = mixedMoment B node3576 node3576Labels := by rfl

end MUB6.Certificate.MixedSemantics

end OAI
